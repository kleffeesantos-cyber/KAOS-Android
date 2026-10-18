// portal_daemon.cpp - roda como root e emula o Portal of Power via FunctionFS.
//
// Mudancas em relacao a versao anterior:
//  - ep0 e atendido o tempo todo (antes ficava parado ate abrir ep1/ep2,
//    e o host dava timeout no meio da enumeracao).
//  - I/O dos endpoints de dados em threads proprias (write no IN bloqueia
//    ate o host fazer poll, e isso travava o loop principal).
//  - Acks do ep0 na direcao certa: OUT = read(), IN = write(). Antes o ACK
//    de SET_IDLE/SET_REPORT era um write() em requisicao OUT, que gera STALL.
//  - SET_REPORT: os dados agora sao lidos do ep0 e tratados como comando.
//  - Strings do FunctionFS validas (antes sobravam bytes e o kernel pode recusar).
//  - Status 'S' no formato do portal real (2 bits por boneco + contador).
//  - Slots chegam do app pelo stdin: "LOAD <slot> <caminho>", "UNLOAD <slot>", "QUIT".
//  - Escritas do jogo (comando 'W') sao gravadas de volta no arquivo do boneco.
//
// Uso: portal_daemon [-v]     (-v = loga cada comando do jogo)

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <errno.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <sys/stat.h>
#include <endian.h>
#include <linux/usb/functionfs.h>
#include <linux/usb/ch9.h>

#ifndef htole32
#define htole32(x) (x)
#endif
#ifndef htole16
#define htole16(x) (x)
#endif

#define FFS_DIR      "/dev/usb-ffs/portal0"
#define MAX_SLOTS    2
#define SLOT_BYTES   1024
#define BLOCK_BYTES  16
#define REPORT_SIZE  32
#define QUEUE_LEN    64

static bool g_verbose = false;

#define LOGI(...) do { printf("[INFO] "); printf(__VA_ARGS__); printf("\n"); fflush(stdout); } while (0)
#define LOGE(...) do { fprintf(stderr, "[ERROR] "); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); \
                       printf("[ERROR] "); printf(__VA_ARGS__); printf("\n"); fflush(stdout); } while (0)
#define LOGV(...) do { if (g_verbose) { LOGI(__VA_ARGS__); } } while (0)

// Descritor de relatorio do portal original (29 bytes)
static const uint8_t hid_report_descriptor[] = {
    0x06, 0x00, 0xFF,        // Usage Page (Vendor 0xFF00)
    0x09, 0x01,              // Usage (1)
    0xA1, 0x01,              // Collection (Application)
    0x19, 0x01, 0x29, 0x40,  //   Usage Min 1, Max 0x40
    0x15, 0x00,              //   Logical Min 0
    0x26, 0xFF, 0x00,        //   Logical Max 255
    0x75, 0x08,              //   Report Size 8
    0x95, 0x20,              //   Report Count 32
    0x81, 0x00,              //   Input
    0x19, 0x01, 0x29, 0x40,  //   Usage Min 1, Max 0x40
    0x91, 0x00,              //   Output
    0xC0                     // End Collection
};

// ---------------------------------------------------------------- estado

enum { SLOT_EMPTY = 0, SLOT_PRESENT = 1, SLOT_REMOVED = 2, SLOT_ADDED = 3 };

struct PortalSlot {
    uint8_t data[SLOT_BYTES];
    char path[512];
    int status;
};

static PortalSlot g_slots[MAX_SLOTS];
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_cond = PTHREAD_COND_INITIALIZER;

struct Report { uint8_t b[REPORT_SIZE]; };
static Report g_queue[QUEUE_LEN];
static int g_qhead = 0, g_qcount = 0;
static uint8_t g_counter = 0;

static volatile bool g_running = true;
static int g_ep0 = -1;
static volatile int g_in_fd = -1;
static volatile int g_out_fd = -1;
static bool g_all_ready_sent = false;

// ---------------------------------------------------------------- fila / status
// Todas as funcoes *_locked exigem g_lock tomado.

static void push_locked(const uint8_t *report) {
    if (g_qcount >= QUEUE_LEN) return;
    memcpy(g_queue[(g_qhead + g_qcount) % QUEUE_LEN].b, report, REPORT_SIZE);
    g_qcount++;
    pthread_cond_signal(&g_cond);
}

// Formato real: 'S' + status(4 bytes LE, 2 bits por boneco) + contador + 0x01
static void build_status_locked(uint8_t out[REPORT_SIZE]) {
    memset(out, 0, REPORT_SIZE);
    out[0] = 'S';
    uint32_t st = 0;
    for (int i = 0; i < MAX_SLOTS; i++) {
        st |= (uint32_t)(g_slots[i].status & 3) << (2 * i);
        if (g_slots[i].status == SLOT_ADDED) g_slots[i].status = SLOT_PRESENT;
        else if (g_slots[i].status == SLOT_REMOVED) g_slots[i].status = SLOT_EMPTY;
    }
    out[1] = st & 0xFF;
    out[2] = (st >> 8) & 0xFF;
    out[3] = (st >> 16) & 0xFF;
    out[4] = (st >> 24) & 0xFF;
    out[5] = g_counter++;
    out[6] = 0x01;
}

static void persist_block_locked(int idx, int block) {
    if (g_slots[idx].path[0] == 0) return;
    int fd = open(g_slots[idx].path, O_WRONLY);
    if (fd < 0) {
        LOGV("persist: nao abriu %s (%s)", g_slots[idx].path, strerror(errno));
        return;
    }
    ssize_t r = pwrite(fd, &g_slots[idx].data[block * BLOCK_BYTES], BLOCK_BYTES, (off_t)block * BLOCK_BYTES);
    (void)r;
    close(fd);
}

// ---------------------------------------------------------------- slots (comandos do app)

static void load_slot(int idx, const char *path) {
    if (idx < 0 || idx >= MAX_SLOTS) { LOGE("LOAD: slot invalido %d", idx); return; }
    int fd = open(path, O_RDONLY);
    if (fd < 0) { LOGE("LOAD: nao abriu %s (%s)", path, strerror(errno)); return; }
    uint8_t tmp[SLOT_BYTES];
    ssize_t n = read(fd, tmp, sizeof(tmp));
    close(fd);
    if (n != SLOT_BYTES) { LOGE("LOAD: arquivo com %zd bytes (esperado %d)", n, SLOT_BYTES); return; }

    pthread_mutex_lock(&g_lock);
    memcpy(g_slots[idx].data, tmp, SLOT_BYTES);
    strncpy(g_slots[idx].path, path, sizeof(g_slots[idx].path) - 1);
    g_slots[idx].path[sizeof(g_slots[idx].path) - 1] = 0;
    g_slots[idx].status = SLOT_ADDED;
    pthread_mutex_unlock(&g_lock);
    LOGI("Slot %d carregado: %s", idx, path);
}

static void unload_slot(int idx) {
    if (idx < 0 || idx >= MAX_SLOTS) { LOGE("UNLOAD: slot invalido %d", idx); return; }
    pthread_mutex_lock(&g_lock);
    if (g_slots[idx].status & 1) g_slots[idx].status = SLOT_REMOVED;
    else g_slots[idx].status = SLOT_EMPTY;
    pthread_mutex_unlock(&g_lock);
    LOGI("Slot %d removido", idx);
}

// ---------------------------------------------------------------- protocolo do portal

static void handle_command(const uint8_t *d, size_t len) {
    if (len < 1) return;
    uint8_t r[REPORT_SIZE];
    memset(r, 0, sizeof(r));

    LOGV("cmd 0x%02x len=%zu", d[0], len);

    pthread_mutex_lock(&g_lock);
    switch (d[0]) {
        case 'R':   // Ready / reset
            r[0] = 'R'; r[1] = 0x02; r[2] = 0x1B;
            push_locked(r);
            break;

        case 'A':   // Activate
            r[0] = 'A'; r[1] = (len > 1) ? d[1] : 0x01; r[2] = 0xFF; r[3] = 0x77;
            push_locked(r);
            break;

        case 'C':   // LED color
            if (len >= 4) {
                r[0] = 'C'; r[1] = d[1]; r[2] = d[2]; r[3] = d[3];
                push_locked(r);
            }
            break;

        case 'J':   // Query (som)
            r[0] = 'J';
            push_locked(r);
            break;

        case 'L':   // Luz do portal Traptanium: sem resposta
            break;

        case 'M':   // Alto-falante
            r[0] = 'M'; r[1] = (len > 1) ? d[1] : 0x00; r[2] = 0x00; r[3] = 0x19;
            push_locked(r);
            break;

        case 'Q': { // Le um bloco do boneco
            if (len >= 3) {
                int idx = d[1] & 0x0F;
                int block = d[2];
                if (idx < MAX_SLOTS && (g_slots[idx].status & 1) && block < SLOT_BYTES / BLOCK_BYTES) {
                    r[0] = 'Q'; r[1] = 0x10 | idx; r[2] = block;
                    memcpy(&r[3], &g_slots[idx].data[block * BLOCK_BYTES], BLOCK_BYTES);
                    push_locked(r);
                }
            }
            break;
        }

        case 'S':   // Status
            build_status_locked(r);
            push_locked(r);
            break;

        case 'V':
            r[0] = 'V';
            push_locked(r);
            break;

        case 'W': { // Escreve um bloco no boneco
            if (len >= 3 + BLOCK_BYTES) {
                int idx = d[1] & 0x0F;
                int block = d[2];
                if (idx < MAX_SLOTS && (g_slots[idx].status & 1) && block < SLOT_BYTES / BLOCK_BYTES) {
                    memcpy(&g_slots[idx].data[block * BLOCK_BYTES], &d[3], BLOCK_BYTES);
                    persist_block_locked(idx, block);
                    r[0] = 'W'; r[1] = 0x10 | idx; r[2] = block;
                    push_locked(r);
                }
            }
            break;
        }

        default:
            LOGV("comando desconhecido 0x%02x", d[0]);
            break;
    }
    pthread_mutex_unlock(&g_lock);
}

// ---------------------------------------------------------------- threads de endpoint

// IN: envia respostas da fila; sem nada na fila, manda status a cada ~10 ms
// (o portal real manda status continuamente). O write bloqueia ate o host fazer poll.
static void *in_thread(void *) {
    while (g_running) {
        int fd = g_in_fd;
        if (fd < 0) { usleep(50000); continue; }

        uint8_t rep[REPORT_SIZE];
        pthread_mutex_lock(&g_lock);
        if (g_qcount == 0) {
            struct timespec ts;
            clock_gettime(CLOCK_REALTIME, &ts);
            ts.tv_nsec += 10 * 1000 * 1000;
            if (ts.tv_nsec >= 1000000000L) { ts.tv_sec++; ts.tv_nsec -= 1000000000L; }
            pthread_cond_timedwait(&g_cond, &g_lock, &ts);
        }
        if (g_qcount > 0) {
            memcpy(rep, g_queue[g_qhead].b, REPORT_SIZE);
            g_qhead = (g_qhead + 1) % QUEUE_LEN;
            g_qcount--;
        } else {
            build_status_locked(rep);
        }
        pthread_mutex_unlock(&g_lock);

        ssize_t w = write(fd, rep, REPORT_SIZE);
        if (w < 0) usleep(20000);   // host desconectado/desabilitado
    }
    return nullptr;
}

// OUT: comandos que o jogo manda pelo endpoint de interrupcao
static void *out_thread(void *) {
    uint8_t buf[64];
    while (g_running) {
        int fd = g_out_fd;
        if (fd < 0) { usleep(50000); continue; }
        ssize_t n = read(fd, buf, sizeof(buf));
        if (n > 0) handle_command(buf, (size_t)n);
        else if (n < 0) usleep(20000);
    }
    return nullptr;
}

static void try_open_endpoints() {
    if (g_in_fd < 0) {
        int fd = open(FFS_DIR "/ep1", O_RDWR);
        if (fd >= 0) { g_in_fd = fd; LOGI("ep1 (IN) aberto: fd=%d", fd); }
    }
    if (g_out_fd < 0) {
        int fd = open(FFS_DIR "/ep2", O_RDWR);
        if (fd >= 0) { g_out_fd = fd; LOGI("ep2 (OUT) aberto: fd=%d", fd); }
    }
    if (!g_all_ready_sent && g_in_fd >= 0 && g_out_fd >= 0) {
        g_all_ready_sent = true;
        printf("ALL_READY\n");
        fflush(stdout);
    }
}

// ---------------------------------------------------------------- descritores

struct __attribute__((packed)) HidClassDesc {
    uint8_t  bLength;
    uint8_t  bDescriptorType;
    uint16_t bcdHID;
    uint8_t  bCountryCode;
    uint8_t  bNumDescriptors;
    uint8_t  bDescriptorType2;
    uint16_t wDescriptorLength;
};

struct __attribute__((packed)) FuncDescs {
    struct usb_interface_descriptor intf;
    HidClassDesc hid;
    struct usb_endpoint_descriptor_no_audio ep_in;
    struct usb_endpoint_descriptor_no_audio ep_out;
};

struct __attribute__((packed)) AllDescs {
    struct usb_functionfs_descs_head_v2 header;
    __le32 fs_count;
    __le32 hs_count;
    FuncDescs fs;
    FuncDescs hs;
};

struct __attribute__((packed)) AllStrings {
    struct usb_functionfs_strings_head header;
    __le16 lang;
    char str[7];    // "Portal" + NUL
};

static void fill_func_descs(FuncDescs *d, uint8_t interval) {
    memset(d, 0, sizeof(*d));

    d->intf.bLength = USB_DT_INTERFACE_SIZE;
    d->intf.bDescriptorType = USB_DT_INTERFACE;
    d->intf.bInterfaceNumber = 0;
    d->intf.bAlternateSetting = 0;
    d->intf.bNumEndpoints = 2;
    d->intf.bInterfaceClass = 0x03;     // HID
    d->intf.bInterfaceSubClass = 0x00;
    d->intf.bInterfaceProtocol = 0x00;
    d->intf.iInterface = 0;

    d->hid.bLength = 9;
    d->hid.bDescriptorType = 0x21;      // HID
    d->hid.bcdHID = htole16(0x0111);
    d->hid.bCountryCode = 0x00;
    d->hid.bNumDescriptors = 1;
    d->hid.bDescriptorType2 = 0x22;     // Report
    d->hid.wDescriptorLength = htole16(sizeof(hid_report_descriptor));

    d->ep_in.bLength = USB_DT_ENDPOINT_SIZE;
    d->ep_in.bDescriptorType = USB_DT_ENDPOINT;
    d->ep_in.bEndpointAddress = USB_DIR_IN | 1;
    d->ep_in.bmAttributes = USB_ENDPOINT_XFER_INT;
    d->ep_in.wMaxPacketSize = htole16(REPORT_SIZE);
    d->ep_in.bInterval = interval;

    d->ep_out.bLength = USB_DT_ENDPOINT_SIZE;
    d->ep_out.bDescriptorType = USB_DT_ENDPOINT;
    d->ep_out.bEndpointAddress = USB_DIR_OUT | 2;
    d->ep_out.bmAttributes = USB_ENDPOINT_XFER_INT;
    d->ep_out.wMaxPacketSize = htole16(REPORT_SIZE);
    d->ep_out.bInterval = interval;
}

static int write_descriptors(int fd) {
    AllDescs descs;
    memset(&descs, 0, sizeof(descs));
    descs.header.magic = htole32(FUNCTIONFS_DESCRIPTORS_MAGIC_V2);
    descs.header.length = htole32(sizeof(descs));
    descs.header.flags = htole32(FUNCTIONFS_HAS_FS_DESC | FUNCTIONFS_HAS_HS_DESC);
    descs.fs_count = htole32(4);
    descs.hs_count = htole32(4);
    fill_func_descs(&descs.fs, 1);      // full-speed: 1 ms
    fill_func_descs(&descs.hs, 4);      // high-speed: 2^(4-1) microframes = 1 ms

    ssize_t ret = write(fd, &descs, sizeof(descs));
    if (ret < 0) {
        LOGE("Falha ao escrever descritores: %d (%s)", errno, strerror(errno));
        return -1;
    }
    LOGI("Descritores escritos: %zd bytes", ret);

    AllStrings strings;
    memset(&strings, 0, sizeof(strings));
    strings.header.magic = htole32(FUNCTIONFS_STRINGS_MAGIC);
    strings.header.length = htole32(sizeof(strings));
    strings.header.str_count = htole32(1);
    strings.header.lang_count = htole32(1);
    strings.lang = htole16(0x0409);
    memcpy(strings.str, "Portal", 7);

    ret = write(fd, &strings, sizeof(strings));
    if (ret < 0) {
        LOGE("Falha ao escrever strings: %d (%s)", errno, strerror(errno));
        return -1;
    }
    LOGI("Strings escritas: %zd bytes", ret);
    return 0;
}

// ---------------------------------------------------------------- ep0

static void handle_setup(const struct usb_ctrlrequest *s) {
    const uint8_t type = s->bRequestType & USB_TYPE_MASK;
    const bool dir_in = (s->bRequestType & USB_DIR_IN) != 0;
    const uint16_t wlen = s->wLength;

    LOGV("SETUP type=0x%02x req=0x%02x val=0x%04x idx=0x%04x len=%u",
         s->bRequestType, s->bRequest, s->wValue, s->wIndex, wlen);

    if (dir_in) {
        uint8_t resp[256];
        memset(resp, 0, sizeof(resp));
        int rlen = -1;

        if (type == USB_TYPE_STANDARD && s->bRequest == USB_REQ_GET_DESCRIPTOR) {
            uint8_t dtype = (s->wValue >> 8) & 0xFF;
            if (dtype == 0x21) {
                LOGI("GET_DESCRIPTOR: HID");
                const uint8_t hid[] = { 0x09, 0x21, 0x11, 0x01, 0x00, 0x01, 0x22,
                                        (uint8_t)(sizeof(hid_report_descriptor) & 0xFF),
                                        (uint8_t)(sizeof(hid_report_descriptor) >> 8) };
                memcpy(resp, hid, sizeof(hid));
                rlen = sizeof(hid);
            } else if (dtype == 0x22) {
                LOGI("GET_DESCRIPTOR: Report (%zu bytes)", sizeof(hid_report_descriptor));
                memcpy(resp, hid_report_descriptor, sizeof(hid_report_descriptor));
                rlen = sizeof(hid_report_descriptor);
            }
        } else if (type == USB_TYPE_CLASS) {
            if (s->bRequest == 0x01) {          // GET_REPORT
                uint8_t st[REPORT_SIZE];
                pthread_mutex_lock(&g_lock);
                build_status_locked(st);
                pthread_mutex_unlock(&g_lock);
                memcpy(resp, st, REPORT_SIZE);
                rlen = REPORT_SIZE;
            } else if (s->bRequest == 0x02) {   // GET_IDLE
                resp[0] = 0;
                rlen = 1;
            } else if (s->bRequest == 0x03) {   // GET_PROTOCOL
                resp[0] = 1;
                rlen = 1;
            }
        }

        if (rlen >= 0) {
            if (rlen > wlen) rlen = wlen;
            ssize_t w = write(g_ep0, resp, rlen);
            if (w < 0) LOGE("write ep0 falhou: %d (%s)", errno, strerror(errno));
        } else {
            LOGV("requisicao IN nao suportada: STALL");
            char dummy;
            ssize_t r = read(g_ep0, &dummy, 0);     // direcao errada = STALL
            (void)r;
        }
        return;
    }

    // Requisicao OUT (host -> device)
    bool known = (type == USB_TYPE_CLASS) &&
                 (s->bRequest == 0x09 || s->bRequest == 0x0A || s->bRequest == 0x0B);

    if (!known) {
        LOGV("requisicao OUT nao suportada: STALL");
        ssize_t w = write(g_ep0, NULL, 0);          // direcao errada = STALL
        (void)w;
        return;
    }

    uint8_t buf[256];
    size_t want = wlen < sizeof(buf) ? wlen : sizeof(buf);
    ssize_t n = read(g_ep0, buf, want);             // le o data stage / confirma o status stage
    if (n < 0) {
        LOGE("read ep0 falhou: %d (%s)", errno, strerror(errno));
        return;
    }
    if (s->bRequest == 0x09 && n > 0) {             // SET_REPORT = comando do jogo
        handle_command(buf, (size_t)n);
    }
}

static void handle_ep0_event() {
    struct usb_functionfs_event ev;
    ssize_t n = read(g_ep0, &ev, sizeof(ev));
    if (n != (ssize_t)sizeof(ev)) {
        if (n < 0 && errno != EAGAIN && errno != EINTR) {
            LOGE("read de evento do ep0 falhou: %d (%s)", errno, strerror(errno));
            g_running = false;
        }
        return;
    }

    switch (ev.type) {
        case FUNCTIONFS_BIND:
            LOGI("evento: BIND");
            break;
        case FUNCTIONFS_ENABLE:
            LOGI("evento: ENABLE (host configurou o dispositivo)");
            try_open_endpoints();
            break;
        case FUNCTIONFS_DISABLE:
            LOGI("evento: DISABLE");
            break;
        case FUNCTIONFS_SUSPEND:
            LOGI("evento: SUSPEND");
            break;
        case FUNCTIONFS_RESUME:
            LOGI("evento: RESUME");
            break;
        case FUNCTIONFS_UNBIND:
            LOGI("evento: UNBIND - encerrando");
            g_running = false;
            break;
        case FUNCTIONFS_SETUP:
            handle_setup(&ev.u.setup);
            break;
        default:
            LOGI("evento desconhecido: %d", ev.type);
            break;
    }
}

// ---------------------------------------------------------------- stdin (comandos do app)

static char g_inbuf[1024];
static size_t g_inlen = 0;
static bool g_stdin_open = true;

static void process_line(char *line) {
    size_t l = strlen(line);
    while (l > 0 && (line[l - 1] == '\r' || line[l - 1] == ' ')) line[--l] = 0;

    int slot;
    char path[512];
    if (sscanf(line, "LOAD %d %511[^\n]", &slot, path) == 2) load_slot(slot, path);
    else if (sscanf(line, "UNLOAD %d", &slot) == 1) unload_slot(slot);
    else if (strncmp(line, "QUIT", 4) == 0) g_running = false;
    else if (l > 0) LOGI("comando desconhecido do app: '%s'", line);
}

static void read_stdin() {
    ssize_t n = read(0, g_inbuf + g_inlen, sizeof(g_inbuf) - g_inlen - 1);
    if (n <= 0) { g_stdin_open = false; return; }
    g_inlen += (size_t)n;
    g_inbuf[g_inlen] = 0;

    char *start = g_inbuf;
    char *nl;
    while ((nl = strchr(start, '\n')) != NULL) {
        *nl = 0;
        process_line(start);
        start = nl + 1;
    }
    size_t rest = g_inlen - (size_t)(start - g_inbuf);
    memmove(g_inbuf, start, rest);
    g_inlen = rest;
    if (g_inlen >= sizeof(g_inbuf) - 1) g_inlen = 0;   // linha gigante: descarta
}

// ---------------------------------------------------------------- main

static void signal_handler(int) { g_running = false; }

int main(int argc, char *argv[]) {
    if (argc > 1 && strcmp(argv[1], "-v") == 0) g_verbose = true;

    FILE *log_file = fopen("/data/local/tmp/portal_daemon.log", "w");
    if (log_file) {
        dup2(fileno(log_file), STDERR_FILENO);
        setbuf(stderr, NULL);
    }

    fprintf(stderr, "=== Portal Daemon iniciando (PID %d, EUID %d) ===\n", getpid(), geteuid());
    if (geteuid() != 0) {
        LOGE("FATAL: precisa rodar como root (EUID=%d)", geteuid());
        return 1;
    }

    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
    signal(SIGPIPE, SIG_IGN);

    memset(g_slots, 0, sizeof(g_slots));

    LOGI("Abrindo ep0...");
    for (int retry = 0; retry < 15 && g_ep0 < 0; retry++) {
        g_ep0 = open(FFS_DIR "/ep0", O_RDWR);
        if (g_ep0 < 0) {
            fprintf(stderr, "ep0 falhou (%d/15): %d (%s)\n", retry + 1, errno, strerror(errno));
            sleep(1);
        }
    }
    if (g_ep0 < 0) {
        LOGE("FATAL: nao abriu ep0");
        return 1;
    }
    LOGI("ep0 aberto: fd=%d", g_ep0);

    if (write_descriptors(g_ep0) < 0) {
        LOGE("FATAL: falha ao escrever descritores/strings");
        return 1;
    }

    printf("READY\n");
    fflush(stdout);

    pthread_t t_in, t_out;
    pthread_create(&t_in, NULL, in_thread, NULL);
    pthread_create(&t_out, NULL, out_thread, NULL);
    pthread_detach(t_in);
    pthread_detach(t_out);

    // Loop principal: ep0 e stdin. O ep0 e atendido imediatamente, sem esperar endpoints.
    while (g_running) {
        struct pollfd fds[2];
        fds[0].fd = g_ep0;
        fds[0].events = POLLIN;
        fds[0].revents = 0;
        fds[1].fd = g_stdin_open ? 0 : -1;
        fds[1].events = POLLIN;
        fds[1].revents = 0;

        int pr = poll(fds, 2, 200);
        if (pr < 0) {
            if (errno == EINTR) continue;
            LOGE("poll falhou: %d (%s)", errno, strerror(errno));
            break;
        }

        try_open_endpoints();
        if (pr == 0) continue;

        if (fds[0].revents & (POLLERR | POLLHUP | POLLNVAL)) {
            LOGE("ep0 fechado/erro (revents=0x%x)", fds[0].revents);
            break;
        }
        if (fds[0].revents & POLLIN) handle_ep0_event();
        if (fds[1].revents & (POLLIN | POLLHUP)) read_stdin();
    }

    LOGI("Encerrando...");
    g_running = false;
    _exit(0);   // as threads de I/O podem estar bloqueadas no kernel
}
