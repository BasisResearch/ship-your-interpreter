#ifdef WHILE_HTIF

#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

volatile uint64_t tohost __attribute__((section(".tohost"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost"), aligned(8)));

#define HTIF_DEV_CONSOLE (1ULL << 56)
#define HTIF_CMD_WRITE   (1ULL << 48)

static void htif_putc(char c) {
    tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
}

ssize_t _write(int fd, const void *buf, size_t len) {
    (void)fd;
    const char *p = buf;
    for (size_t i = 0; i < len; i++) htif_putc(p[i]);
    return (ssize_t)len;
}

ssize_t _read(int fd, void *buf, size_t len) {
    (void)fd; (void)buf; (void)len;
    return 0;
}

int _open(const char *path, int flags, int mode) {
    (void)path; (void)flags; (void)mode;
    errno = ENOENT;
    return -1;
}

int _close(int fd) { (void)fd; return 0; }

off_t _lseek(int fd, off_t offset, int whence) {
    (void)fd; (void)offset; (void)whence;
    errno = ESPIPE;
    return -1;
}

int _fstat(int fd, struct stat *st) {
    memset(st, 0, sizeof *st);
    st->st_mode = (fd <= 2) ? S_IFCHR : S_IFREG;
    return 0;
}

int _isatty(int fd) { return fd <= 2; }

extern char _end[];
extern char __heap_end[];

void *_sbrk(ptrdiff_t incr) {
    static char *brk;
    if (!brk) brk = _end;
    if (brk + incr > __heap_end) { errno = ENOMEM; return (void *)-1; }
    char *prev = brk;
    brk += incr;
    return prev;
}

void _exit(int code) {
    tohost = ((uint64_t)(uint32_t)code << 1) | 1;
    for (;;) {}
}

int _kill(int pid, int sig) { (void)pid; (void)sig; errno = EINVAL; return -1; }
int _getpid(void) { return 1; }

#else

typedef int not_empty_translation_unit;
#endif
