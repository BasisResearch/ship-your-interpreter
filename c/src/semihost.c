/* RISC-V semihosting back end for newlib.
 *
 * Implements the low-level syscalls (_read, _write, _open, _sbrk, _exit,
 * ...) in terms of the RISC-V semihosting protocol, which QEMU serves
 * when started with `-semihosting-config enable=on`. This lets the
 * interpreter use ordinary stdio (printf, fgets, fopen on *host* files)
 * while running as a bare-metal kernel image. */
#ifdef WHILE_BAREMETAL

#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>

#define SYS_OPEN   0x01
#define SYS_CLOSE  0x02
#define SYS_WRITE  0x05
#define SYS_READ   0x06
#define SYS_SEEK   0x0A
#define SYS_FLEN   0x0C
#define SYS_EXIT   0x18

/* The magic slli/ebreak/srai sequence identifies a semihosting call. */
long semihost_call(long op, void *arg) {
    register long a0 asm("a0") = op;
    register long a1 asm("a1") = (long)arg;
    asm volatile(
        ".option push\n"
        ".option norvc\n"
        ".balign 16\n"
        "slli zero, zero, 0x1f\n"
        "ebreak\n"
        "srai zero, zero, 7\n"
        ".option pop\n"
        : "+r"(a0)
        : "r"(a1)
        : "memory");
    return a0;
}

/* --- fd table: newlib fds -> semihosting handles ----------------------- */

#define MAX_FDS 32
static long handles[MAX_FDS];
static int fd_used[MAX_FDS];

/* SYS_OPEN mode indices per the semihosting spec ("rb"=1, "wb"=5, ...) */
static long sh_open(const char *path, int mode_index) {
    struct { const char *path; long mode; long len; } block =
        { path, mode_index, (long)strlen(path) };
    return semihost_call(SYS_OPEN, &block);
}

static void ensure_std_fds(void) {
    if (fd_used[0]) return;
    /* ":tt" is the semihosting console; r for stdin, w for stdout/stderr */
    handles[0] = sh_open(":tt", 0);
    handles[1] = sh_open(":tt", 4);
    handles[2] = sh_open(":tt", 8);
    fd_used[0] = fd_used[1] = fd_used[2] = 1;
}

int _open(const char *path, int flags, int mode) {
    (void)mode;
    ensure_std_fds();
    int mode_index;
    int rw = flags & (O_RDONLY | O_WRONLY | O_RDWR);
    if (rw == O_RDONLY) mode_index = 1;                 /* "rb" */
    else if (flags & O_APPEND) mode_index = 9;          /* "ab" */
    else if (rw == O_WRONLY) mode_index = 5;            /* "wb" */
    else mode_index = (flags & O_CREAT) ? 7 : 3;        /* "w+b" / "r+b" */

    long h = sh_open(path, mode_index);
    if (h == -1) { errno = ENOENT; return -1; }
    for (int fd = 3; fd < MAX_FDS; fd++) {
        if (!fd_used[fd]) {
            fd_used[fd] = 1;
            handles[fd] = h;
            return fd;
        }
    }
    errno = EMFILE;
    return -1;
}

int _close(int fd) {
    if (fd < 0 || fd >= MAX_FDS || !fd_used[fd]) { errno = EBADF; return -1; }
    if (fd >= 3) {
        long block[1] = { handles[fd] };
        semihost_call(SYS_CLOSE, block);
        fd_used[fd] = 0;
    }
    return 0;
}

ssize_t _write(int fd, const void *buf, size_t len) {
    ensure_std_fds();
    if (fd < 0 || fd >= MAX_FDS || !fd_used[fd]) { errno = EBADF; return -1; }
    struct { long h; const void *buf; long len; } block =
        { handles[fd], buf, (long)len };
    long not_written = semihost_call(SYS_WRITE, &block);
    return (ssize_t)((long)len - not_written);
}

ssize_t _read(int fd, void *buf, size_t len) {
    ensure_std_fds();
    if (fd < 0 || fd >= MAX_FDS || !fd_used[fd]) { errno = EBADF; return -1; }
    struct { long h; void *buf; long len; } block =
        { handles[fd], buf, (long)len };
    long not_read = semihost_call(SYS_READ, &block);
    return (ssize_t)((long)len - not_read);
}

off_t _lseek(int fd, off_t offset, int whence) {
    if (fd < 0 || fd >= MAX_FDS || !fd_used[fd]) { errno = EBADF; return -1; }
    long pos = offset;
    if (whence == SEEK_END) {
        long flen_block[1] = { handles[fd] };
        long len = semihost_call(SYS_FLEN, flen_block);
        if (len < 0) { errno = EIO; return -1; }
        pos = len + offset;
    } else if (whence != SEEK_SET) {
        errno = EINVAL; /* SEEK_CUR unsupported (position not tracked) */
        return -1;
    }
    struct { long h; long pos; } block = { handles[fd], pos };
    if (semihost_call(SYS_SEEK, &block) < 0) { errno = EIO; return -1; }
    return (off_t)pos;
}

int _fstat(int fd, struct stat *st) {
    memset(st, 0, sizeof *st);
    st->st_mode = (fd <= 2) ? S_IFCHR : S_IFREG;
    return 0;
}

int _isatty(int fd) { return fd <= 2; }

/* --- heap -------------------------------------------------------------- */

extern char _end[];       /* from link.ld */
extern char __heap_end[];

void *_sbrk(ptrdiff_t incr) {
    static char *brk;
    if (!brk) brk = _end;
    if (brk + incr > __heap_end) { errno = ENOMEM; return (void *)-1; }
    char *prev = brk;
    brk += incr;
    return prev;
}

/* --- process ----------------------------------------------------------- */

void _exit(int code) {
    /* 64-bit semihosting SYS_EXIT: pointer to {reason, subcode} */
    long block[2] = { 0x20026 /* ADP_Stopped_ApplicationExit */, code };
    semihost_call(SYS_EXIT, block);
    for (;;) {}
}

int _kill(int pid, int sig) { (void)pid; (void)sig; errno = EINVAL; return -1; }
int _getpid(void) { return 1; }

#else
/* Host build: nothing here; the OS provides the syscalls. */
typedef int not_empty_translation_unit;
#endif
