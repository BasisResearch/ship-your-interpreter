#include "parser.h"
#include "interp.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(WHILE_BAREMETAL) && !defined(WHILE_HTIF)
long semihost_call(long op, void *arg); /* semihost.c */
#endif
#ifdef WHILE_HTIF
extern const char _script_start[]; /* script.S; NUL-terminated */
#endif

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    size_t cap = 4096, len = 0;
    char *buf = malloc(cap);
    if (!buf) { fclose(f); return NULL; }
    for (;;) {
        if (len + 1024 + 1 > cap) {
            cap *= 2;
            char *nb = realloc(buf, cap);
            if (!nb) { free(buf); fclose(f); return NULL; }
            buf = nb;
        }
        size_t n = fread(buf + len, 1, 1024, f);
        len += n;
        if (n < 1024) break;
    }
    fclose(f);
    buf[len] = '\0';
    return buf;
}

static int run_source(Interp *in, const char *src, int repl_mode) {
    int count = 0;
    char err[256];
    Stmt **stmts = parse_program(src, &count, err, sizeof err);
    if (!stmts) {
        fprintf(stderr, "%s\n", err);
        return 65;
    }
    if (interp_run(in, stmts, count, repl_mode)) {
        fprintf(stderr, "%s\n", in->err_msg);
        return 70;
    }
    return 0;
}

static int run_file(const char *path) {
    char *src = read_file(path);
    if (!src) {
        fprintf(stderr, "error: cannot open '%s'\n", path);
        return 66;
    }
    Interp in;
    interp_init(&in);
    return run_source(&in, src, 0);
}

/* Net bracket depth of a chunk of source, ignoring strings and comments.
 * Used by the REPL to decide whether to keep reading continuation lines. */
static int bracket_depth(const char *s) {
    int depth = 0;
    while (*s) {
        char c = *s++;
        if (c == '/' && *s == '/') {
            while (*s && *s != '\n') s++;
        } else if (c == '/' && *s == '*') {
            s++;
            while (*s && !(s[0] == '*' && s[1] == '/')) s++;
            if (*s) s += 2;
        } else if (c == '"') {
            while (*s && *s != '"') {
                if (*s == '\\' && s[1]) s++;
                s++;
            }
            if (*s) s++;
        } else if (c == '(' || c == '{') {
            depth++;
        } else if (c == ')' || c == '}') {
            depth--;
        }
    }
    return depth;
}

static int repl(void) {
    printf("While language v1.0 -- C-style syntax, type ctrl-D to exit\n");
    Interp in;
    interp_init(&in);

    char line[1024];
    size_t cap = 4096;
    char *buf = malloc(cap);
    if (!buf) return 1;

    for (;;) {
        buf[0] = '\0';
        size_t len = 0;
        fputs("> ", stdout);
        fflush(stdout);
        for (;;) {
            if (!fgets(line, sizeof line, stdin)) {
                if (len == 0) { putchar('\n'); free(buf); return 0; }
                break; /* run whatever we have */
            }
            size_t ll = strlen(line);
            if (len + ll + 1 > cap) {
                cap = (len + ll + 1) * 2;
                char *nb = realloc(buf, cap);
                if (!nb) { free(buf); return 1; }
                buf = nb;
            }
            memcpy(buf + len, line, ll + 1);
            len += ll;
            if (bracket_depth(buf) <= 0) break;
            fputs(".. ", stdout);
            fflush(stdout);
        }
        if (buf[0] == '\0' || strspn(buf, " \t\r\n") == strlen(buf))
            continue;
        run_source(&in, buf, 1); /* errors are printed; REPL continues */
    }
}

#if defined(WHILE_BAREMETAL) && !defined(WHILE_HTIF)
/* Under qemu-system-riscv64 our crt0 passes argc==0. Fetch the command
 * line that was supplied via `-semihosting-config ...,arg=...` using the
 * SYS_GET_CMDLINE semihosting call and split it on spaces. */
#define SYS_GET_CMDLINE 0x15
static int fetch_cmdline(char ***argv_out) {
    static char cmdline[512];
    static char *argv[16];
    struct { char *buf; long size; } block = { cmdline, sizeof cmdline - 1 };
    if (semihost_call(SYS_GET_CMDLINE, &block) != 0) return 0;
    cmdline[sizeof cmdline - 1] = '\0';
    int argc = 0;
    char *p = cmdline;
    while (*p && argc < 15) {
        while (*p == ' ') p++;
        if (!*p) break;
        argv[argc++] = p;
        while (*p && *p != ' ') p++;
        if (*p) *p++ = '\0';
    }
    argv[argc] = NULL;
    *argv_out = argv;
    return argc;
}
#endif

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IONBF, 0);
#ifdef WHILE_HTIF
    (void)argc; (void)argv;
    Interp in;
    interp_init(&in);
    return run_source(&in, _script_start, 0);
#else
#ifdef WHILE_BAREMETAL
    if (argc <= 0 || !argv) argc = fetch_cmdline(&argv);
#endif
    if (argc >= 2) return run_file(argv[1]);
    return repl();
#endif
}
