#ifndef WHILE_INTERP_H
#define WHILE_INTERP_H

#include "ast.h"
#include "value.h"
#include "env.h"
#include <setjmp.h>

struct Interp {
    Env *globals;
    int call_depth;
    jmp_buf on_error;
    char err_msg[256];
};

void interp_init(Interp *in);

/* Execute a parsed program in the interpreter's global environment.
 * If repl_mode is nonzero, top-level expression statements print their
 * value (unless it is null). Returns 0 on success; on a runtime error
 * returns nonzero with a diagnostic in in->err_msg. */
int interp_run(Interp *in, Stmt **stmts, int count, int repl_mode);

#endif
