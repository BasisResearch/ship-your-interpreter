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

int interp_run(Interp *in, Stmt **stmts, int count, int repl_mode);

#endif
