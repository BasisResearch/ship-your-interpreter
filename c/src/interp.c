#include "interp.h"
#include "lexer.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_CALL_DEPTH 1000
#define MAX_ARGS 32

typedef enum { EXEC_NORMAL, EXEC_BREAK, EXEC_CONTINUE, EXEC_RETURN } ExecStatus;

static ExecStatus exec_stmt(Interp *in, Stmt *s, Env *env, Value *ret);
static Value eval_expr(Interp *in, Expr *e, Env *env);

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

static void runtime_error(Interp *in, int line, const char *fmt,
                          const char *a1, const char *a2) {
    char body[192];
    snprintf(body, sizeof body, fmt, a1, a2);
    snprintf(in->err_msg, sizeof in->err_msg,
             "runtime error [line %d]: %s", line, body);
    longjmp(in->on_error, 1);
}

/* --- built-in functions ------------------------------------------------ */

static Value native_print(Interp *in, int argc, Value *args, int line) {
    (void)in; (void)line;
    for (int i = 0; i < argc; i++) {
        if (i > 0) fputc(' ', stdout);
        value_print(args[i], stdout);
    }
    return value_null();
}

static Value native_println(Interp *in, int argc, Value *args, int line) {
    native_print(in, argc, args, line);
    fputc('\n', stdout);
    return value_null();
}

static Value native_assert(Interp *in, int argc, Value *args, int line) {
    if (argc < 1 || argc > 2)
        runtime_error(in, line, "assert() takes 1 or 2 arguments", 0, 0);
    if (!value_truthy(args[0])) {
        const char *msg = (argc == 2 && args[1].kind == VAL_STR)
                              ? args[1].as.s : "assertion failed";
        runtime_error(in, line, "%s", msg, 0);
    }
    return value_null();
}

static void define_native(Interp *in, const char *name, NativeFn fn) {
    Value v;
    v.kind = VAL_NATIVE;
    v.as.native.name = name;
    v.as.native.fn = fn;
    env_define(in->globals, name, v);
}

void interp_init(Interp *in) {
    in->globals = env_new(NULL);
    in->call_depth = 0;
    in->err_msg[0] = '\0';
    define_native(in, "print", native_print);
    define_native(in, "println", native_println);
    define_native(in, "assert", native_assert);
}

/* --- expression evaluation --------------------------------------------- */

static long long int_operand(Interp *in, Value v, int line, const char *op) {
    if (v.kind != VAL_INT)
        runtime_error(in, line, "operand of '%s' must be an int, got %s",
                      op, value_kind_name(v));
    return v.as.i;
}

static char *stringify(Value v) {
    if (v.kind == VAL_STR) {
        char *s = xmalloc(strlen(v.as.s) + 1);
        strcpy(s, v.as.s);
        return s;
    }
    char buf[64];
    switch (v.kind) {
    case VAL_NULL: strcpy(buf, "null"); break;
    case VAL_BOOL: strcpy(buf, v.as.b ? "true" : "false"); break;
    case VAL_INT: snprintf(buf, sizeof buf, "%lld", v.as.i); break;
    case VAL_FN: {
        const char *name = v.as.fn->fn_expr->as.fn.name;
        if (name) snprintf(buf, sizeof buf, "<fn %s>", name);
        else strcpy(buf, "<fn>");
        break;
    }
    default: strcpy(buf, "<native fn>"); break;
    }
    char *s = xmalloc(strlen(buf) + 1);
    strcpy(s, buf);
    return s;
}

static Value eval_binary(Interp *in, Expr *e, Env *env) {
    Value l = eval_expr(in, e->as.binary.left, env);
    Value r = eval_expr(in, e->as.binary.right, env);
    int op = e->as.binary.op;
    int line = e->line;

    switch (op) {
    case T_PLUS:
        if (l.kind == VAL_STR || r.kind == VAL_STR) {
            char *ls = stringify(l), *rs = stringify(r);
            char *s = xmalloc(strlen(ls) + strlen(rs) + 1);
            strcpy(s, ls);
            strcat(s, rs);
            free(ls);
            free(rs);
            return value_str(s);
        }
        return value_int(int_operand(in, l, line, "+") +
                         int_operand(in, r, line, "+"));
    case T_MINUS:
        return value_int(int_operand(in, l, line, "-") -
                         int_operand(in, r, line, "-"));
    case T_STAR:
        return value_int(int_operand(in, l, line, "*") *
                         int_operand(in, r, line, "*"));
    case T_SLASH: {
        long long a = int_operand(in, l, line, "/");
        long long b = int_operand(in, r, line, "/");
        if (b == 0) runtime_error(in, line, "division by zero", 0, 0);
        return value_int(a / b);
    }
    case T_PERCENT: {
        long long a = int_operand(in, l, line, "%%");
        long long b = int_operand(in, r, line, "%%");
        if (b == 0) runtime_error(in, line, "modulo by zero", 0, 0);
        return value_int(a % b);
    }
    case T_EQ_EQ: return value_bool(value_equal(l, r));
    case T_BANG_EQ: return value_bool(!value_equal(l, r));
    case T_LT: case T_LE: case T_GT: case T_GE: {
        long long cmp;
        if (l.kind == VAL_STR && r.kind == VAL_STR) {
            cmp = strcmp(l.as.s, r.as.s);
        } else {
            const char *name = op == T_LT ? "<" : op == T_LE ? "<="
                             : op == T_GT ? ">" : ">=";
            long long a = int_operand(in, l, line, name);
            long long b = int_operand(in, r, line, name);
            cmp = (a > b) - (a < b);
        }
        switch (op) {
        case T_LT: return value_bool(cmp < 0);
        case T_LE: return value_bool(cmp <= 0);
        case T_GT: return value_bool(cmp > 0);
        default: return value_bool(cmp >= 0);
        }
    }
    default:
        runtime_error(in, line, "unknown binary operator", 0, 0);
        return value_null();
    }
}

static Value call_value(Interp *in, Value callee, int argc, Value *args,
                        int line) {
    if (callee.kind == VAL_NATIVE)
        return callee.as.native.fn(in, argc, args, line);

    if (callee.kind != VAL_FN)
        runtime_error(in, line, "cannot call a %s value",
                      value_kind_name(callee), 0);

    Closure *cl = callee.as.fn;
    Expr *fe = cl->fn_expr;
    if (argc != fe->as.fn.paramc) {
        char buf[96];
        snprintf(buf, sizeof buf, "%s expects %d argument(s), got %d",
                 fe->as.fn.name ? fe->as.fn.name : "<fn>",
                 fe->as.fn.paramc, argc);
        runtime_error(in, line, "%s", buf, 0);
    }
    if (++in->call_depth > MAX_CALL_DEPTH) {
        in->call_depth = 0;
        runtime_error(in, line, "stack overflow (call depth > 1000)", 0, 0);
    }

    Env *env = env_new(cl->env);
    for (int i = 0; i < argc; i++)
        env_define(env, fe->as.fn.params[i], args[i]);

    Value ret = value_null();
    Stmt *body = fe->as.fn.body;
    ExecStatus st = EXEC_NORMAL;
    for (int i = 0; i < body->as.block.count; i++) {
        st = exec_stmt(in, body->as.block.stmts[i], env, &ret);
        if (st != EXEC_NORMAL) break;
    }
    in->call_depth--;
    if (st == EXEC_BREAK || st == EXEC_CONTINUE)
        runtime_error(in, line, "'break'/'continue' outside of a loop", 0, 0);
    return st == EXEC_RETURN ? ret : value_null();
}

static Value eval_expr(Interp *in, Expr *e, Env *env) {
    switch (e->kind) {
    case EX_INT: return value_int(e->as.int_val);
    case EX_STR: return value_str(e->as.str_val);
    case EX_BOOL: return value_bool(e->as.bool_val);
    case EX_NULL: return value_null();
    case EX_VAR: {
        Value v;
        if (!env_get(env, e->as.var_name, &v))
            runtime_error(in, e->line, "undefined variable '%s'",
                          e->as.var_name, 0);
        return v;
    }
    case EX_ASSIGN: {
        Value v = eval_expr(in, e->as.assign.value, env);
        if (!env_set(env, e->as.assign.name, v))
            runtime_error(in, e->line,
                          "cannot assign to undefined variable '%s'"
                          " (declare it with 'var')", e->as.assign.name, 0);
        return v;
    }
    case EX_BINARY: return eval_binary(in, e, env);
    case EX_LOGICAL: {
        Value l = eval_expr(in, e->as.logical.left, env);
        if (e->as.logical.op == T_OR_OR) {
            if (value_truthy(l)) return value_bool(1);
            return value_bool(value_truthy(eval_expr(in, e->as.logical.right, env)));
        }
        if (!value_truthy(l)) return value_bool(0);
        return value_bool(value_truthy(eval_expr(in, e->as.logical.right, env)));
    }
    case EX_UNARY: {
        Value v = eval_expr(in, e->as.unary.operand, env);
        if (e->as.unary.op == T_MINUS)
            return value_int(-int_operand(in, v, e->line, "-"));
        return value_bool(!value_truthy(v));
    }
    case EX_CALL: {
        Value callee = eval_expr(in, e->as.call.callee, env);
        int argc = e->as.call.argc;
        if (argc > MAX_ARGS)
            runtime_error(in, e->line, "too many arguments (max 32)", 0, 0);
        Value args[MAX_ARGS];
        for (int i = 0; i < argc; i++)
            args[i] = eval_expr(in, e->as.call.args[i], env);
        return call_value(in, callee, argc, args, e->line);
    }
    case EX_FN: {
        Closure *cl = xmalloc(sizeof *cl);
        cl->fn_expr = e;
        cl->env = env;
        Value v;
        v.kind = VAL_FN;
        v.as.fn = cl;
        return v;
    }
    }
    runtime_error(in, e->line, "unknown expression kind", 0, 0);
    return value_null();
}

/* --- statement execution ----------------------------------------------- */

static ExecStatus exec_stmt(Interp *in, Stmt *s, Env *env, Value *ret) {
    switch (s->kind) {
    case ST_EXPR:
        eval_expr(in, s->as.expr, env);
        return EXEC_NORMAL;
    case ST_VAR: {
        Value v = s->as.var_decl.init
                      ? eval_expr(in, s->as.var_decl.init, env)
                      : value_null();
        env_define(env, s->as.var_decl.name, v);
        return EXEC_NORMAL;
    }
    case ST_BLOCK: {
        Env *inner = env_new(env);
        for (int i = 0; i < s->as.block.count; i++) {
            ExecStatus st = exec_stmt(in, s->as.block.stmts[i], inner, ret);
            if (st != EXEC_NORMAL) return st;
        }
        return EXEC_NORMAL;
    }
    case ST_IF: {
        if (value_truthy(eval_expr(in, s->as.if_stmt.cond, env)))
            return exec_stmt(in, s->as.if_stmt.then_branch, env, ret);
        if (s->as.if_stmt.else_branch)
            return exec_stmt(in, s->as.if_stmt.else_branch, env, ret);
        return EXEC_NORMAL;
    }
    case ST_WHILE:
        while (value_truthy(eval_expr(in, s->as.while_stmt.cond, env))) {
            ExecStatus st = exec_stmt(in, s->as.while_stmt.body, env, ret);
            if (st == EXEC_BREAK) break;
            if (st == EXEC_RETURN) return st;
        }
        return EXEC_NORMAL;
    case ST_FOR: {
        Env *outer = env_new(env); /* scope for the init variable */
        if (s->as.for_stmt.init)
            exec_stmt(in, s->as.for_stmt.init, outer, ret);
        for (;;) {
            if (s->as.for_stmt.cond &&
                !value_truthy(eval_expr(in, s->as.for_stmt.cond, outer)))
                break;
            ExecStatus st = exec_stmt(in, s->as.for_stmt.body, outer, ret);
            if (st == EXEC_BREAK) break;
            if (st == EXEC_RETURN) return st;
            if (s->as.for_stmt.step)
                eval_expr(in, s->as.for_stmt.step, outer);
        }
        return EXEC_NORMAL;
    }
    case ST_RETURN:
        *ret = s->as.expr ? eval_expr(in, s->as.expr, env) : value_null();
        return EXEC_RETURN;
    case ST_BREAK: return EXEC_BREAK;
    case ST_CONTINUE: return EXEC_CONTINUE;
    }
    return EXEC_NORMAL;
}

int interp_run(Interp *in, Stmt **stmts, int count, int repl_mode) {
    if (setjmp(in->on_error)) {
        in->call_depth = 0;
        return 1;
    }
    for (int i = 0; i < count; i++) {
        Stmt *s = stmts[i];
        if (repl_mode && s->kind == ST_EXPR) {
            Value v = eval_expr(in, s->as.expr, in->globals);
            if (v.kind != VAL_NULL) {
                value_print(v, stdout);
                fputc('\n', stdout);
            }
            continue;
        }
        Value ret = value_null();
        ExecStatus st = exec_stmt(in, s, in->globals, &ret);
        if (st == EXEC_RETURN) {
            snprintf(in->err_msg, sizeof in->err_msg,
                     "runtime error [line %d]: 'return' outside of a function",
                     s->line);
            return 1;
        }
        if (st == EXEC_BREAK || st == EXEC_CONTINUE) {
            snprintf(in->err_msg, sizeof in->err_msg,
                     "runtime error [line %d]: 'break'/'continue' outside of a loop",
                     s->line);
            return 1;
        }
    }
    return 0;
}
