#include "parser.h"
#include "lexer.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>

typedef struct {
    Lexer lx;
    Token cur;
    char *errbuf;
    size_t errsz;
    jmp_buf on_error;
} Parser;

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

static char *copy_range(const char *start, int len) {
    char *s = xmalloc((size_t)len + 1);
    memcpy(s, start, (size_t)len);
    s[len] = '\0';
    return s;
}

static void parse_error(Parser *p, int line, const char *fmt, const char *arg) {
    snprintf(p->errbuf, p->errsz, "parse error [line %d]: ", line);
    size_t off = strlen(p->errbuf);
    snprintf(p->errbuf + off, p->errsz - off, fmt, arg);
    longjmp(p->on_error, 1);
}

static void advance(Parser *p) {
    p->cur = lexer_next(&p->lx);
    if (p->cur.type == T_ERROR)
        parse_error(p, p->cur.line, "%s", p->cur.start);
}

static int check(Parser *p, TokType t) { return p->cur.type == t; }

static int match(Parser *p, TokType t) {
    if (!check(p, t)) return 0;
    advance(p);
    return 1;
}

static Token expect(Parser *p, TokType t, const char *what) {
    if (!check(p, t)) {
        char msg[128];
        snprintf(msg, sizeof msg, "expected %s but found %s",
                 what, token_type_name(p->cur.type));
        parse_error(p, p->cur.line, "%s", msg);
    }
    Token tok = p->cur;
    advance(p);
    return tok;
}

/* One extra token of lookahead (used to tell `fn name(...)` declarations
 * apart from anonymous `fn (...)` expressions). Cheap: the lexer is just
 * a pair of pointers, so we copy it and rewind. */
static Token peek2(Parser *p) {
    Lexer saved = p->lx;
    Token t = lexer_next(&saved);
    return t;
}

static Expr *new_expr(ExprKind kind, int line) {
    Expr *e = xmalloc(sizeof *e);
    memset(e, 0, sizeof *e);
    e->kind = kind;
    e->line = line;
    return e;
}

static Stmt *new_stmt(StmtKind kind, int line) {
    Stmt *s = xmalloc(sizeof *s);
    memset(s, 0, sizeof *s);
    s->kind = kind;
    s->line = line;
    return s;
}

/* --- expressions ------------------------------------------------------- */

static Expr *expression(Parser *p);
static Stmt *block(Parser *p);

static char *unescape_string(Parser *p, Token tok) {
    /* tok covers the quotes; produce contents with escapes resolved */
    const char *src = tok.start + 1;
    int n = tok.len - 2;
    char *out = xmalloc((size_t)n + 1);
    int j = 0;
    for (int i = 0; i < n; i++) {
        char c = src[i];
        if (c == '\\' && i + 1 < n) {
            i++;
            switch (src[i]) {
            case 'n': out[j++] = '\n'; break;
            case 't': out[j++] = '\t'; break;
            case 'r': out[j++] = '\r'; break;
            case '\\': out[j++] = '\\'; break;
            case '"': out[j++] = '"'; break;
            case '0': out[j++] = '\0'; break;
            default:
                parse_error(p, tok.line, "%s", "invalid escape sequence in string");
            }
        } else {
            out[j++] = c;
        }
    }
    out[j] = '\0';
    return out;
}

static Expr *fn_expr(Parser *p, char *name, int line) {
    /* 'fn' already consumed; name is NULL for anonymous functions */
    Expr *e = new_expr(EX_FN, line);
    e->as.fn.name = name;
    expect(p, T_LPAREN, "'(' after 'fn'");
    int cap = 4, count = 0;
    char **params = xmalloc(sizeof(char *) * (size_t)cap);
    if (!check(p, T_RPAREN)) {
        do {
            Token id = expect(p, T_IDENT, "parameter name");
            if (count == cap) {
                cap *= 2;
                params = realloc(params, sizeof(char *) * (size_t)cap);
                if (!params) { fprintf(stderr, "out of memory\n"); exit(1); }
            }
            params[count++] = copy_range(id.start, id.len);
        } while (match(p, T_COMMA));
    }
    expect(p, T_RPAREN, "')' after parameters");
    e->as.fn.params = params;
    e->as.fn.paramc = count;
    e->as.fn.body = block(p);
    return e;
}

static Expr *primary(Parser *p) {
    Token tok = p->cur;
    switch (tok.type) {
    case T_NUMBER: {
        advance(p);
        Expr *e = new_expr(EX_INT, tok.line);
        char *text = copy_range(tok.start, tok.len);
        e->as.int_val = strtoll(text, NULL, 10);
        free(text);
        return e;
    }
    case T_STRING: {
        advance(p);
        Expr *e = new_expr(EX_STR, tok.line);
        e->as.str_val = unescape_string(p, tok);
        return e;
    }
    case T_KW_TRUE: case T_KW_FALSE: {
        advance(p);
        Expr *e = new_expr(EX_BOOL, tok.line);
        e->as.bool_val = (tok.type == T_KW_TRUE);
        return e;
    }
    case T_KW_NULL:
        advance(p);
        return new_expr(EX_NULL, tok.line);
    case T_IDENT: {
        advance(p);
        Expr *e = new_expr(EX_VAR, tok.line);
        e->as.var_name = copy_range(tok.start, tok.len);
        return e;
    }
    case T_LPAREN: {
        advance(p);
        Expr *e = expression(p);
        expect(p, T_RPAREN, "')' after expression");
        return e;
    }
    case T_KW_FN:
        advance(p);
        return fn_expr(p, NULL, tok.line);
    default:
        parse_error(p, tok.line, "unexpected %s in expression",
                    token_type_name(tok.type));
        return NULL; /* unreachable */
    }
}

static Expr *call(Parser *p) {
    Expr *e = primary(p);
    while (check(p, T_LPAREN)) {
        int line = p->cur.line;
        advance(p);
        int cap = 4, count = 0;
        Expr **args = xmalloc(sizeof(Expr *) * (size_t)cap);
        if (!check(p, T_RPAREN)) {
            do {
                if (count == cap) {
                    cap *= 2;
                    args = realloc(args, sizeof(Expr *) * (size_t)cap);
                    if (!args) { fprintf(stderr, "out of memory\n"); exit(1); }
                }
                args[count++] = expression(p);
            } while (match(p, T_COMMA));
        }
        expect(p, T_RPAREN, "')' after arguments");
        Expr *c = new_expr(EX_CALL, line);
        c->as.call.callee = e;
        c->as.call.args = args;
        c->as.call.argc = count;
        e = c;
    }
    return e;
}

static Expr *unary(Parser *p) {
    if (check(p, T_MINUS) || check(p, T_BANG)) {
        Token op = p->cur;
        advance(p);
        Expr *e = new_expr(EX_UNARY, op.line);
        e->as.unary.op = op.type;
        e->as.unary.operand = unary(p);
        return e;
    }
    return call(p);
}

static Expr *binary_level(Parser *p, Expr *(*next)(Parser *),
                          const TokType *ops, int nops) {
    Expr *e = next(p);
    for (;;) {
        int matched = 0;
        for (int i = 0; i < nops; i++) {
            if (check(p, ops[i])) {
                Token op = p->cur;
                advance(p);
                Expr *b = new_expr(EX_BINARY, op.line);
                b->as.binary.op = op.type;
                b->as.binary.left = e;
                b->as.binary.right = next(p);
                e = b;
                matched = 1;
                break;
            }
        }
        if (!matched) return e;
    }
}

static Expr *factor(Parser *p) {
    static const TokType ops[] = { T_STAR, T_SLASH, T_PERCENT };
    return binary_level(p, unary, ops, 3);
}

static Expr *term(Parser *p) {
    static const TokType ops[] = { T_PLUS, T_MINUS };
    return binary_level(p, factor, ops, 2);
}

static Expr *comparison(Parser *p) {
    static const TokType ops[] = { T_LT, T_LE, T_GT, T_GE };
    return binary_level(p, term, ops, 4);
}

static Expr *equality(Parser *p) {
    static const TokType ops[] = { T_EQ_EQ, T_BANG_EQ };
    return binary_level(p, comparison, ops, 2);
}

static Expr *logic_and(Parser *p) {
    Expr *e = equality(p);
    while (check(p, T_AND_AND)) {
        int line = p->cur.line;
        advance(p);
        Expr *l = new_expr(EX_LOGICAL, line);
        l->as.logical.op = T_AND_AND;
        l->as.logical.left = e;
        l->as.logical.right = equality(p);
        e = l;
    }
    return e;
}

static Expr *logic_or(Parser *p) {
    Expr *e = logic_and(p);
    while (check(p, T_OR_OR)) {
        int line = p->cur.line;
        advance(p);
        Expr *l = new_expr(EX_LOGICAL, line);
        l->as.logical.op = T_OR_OR;
        l->as.logical.left = e;
        l->as.logical.right = logic_and(p);
        e = l;
    }
    return e;
}

static Expr *assignment(Parser *p) {
    Expr *e = logic_or(p);
    if (check(p, T_EQ)) {
        Token eq = p->cur;
        advance(p);
        if (e->kind != EX_VAR)
            parse_error(p, eq.line, "%s", "invalid assignment target");
        Expr *a = new_expr(EX_ASSIGN, eq.line);
        a->as.assign.name = e->as.var_name;
        a->as.assign.value = assignment(p);
        return a;
    }
    return e;
}

static Expr *expression(Parser *p) { return assignment(p); }

/* --- statements -------------------------------------------------------- */

static Stmt *statement(Parser *p);
static Stmt *declaration(Parser *p);

static Stmt *block(Parser *p) {
    Token open = expect(p, T_LBRACE, "'{'");
    int cap = 8, count = 0;
    Stmt **stmts = xmalloc(sizeof(Stmt *) * (size_t)cap);
    while (!check(p, T_RBRACE) && !check(p, T_EOF)) {
        if (count == cap) {
            cap *= 2;
            stmts = realloc(stmts, sizeof(Stmt *) * (size_t)cap);
            if (!stmts) { fprintf(stderr, "out of memory\n"); exit(1); }
        }
        stmts[count++] = declaration(p);
    }
    expect(p, T_RBRACE, "'}' after block");
    Stmt *s = new_stmt(ST_BLOCK, open.line);
    s->as.block.stmts = stmts;
    s->as.block.count = count;
    return s;
}

static Stmt *var_decl(Parser *p) {
    int line = p->cur.line;
    advance(p); /* 'var' */
    Token id = expect(p, T_IDENT, "variable name");
    Stmt *s = new_stmt(ST_VAR, line);
    s->as.var_decl.name = copy_range(id.start, id.len);
    s->as.var_decl.init = match(p, T_EQ) ? expression(p) : NULL;
    expect(p, T_SEMI, "';' after variable declaration");
    return s;
}

static Stmt *if_stmt(Parser *p) {
    int line = p->cur.line;
    advance(p); /* 'if' */
    expect(p, T_LPAREN, "'(' after 'if'");
    Stmt *s = new_stmt(ST_IF, line);
    s->as.if_stmt.cond = expression(p);
    expect(p, T_RPAREN, "')' after if condition");
    s->as.if_stmt.then_branch = statement(p);
    s->as.if_stmt.else_branch = match(p, T_KW_ELSE) ? statement(p) : NULL;
    return s;
}

static Stmt *while_stmt(Parser *p) {
    int line = p->cur.line;
    advance(p); /* 'while' */
    expect(p, T_LPAREN, "'(' after 'while'");
    Stmt *s = new_stmt(ST_WHILE, line);
    s->as.while_stmt.cond = expression(p);
    expect(p, T_RPAREN, "')' after while condition");
    s->as.while_stmt.body = statement(p);
    return s;
}

static Stmt *for_stmt(Parser *p) {
    int line = p->cur.line;
    advance(p); /* 'for' */
    expect(p, T_LPAREN, "'(' after 'for'");
    Stmt *s = new_stmt(ST_FOR, line);

    if (match(p, T_SEMI)) {
        s->as.for_stmt.init = NULL;
    } else if (check(p, T_KW_VAR)) {
        s->as.for_stmt.init = var_decl(p);
    } else {
        Stmt *init = new_stmt(ST_EXPR, p->cur.line);
        init->as.expr = expression(p);
        expect(p, T_SEMI, "';' after for-loop initializer");
        s->as.for_stmt.init = init;
    }

    s->as.for_stmt.cond = check(p, T_SEMI) ? NULL : expression(p);
    expect(p, T_SEMI, "';' after for-loop condition");
    s->as.for_stmt.step = check(p, T_RPAREN) ? NULL : expression(p);
    expect(p, T_RPAREN, "')' after for-loop clauses");
    s->as.for_stmt.body = statement(p);
    return s;
}

static Stmt *statement(Parser *p) {
    switch (p->cur.type) {
    case T_LBRACE: return block(p);
    case T_KW_IF: return if_stmt(p);
    case T_KW_WHILE: return while_stmt(p);
    case T_KW_FOR: return for_stmt(p);
    case T_KW_RETURN: {
        int line = p->cur.line;
        advance(p);
        Stmt *s = new_stmt(ST_RETURN, line);
        s->as.expr = check(p, T_SEMI) ? NULL : expression(p);
        expect(p, T_SEMI, "';' after return value");
        return s;
    }
    case T_KW_BREAK: {
        Stmt *s = new_stmt(ST_BREAK, p->cur.line);
        advance(p);
        expect(p, T_SEMI, "';' after 'break'");
        return s;
    }
    case T_KW_CONTINUE: {
        Stmt *s = new_stmt(ST_CONTINUE, p->cur.line);
        advance(p);
        expect(p, T_SEMI, "';' after 'continue'");
        return s;
    }
    default: {
        Stmt *s = new_stmt(ST_EXPR, p->cur.line);
        s->as.expr = expression(p);
        expect(p, T_SEMI, "';' after expression");
        return s;
    }
    }
}

static Stmt *declaration(Parser *p) {
    if (check(p, T_KW_VAR)) return var_decl(p);
    if (check(p, T_KW_FN) && peek2(p).type == T_IDENT) {
        /* `fn name(params) { ... }` declares a variable bound to a
         * function value; anonymous `fn (...) {...}` falls through to the
         * expression parser. */
        int line = p->cur.line;
        advance(p); /* 'fn' */
        Token id = expect(p, T_IDENT, "function name");
        char *name = copy_range(id.start, id.len);
        Stmt *s = new_stmt(ST_VAR, line);
        s->as.var_decl.name = name;
        s->as.var_decl.init = fn_expr(p, name, line);
        return s;
    }
    return statement(p);
}

Stmt **parse_program(const char *src, int *count, char *errbuf, size_t errsz) {
    Parser p;
    p.errbuf = errbuf;
    p.errsz = errsz;
    lexer_init(&p.lx, src);
    if (setjmp(p.on_error)) return NULL;
    advance(&p);

    int cap = 16, n = 0;
    Stmt **stmts = xmalloc(sizeof(Stmt *) * (size_t)cap);
    while (!check(&p, T_EOF)) {
        if (n == cap) {
            cap *= 2;
            stmts = realloc(stmts, sizeof(Stmt *) * (size_t)cap);
            if (!stmts) { fprintf(stderr, "out of memory\n"); exit(1); }
        }
        stmts[n++] = declaration(&p);
    }
    *count = n;
    return stmts;
}
