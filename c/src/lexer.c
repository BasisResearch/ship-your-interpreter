#include "lexer.h"
#include <string.h>
#include <ctype.h>

void lexer_init(Lexer *lx, const char *src) {
    lx->cur = src;
    lx->line = 1;
}

static Token make_tok(Lexer *lx, TokType type, const char *start) {
    Token t;
    t.type = type;
    t.start = start;
    t.len = (int)(lx->cur - start);
    t.line = lx->line;
    return t;
}

static Token error_tok(Lexer *lx, const char *msg) {
    Token t;
    t.type = T_ERROR;
    t.start = msg;
    t.len = (int)strlen(msg);
    t.line = lx->line;
    return t;
}

/* Skip whitespace and comments. Returns an error message for an
 * unterminated block comment, NULL otherwise. */
static const char *skip_ws(Lexer *lx) {
    for (;;) {
        char c = *lx->cur;
        if (c == ' ' || c == '\t' || c == '\r') {
            lx->cur++;
        } else if (c == '\n') {
            lx->line++;
            lx->cur++;
        } else if (c == '/' && lx->cur[1] == '/') {
            while (*lx->cur && *lx->cur != '\n') lx->cur++;
        } else if (c == '/' && lx->cur[1] == '*') {
            lx->cur += 2;
            while (*lx->cur && !(lx->cur[0] == '*' && lx->cur[1] == '/')) {
                if (*lx->cur == '\n') lx->line++;
                lx->cur++;
            }
            if (!*lx->cur) return "unterminated block comment";
            lx->cur += 2;
        } else {
            return 0;
        }
    }
}

static const struct { const char *word; TokType type; } keywords[] = {
    {"var", T_KW_VAR}, {"fn", T_KW_FN}, {"if", T_KW_IF}, {"else", T_KW_ELSE},
    {"while", T_KW_WHILE}, {"for", T_KW_FOR}, {"return", T_KW_RETURN},
    {"break", T_KW_BREAK}, {"continue", T_KW_CONTINUE},
    {"true", T_KW_TRUE}, {"false", T_KW_FALSE}, {"null", T_KW_NULL},
    {0, 0}
};

Token lexer_next(Lexer *lx) {
    const char *err = skip_ws(lx);
    if (err) return error_tok(lx, err);

    const char *start = lx->cur;
    char c = *lx->cur;
    if (!c) return make_tok(lx, T_EOF, start);
    lx->cur++;

    if (isdigit((unsigned char)c)) {
        while (isdigit((unsigned char)*lx->cur)) lx->cur++;
        return make_tok(lx, T_NUMBER, start);
    }

    if (isalpha((unsigned char)c) || c == '_') {
        while (isalnum((unsigned char)*lx->cur) || *lx->cur == '_') lx->cur++;
        int len = (int)(lx->cur - start);
        for (int i = 0; keywords[i].word; i++) {
            if ((int)strlen(keywords[i].word) == len &&
                memcmp(keywords[i].word, start, (size_t)len) == 0) {
                return make_tok(lx, keywords[i].type, start);
            }
        }
        return make_tok(lx, T_IDENT, start);
    }

    switch (c) {
    case '(': return make_tok(lx, T_LPAREN, start);
    case ')': return make_tok(lx, T_RPAREN, start);
    case '{': return make_tok(lx, T_LBRACE, start);
    case '}': return make_tok(lx, T_RBRACE, start);
    case ',': return make_tok(lx, T_COMMA, start);
    case ';': return make_tok(lx, T_SEMI, start);
    case '+': return make_tok(lx, T_PLUS, start);
    case '-': return make_tok(lx, T_MINUS, start);
    case '*': return make_tok(lx, T_STAR, start);
    case '/': return make_tok(lx, T_SLASH, start);
    case '%': return make_tok(lx, T_PERCENT, start);
    case '!':
        if (*lx->cur == '=') { lx->cur++; return make_tok(lx, T_BANG_EQ, start); }
        return make_tok(lx, T_BANG, start);
    case '=':
        if (*lx->cur == '=') { lx->cur++; return make_tok(lx, T_EQ_EQ, start); }
        return make_tok(lx, T_EQ, start);
    case '<':
        if (*lx->cur == '=') { lx->cur++; return make_tok(lx, T_LE, start); }
        return make_tok(lx, T_LT, start);
    case '>':
        if (*lx->cur == '=') { lx->cur++; return make_tok(lx, T_GE, start); }
        return make_tok(lx, T_GT, start);
    case '&':
        if (*lx->cur == '&') { lx->cur++; return make_tok(lx, T_AND_AND, start); }
        return error_tok(lx, "unexpected character '&' (did you mean '&&'?)");
    case '|':
        if (*lx->cur == '|') { lx->cur++; return make_tok(lx, T_OR_OR, start); }
        return error_tok(lx, "unexpected character '|' (did you mean '||'?)");
    case '"': {
        while (*lx->cur && *lx->cur != '"') {
            if (*lx->cur == '\n') lx->line++;
            if (*lx->cur == '\\' && lx->cur[1]) lx->cur++;
            lx->cur++;
        }
        if (!*lx->cur) return error_tok(lx, "unterminated string literal");
        lx->cur++; /* closing quote */
        return make_tok(lx, T_STRING, start);
    }
    default:
        return error_tok(lx, "unexpected character");
    }
}

const char *token_type_name(TokType t) {
    switch (t) {
    case T_EOF: return "end of input";
    case T_ERROR: return "error";
    case T_IDENT: return "identifier";
    case T_NUMBER: return "number";
    case T_STRING: return "string";
    case T_LPAREN: return "'('";
    case T_RPAREN: return "')'";
    case T_LBRACE: return "'{'";
    case T_RBRACE: return "'}'";
    case T_COMMA: return "','";
    case T_SEMI: return "';'";
    case T_PLUS: return "'+'";
    case T_MINUS: return "'-'";
    case T_STAR: return "'*'";
    case T_SLASH: return "'/'";
    case T_PERCENT: return "'%'";
    case T_BANG: return "'!'";
    case T_BANG_EQ: return "'!='";
    case T_EQ: return "'='";
    case T_EQ_EQ: return "'=='";
    case T_LT: return "'<'";
    case T_LE: return "'<='";
    case T_GT: return "'>'";
    case T_GE: return "'>='";
    case T_AND_AND: return "'&&'";
    case T_OR_OR: return "'||'";
    case T_KW_VAR: return "'var'";
    case T_KW_FN: return "'fn'";
    case T_KW_IF: return "'if'";
    case T_KW_ELSE: return "'else'";
    case T_KW_WHILE: return "'while'";
    case T_KW_FOR: return "'for'";
    case T_KW_RETURN: return "'return'";
    case T_KW_BREAK: return "'break'";
    case T_KW_CONTINUE: return "'continue'";
    case T_KW_TRUE: return "'true'";
    case T_KW_FALSE: return "'false'";
    case T_KW_NULL: return "'null'";
    }
    return "unknown";
}
