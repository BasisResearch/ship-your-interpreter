#ifndef WHILE_LEXER_H
#define WHILE_LEXER_H

typedef enum {
    T_EOF, T_ERROR,
    T_IDENT, T_NUMBER, T_STRING,
    T_LPAREN, T_RPAREN, T_LBRACE, T_RBRACE, T_COMMA, T_SEMI,
    T_PLUS, T_MINUS, T_STAR, T_SLASH, T_PERCENT,
    T_BANG, T_BANG_EQ, T_EQ, T_EQ_EQ, T_LT, T_LE, T_GT, T_GE,
    T_AND_AND, T_OR_OR,
    T_KW_VAR, T_KW_FN, T_KW_IF, T_KW_ELSE, T_KW_WHILE, T_KW_FOR,
    T_KW_RETURN, T_KW_BREAK, T_KW_CONTINUE, T_KW_TRUE, T_KW_FALSE, T_KW_NULL
} TokType;

typedef struct {
    TokType type;
    const char *start;  /* points into source; for T_ERROR: static message */
    int len;
    int line;
} Token;

typedef struct {
    const char *cur;
    int line;
} Lexer;

void lexer_init(Lexer *lx, const char *src);
Token lexer_next(Lexer *lx);
const char *token_type_name(TokType t);

#endif
