#ifndef WHILE_AST_H
#define WHILE_AST_H

typedef struct Expr Expr;
typedef struct Stmt Stmt;

typedef enum {
    EX_INT, EX_STR, EX_BOOL, EX_NULL, EX_VAR,
    EX_ASSIGN, EX_BINARY, EX_LOGICAL, EX_UNARY, EX_CALL, EX_FN
} ExprKind;

struct Expr {
    ExprKind kind;
    int line;
    union {
        long long int_val;
        char *str_val;
        int bool_val;
        char *var_name;
        struct { char *name; Expr *value; } assign;
        struct { int op; Expr *left, *right; } binary;   /* op: TokType */
        struct { int op; Expr *left, *right; } logical;  /* && || */
        struct { int op; Expr *operand; } unary;         /* - ! */
        struct { Expr *callee; Expr **args; int argc; } call;
        struct { char *name; char **params; int paramc; Stmt *body; } fn;
    } as;
};

typedef enum {
    ST_EXPR, ST_VAR, ST_BLOCK, ST_IF, ST_WHILE, ST_FOR,
    ST_RETURN, ST_BREAK, ST_CONTINUE
} StmtKind;

struct Stmt {
    StmtKind kind;
    int line;
    union {
        Expr *expr;  /* ST_EXPR; ST_RETURN (may be NULL) */
        struct { char *name; Expr *init; } var_decl;     /* init may be NULL */
        struct { Stmt **stmts; int count; } block;
        struct { Expr *cond; Stmt *then_branch; Stmt *else_branch; } if_stmt;
        struct { Expr *cond; Stmt *body; } while_stmt;
        struct { Stmt *init; Expr *cond; Expr *step; Stmt *body; } for_stmt;
    } as;
};

#endif
