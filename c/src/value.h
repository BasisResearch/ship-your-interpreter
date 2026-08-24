#ifndef WHILE_VALUE_H
#define WHILE_VALUE_H

#include "ast.h"
#include <stdio.h>

typedef struct Env Env;
typedef struct Interp Interp;
typedef struct Value Value;
typedef struct Closure Closure;

typedef Value (*NativeFn)(Interp *in, int argc, Value *args, int line);

typedef enum { VAL_NULL, VAL_BOOL, VAL_INT, VAL_STR, VAL_FN, VAL_NATIVE } ValueKind;

struct Value {
    ValueKind kind;
    union {
        int b;
        long long i;
        char *s;
        Closure *fn;
        struct { const char *name; NativeFn fn; } native;
    } as;
};

struct Closure {
    Expr *fn_expr;  /* EX_FN node: params + body (+ optional name) */
    Env *env;       /* environment the function was created in */
};

Value value_null(void);
Value value_bool(int b);
Value value_int(long long i);
Value value_str(char *s);       /* takes ownership of s */

int value_truthy(Value v);
int value_equal(Value a, Value b);
void value_print(Value v, FILE *out);
const char *value_kind_name(Value v);

#endif
