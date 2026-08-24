#include "value.h"
#include <string.h>

Value value_null(void) {
    Value v;
    v.kind = VAL_NULL;
    v.as.i = 0;
    return v;
}

Value value_bool(int b) {
    Value v;
    v.kind = VAL_BOOL;
    v.as.b = b != 0;
    return v;
}

Value value_int(long long i) {
    Value v;
    v.kind = VAL_INT;
    v.as.i = i;
    return v;
}

Value value_str(char *s) {
    Value v;
    v.kind = VAL_STR;
    v.as.s = s;
    return v;
}

int value_truthy(Value v) {
    switch (v.kind) {
    case VAL_NULL: return 0;
    case VAL_BOOL: return v.as.b;
    case VAL_INT: return v.as.i != 0;
    default: return 1; /* strings and functions are truthy */
    }
}

int value_equal(Value a, Value b) {
    if (a.kind != b.kind) return 0;
    switch (a.kind) {
    case VAL_NULL: return 1;
    case VAL_BOOL: return a.as.b == b.as.b;
    case VAL_INT: return a.as.i == b.as.i;
    case VAL_STR: return strcmp(a.as.s, b.as.s) == 0;
    case VAL_FN: return a.as.fn == b.as.fn;
    case VAL_NATIVE: return a.as.native.fn == b.as.native.fn;
    }
    return 0;
}

void value_print(Value v, FILE *out) {
    switch (v.kind) {
    case VAL_NULL: fputs("null", out); break;
    case VAL_BOOL: fputs(v.as.b ? "true" : "false", out); break;
    case VAL_INT: fprintf(out, "%lld", v.as.i); break;
    case VAL_STR: fputs(v.as.s, out); break;
    case VAL_FN: {
        const char *name = v.as.fn->fn_expr->as.fn.name;
        if (name) fprintf(out, "<fn %s>", name);
        else fputs("<fn>", out);
        break;
    }
    case VAL_NATIVE: fprintf(out, "<native fn %s>", v.as.native.name); break;
    }
}

const char *value_kind_name(Value v) {
    switch (v.kind) {
    case VAL_NULL: return "null";
    case VAL_BOOL: return "bool";
    case VAL_INT: return "int";
    case VAL_STR: return "string";
    case VAL_FN: return "function";
    case VAL_NATIVE: return "native function";
    }
    return "unknown";
}
