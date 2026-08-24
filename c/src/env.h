#ifndef WHILE_ENV_H
#define WHILE_ENV_H

#include "value.h"

/* Lexical environment: a growable name/value table with a parent link.
 * Closures keep environments alive; nothing is freed (no GC by design). */
struct Env {
    int count, cap;
    char **names;
    Value *vals;
    Env *parent;
};

Env *env_new(Env *parent);
/* Define (or overwrite) name in this exact scope. */
void env_define(Env *env, const char *name, Value v);
/* Look up name here or in any ancestor. Returns 0 if not found. */
int env_get(Env *env, const char *name, Value *out);
/* Assign to an existing binding here or in any ancestor. 0 if not found. */
int env_set(Env *env, const char *name, Value v);

#endif
