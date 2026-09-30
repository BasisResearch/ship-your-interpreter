#ifndef WHILE_ENV_H
#define WHILE_ENV_H

#include "value.h"

struct Env {
    int count, cap;
    char **names;
    Value *vals;
    Env *parent;
};

Env *env_new(Env *parent);

void env_define(Env *env, const char *name, Value v);

int env_get(Env *env, const char *name, Value *out);

int env_set(Env *env, const char *name, Value v);

#endif
