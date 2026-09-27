#include "env.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    return p;
}

Env *env_new(Env *parent) {
    Env *env = xmalloc(sizeof *env);
    env->count = 0;
    env->cap = 0;
    env->names = NULL;
    env->vals = NULL;
    env->parent = parent;
    return env;
}

void env_define(Env *env, const char *name, Value v) {
    for (int i = 0; i < env->count; i++) {
        if (strcmp(env->names[i], name) == 0) {
            env->vals[i] = v;
            return;
        }
    }
    if (env->count == env->cap) {
        env->cap = env->cap ? env->cap * 2 : 8;
        env->names = realloc(env->names, sizeof(char *) * (size_t)env->cap);
        env->vals = realloc(env->vals, sizeof(Value) * (size_t)env->cap);
        if (!env->names || !env->vals) { fprintf(stderr, "out of memory\n"); exit(1); }
    }
    char *copy = xmalloc(strlen(name) + 1);
    strcpy(copy, name);
    env->names[env->count] = copy;
    env->vals[env->count] = v;
    env->count++;
}

int env_get(Env *env, const char *name, Value *out) {
    for (; env; env = env->parent) {
        for (int i = 0; i < env->count; i++) {
            if (strcmp(env->names[i], name) == 0) {
                *out = env->vals[i];
                return 1;
            }
        }
    }
    return 0;
}

int env_set(Env *env, const char *name, Value v) {
    for (; env; env = env->parent) {
        for (int i = 0; i < env->count; i++) {
            if (strcmp(env->names[i], name) == 0) {
                env->vals[i] = v;
                return 1;
            }
        }
    }
    return 0;
}
