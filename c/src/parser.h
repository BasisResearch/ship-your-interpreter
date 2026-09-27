#ifndef WHILE_PARSER_H
#define WHILE_PARSER_H

#include "ast.h"
#include <stddef.h>

Stmt **parse_program(const char *src, int *count, char *errbuf, size_t errsz);

#endif
