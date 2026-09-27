#ifndef WHILE_PARSER_H
#define WHILE_PARSER_H

#include "ast.h"
#include <stddef.h>

/* Parse a whole program. On success returns an array of statements and
 * stores its length in *count. On error returns NULL and writes a
 * diagnostic into errbuf. AST memory is heap-allocated and lives for the
 * rest of the process (this interpreter never frees program structures). */
Stmt **parse_program(const char *src, int *count, char *errbuf, size_t errsz);

#endif
