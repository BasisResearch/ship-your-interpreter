#!/usr/bin/env python3
"""wl_to_lean.py — transpile a `.wl` program to a Lean `Vsa.While.Program`
term (ANALYSIS ONLY, gap-1a of experiments/invariant-gen-plan.md).

The While layer has NO Lean parser (Vsa/While/Ast.lean is an AST builder only;
the parser lives in the C interpreter compiled into the ELF).  For the relational
spec-trace driver we need the SAME program the machine runs, expressed as the
real `Stmt`/`Expr` AST so `kindOfStmt`/`kindOfExpr` tags are the genuine spec
tags.  This small recursive-descent transpiler emits that AST term.

It covers the corpus's `.wl` surface: var/assign, if/else, while, for, break,
continue, return, blocks, function literals+decls, calls, println/print, string
+ int + bool + null literals, the binary/logical/unary operators, and comments.

Emits a Lean snippet defining `def <name> : Vsa.While.Program := [ … ]` that the
general spec driver imports and `#eval`s.  Nothing here enters a proof.

Usage:
  python3 scripts/wl_to_lean.py --wl /tmp/wl-test/tests/while.wl --name prog \
      --out /tmp/spec/while_ast.lean
"""
import argparse
import re
import sys

# ---------------------------------------------------------------------------
# Lexer
# ---------------------------------------------------------------------------

# NOTE: `print`/`println` are BUILTINS called as functions (`.call (.var
# "println") …`), not statement keywords, so they are lexed as identifiers.
KEYWORDS = {"var", "if", "else", "while", "for", "return", "break", "continue",
            "fn", "true", "false", "null"}
# multi-char operators first so they win the maximal munch
OPS = ["==", "!=", "<=", ">=", "&&", "||", "=", "<", ">", "+", "-", "*", "/",
       "%", "!", "(", ")", "{", "}", "[", "]", ";", ",", "."]


def lex(src):
    # strip // line comments and /* */ block comments
    src = re.sub(r"//[^\n]*", "", src)
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
    toks = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if c == '"':
            j = i + 1
            buf = []
            while j < n and src[j] != '"':
                if src[j] == "\\" and j + 1 < n:
                    esc = src[j + 1]
                    buf.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(esc, esc))
                    j += 2
                else:
                    buf.append(src[j])
                    j += 1
            toks.append(("str", "".join(buf)))
            i = j + 1
            continue
        if c.isdigit():
            j = i
            while j < n and src[j].isdigit():
                j += 1
            toks.append(("int", src[i:j]))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] == "_"):
                j += 1
            w = src[i:j]
            toks.append(("kw" if w in KEYWORDS else "id", w))
            i = j
            continue
        for op in OPS:
            if src.startswith(op, i):
                toks.append(("op", op))
                i += len(op)
                break
        else:
            sys.exit(f"wl_to_lean: lex error at {src[i:i+16]!r}")
    toks.append(("eof", ""))
    return toks


# ---------------------------------------------------------------------------
# Parser (recursive descent) — produces Lean AST strings directly
# ---------------------------------------------------------------------------

BINOP = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
         "==": "eq", "!=": "ne", "<": "lt", "<=": "le", ">": "gt", ">=": "ge"}
# precedence climbing table (higher binds tighter)
PREC = {"||": 1, "&&": 2, "==": 3, "!=": 3, "<": 4, "<=": 4, ">": 4, ">=": 4,
        "+": 5, "-": 5, "*": 6, "/": 6, "%": 6}


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i]

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def eat(self, kind, val=None):
        k, v = self.t[self.i]
        if k != kind or (val is not None and v != val):
            sys.exit(f"wl_to_lean: parse error at #{self.i} {(k, v)}, want {(kind, val)}")
        self.i += 1
        return v

    def is_op(self, v):
        return self.peek() == ("op", v)

    def is_kw(self, v):
        return self.peek() == ("kw", v)

    # ---- expressions ----
    def expr(self):
        return self.assign_expr()

    def assign_expr(self):
        left = self.bin_expr(0)
        if self.is_op("="):
            self.next()
            rhs = self.assign_expr()
            # only `var x` on the left is a valid assign target in the surface
            m = re.match(r"\.var (\"[^\"]*\")$", left)
            if m:
                return f".assign {m.group(1)} ({rhs})"
            sys.exit(f"wl_to_lean: bad assign target {left}")
        return left

    def bin_expr(self, minp):
        left = self.unary()
        while True:
            k, v = self.peek()
            if k == "op" and v in PREC and PREC[v] >= minp:
                self.next()
                right = self.bin_expr(PREC[v] + 1)
                if v in ("&&", "||"):
                    lo = "and" if v == "&&" else "or"
                    left = f".logical .{lo} ({left}) ({right})"
                else:
                    left = f".binary .{BINOP[v]} ({left}) ({right})"
            else:
                return left

    def unary(self):
        if self.is_op("-"):
            self.next()
            return f".unary .neg ({self.unary()})"
        if self.is_op("!"):
            self.next()
            return f".unary .not ({self.unary()})"
        return self.postfix()

    def postfix(self):
        e = self.atom()
        while self.is_op("("):
            self.next()
            args = []
            if not self.is_op(")"):
                args.append(self.expr())
                while self.is_op(","):
                    self.next()
                    args.append(self.expr())
            self.eat("op", ")")
            e = f".call ({e}) [{', '.join(args)}]"
        return e

    def atom(self):
        k, v = self.peek()
        if k == "int":
            self.next()
            return f".int {v}"
        if k == "str":
            self.next()
            return f".str {lean_str(v)}"
        if self.is_kw("true"):
            self.next()
            return ".bool true"
        if self.is_kw("false"):
            self.next()
            return ".bool false"
        if self.is_kw("null"):
            self.next()
            return ".null"
        if self.is_kw("fn"):
            return self.fn_literal()
        if k == "id":
            self.next()
            return f'.var "{v}"'
        if self.is_op("("):
            self.next()
            e = self.expr()
            self.eat("op", ")")
            return e
        sys.exit(f"wl_to_lean: unexpected token in expr {(k, v)}")

    def fn_literal(self):
        self.eat("kw", "fn")
        name = "none"
        if self.peek()[0] == "id":
            name = f'(some "{self.next()[1]}")'
        self.eat("op", "(")
        params = []
        if not self.is_op(")"):
            params.append(self.eat("id"))
            while self.is_op(","):
                self.next()
                params.append(self.eat("id"))
        self.eat("op", ")")
        body = self.block_stmts()
        plist = "[" + ", ".join(f'"{p}"' for p in params) + "]"
        return f".fn {name} {plist} [{', '.join(body)}]"

    # ---- statements ----
    def block_stmts(self):
        self.eat("op", "{")
        ss = []
        while not self.is_op("}"):
            ss.append(self.stmt())
        self.eat("op", "}")
        return ss

    def stmt(self):
        if self.is_kw("var"):
            self.next()
            x = self.eat("id")
            init = "none"
            if self.is_op("="):
                self.next()
                init = f"(some ({self.expr()}))"
            self.opt_semi()
            return f'.varDecl "{x}" {init}'
        if self.is_kw("if"):
            return self.if_stmt()
        if self.is_kw("while"):
            self.next()
            self.eat("op", "(")
            c = self.expr()
            self.eat("op", ")")
            body = self.stmt_or_block()
            return f".whileStmt ({c}) ({body})"
        if self.is_kw("for"):
            return self.for_stmt()
        if self.is_kw("return"):
            self.next()
            if self.is_op(";"):
                self.next()
                return ".ret none"
            e = self.expr()
            self.opt_semi()
            return f".ret (some ({e}))"
        if self.is_kw("break"):
            self.next()
            self.opt_semi()
            return ".brk"
        if self.is_kw("continue"):
            self.next()
            self.opt_semi()
            return ".cont"
        if self.is_kw("fn"):
            # top-level fn decl desugars to `var f = fn f(...) {...}` (Ast.lean note)
            lit = self.fn_literal()
            m = re.match(r"\.fn \(some (\"[^\"]*\")\)", lit)
            if m:
                return f'.varDecl {m.group(1)} (some ({lit}))'
            return f".expr ({lit})"
        if self.is_op("{"):
            return f".block [{', '.join(self.block_stmts())}]"
        # expression statement
        e = self.expr()
        self.opt_semi()
        return f".expr ({e})"

    def if_stmt(self):
        self.eat("kw", "if")
        self.eat("op", "(")
        c = self.expr()
        self.eat("op", ")")
        thn = self.stmt_or_block()
        els = "none"
        if self.is_kw("else"):
            self.next()
            els = f"(some ({self.stmt_or_block()}))"
        return f".ifStmt ({c}) ({thn}) {els}"

    def for_stmt(self):
        self.eat("kw", "for")
        self.eat("op", "(")
        init = "none"
        if not self.is_op(";"):
            # init is a var-decl or expr statement, no trailing semi consumed here
            if self.is_kw("var"):
                init = f"(some ({self.stmt()}))"   # stmt eats its own semi
            else:
                init = f"(some (.expr ({self.expr()})))"
                self.eat("op", ";")
        else:
            self.eat("op", ";")
        cond = "none"
        if not self.is_op(";"):
            cond = f"(some ({self.expr()}))"
        self.eat("op", ";")
        step = "none"
        if not self.is_op(")"):
            step = f"(some ({self.expr()}))"
        self.eat("op", ")")
        body = self.stmt_or_block()
        return f".forStmt {init} {cond} {step} ({body})"

    def stmt_or_block(self):
        if self.is_op("{"):
            return f".block [{', '.join(self.block_stmts())}]"
        return self.stmt()

    def opt_semi(self):
        if self.is_op(";"):
            self.next()

    def program(self):
        ss = []
        while self.peek()[0] != "eof":
            ss.append(self.stmt())
        return ss


def transpile(src, name):
    p = P(lex(src))
    stmts = p.program()
    body = ",\n  ".join(stmts)
    return (f"-- GENERATED by scripts/wl_to_lean.py (ANALYSIS ONLY)\n"
            f"def {name} : Vsa.While.Program := [\n  {body}\n]\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wl", required=True)
    ap.add_argument("--name", default="prog")
    ap.add_argument("--out")
    args = ap.parse_args()
    src = open(args.wl).read()
    out = transpile(src, args.name)
    if args.out:
        open(args.out, "w").write(out)
        print(f"[wl_to_lean] wrote {args.out} ({len(out)} bytes)")
    else:
        sys.stdout.write(out)


if __name__ == "__main__":
    main()
