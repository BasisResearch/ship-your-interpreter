#!/usr/bin/env python3
"""wl_fuzz.py — random While programs for the encoder differential test.

`experiments/smt/DIFFTEST-PLAN.md`'s corpus section: ten hand-written programs
exercise the common arms and nothing else, and the gap is a list rather than an
estimate because phase 1 reports which spans a corpus enters.  This fills the
list mechanically.

Two constraints shape the generator.

* **Size.**  `c/src/script.S` `.incbin`s the program into `.rodata`, which sits
  after `.text`, so a program of a different length moves every rodata address
  and (`-mcmodel=medany`) rewrites the `auipc`/`addi` pairs in `.text`.  Every
  program is padded to the proof script's length, so it must not EXCEED it.
* **Termination.**  A trace of a program that does not halt is a trace of the
  fuel cut.  Loops are emitted only in shapes whose counter is monotone towards
  a literal bound, and `break`/`continue` never sit on the increment's path.

`--errors` lets a fraction of programs end in a runtime error (division by zero,
an undefined variable, a type error) — those are the only way into the error-site
arms, and `c/tests/err_*.wl` is the existing shape.
"""
import argparse
import os
import random
import subprocess
import sys

MAXLEN = 453           # len(c/tests/while.wl), the proof ELF's script

INT_OPS = ["+", "-", "*", "/", "%"]
CMP_OPS = ["<", "<=", ">", ">=", "==", "!="]
INTERESTING = [0, 1, 2, 3, 7, 10, 42, 100, 255, 256, 1000, 65535,
               2147483647, 4294967296, 9223372036854775807]


class Gen:
    def __init__(self, rnd, errors=False):
        self.r = rnd
        self.errors = errors
        self.scopes = [[]]
        self.fns = []
        self.n = 0

    def fresh(self, p="v"):
        self.n += 1
        return f"{p}{self.n}"

    def vars(self):
        return [v for s in self.scopes for v in s]

    def assignable(self):
        """Everything in scope EXCEPT the loop counters — assigning to one is
        how a generated program stops terminating, and a trace of a program that
        does not halt is a trace of the fuel cut."""
        return [v for v in self.vars() if not v.startswith("i")]

    # ---------------------------------------------------------- expressions
    def int_expr(self, d=0):
        r = self.r
        vs = self.vars()
        c = r.random()
        if d >= 2 or c < 0.30:
            return str(r.choice(INTERESTING))
        if vs and c < 0.55:
            return r.choice(vs)
        if c < 0.62:
            return f"(0 - {self.int_expr(d + 1)})"
        if c < 0.68 and self.fns:
            f = r.choice(self.fns)
            return f"{f[0]}({', '.join(self.int_expr(d + 1) for _ in range(f[1]))})"
        op = r.choice(INT_OPS)
        rhs = self.int_expr(d + 1)
        if op in ("/", "%") and not self.errors:
            # keep the divisor non-zero unless we are hunting the error arm
            rhs = f"({rhs} + 1)" if rhs.lstrip("-").isdigit() and int(rhs) == 0 else rhs
            if rhs == "0":
                rhs = "1"
        return f"({self.int_expr(d + 1)} {op} {rhs})"

    def str_expr(self, d=0):
        r = self.r
        lits = ['"a"', '"abc"', '"abd"', '""', '"zz"', '"hello"', '"\\n"', '"\\t"']
        if d >= 2 or r.random() < 0.6:
            return r.choice(lits)
        return f"({self.str_expr(d + 1)} + {self.any_expr(d + 1)})"

    def bool_expr(self, d=0):
        r = self.r
        c = r.random()
        if d >= 2 or c < 0.2:
            return r.choice(["true", "false"])
        if c < 0.5:
            return f"({self.int_expr(d + 1)} {r.choice(CMP_OPS)} {self.int_expr(d + 1)})"
        if c < 0.65:
            return f"({self.str_expr(d + 1)} {r.choice(CMP_OPS)} {self.str_expr(d + 1)})"
        if c < 0.75:
            return f"(!{self.bool_expr(d + 1)})"
        if c < 0.85:
            return f"({self.any_expr(d + 1)} == null)"
        return f"({self.bool_expr(d + 1)} {r.choice(['&&', '||'])} {self.bool_expr(d + 1)})"

    def any_expr(self, d=0):
        c = self.r.random()
        if c < 0.5:
            return self.int_expr(d)
        if c < 0.75:
            return self.str_expr(d)
        if c < 0.95:
            return self.bool_expr(d)
        return "null"

    # ----------------------------------------------------------- statements
    def stmt(self, d, ind, inloop):
        r = self.r
        c = r.random()
        p = "  " * ind
        if c < 0.22:
            v = self.fresh()
            self.scopes[-1].append(v)
            init = "" if r.random() < 0.15 else f" = {self.any_expr()}"
            return [f"{p}var {v}{init};"]
        if c < 0.38 and self.assignable():
            return [f"{p}{r.choice(self.assignable())} = {self.any_expr()};"]
        if c < 0.52:
            return [f"{p}println({self.any_expr()});"]
        if c < 0.62 and d < 2:
            self.scopes.append([])
            body = self.block(d + 1, ind, inloop)
            self.scopes.pop()
            return body
        if c < 0.76 and d < 2:
            out = [f"{p}if ({self.bool_expr()}) {{"]
            self.scopes.append([])
            out += self.stmts(d + 1, ind + 1, inloop, 2)
            self.scopes.pop()
            out.append(f"{p}}}")
            if r.random() < 0.5:
                out[-1] = f"{p}}} else {{"
                self.scopes.append([])
                out += self.stmts(d + 1, ind + 1, inloop, 2)
                self.scopes.pop()
                out.append(f"{p}}}")
            return out
        if c < 0.88 and d < 2:
            # a bounded loop: the counter is declared here, compared against a
            # literal, and incremented on every path out of the body
            i = self.fresh("i")
            n = r.randint(1, 5)
            self.scopes.append([i])
            if r.random() < 0.5:
                out = [f"{p}for (var {i} = 0; {i} < {n}; {i} = {i} + 1) {{"]
                out += self.stmts(d + 1, ind + 1, True, 2)
                out.append(f"{p}}}")
            else:
                out = [f"{p}var {i} = 0;", f"{p}while ({i} < {n}) {{"]
                out += self.stmts(d + 1, ind + 1, False, 2)
                out.append(f"{p}  {i} = {i} + 1;", )
                out.append(f"{p}}}")
            self.scopes.pop()
            return out
        if c < 0.93 and inloop:
            return [f"{p}{r.choice(['break', 'continue'])};"]
        return [f"{p}{self.any_expr()};"]

    def stmts(self, d, ind, inloop, k):
        out = []
        for _ in range(self.r.randint(1, k)):
            out += self.stmt(d, ind, inloop)
        return out

    def block(self, d, ind, inloop):
        p = "  " * ind
        return [f"{p}{{"] + self.stmts(d + 1, ind + 1, inloop, 2) + [f"{p}}}"]

    def fn(self):
        r = self.r
        name = self.fresh("f")
        k = r.randint(0, 2)
        ps = [self.fresh("p") for _ in range(k)]
        self.scopes.append(list(ps))
        body = self.stmts(1, 1, False, 2)
        if r.random() < 0.8:
            body.append(f"  return {self.any_expr()};")
        else:
            body.append("  return;")
        self.scopes.pop()
        self.fns.append((name, k))
        return [f"fn {name}({', '.join(ps)}) {{"] + body + ["}"]

    def program(self):
        r = self.r
        out = ["// generated by scripts/wl_fuzz.py"]
        for _ in range(r.randint(0, 2)):
            out += self.fn()
        out += self.stmts(0, 0, False, 6)
        if self.errors:
            out.append(r.choice([
                "println(1 / 0);", "println(undefined_name);",
                'println(1 + true);', 'println("a" - "b");',
                "println(7 % 0);",
            ]))
        return "\n".join(out) + "\n"


def gen_one(seed, errors, host):
    """One program that fits, parses and (unless `errors`) runs cleanly."""
    r = random.Random(seed)
    for _ in range(60):
        src = Gen(r, errors).program()
        if len(src.encode()) > MAXLEN:
            continue
        if host:
            try:
                p = subprocess.run([host, "/dev/stdin"], input=src,
                                   capture_output=True, text=True, timeout=10)
            except subprocess.TimeoutExpired:
                continue      # did not halt: a trace of it would be a fuel cut
            if errors:
                if p.returncode == 0:
                    continue          # wanted a fault, did not get one
            elif p.returncode != 0:
                continue
        return src
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--errors", type=float, default=0.2,
                    help="fraction of programs that end in a runtime error")
    ap.add_argument("--out", required=True)
    ap.add_argument("--host", default=os.path.join(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))), "c", "while"),
        help="host interpreter used to reject programs that do not run")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    host = a.host if os.path.exists(a.host) else None
    if host is None:
        print("wl_fuzz: no host interpreter; generated programs are unvalidated",
              file=sys.stderr)
    made = 0
    for k in range(a.n):
        seed = a.seed * 100000 + k
        errs = (k % max(1, int(1 / a.errors))) == 0 if a.errors > 0 else False
        src = gen_one(seed, errs, host)
        if src is None:
            continue
        nm = f"fz{a.seed:03d}_{k:03d}{'e' if errs else ''}"
        open(os.path.join(a.out, nm + ".wl"), "w").write(src)
        made += 1
    print(f"[wl_fuzz] {made}/{a.n} programs -> {a.out}")


if __name__ == "__main__":
    main()
