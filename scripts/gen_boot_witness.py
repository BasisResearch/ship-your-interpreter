#!/usr/bin/env python3
"""Generate loader-derived boot witnesses (`Vsa/Sim/Boot`, REVIEW.md P4).

A program's boot state at `interp_run`'s entry is the ELF loader's memory
(`initializeMemory .B64`) with the emulator's store log from `_start` to the
entry applied, and the entry row's registers. This tool turns the emulator's
`--trace-all` output into Lean data the kernel checks (`Vsa.Sim.Boot.LogCheck`).

Subcommands (all scratch output goes under `--work`, outside the repository):

  corpus  --work W --emulator E WL...   build one ELF per script by patching the
          proof ELF's script blob (`_script_start`, 453 bytes + NUL), trace each
          to the entry, and dump the loader pieces natively
          (`scripts/boot_elf_pieces.lean`).
  image   --work W                      emit `Vsa/Sim/Boot/ImageData.lean`: the
          loader bytes outside `.text`/`.rodata` (identical for every script).
  program --work W NAME...              emit `Vsa/Sim/Boot/Gen/<Name>.lean` per
          traced program: script bytes, packed store log, final byte map,
          entry registers, and the per-trace boundary checks.
  check-elf --work W                    evaluate `ElfLoads elf script` natively for
          every generated trace's ELF (needs `lake build VsaBoot`).

Every generated fact is re-checked by the Lean kernel; this tool is trusted for
nothing but producing candidates. `corpus` additionally checks that each ELF's
native loader pieces equal the proof ELF's outside the script blob.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

PROOF_ELF = ROOT / "c" / "while-riscv-htif.elf"
BOOT_DIR = ROOT / "Vsa" / "Sim" / "Boot"
INTERP_RUN = 0x800043EC
SCRIPT_BASE = 0x80018BE0
SCRIPT_LEN = 453
TEXT_BASE, TEXT_END = 0x80000000, 0x80018BE0
RODATA_END = 0x8001ACF0
SEG_BASE, SEG_SIZE = 0x80000000, 113040
DATA_BASE, DATA_END = RODATA_END, SEG_BASE + SEG_SIZE
PAGE = 256
LOG_PAGE = 64


# ------------------------------------------------------------------ helpers
def pack(items, bits):
    n = 0
    for i, x in enumerate(items):
        assert 0 <= x < (1 << bits), (x, bits)
        n |= x << (bits * i)
    return n


def if_tree(var, n, leaf, pivot=None):
    """Balanced `if var < p then … else …` over leaves `0 … n-1`."""
    pivot = pivot or (lambda k: str(k))

    def go(lo, hi):
        if hi - lo == 1:
            return leaf(lo)
        mid = (lo + hi) // 2
        return f"(if {var} < {pivot(mid)} then {go(lo, mid)} else {go(mid, hi)})"

    return go(0, n)


def byte_pages(name, data, doc):
    """Lean defs for a packed byte function `name (offset) : BitVec 8`."""
    pages = [data[i:i + PAGE] for i in range(0, len(data), PAGE)]
    out = []
    for i, pg in enumerate(pages):
        out.append(f"private def {name}Page{i} : Nat := {hex(pack(pg, 8))}")
    out.append("")
    out.append(f"private def {name}Page (page : Nat) : Nat :=\n  "
               + if_tree("page", len(pages), lambda k: f"{name}Page{k}"))
    out.append("")
    out.append(f"/-- {doc} -/")
    out.append(f"def {name} (offset : Nat) : BitVec 8 :=\n"
               f"  BitVec.ofNat 8 (Nat.shiftRight ({name}Page (offset / {PAGE})) (8 * (offset % {PAGE})))")
    return out


def read_pieces(path):
    """`(kind, base, bytes)` per line of a `boot_elf_pieces.lean` dump."""
    out = {}
    for line in open(path):
        fields = line.rstrip("\n").split("\t")
        if len(fields) != 4 or fields[1] not in ("seg", "bob"):
            continue
        p, kind, base, hx = fields
        out.setdefault(p, []).append((kind, int(base), bytes.fromhex(hx)))
    return out


def piece_bytes(pieces):
    """Address → byte, in insertion order (later pieces do not overwrite: the
    loader panics on a repeated address, checked here)."""
    mem = {}
    for _, base, data in pieces:
        for i, b in enumerate(data):
            if base + i in mem:
                raise SystemExit(f"loader piece overlap at {base + i:#x}")
            mem[base + i] = b
    return mem


# ------------------------------------------------------------------ corpus
def cmd_corpus(args):
    from difftest import elf_symbols
    from difftest_lib import Image

    work = Path(args.work)
    for d in ("elfs", "traces"):
        (work / d).mkdir(parents=True, exist_ok=True)
    img = Image(str(PROOF_ELF))
    assert elf_symbols(img)["_script_start"] == SCRIPT_BASE
    names = []
    for wl in args.wl:
        name = Path(wl).stem
        src = open(wl, "rb").read()
        if len(src) > SCRIPT_LEN:
            raise SystemExit(f"{wl}: {len(src)} bytes exceeds the {SCRIPT_LEN}-byte blob")
        raw = bytearray(img.raw)
        v, off, sz = img.segs[0]
        fo = off + (SCRIPT_BASE - v)
        assert raw[fo + SCRIPT_LEN] == 0
        raw[fo:fo + SCRIPT_LEN] = src + b"\n" * (SCRIPT_LEN - len(src))
        (work / "elfs" / f"{name}.elf").write_bytes(raw)
        names.append(name)
    (work / "elfs" / "proof.elf").write_bytes(img.raw)
    names.append("proof")
    def trace(name):
        path = work / "traces" / f"{name}.entry-trace.tsv"
        cmd = (f"{args.emulator} {work}/elfs/{name}.elf --trace-all --max-steps {args.max_steps}"
               f" 2>&1 >/dev/null | awk -F'\\t' '/^T\\t/{{print; if ($3==\"{INTERP_RUN:x}\") exit}}'"
               f" > {path}")
        subprocess.run(cmd, shell=True, check=True)
        return name, sum(1 for _ in open(path))

    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for name, rows in ex.map(trace, names):
            print(name, rows, "rows")
    elfs = [str(work / "elfs" / f"{n}.elf") for n in names]
    dump = subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "scripts" / "boot_elf_pieces.lean")]
                          + elfs, cwd=ROOT, check=True, capture_output=True, text=True).stdout
    (work / "pieces.tsv").write_text(dump)
    pieces = read_pieces(work / "pieces.tsv")
    ref = piece_bytes(pieces[str(work / "elfs" / "proof.elf")])
    for e in elfs:
        mem = piece_bytes(pieces[e])
        if mem.keys() != ref.keys():
            raise SystemExit(f"{e}: loader pieces differ in shape from the proof ELF")
        bad = [a for a in mem if mem[a] != ref[a] and not SCRIPT_BASE <= a < SCRIPT_BASE + SCRIPT_LEN]
        if bad:
            raise SystemExit(f"{e}: loader bytes differ outside the script blob at {bad[0]:#x}")
    print("pieces agree outside the script blob:", len(elfs), "ELFs")


# ------------------------------------------------------------------ image
def proof_pieces(work):
    pieces = read_pieces(Path(work) / "pieces.tsv")
    key = str(Path(work) / "elfs" / "proof.elf")
    return pieces[key]


def cmd_image(args):
    pieces = proof_pieces(args.work)
    shape = [(base, len(data)) for _, base, data in pieces]
    mem = piece_bytes(pieces)
    low = [(b, n) for b, n in shape if n and b < SEG_BASE]
    assert [(b, n) for b, n in shape if b >= SEG_BASE] == [(SEG_BASE, SEG_SIZE)], shape
    out = [
        "import Vsa.Elf",
        "",
        "/-! Generated by `scripts/gen_boot_witness.py image` from the proof ELF's",
        "loader pieces (`scripts/boot_elf_pieces.lean`). Packed data only. -/",
        "",
        "namespace Vsa.Sim.Boot",
        "",
        "/-- The loader's pieces `(base, size)`, in `initializeMemory`'s insertion order. -/",
        "def bootPieces : List (Nat × Nat) :=",
        "  [" + ", ".join(f"({b:#x}, {n})" for b, n in shape) + "]",
        "",
    ]
    # low pieces: the RISC-V attributes segment at 0 and ELFSage's bits and bobs
    lows = []
    for i, (b, n) in enumerate(low):
        data = [mem[b + k] for k in range(n)]
        out.append(f"private def bootLow{i} : Nat := {hex(pack(data, 8))}")
        lows.append((b, n, i))
    out.append("")
    out.append("/-- Loader bytes below RAM (ELF metadata the loader also inserts). -/")
    body = "0#8"
    for b, n, i in reversed(lows):
        body = (f"if {b:#x} ≤ x ∧ x < {b + n:#x} then "
                f"BitVec.ofNat 8 (Nat.shiftRight bootLow{i} (8 * (x - {b:#x}))) else {body}")
    out.append(f"def bootLowByte (x : Nat) : BitVec 8 :=\n  {body}")
    out.append("")
    data = [mem[a] for a in range(DATA_BASE, DATA_END)]
    out += byte_pages("bootDataByte", data,
                      f"Loader bytes `[{DATA_BASE:#x}, {DATA_END:#x})` (`.tohost`, `.data`, "
                      f"initialised `.init_array`), by offset from `{DATA_BASE:#x}`.")
    out.append("")
    out.append("end Vsa.Sim.Boot")
    (BOOT_DIR / "ImageData.lean").write_text("\n".join(out) + "\n")
    print("wrote", BOOT_DIR / "ImageData.lean")


def cmd_check_elf(args):
    """Evaluate `ElfLoads elf script` natively for each traced ELF (the parse
    of a concrete file, which the kernel does not reduce)."""
    work = Path(args.work)
    names = [f.stem for f in sorted((BOOT_DIR / "Gen").glob("*.lean"))]
    by_lean = {lean_name(f.stem): f.stem for f in (work / "elfs").glob("*.elf")}
    lines = ["import VsaBoot", "open Vsa.Sim.Boot LeanRV64DExecutable", "",
             "def check (path : String) (script : Nat) : IO Bool := do",
             "  let bytes ← IO.FS.readBinFile path",
             "  match mkRawELFFile? bytes with",
             "  | .ok (.elf64 elf) => pure (decide (elfPieces elf = imagePieces script))",
             "  | _ => pure false", "",
             "def main : IO UInt32 := do", "  let mut bad := 0"]
    for n in names:
        elf = work / "elfs" / f"{by_lean[n]}.elf"
        lines += [f"  let ok ← check \"{elf}\" Vsa.Sim.Boot.Gen.{n}.script",
                  f"  IO.println s!\"{by_lean[n]}: ElfLoads {{ok}}\"",
                  "  if !ok then bad := bad + 1"]
    lines += ["  return bad"]
    src = work / "boot_elf_check.lean"
    src.write_text("\n".join(lines) + "\n")
    r = subprocess.run(["lake", "env", "lean", "--run", str(src)], cwd=ROOT)
    if r.returncode:
        raise SystemExit(f"ElfLoads failed for {r.returncode} ELF(s)")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("corpus")
    c.add_argument("--work", required=True)
    c.add_argument("--emulator", required=True)
    c.add_argument("--max-steps", type=int, default=200000)
    c.add_argument("--jobs", type=int, default=16)
    c.add_argument("wl", nargs="+")
    i = sub.add_parser("image")
    i.add_argument("--work", required=True)
    p = sub.add_parser("program")
    p.add_argument("--work", required=True)
    p.add_argument("names", nargs="+")
    e = sub.add_parser("check-elf")
    e.add_argument("--work", required=True)
    args = ap.parse_args()
    {"corpus": cmd_corpus, "image": cmd_image, "program": cmd_program,
     "check-elf": cmd_check_elf}[args.cmd](args)


RUN_MAX = 64
# Programs whose cost evaluation is out of the kernel's reach (recursion.wl:
# fib(20) allocates ~22k frames in a list-backed store).
SLOW_COST = {"recursion"}
# The source ASTs of `Vsa/While/Programs.lean` the traced scripts parse to.
SOURCE = {"proof": "whileWl", "while": "whileWl", "arithmetic": "arithmeticWl", "for": "forWl",
          "scope": "scopeWl", "strings": "stringsWl", "recursion": "recursionWl"}
CHUNK = 1024


def lean_name(name):
    return "".join(w.capitalize() for w in name.replace("-", "_").split("_"))


def read_trace(path):
    """(store log, entry row) of an entry trace."""
    log, entry = [], None
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if p[0] != "T":
            continue
        if int(p[2], 16) == INTERP_RUN:
            entry = p
            break
        if len(p) > 35 and p[35][:1] == "S":
            log.append((int(p[36], 16), int(p[35][1:]), int(p[38], 16)))
        elif len(p) > 35 and p[35][:1] not in ("L", "O"):
            raise SystemExit(f"{path}: unexpected memory operand {p[35]}")
    if entry is None:
        raise SystemExit(f"{path}: the trace does not reach interp_run")
    return log, entry


def final_runs(log):
    fin = {}
    for i, (a, w, v) in enumerate(log):
        assert w in (1, 2, 4, 8) and a + w <= 1 << 32
        for j in range(w):
            fin[a + j] = (i, (v >> (8 * j)) & 0xFF)
    runs = []
    for k in sorted(fin):
        if runs and runs[-1][0] + len(runs[-1][1]) == k and len(runs[-1][1]) < RUN_MAX:
            runs[-1][1].append(fin[k])
        else:
            runs.append([k, [fin[k]]])
    return runs


def run_tree(runs):
    def go(lo, hi):
        if hi - lo == 1:
            b, cells = runs[lo]
            return f"(.leaf ⟨{b:#x}, {len(cells)}, {hex(pack([i | (x << 24) for i, x in cells], 32))}⟩)"
        mid = (lo + hi) // 2
        return f"(.node {runs[mid][0]:#x}\n    {go(lo, mid)}\n    {go(mid, hi)})"
    return go(0, len(runs))


def entry_memory(work, name, log):
    """The entry memory as a dict: loader pieces, then the stores."""
    pieces = read_pieces(work / "pieces.tsv")[str(work / "elfs" / f"{name}.elf")]
    mem = piece_bytes(pieces)
    for a, w, v in log:
        for j in range(w):
            mem[a + j] = (v >> (8 * j)) & 0xFF
    return mem


def rd(mem, a, n):
    return sum(mem[a + i] << (8 * i) for i in range(n))


def ast_bytes(mem, stmts, count):
    """Every byte the representation relations read for the program at
    `stmts` (node fields, pointer arrays, strings with their NUL)."""
    seen = set()

    def touch(a, n):
        seen.update(range(a, a + n))

    def cstr(a):
        k = a
        while mem[k] != 0:
            k += 1
        touch(a, k - a + 1)

    def expr(a):
        k = rd(mem, a, 4)
        touch(a, 4)
        if k == 0:
            touch(a + 8, 8)
        elif k in (1, 4):
            touch(a + 8, 8); cstr(rd(mem, a + 8, 8))
        elif k == 2:
            touch(a + 8, 4)
        elif k == 5:
            touch(a + 8, 16); cstr(rd(mem, a + 8, 8)); expr(rd(mem, a + 16, 8))
        elif k in (6, 7):
            touch(a + 8, 4); touch(a + 16, 16); expr(rd(mem, a + 16, 8)); expr(rd(mem, a + 24, 8))
        elif k == 8:
            touch(a + 8, 4); touch(a + 16, 8); expr(rd(mem, a + 16, 8))
        elif k == 9:
            touch(a + 8, 16); touch(a + 24, 4)
            expr(rd(mem, a + 8, 8))
            args, argc = rd(mem, a + 16, 8), rd(mem, a + 24, 4)
            for i in range(argc):
                touch(args + 8 * i, 8); expr(rd(mem, args + 8 * i, 8))
        elif k == 10:
            touch(a + 8, 16); touch(a + 24, 4); touch(a + 32, 8)
            nm = rd(mem, a + 8, 8)
            if nm:
                cstr(nm)
            params, pc = rd(mem, a + 16, 8), rd(mem, a + 24, 4)
            for i in range(pc):
                touch(params + 8 * i, 8); cstr(rd(mem, params + 8 * i, 8))
            stmt(rd(mem, a + 32, 8))
        elif k != 3:
            raise SystemExit(f"bad expr kind {k} at {a:#x}")

    def opt_stmt(f):
        touch(f, 8)
        if rd(mem, f, 8):
            stmt(rd(mem, f, 8))

    def opt_expr(f):
        touch(f, 8)
        if rd(mem, f, 8):
            expr(rd(mem, f, 8))

    def stmt(a):
        k = rd(mem, a, 4)
        touch(a, 4)
        if k in (0, 6):
            touch(a + 8, 8)
            if rd(mem, a + 8, 8):
                expr(rd(mem, a + 8, 8))
        elif k == 1:
            touch(a + 8, 16); cstr(rd(mem, a + 8, 8))
            if rd(mem, a + 16, 8):
                expr(rd(mem, a + 16, 8))
        elif k == 2:
            touch(a + 8, 8); touch(a + 16, 4)
            st, n = rd(mem, a + 8, 8), rd(mem, a + 16, 4)
            for i in range(n):
                touch(st + 8 * i, 8); stmt(rd(mem, st + 8 * i, 8))
        elif k == 3:
            touch(a + 8, 24); expr(rd(mem, a + 8, 8)); stmt(rd(mem, a + 16, 8))
            if rd(mem, a + 24, 8):
                stmt(rd(mem, a + 24, 8))
        elif k == 4:
            touch(a + 8, 16); expr(rd(mem, a + 8, 8)); stmt(rd(mem, a + 16, 8))
        elif k == 5:
            opt_stmt(a + 8); opt_expr(a + 16); opt_expr(a + 24); touch(a + 32, 8)
            stmt(rd(mem, a + 32, 8))
        elif k not in (7, 8):
            raise SystemExit(f"bad stmt kind {k} at {a:#x}")

    for i in range(count):
        touch(stmts + 8 * i, 8); stmt(rd(mem, stmts + 8 * i, 8))
    return seen


def lean_str(mem, a):
    out, k = [], a
    while mem[k] != 0:
        c = mem[k]
        out.append({0x5C: "\\\\", 0x22: '\\"', 0x0A: "\\n", 0x09: "\\t"}.get(
            c, chr(c) if 32 <= c < 127 else f"\\x{c:02x}"))
        k += 1
    return '"' + "".join(out) + '"'


BINOPS = {11: "add", 12: "sub", 13: "mul", 14: "div", 15: "mod", 17: "ne", 19: "eq",
          20: "lt", 21: "le", 22: "gt", 23: "ge"}


def ast_term(mem, stmts, count):
    """The represented program as a Lean `Program` term."""
    def lst(xs):
        return "[" + ", ".join(xs) + "]"

    def expr(a):
        k = rd(mem, a, 4)
        if k == 0:
            v = rd(mem, a + 8, 8)
            v = v - (1 << 64) if v >= 1 << 63 else v
            return f"(.int ({v}))"
        if k == 1:
            return f"(.str {lean_str(mem, rd(mem, a + 8, 8))})"
        if k == 2:
            return "(.bool true)" if rd(mem, a + 8, 4) else "(.bool false)"
        if k == 3:
            return ".null"
        if k == 4:
            return f"(.var {lean_str(mem, rd(mem, a + 8, 8))})"
        if k == 5:
            return f"(.assign {lean_str(mem, rd(mem, a + 8, 8))} {expr(rd(mem, a + 16, 8))})"
        if k == 6:
            return f"(.binary .{BINOPS[rd(mem, a + 8, 4)]} {expr(rd(mem, a + 16, 8))} {expr(rd(mem, a + 24, 8))})"
        if k == 7:
            op = {24: "and", 25: "or"}[rd(mem, a + 8, 4)]
            return f"(.logical .{op} {expr(rd(mem, a + 16, 8))} {expr(rd(mem, a + 24, 8))})"
        if k == 8:
            op = {12: "neg", 16: "not"}[rd(mem, a + 8, 4)]
            return f"(.unary .{op} {expr(rd(mem, a + 16, 8))})"
        if k == 9:
            args, argc = rd(mem, a + 16, 8), rd(mem, a + 24, 4)
            return f"(.call {expr(rd(mem, a + 8, 8))} {lst([expr(rd(mem, args + 8 * i, 8)) for i in range(argc)])})"
        if k == 10:
            nm = rd(mem, a + 8, 8)
            name = f"(some {lean_str(mem, nm)})" if nm else "none"
            params, pc = rd(mem, a + 16, 8), rd(mem, a + 24, 4)
            ps = lst([lean_str(mem, rd(mem, params + 8 * i, 8)) for i in range(pc)])
            body = rd(mem, a + 32, 8)
            assert rd(mem, body, 4) == 2
            st, n = rd(mem, body + 8, 8), rd(mem, body + 16, 4)
            return f"(.fn {name} {ps} {lst([stmt(rd(mem, st + 8 * i, 8)) for i in range(n)])})"
        raise SystemExit(f"bad expr kind {k}")

    def opt(f, g):
        q = rd(mem, f, 8)
        return f"(some {g(q)})" if q else "none"

    def stmt(a):
        k = rd(mem, a, 4)
        if k == 0:
            return f"(.expr {expr(rd(mem, a + 8, 8))})"
        if k == 1:
            return f"(.varDecl {lean_str(mem, rd(mem, a + 8, 8))} {opt(a + 16, expr)})"
        if k == 2:
            st, n = rd(mem, a + 8, 8), rd(mem, a + 16, 4)
            return f"(.block {lst([stmt(rd(mem, st + 8 * i, 8)) for i in range(n)])})"
        if k == 3:
            return f"(.ifStmt {expr(rd(mem, a + 8, 8))} {stmt(rd(mem, a + 16, 8))} {opt(a + 24, stmt)})"
        if k == 4:
            return f"(.whileStmt {expr(rd(mem, a + 8, 8))} {stmt(rd(mem, a + 16, 8))})"
        if k == 5:
            return (f"(.forStmt {opt(a + 8, stmt)} {opt(a + 16, expr)} {opt(a + 24, expr)} "
                    f"{stmt(rd(mem, a + 32, 8))})")
        if k == 6:
            return f"(.ret {opt(a + 8, expr)})"
        return {7: ".brk", 8: ".cont"}[k]

    return lst([stmt(rd(mem, stmts + 8 * i, 8)) for i in range(count)])


def heap_walk(mem):
    top, brkv = rd(mem, 0x8001AD20, 8), rd(mem, 0x8001B990, 8)
    p, chunks = 0x8001C170, []
    while p != top:
        h = rd(mem, p + 8, 8)
        sz = h // 4 * 4
        chunks.append((p, sz, rd(mem, p + sz + 8, 8) % 2 == 1))
        p += sz
    bins = []
    for i in range(128):
        b = 0x8001AD10 + 16 * i
        q, qs = rd(mem, b + 16, 8), []
        while i > 0 and q != b:
            qs.append(q); q = rd(mem, q + 16, 8)
        bins.append(qs)
    while bins and not bins[-1]:
        bins.pop()
    return top, brkv, chunks, bins


def boot_own(mem, stmts, count, chunks):
    env = rd(mem, 0x87FFFE10, 8)
    cap, pn, pv = rd(mem, env + 4, 4), rd(mem, env + 8, 8), rd(mem, env + 16, 8)
    keys = [rd(mem, pn + 8 * i, 8) for i in range(3)]
    names = [rd(mem, pv + 24 * i + 8, 8) for i in range(3)]
    live = [(c + 16, sz - 8) for c, sz, inuse in chunks if inuse]
    touched = ast_bytes(mem, stmts, count)
    ast = sorted({e for e in live for k in [None] if any(e[0] <= b < e[0] + e[1] for b in touched)})
    frame = {e for e in live if e[0] <= env < e[0] + e[1] or e[0] in (pn, pv)}
    assert not (set(ast) & frame), "AST bytes in the global frame's blocks"
    missing = [b for b in touched if not any(e[0] <= b < e[0] + e[1] for e in ast)]
    assert not missing, f"AST bytes outside live payloads: {missing[:3]}"
    return dict(env=env, cap=cap, pn=pn, pv=pv, keys=keys, names=names, ast=ast)


def cmd_program(args):
    work = Path(args.work)
    for name in args.names:
        log, entry = read_trace(work / "traces" / f"{name}.entry-trace.tsv")
        script = (work / "elfs" / f"{name}.elf").read_bytes()
        from difftest_lib import Image
        img = Image(str(work / "elfs" / f"{name}.elf"))
        blob = [img.byte(SCRIPT_BASE + k) for k in range(SCRIPT_LEN)]
        runs = final_runs(log)
        enc = [a | (w << 32) | (v << 36) for a, w, v in log]
        pages = [enc[i:i + LOG_PAGE] for i in range(0, len(enc), LOG_PAGE)]
        regs = [int(x, 16) for x in entry[4:35]]
        mem = entry_memory(work, name, log)
        stmts, count = int(entry[4 + 10], 16), int(entry[4 + 11], 16)
        top, brkv, chunks, bins = heap_walk(mem)
        own = boot_own(mem, stmts, count, chunks)
        payload = lambda x: next((c + 16, sz - 8) for c, sz, u in chunks
                                 if u and c + 16 <= x < c + sz + 8)
        blocks = [payload(own["env"]), payload(own["pn"]), payload(own["pv"])]
        genv = rd(mem, 0x87FFFE10, 8)
        gpv = rd(mem, genv + 16, 8)
        gname = rd(mem, gpv + 8, 8)
        ln = lean_name(name)
        nchunks = (len(log) + CHUNK - 1) // CHUNK
        out = [
            "import Vsa.Sim.Boot.Physical",
            "import Vsa.While.Programs",
            "",
            "/-!",
            f"# Boot trace of `{name}.wl` (generated by `scripts/gen_boot_witness.py program`)",
            "",
            f"The script build's entry state at `interp_run` (emulator step {int(entry[1])}):",
            f"{len(log)} stores from `_start` (`log`), their final bytes (`runs`, {len(runs)} runs),",
            "and the entry row's general registers (`gprs`). `logOk` is the kernel's check",
            "that `runs` is exactly the store log's effect.",
            "-/",
            "",
            f"namespace Vsa.Sim.Boot.Gen.{ln}",
            "",
            "open Vsa.Sim.Boot",
            "",
            f"/-- The script blob (453 bytes, little-endian). -/",
            f"def script : Nat := {hex(pack(blob, 8))}",
            "",
        ]
        for i, pg in enumerate(pages):
            out.append(f"private def logPage{i} : Nat := {hex(pack(pg, 128))}")
        out.append("")
        out.append("private def logPage (i : Nat) : Nat :=\n  "
                   + if_tree("i", len(pages), lambda k: f"logPage{k}"))
        out += [
            "",
            "/-- The stores from `_start` to the entry, in program order. -/",
            f"def log : PackedLog := ⟨logPage, {len(log)}⟩",
            "",
            "/-- The final byte of every stored address, with its last writer. -/",
            f"def runs : RunTree :=\n  {run_tree(runs)}",
            "",
            "/-- `x1 … x31` at the entry. -/",
            "def gprs : List (Nat × BitVec 64) :=",
            "  [" + ",\n   ".join(f"({r + 1}, {v:#x}#64)" for r, v in enumerate(regs)) + "]",
            "",
            f"/-- Architectural steps from `_start` to the entry. -/",
            f"def entrySteps : Nat := {int(entry[1])}",
            "",
        ]
        for k in range(nchunks):
            out.append(f"theorem stores{k} : storesIn log runs {k * CHUNK} {CHUNK} = true := by decide +kernel")
        out += [
            "",
            f"theorem stores_ok : ∀ c ∈ chunks 0 {CHUNK} {nchunks}, storesIn log runs c.1 c.2 = true := by",
            "  intro c hc",
            "  simp only [chunks, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceAdd] at hc",
            "  rcases hc with " + " | ".join("rfl" for _ in range(nchunks)),
        ] + [f"  · exact stores{k}" for k in range(nchunks)] + [
            "",
            "theorem runs_ok : ∀ r ∈ runs.runs, runOk log r r.len = true := by decide +kernel",
            "",
            "/-- The final byte map is the store log's effect. -/",
            "theorem logOk : LogOk log runs :=",
            f"  ⟨fun _ hi => chunks_cover stores_ok (Nat.zero_le _) (by change _ < {len(log)} at hi; omega),",
            "    runs_ok⟩",
            "",
            "/-- The entry memory, byte by byte. -/",
            "theorem mem_get (x : Nat) : (bootMem script log)[x]? = bootView script runs x :=",
            "  bootMem_get logOk x",
            "",
            "theorem view : ViewOf (bootMem script log) (bootView script runs) := bootMem_view logOk",
            "",
            "/-- The global frame and the shared bytes at the entry. -/",
            "def own : BootOwn where",
            f"  env := {own['env']:#x}",
            f"  cap := {own['cap']}",
            f"  pn := {own['pn']:#x}",
            f"  pv := {own['pv']:#x}",
        ] + [f"  key{i} := {k:#x}" for i, k in enumerate(own['keys'])] + [
            f"  name{i} := {k:#x}" for i, k in enumerate(own['names'])] + [
            "  ast :=",
            "    [" + ",\n     ".join(f"({a:#x}, {n:#x})" for a, n in own['ast']) + "]",
            "",
            "/-- The dlmalloc heap: the chunk walk from `_end` and the bin lists. -/",
            f"def top : Nat := {top:#x}",
            f"def brkv : Nat := {brkv:#x}",
            "def chunks : List Vsa.Sim.DlHeap.Chunk :=",
            "  [" + ",\n   ".join(f"⟨{a:#x}, {sz:#x}, {'true' if u else 'false'}⟩" for a, sz, u in chunks) + "]",
            "def bins : List (List Nat) := " + repr(bins).replace("'", ""),
            "",
            "theorem ownOk : OwnOk own := by",
            "  constructor <;> decide +kernel",
            "",
            "theorem frameOk : FrameOk (bootView script runs) own := by",
            "  constructor <;> decide +kernel",
            "",
            "/-- The entry registers as a function (`x0` and unlisted indices read 0). -/",
            "def regs (n : Nat) : BitVec 64 := (Vsa.Sim.lookupG n gprs).getD 0",
            "",
            f"def stmts : Nat := {stmts:#x}",
            f"def count : Nat := {count}",
            "",
            "theorem bootRegs : BootRegs regs stmts count := by constructor <;> decide +kernel",
            "",
            "/-- The initial store, checked with `interp_run`'s prologue footprint masked out. -/",
            "theorem storeOk : frameCheck (maskView prologueMask (bootView script runs)) bootNatives",
            "    own.env initFrame = true := by decide +kernel",
            "",
            "theorem heapFactsOk : HeapFactsOk (bootView script runs) own top brkv chunks",
            f"    ({blocks[0][0]:#x}, {blocks[0][1]:#x}) ({blocks[1][0]:#x}, {blocks[1][1]:#x})"
            f" ({blocks[2][0]:#x}, {blocks[2][1]:#x}) := by",
            "  constructor <;> decide +kernel",
            "",
            "/-- The entry's read facts, in any memory the entry view is a partial view",
            "of: the real (sparse) memory and every extension of it, such as its zero fill. -/",
            "theorem memFacts {m : Vsa.MemRepr.Mem} (hv : PartialView m (bootView script runs))",
            "    (hstack : ∀ k, Vsa.Sim.LayoutInstance.stackSL.lo ≤ k →",
            "      k < Vsa.Sim.LayoutInstance.stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :",
            "    BootMemFacts m own.env where",
            "  mainRa := by boot_readp hv",
            "  text := hv.text (by decide +kernel)",
            "  rodata := hv.rodata (by decide +kernel)",
            "  statics := by",
            "    unfold Vsa.Sim.Code.ImageStaticsLoaded Vsa.Sim.Code.imgLldFmt Vsa.Sim.Code.imgDecPointStr",
            "      Vsa.Sim.Code.imgParseSlotD Vsa.Sim.Code.imgParseSlotL Vsa.Sim.Code.imgFnSlot",
            "      Vsa.Sim.Code.imgDecPointPtr Vsa.Sim.Code.imgMbCurMax Vsa.Sim.Code.imgImpurePtr",
            "    boot_factsp hv",
            "  console := by boot_factsp hv",
            "  exitRuntime := by boot_factsp hv",
            "  globals := by boot_readp hv",
            "  depth := by boot_readp hv",
            "  stackBytes := hstack",
            "",
            "/-- The represented program, decoded from the entry memory. -/",
            f"def prog : Vsa.While.Program :=\n  {ast_term(mem, stmts, count)}",
            "",
            "/-- The decoder finds `prog` at `stmts`, reading only shared bytes. -/",
            "theorem progOk : decodesTo (bootView script runs) own.sharedB 100000 stmts count prog = true := by",
            "  decide +kernel",
            "",
            "theorem fitsOk : Vsa.Sim.LayoutInstance.programStackFits prog = true := by decide +kernel",
            "",
        ] + ([] if name not in SOURCE else [
            "/-- The parser's AST is the source program of `Vsa/While/Programs.lean`. -/",
            f"theorem prog_eq : prog = Vsa.While.Programs.{SOURCE[name]} :=",
            "  stmtsBeq_sound (by decide +kernel)",
            "",
        ]) + [
        ] + ([] if name in SLOW_COST else [
            "/-- Every terminating derivation of `prog` fits the heap above `top`. -/",
            "theorem capacityOk : capOk 1000 prog top = true := by decide +kernel",
            "",
        ]) + [
            "theorem heapOk : heapCheck (bootView script runs) own.exts",
            "    [(own.pn, 8 * own.cap), (own.pv, 24 * own.cap)] top brkv chunks bins = true := by",
            "  decide +kernel",
            "",
        ] + ([] if name in SLOW_COST else [
            "/-- **The witness**, at the entry registers over any memory extending the",
            "entry memory in which every stack byte is present. -/",
            "theorem loadedAt {m : Vsa.MemRepr.Mem} (hv : PartialView m (bootView script runs))",
            "    (hstack : ∀ k, Vsa.Sim.LayoutInstance.stackSL.lo ≤ k →",
            "      k < Vsa.Sim.LayoutInstance.stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :",
            "    Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog (bootConfig m regs entrySteps) :=",
            "  loaded_of hv (memFacts hv hstack) bootRegs ownOk frameOk storeOk heapOk heapFactsOk progOk",
            "    capacityOk fitsOk",
            "",
            "/-- The real entry state is `Loaded` for `prog`, given every stack byte present",
            "(REVIEW.md C3; lane B2's P3 discharges it through the zero fill). -/",
            "theorem loaded",
            "    (hstack : ∀ k, Vsa.Sim.LayoutInstance.stackSL.lo ≤ k →",
            "      k < Vsa.Sim.LayoutInstance.stackSL.hi → ∃ b : BitVec 8, (bootMem script log)[k]? = some b) :",
            "    Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout prog",
            "      (bootConfig (bootMem script log) regs entrySteps) :=",
            "  loadedAt view.partial hstack",
            "",
        ]) + [
            f"end Vsa.Sim.Boot.Gen.{ln}",
        ]
        dst = BOOT_DIR / "Gen" / f"{ln}.lean"
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text("\n".join(out) + "\n")
        print("wrote", dst, len(log), "stores", len(runs), "runs")
    write_index()


def write_index():
    """`VsaBoot.lean`: the boot infrastructure and every generated trace."""
    mods = ["Vsa.While.CostEval", "Vsa.Sim.Boot.Image", "Vsa.Sim.Boot.Store", "Vsa.Sim.Boot.Ast", "Vsa.Sim.Boot.Capacity", "Vsa.Sim.Boot.Heap",
            "Vsa.Sim.Boot.Owned", "Vsa.Sim.Boot.Physical", "Vsa.Sim.Boot.Elf", "Vsa.Sim.Boot.EndToEnd"]
    mods += [f"Vsa.Sim.Boot.Gen.{f.stem}" for f in sorted((BOOT_DIR / "Gen").glob("*.lean"))]
    (ROOT / "VsaBoot.lean").write_text("".join(f"import {m}\n" for m in mods))


if __name__ == "__main__":
    main()
