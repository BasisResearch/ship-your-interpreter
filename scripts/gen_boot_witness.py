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
          entry registers.

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
    args = ap.parse_args()
    {"corpus": cmd_corpus, "image": cmd_image, "program": cmd_program}[args.cmd](args)


RUN_MAX = 64
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
        ln = lean_name(name)
        nchunks = (len(log) + CHUNK - 1) // CHUNK
        out = [
            "import Vsa.Sim.Boot.Image",
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
            f"end Vsa.Sim.Boot.Gen.{ln}",
        ]
        dst = BOOT_DIR / "Gen" / f"{ln}.lean"
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text("\n".join(out) + "\n")
        print("wrote", dst, len(log), "stores", len(runs), "runs")


if __name__ == "__main__":
    main()
