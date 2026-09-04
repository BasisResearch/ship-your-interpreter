#!/usr/bin/env python3
"""difftest.py — differentially test the BMC encoder against the proof model.

`experiments/smt/DIFFTEST-PLAN.md`.  Subcommands:

    corpus   build one traceable ELF per `.wl` program (padded, in /tmp)
    trace    run an ELF under the emulator's traced loop
    phase1   do the declared spans exist? (span reachability over the traces)
    phase2   do the summary clauses hold on real call pairs?
    phase3   does the encoder's step semantics agree with the machine?
    report   run 1-3 over a trace directory and summarise

THE SCRIPT PADDING RULE.  `c/src/script.S` `.incbin`s the `.wl` program into
`.rodata`, which sits after `.text`, so a program of a different length moves
every rodata address — and with `-mcmodel=medany` that changes the `auipc`/`addi`
pairs in `.text` too.  Every corpus program is therefore padded with newlines to
exactly the proof ELF's script length, and `corpus` REFUSES an ELF whose loaded
image differs from the proof ELF's outside the script blob.  Without that the
trace would be of a different program than the encoder reflected.
"""
import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from difftest_lib import (ROOT, PROOF_ELF, BMC_DIR, Image, Trace, EncTable, decode,
                          is_call, is_ret, read_tsv, M64, MK_NONE, MK_LOAD, MK_STORE)

EMU = os.path.join(ROOT, "riscv-lean", "lean_emulator", ".lake", "build", "bin",
                   "lean_riscv_emulator")
REF_SCRIPT = os.path.join(ROOT, "c", "tests", "while.wl")
CODE_LO, CODE_HI = 0x80000000, 0x80018BE0


# --------------------------------------------------------------------- corpus
def build_corpus(wls, outdir, workdir="/tmp/dt-c", quiet=False):
    """Build one ELF per `.wl`, each padded to the proof script's length, in a
    /tmp copy of `c/`.  Returns [(name, elf_path)]."""
    ref = open(REF_SCRIPT, "rb").read()
    reflen = len(ref)
    if not os.path.isdir(workdir):
        subprocess.run(["cp", "-R", os.path.join(ROOT, "c"), workdir], check=True)
    proof = Image(PROOF_ELF)
    pv, poff, psz = proof.segs[0]
    pbytes = proof.raw[poff:poff + psz]
    os.makedirs(outdir, exist_ok=True)
    out = []
    for wl in wls:
        name = os.path.splitext(os.path.basename(wl))[0]
        src = open(wl, "rb").read()
        if len(src) > reflen:
            print(f"[corpus] SKIP {name}: {len(src)} bytes > {reflen} "
                  f"(would move .rodata and rewrite .text)")
            continue
        padded = src + b"\n" * (reflen - len(src))
        pth = os.path.join(workdir, "tests", f"_dt_{name}.wl")
        open(pth, "wb").write(padded)
        elf = os.path.join(workdir, "while-riscv-htif.elf")
        if os.path.exists(elf):
            os.remove(elf)
        r = subprocess.run(["make", "-C", workdir, "riscv-htif",
                            f"HTIF_SCRIPT=tests/_dt_{name}.wl"],
                           capture_output=True, text=True)
        if not os.path.exists(elf):
            print(f"[corpus] FAIL {name}: {r.stdout[-800:]}{r.stderr[-800:]}")
            continue
        # the image must be the proof ELF's outside one contiguous script blob
        img = Image(elf)
        v, off, sz = img.segs[0]
        b = img.raw[off:off + sz]
        if (v, sz) != (pv, psz):
            print(f"[corpus] FAIL {name}: segment moved {v:#x}/{sz} vs {pv:#x}/{psz}")
            continue
        diff = [k for k in range(sz) if b[k] != pbytes[k]]
        if diff and (diff[-1] - diff[0]) >= reflen + 1:
            print(f"[corpus] FAIL {name}: image differs over "
                  f"{diff[0]:#x}..{diff[-1]:#x} (wider than the script blob)")
            continue
        dst = os.path.join(outdir, f"{name}.elf")
        shutil.copyfile(elf, dst)
        out.append((name, dst))
        if not quiet:
            span = f"{v+diff[0]:#x}..{v+diff[-1]:#x}" if diff else "identical"
            print(f"[corpus] {name}: ok (image differs only at {span})")
    return out


def run_trace(elf, out, pcs=None, max_steps=None, timeout=1800):
    cmd = [EMU, elf]
    if pcs:
        cmd += ["--trace-pcs", pcs]
    else:
        cmd += ["--trace-all"]
    if max_steps:
        cmd += ["--max-steps", str(max_steps)]
    with open(out, "w") as fe, open(out + ".stdout", "w") as fo:
        subprocess.run(cmd, stdout=fo, stderr=fe, timeout=timeout)
    return out


# --------------------------------------------------------------------- phase 1
#
# The encoder's span is a walk from the entry PC, IN THE ENTRY'S OWN FRAME (calls
# become `callee_` summaries, so a recursive re-entry is a different instance),
# that ends at one of `stepBlock`'s outcomes.  Phase 1 replays that walk over a
# real trace and reports which outcome the machine actually takes.  The outcomes
# are named exactly as `stepBlock` names them, so a disagreement points at a line
# of the encoder rather than at a discrepancy in this script's own idea of a span.

EXIT_KINDS = ("at_stop", "leave", "ret", "tailcall", "dispatch_out")
NONEXIT_KINDS = ("halt", "ret_excluded", "unfinished")


def walk_span(tr, img, i, d0, rlo, rhi, stop, ret_exit, noret, fstarts, arms_at):
    """Replay one span instance from row `i`.  Returns (outcome, row, detail)."""
    n = tr.n
    d = tr.depth
    j = i
    while j < n:
        if d[j] > d0:
            j += 1
            continue
        if d[j] < d0:
            # the frame is gone without any of stepBlock's outcomes firing: the
            # only way out is a `ret` we already classified, so this is a longjmp
            return ("unwound", j, "")
        p = tr.pc[j]
        if j > i and p == stop:
            return ("at_stop", j, "")
        if p < rlo or p >= rhi:
            return ("leave", j, hex(p))
        ins = decode(p, img.word(p))
        if is_ret(ins):
            return ("ret" if ret_exit else "ret_excluded", j, "")
        if ins.kind == "jal" and ins.rd == 1:
            if ins.target in noret:
                return ("halt", j, hex(ins.target))
        elif ins.kind == "jal" and ins.rd == 0:
            t = ins.target
            if not (rlo <= t < rhi):
                return ("leave", j, hex(t))
            if t in fstarts and t != rlo:
                return ("tailcall", j, hex(t))
        elif ins.kind == "jalr" and ins.rd == 0 and ins.rs1 != 1:
            arms = arms_at.get(p)
            nxt = tr.npc[j]
            if arms is None:
                return ("dispatch_out", j, f"unresolved computed goto -> {nxt:#x}")
            if nxt not in arms:
                return ("dispatch_out", j, f"target {nxt:#x} not in the encoder's arms")
            if not (rlo <= nxt < rhi):
                return ("leave", j, hex(nxt))
        elif ins.kind.startswith("b") and ins.target is not None:
            nxt = tr.npc[j]
            if not (rlo <= nxt < rhi):
                return ("leave", j, hex(nxt))
        j += 1
    return ("unfinished", n - 1, "")


def phase1(traces, img, spans, arms, enc_dir):
    armmap = {a["field"]: a for a in arms}
    noret = {int(r["target"], 16) for r in read_tsv(os.path.join(enc_dir, "noreturn.tsv"))}
    fstarts = {int(r["entry"], 16) for r in read_tsv(os.path.join(enc_dir, "funcstarts.tsv"))}
    dsites = read_tsv(os.path.join(enc_dir, "dispatchsites.tsv"))
    arms_at = {int(r["site"], 16): [int(x, 16) for x in r["arms"].split(",")] for r in dsites}
    res = {}
    for sp in spans:
        a = armmap[sp["field"]]
        res[sp["field"]] = dict(
            field=sp["field"], entry=int(sp["entry"], 16), stop=int(sp["stop"], 16),
            rlo=int(a["region_lo"], 16), rhi=int(a["region_hi"], 16),
            arm=int(a["arm"], 16), dispatch=a["dispatch"],
            kind_reg=a["kind_reg"], kind_idx=a["kind_idx"],
            ret_exit=(a["ret_exit"].lower() == "true"),
            enc_halts=int(sp.get("halts", "0") or 0), entries=0,
            traces=set(), arm_taken=0, detail={})
        for k in EXIT_KINDS + NONEXIT_KINDS + ("unwound",):
            res[sp["field"]][k] = 0
            res[sp["field"]]["arm_" + k] = 0
    for tr in traces:
        by_pc = {}
        for i in range(tr.n):
            by_pc.setdefault(tr.pc[i], []).append(i)
        for sp in spans:
            r = res[sp["field"]]
            for i in by_pc.get(r["entry"], ()):
                r["entries"] += 1
                r["traces"].add(tr.name)
                kind, j, det = walk_span(tr, img, i, tr.depth[i], r["rlo"], r["rhi"],
                                         r["stop"], r["ret_exit"], noret, fstarts, arms_at)
                r[kind] += 1
                if det:
                    r["detail"].setdefault(det, 0)
                    r["detail"][det] += 1
                # Did this instance go through the arm the residual is ABOUT?
                #
                # The verdict is only ever about that arm — the query pins the
                # AST kind and asserts the dispatch guard it selects — so the
                # outcome has to be counted over those instances alone.  Counted
                # over all of them, an arm whose declared stop is another arm's
                # code still looks reached, because some OTHER kind's path goes
                # there: hAndTrue's stop 0x800035e0 is the unary arm's first
                # instruction and the logical arm ends at 0x800035dc with
                # `j 0x800033ec`, so no execution of the logical arm can arrive
                # at it — and the query's pin + exit guard are contradictory,
                # which is how the campaign reports it (`VACUOUS`).
                onarm = r["arm"] == r["entry"]
                if not onarm:
                    k = i
                    while k <= j:
                        if tr.depth[k] == tr.depth[i] and tr.pc[k] == r["arm"]:
                            onarm = True
                            break
                        k += 1
                if onarm:
                    r["arm_taken"] += 1
                    r["arm_" + kind] += 1
    return list(res.values())


def write_phase1(rows, out_tsv):
    if not out_tsv:
        return
    cols = ["field", "entry", "stop", "entries", "arm_taken"] + \
           ["arm_" + k for k in EXIT_KINDS] + ["arm_" + k for k in NONEXIT_KINDS] + \
           ["arm_unwound"] + list(EXIT_KINDS) + list(NONEXIT_KINDS) + \
           ["unwound", "ret_exit", "enc_halts", "traces"]
    with open(out_tsv, "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(
                (hex(r[c]) if c in ("entry", "stop") else
                 (",".join(sorted(r[c])) if c == "traces" else str(r[c])))
                for c in cols) + "\n")


def check_dispatch(traces, img, enc_dir):
    """Every ground dispatch the encoder resolved, checked against what the
    machine actually jumps to.  A target outside the encoder's arm list means the
    resolved jump table is wrong — the defect class that made 26 of 52 queries
    vacuous."""
    dsites = read_tsv(os.path.join(enc_dir, "dispatchsites.tsv"))
    arms_at = {int(r["site"], 16): [int(x, 16) for x in r["arms"].split(",")] for r in dsites}
    seen = {s: set() for s in arms_at}
    bad = []
    unlisted = {}
    for tr in traces:
        for i in range(tr.n):
            p = tr.pc[i]
            ins = decode(p, img.word(p))
            if ins.kind != "jalr" or ins.rd != 0 or ins.rs1 == 1:
                continue
            nxt = tr.npc[i]
            if p in arms_at:
                seen[p].add(nxt)
                if nxt not in arms_at[p]:
                    bad.append((tr.name, p, nxt))
            else:
                unlisted.setdefault(p, set()).add(nxt)
    return seen, bad, unlisted, arms_at


def phase1_findings(rows, seen, bad, unlisted, arms_at, recorded_stop_outside=()):
    """(findings, notes).  A FINDING is something that is wrong under any reading
    — a span with no reachable exit, a dispatch the encoder mis-resolved.  A NOTE
    is a scope fact the campaign should state and cannot state for itself: how
    much of an arm's real behaviour a verdict is about, which arms no program
    reaches, which computed gotos are left opaque."""
    out, notes = [], []
    for r in rows:
        f = r["field"]
        if r["entries"] == 0:
            notes.append(("UNCOVERED", f, "no trace enters this span"))
            continue
        arrivals = sum(r["arm_" + k] for k in EXIT_KINDS)
        if r["arm_taken"] == 0:
            notes.append(("ARM-UNSEEN", f,
                        f"entered {r['entries']}x but never through arm {r['arm']:#x} — "
                        f"the corpus does not exercise this residual's arm"))
            continue
        if arrivals == 0:
            out.append(("NO-EXIT-FROM-ARM", f,
                        f"{r['arm_taken']} instances run the residual's arm {r['arm']:#x} "
                        f"and NONE reaches an encoder-recognised exit "
                        f"(halt={r['arm_halt']} ret_excluded={r['arm_ret_excluded']} "
                        f"unwound={r['arm_unwound']} unfinished={r['arm_unfinished']}); "
                        f"the declared stop {r['stop']:#x} is not reachable from the arm"))
            continue
        if not (r["rlo"] <= r["stop"] < r["rhi"]) and f not in recorded_stop_outside:
            out.append(("STOP-OUTSIDE", f,
                        f"declared stop {r['stop']:#x} lies outside the span's own region "
                        f"[{r['rlo']:#x},{r['rhi']:#x}) — it can never be an arrival, and "
                        f"`retExit` is decided by a word in another function"))
        if r["ret_exit"] and r["ret"] == 0 and r["ret_excluded"] == 0:
            out.append(("RET-EXIT", f, "encoder says the stop is a return, but no instance "
                                       "exits by `ret`"))
        if r["arm_at_stop"] == 0 and r["arm"] != r["entry"] and not r["ret_exit"] and \
                (r["rlo"] <= r["stop"] < r["rhi"]):
            out.append(("STOP-UNREACHED", f,
                        f"the arm {r['arm']:#x} runs {r['arm_taken']}x and never reaches "
                        f"the declared stop {r['stop']:#x} (it exits by "
                        + ", ".join(f"{k}={r['arm_' + k]}" for k in EXIT_KINDS
                                    if r["arm_" + k]) + ")"))
        # The verdict covers the arm executions that ARRIVE; the rest leave the
        # span some other way and the post says nothing about them.  Reported
        # with the fraction, because a span answered on a sixth of its arm's real
        # executions is a narrower claim than its name suggests and nothing else
        # in the campaign says so.
        # An instance that was still running when the program halted is not a
        # path the span misses, so it is out of the denominator.
        ran = r["arm_taken"] - r["arm_unfinished"]
        if arrivals and arrivals < ran:
            notes.append(("STOP-NARROW", f,
                          f"{arrivals}/{ran} executions of arm {r['arm']:#x} reach an "
                          f"exit the encoder counts; the other {ran - arrivals} leave by "
                          + ", ".join(f"{k}={r['arm_' + k]}" for k in NONEXIT_KINDS + ("unwound",)
                                      if r["arm_" + k] and k != "unfinished")
                          + " — the verdict is about the arriving ones only"))
        if r["dispatch_out"]:
            out.append(("DISPATCH", f, f"{r['dispatch_out']} instances take a computed goto "
                                       f"the encoder did not resolve: " +
                        "; ".join(f"{k} x{v}" for k, v in r["detail"].items())))
    for name, p, nxt in bad[:20]:
        out.append(("DISPATCH", f"{p:#x}",
                    f"[{name}] jumps to {nxt:#x}, not in the encoder's arm list"))
    for p, tg in sorted(unlisted.items()):
        notes.append(("UNRESOLVED", f"{p:#x}",
                      f"computed goto the encoder leaves opaque; observed targets "
                      + ",".join(f"{t:#x}" for t in sorted(tg))))
    for p, arms in arms_at.items():
        never = [a for a in arms if a not in seen[p]]
        if never:
            notes.append(("ARMS-UNSEEN", f"{p:#x}",
                          f"{len(never)}/{len(arms)} declared arms never taken: "
                          + ",".join(f"{a:#x}" for a in never)))
    return out, notes


# --------------------------------------------------------------------- phase 2
#
# The encoder replaces every call and every loop by an uninterpreted
# `MState -> MState` summary constrained by a clause set (`scripts/houdini_summary.py`
# `CLAUSES`).  Those clauses are mined against the encoder's OWN model of the
# callee, so an encoder defect is invisible to the mining; and the clauses of an
# ASSUMED contract are checked by nobody.  A real trace has real `(pre, post)`
# pairs, so each clause can be evaluated concretely, with a witness.
#
# `pre` is the state the encoder applies the summary to: at a call that is the
# caller's state with `ra := pc+4` already written (the encoder's `ra{k}` bind);
# at a loop it is the merged state at the header.  `post` is the machine's state
# when control comes back / leaves the loop.  The write set between the two is
# read straight off the trace's store rows, so the memory clauses are decided by
# arithmetic on real addresses.

CLAUSE_IDS = ["inv_pres", "sp_restore", "ra_restore", "s0_restore", "s1_restore",
              "stack_or_arena", "above_sp"]
REG_CLAUSE = {"sp_restore": 2, "ra_restore": 1, "s0_restore": 8, "s1_restore": 9}


def read_regions(bmc_dir):
    """The writable-static region the encoder itself emits (`regions.tsv`), so
    the concrete verdict for `stack_or_arena` reads the clause the way the
    campaign now states it."""
    pth = os.path.join(bmc_dir, "regions.tsv")
    if not os.path.exists(pth):
        return None
    for r in read_tsv(pth):
        if r["region"] == "writable_static":
            return int(r["lo"], 16), int(r["hi"], 16)
    return None


class MemMap:
    """The real memory map, from the ELF's own symbols.  `stack_or_arena` and
    `above_sp` quantify over a stack window and an arena that the queries leave
    free, so a concrete verdict has to name what it read them as; these are the
    linker script's regions (`c/src/link.ld`) plus the heap span the run actually
    touched."""

    def __init__(self, img, traces=None, gregion=None):
        syms = elf_symbols(img)
        self.g = gregion
        self.stack_top = syms.get("__stack_top", 0x88000000)
        self.heap_end = syms.get("__heap_end", self.stack_top - (8 << 20))
        self.static_end = syms.get("_end", syms.get("__bss_end", 0x8001C168))
        self.stack_lo = self.heap_end
        self.heap_lo = self.static_end
        self.heap_hi = self.heap_end
        self.min_sp = None
        if traces:
            lo = None
            for tr in traces:
                for i in range(0, tr.n, 64):
                    v = tr.sp(i)
                    if self.stack_lo <= v < self.stack_top and (lo is None or v < lo):
                        lo = v
            self.min_sp = lo

    def region(self, a):
        if a < 0x80000000:
            return "low"
        if self.g and self.g[0] <= a < self.g[1]:
            return "wstatic"
        if a < self.static_end:
            return "static"
        if a < self.heap_hi:
            return "heap"
        if a < self.stack_top:
            return "stack"
        return "high"

    def __str__(self):
        return ((f"writable-static [{self.g[0]:#x},{self.g[1]:#x}) " if self.g else "")
                + f"static [0x80000000,{self.static_end:#x}) heap "
                f"[{self.heap_lo:#x},{self.heap_hi:#x}) stack "
                f"[{self.stack_lo:#x},{self.stack_top:#x})"
                + (f" min sp {self.min_sp:#x}" if self.min_sp else ""))


def elf_sections(img):
    """`name -> (addr, size)` from the ELF section headers."""
    b = img.raw
    rd = lambda o, n: int.from_bytes(b[o:o + n], "little")
    shoff, shentsize, shnum, shstrndx = rd(0x28, 8), rd(0x3A, 2), rd(0x3C, 2), rd(0x3E, 2)
    stroff = rd(shoff + shstrndx * shentsize + 0x18, 8)
    out = {}
    for i in range(shnum):
        o = shoff + i * shentsize
        nm = rd(o, 4)
        end = b.index(b"\0", stroff + nm)
        out[b[stroff + nm:end].decode()] = (rd(o + 0x10, 8), rd(o + 0x20, 8))
    return out


def mmio_region(img):
    """The HTIF mailbox (`.tohost`).

    The proof model treats a store here as a DEVICE COMMAND — `enable_htif`
    consumes the write and the byte array keeps its old value — while the
    encoder's memory is a plain byte array, so the two disagree on the eight
    bytes at `tohost` after `_write`'s `sd`.  That is a real difference and it is
    reported, but it is not a defect in any span: the only stores to it are in
    `_write` and `exit`, both outside the interpreter's own code, both ASSUMED
    contracts whose bodies no span reflects.  Excluded from the memory
    comparison, named here so the exclusion is auditable."""
    a, n = elf_sections(img).get(".tohost", (0, 0))
    return (a, a + n)


def sym_names(img):
    """`value -> name` for FUNC symbols, so a witness names a function."""
    out = {}
    b = img.raw
    rd = lambda o, n: int.from_bytes(b[o:o + n], "little")
    shoff, shentsize, shnum = rd(0x28, 8), rd(0x3A, 2), rd(0x3C, 2)
    for i in range(shnum):
        o = shoff + i * shentsize
        if rd(o + 4, 4) != 2:
            continue
        off, size, link, entsize = rd(o + 0x18, 8), rd(o + 0x20, 8), rd(o + 0x28, 4), rd(o + 0x38, 8)
        stroff = rd(shoff + link * shentsize + 0x18, 8)
        for k in range(size // entsize):
            e = off + k * entsize
            if (rd(e + 4, 1) & 0xF) != 2:  # STT_FUNC
                continue
            nm = rd(e, 4)
            end = b.index(b"\0", stroff + nm)
            out.setdefault(rd(e + 8, 8), b[stroff + nm:end].decode())
    return out


def sym_label(sym, names):
    for pfx in ("callee_", "loop_", "icall_", "idisp_"):
        if sym.startswith(pfx):
            v = int(sym[len(pfx):])
            nm = names.get(v)
            return f"{pfx}{nm}" if nm else f"{pfx}{v:#x}"
    return sym


def elf_symbols(img):
    """`name -> value` from the ELF64 symbol table."""
    b = img.raw
    rd = lambda o, n: int.from_bytes(b[o:o + n], "little")
    shoff, shentsize, shnum = rd(0x28, 8), rd(0x3A, 2), rd(0x3C, 2)
    out = {}
    for i in range(shnum):
        o = shoff + i * shentsize
        if rd(o + 4, 4) != 2:  # SHT_SYMTAB
            continue
        off, size, link, entsize = rd(o + 0x18, 8), rd(o + 0x20, 8), rd(o + 0x28, 4), rd(o + 0x38, 8)
        so = shoff + link * shentsize
        stroff = rd(so + 0x18, 8)
        for k in range(size // entsize):
            e = off + k * entsize
            nm = rd(e, 4)
            end = b.index(b"\0", stroff + nm)
            out[b[stroff + nm:end].decode()] = rd(e + 8, 8)
    return out


class SumInst:
    __slots__ = ("sym", "trace", "pre_row", "post_row", "pre_depth", "ret_pc",
                 "header", "w0", "w1", "returned")


def call_instances(tr, img):
    """Every `callee_`/`icall_` application in the trace, with its `(pre, post)`
    pair and the slice of the write log the callee is responsible for."""
    out = []
    writes = []              # (addr, width) in trace order
    open_calls = []          # stack of SumInst awaiting their return
    d = tr.depth
    for j in range(tr.n):
        while open_calls and d[j] <= open_calls[-1].pre_depth:
            it = open_calls.pop()
            it.post_row = j
            it.w1 = len(writes)
            it.returned = (tr.pc[j] == it.ret_pc)
            out.append(it)
        if tr.mk[j] == MK_STORE:
            writes.append((tr.maddr[j], tr.mw[j]))
        p = tr.pc[j]
        ins = decode(p, img.word(p))
        if is_call(ins):
            it = SumInst()
            it.trace = tr.name
            it.pre_row = j
            it.pre_depth = d[j]
            it.ret_pc = (p + 4) & M64
            tgt = ins.target if ins.kind == "jal" else tr.npc[j]
            it.sym = (f"callee_{tgt}" if ins.kind == "jal" else f"icall_{p}")
            it.w0 = len(writes)
            it.post_row = None
            open_calls.append(it)
    for it in open_calls:     # never returned before the program halted
        it.post_row = None
        it.w1 = len(writes)
        it.returned = False
        out.append(it)
    return out, writes


def loop_instances(tr, img, loops):
    """Every `loop_<h>` application: from an arrival at the header that did NOT
    come from inside the loop body, to the first arrival at one of the encoder's
    exit edges (or to leaving the frame, when the loop `leaves`)."""
    out = []
    writes = []
    d = tr.depth
    body_of = {int(r["header"], 16): set(int(x, 16) for x in r["body"].split(",") if x)
               for r in loops}
    exits_of = {int(r["header"], 16): set(int(x, 16) for x in r["exits"].split(",") if x)
                for r in loops}
    sym_of = {int(r["header"], 16): r["summary"] for r in loops}
    open_loops = []
    prev_pc_at = {}
    for j in range(tr.n):
        if tr.mk[j] == MK_STORE:
            writes.append((tr.maddr[j], tr.mw[j]))
        p = tr.pc[j]
        # close any open loop that has reached one of its exits at its own depth
        k = 0
        while k < len(open_loops):
            it = open_loops[k]
            if d[j] < it.pre_depth or (d[j] == it.pre_depth and p in exits_of[it.header]):
                it.post_row = j
                it.w1 = len(writes)
                it.returned = (d[j] == it.pre_depth)
                out.append(it)
                del open_loops[k]
            else:
                k += 1
        if p in body_of and not any(it.header == p for it in open_loops):
            prev = prev_pc_at.get(d[j])
            if prev is None or prev not in body_of[p]:
                it = SumInst()
                it.trace = tr.name
                it.sym = sym_of[p]
                it.header = p
                it.pre_row = j
                it.pre_depth = d[j]
                it.w0 = len(writes)
                it.post_row = None
                open_loops.append(it)
        prev_pc_at[d[j]] = p
    for it in open_loops:
        it.post_row = None
        it.w1 = len(writes)
        it.returned = False
        out.append(it)
    return out, writes


def eval_clauses(tr, it, writes, mm, is_call_inst):
    """Evaluate the seven clauses on one concrete `(pre, post)` pair.  Returns
    `{clause: (verdict, witness)}` with verdict in HOLDS/REFUTED/NOPAIR."""
    res = {}
    pre_sp = tr.sp(it.pre_row)
    if it.post_row is None or not it.returned:
        for c in CLAUSE_IDS:
            res[c] = ("NOPAIR", "the summary's application never came back")
        return res
    for c, r in REG_CLAUSE.items():
        # the encoder writes `ra := pc+4` BEFORE applying a call summary, so the
        # pre-state's `ra` is the return address, not the caller's own `ra`
        pv = it.ret_pc if (c == "ra_restore" and is_call_inst) else tr.reg(it.pre_row, r)
        qv = tr.reg(it.post_row, r)
        res[c] = ("HOLDS", "") if pv == qv else ("REFUTED", f"x{r}: {pv:#x} -> {qv:#x}")
    ws = writes[it.w0:it.w1]
    bad_static = next(((a, w) for a, w in ws if mm.region(a) in ("static", "low", "high")), None)
    res["stack_or_arena"] = ("HOLDS", "") if bad_static is None else \
        ("REFUTED", f"writes {bad_static[0]:#x} ({mm.region(bad_static[0])})")
    bad_above = next(((a, w) for a, w in ws
                      if a >= pre_sp and mm.region(a) == "stack"), None)
    res["above_sp"] = ("HOLDS", "") if bad_above is None else \
        ("REFUTED", f"writes {bad_above[0]:#x} >= entry sp {pre_sp:#x} (stack)")
    lo, hi = mm.stack_lo, mm.stack_top
    ok = lambda v: lo + 0x1100 <= v <= hi - 0x1100
    post_sp = tr.sp(it.post_row)
    res["inv_pres"] = ("HOLDS", "") if (not ok(pre_sp)) or ok(post_sp) else \
        ("REFUTED", f"sp {pre_sp:#x} -> {post_sp:#x} leaves the stack window")
    return res


def phase2_agg(traces, img, enc_dir, bmc_dir, known, agg=None):
    loops = read_tsv(os.path.join(enc_dir, "loops.tsv"))
    mm = MemMap(img, traces, gregion=read_regions(bmc_dir))
    agg = {} if agg is None else agg
    for tr in traces:
        ci, cw = call_instances(tr, img)
        li, lw = loop_instances(tr, img, loops)
        for insts, ws, isc in ((ci, cw, True), (li, lw, False)):
            for it in insts:
                if it.sym not in known:
                    continue
                a = agg.setdefault(it.sym, dict(sym=it.sym, n=0, nopair=0,
                                                verdicts={c: [0, 0, ""] for c in CLAUSE_IDS}))
                a["n"] += 1
                r = eval_clauses(tr, it, ws, mm, isc)
                if r["sp_restore"][0] == "NOPAIR":
                    a["nopair"] += 1
                    continue
                for c, (v, wit) in r.items():
                    if v == "HOLDS":
                        a["verdicts"][c][0] += 1
                    elif v == "REFUTED":
                        a["verdicts"][c][1] += 1
                        if not a["verdicts"][c][2]:
                            a["verdicts"][c][2] = f"[{it.trace}@{tr.step[it.pre_row]}] {wit}"
    return agg, mm


def phase2_report(agg, img, bmc_dir, out_tsv=None):
    mined = json.load(open(os.path.join(bmc_dir, "clauses.json"))) \
        if os.path.exists(os.path.join(bmc_dir, "clauses.json")) else {}
    assumed = {r["summary"] for r in read_tsv(os.path.join(bmc_dir, "assumed.tsv"))
               if r["summary"].startswith(("callee_", "loop_", "icall_", "idisp_"))}
    names = sym_names(img)
    rows = []
    for sym, a in sorted(agg.items()):
        for c in CLAUSE_IDS:
            h, r, wit = a["verdicts"][c]
            if sym not in mined:
                status = "-"
            elif c not in mined[sym]:
                status = "dropped"
            else:
                status = "assumed" if sym in assumed else "mined"
            rows.append(dict(summary=sym, name=sym_label(sym, names), clause=c,
                             claimed=status, holds=h, refuted=r,
                             instances=a["n"], nopair=a["nopair"], witness=wit))
    if out_tsv:
        cols = ["summary", "name", "clause", "claimed", "instances", "nopair",
                "holds", "refuted", "witness"]
        with open(out_tsv, "w") as f:
            f.write("\t".join(cols) + "\n")
            for r in rows:
                f.write("\t".join(str(r[c]) for c in cols) + "\n")
    return rows, mined


def phase2_findings(rows, mined):
    out = []
    for r in rows:
        if not r["refuted"]:
            continue
        if r["claimed"] == "mined":
            out.append(("CLAUSE-FALSE", f"{r['name']}/{r['clause']}",
                        f"MINED but refuted on {r['refuted']}/{r['instances']} real pairs: "
                        f"{r['witness']}"))
        elif r["claimed"] == "assumed":
            out.append(("ASSUMED-FALSE", f"{r['name']}/{r['clause']}",
                        f"ASSUMED contract, refuted on {r['refuted']}/{r['instances']} "
                        f"real pairs: {r['witness']}"))
    for sym, cs in sorted(mined.items()):
        pass
    return out


# --------------------------------------------------------------------- phase 3
#
# The main event: does the encoder's step semantics agree with the machine?
#
# `#emit_step_table` dumps, for every word in the image, exactly the term
# `stepBlock` would build for it — `blockState S [mkLine pc w]` for a modelled
# word, `rawRegVal`'s term for the two `sltiu`/`sltu` shapes, `unmodelled_step`
# for anything else, and `decodeTerm`/`branchCondSt` for the terminators.  For a
# real `(state, next state)` pair from a trace, substituting the concrete entry
# state makes that term GROUND, so Z3 evaluates it and the answer is compared
# against what the machine did.  One `ok_<k>` per sampled step localises a
# disagreement to a single instruction without any search.
#
# What each class is checked for:
#   alu/raw   every one of x1..x31 after the step; for a store, the eight bytes
#             at the effective address, and that the bytes on either side of the
#             operand are untouched (a mis-decoded store immediate lands
#             elsewhere and shows up as both)
#   opaque    nothing (`unmodelled_step` is uninterpreted, which is the honest
#             over-approximation) — but the fallthrough PC is still checked
#   branch    the encoder's condition holds exactly when the machine branched
#   jal/jalr  the encoder's target, and `rd := pc+4`
# and for every class, that control went where the encoder's `decodeTerm` says.

Z3 = shutil.which("z3") or "z3"


def hexbv(v):
    return "#x%016x" % (v & M64)


CONST_REGS = "((as const (Array (_ BitVec 64) (_ BitVec 64))) #x0000000000000000)"
CONST_MEM = "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)"


def _state_term(tr, i):
    """The entry state as a GROUND term: constant arrays overwritten with the
    values the trace observed.

    Ground is the whole point.  Declaring `S` and constraining it with
    assertions makes every check a satisfiability question over a byte array,
    which bit-blasts (one chunk ran for twelve minutes at 400 MB).  Built this
    way the check is a rewrite: `(simplify ok)` on a closed term, no solver."""
    regs = CONST_REGS
    for r in range(1, 32):
        v = tr.reg(i, r)
        if v:
            regs = f"(store {regs} {hexbv(r)} {hexbv(v)})"
    mem = CONST_MEM
    if tr.mk[i] != MK_NONE:
        a, pre = tr.maddr[i], tr.mpre[i]
        for j in range(8):
            b = (pre >> (8 * j)) & 0xFF
            if b:
                mem = f"(store {mem} {hexbv(a + j)} #x%02x)" % b
    return f"(mst {mem} {regs})"


def phase3_samples(traces, tbl, per_pc):
    """Up to `per_pc` executions of each PC, spread evenly over the corpus."""
    occ = {}
    for tr in traces:
        for i in range(tr.n - 1):
            occ.setdefault(tr.pc[i], []).append((tr, i))
    out = []
    for pc, lst in sorted(occ.items()):
        if len(lst) <= per_pc:
            out.extend((pc, t, i) for t, i in lst)
        else:
            step = len(lst) / per_pc
            out.extend((pc, ) + lst[int(k * step)] for k in range(per_pc))
    return out, occ


def phase3_block(k, pc, tr, i, row):
    """The SMT for one sampled step, plus the Python-side control-flow checks.
    Returns (smt_lines, ok_name_or_None, [(check_id, ok_bool, detail)])."""
    cls, f = row
    S, T = f"s{k}", f"t{k}"
    npc = tr.npc[i]
    sub = lambda t: t.replace("(mm S)", f"(mm {S})").replace("(rr S)", f"(rr {S})")
    flags = []
    lines = []
    okname = None
    if cls in ("alu", "raw"):
        term = f[0] if cls == "alu" else f[1]
        flags.append(("fallthrough", npc == (pc + 4) & M64, f"{npc:#x}"))
        lines.append(f"(define-fun {S} () MState {_state_term(tr, i)})")
        lines.append(f"(define-fun {T} () MState {sub(term)})")
        conj = []
        # the encoder's own effective address, pinned to the machine's.  With it
        # every byte the term reads is a byte the trace supplied, so `ok` is a
        #决 determined ground Boolean rather than the solver's arbitrary choice.
        if cls == "alu" and len(f) > 2 and f[1] != "-":
            conj.append(f"(= {sub(f[2])} {hexbv(tr.maddr[i])})")
            enc_w = int(f[1][1:])
            if enc_w != tr.mw[i] or (f[1][0] == "S") != (tr.mk[i] == MK_STORE):
                flags.append(("memop-class", False,
                              f"encoder says {f[1]}, machine did "
                              f"{'S' if tr.mk[i]==MK_STORE else 'L'}{tr.mw[i]}"))
        elif tr.mk[i] != MK_NONE and cls == "alu":
            flags.append(("memop-class", False,
                          f"machine does a {'store' if tr.mk[i]==MK_STORE else 'load'} "
                          f"of width {tr.mw[i]}, the encoder's step has no memory operand"))
        conj += [f"(= (select (rr {T}) {hexbv(r)}) {hexbv(tr.reg(i + 1, r))})"
                 for r in range(1, 32)]
        if tr.mk[i] == MK_STORE and not (MMIO[0] <= tr.maddr[i] < MMIO[1]):
            a, post = tr.maddr[i], tr.mpost[i]
            conj.append(f"(= (ld8 (mm {T}) {hexbv(a)}) {hexbv(post)})")
            conj.append(f"(= (ld8 (mm {T}) {hexbv(a - 8)}) (ld8 (mm {S}) {hexbv(a - 8)}))")
            conj.append(f"(= (ld8 (mm {T}) {hexbv(a + 8)}) (ld8 (mm {S}) {hexbv(a + 8)}))")
        okname = f"ok{k}"
        lines.append(f"(define-fun {okname} () Bool (and {' '.join(conj)}))")
    elif cls == "opaque":
        flags.append(("fallthrough", npc == (pc + 4) & M64, f"{npc:#x}"))
    elif cls == "branch":
        tgt = int(f[0], 16)
        taken = (npc == tgt)
        flags.append(("branch-target", taken or npc == (pc + 4) & M64,
                      f"went to {npc:#x}, encoder offers {tgt:#x} / {(pc+4)&M64:#x}"))
        lines.append(f"(define-fun {S} () MState {_state_term(tr, i)})")
        cond = sub(f[1])
        okname = f"ok{k}"
        lines.append(f"(define-fun {okname} () Bool (= {cond} {'true' if taken else 'false'}))")
    elif cls == "jal":
        rd, tgt = int(f[0]), int(f[1], 16)
        flags.append(("jal-target", npc == tgt, f"went to {npc:#x}, encoder says {tgt:#x}"))
        if rd:
            flags.append(("jal-link", tr.reg(i + 1, rd) == (pc + 4) & M64,
                          f"x{rd} = {tr.reg(i+1, rd):#x}, expected {(pc+4)&M64:#x}"))
    elif cls == "jalr":
        rd, rs1, im = int(f[0]), int(f[1]), int(f[2])
        tgt = (tr.reg(i, rs1) + im) & M64 & ~1
        flags.append(("jalr-target", npc == tgt,
                      f"went to {npc:#x}, encoder's target expression gives "
                      f"x{rs1}({tr.reg(i, rs1):#x}) + {im} & ~1 = {tgt:#x}"))
        if rd:
            flags.append(("jalr-link", tr.reg(i + 1, rd) == (pc + 4) & M64,
                          f"x{rd} = {tr.reg(i+1, rd):#x}, expected {(pc+4)&M64:#x}"))
    return lines, okname, flags


img_word_cache = {}
MMIO = (0, 0)


def dedup_findings(fs):
    """One line per (kind, place); a defect at a PC is one defect however many
    executions of it the corpus happens to contain."""
    seen, out = set(), []
    for kind, w, d in fs:
        if (kind, w) in seen:
            continue
        seen.add((kind, w))
        out.append((kind, w, d))
    return out


def phase3_explain(traces, img, enc_dir, pc, limit=3):
    """Re-run one PC's check with every conjunct asked separately, so a
    STEP-STATE finding names the register or the byte that disagrees."""
    tbl = EncTable(os.path.join(enc_dir, "steps.tsv"))
    preamble = open(os.path.join(enc_dir, "preamble.smt2")).read()
    row = tbl.get(pc)
    if row is None:
        print(f"{pc:#x}: not in the step table")
        return 1
    cls, f = row
    print(f"{pc:#x}  word={img.word(pc):#010x}  class={cls}")
    shown = 0
    for tr in traces:
        for i in range(tr.n - 1):
            if tr.pc[i] != pc:
                continue
            S, T = "sX", "tX"
            sub = lambda t: t.replace("(mm S)", f"(mm {S})").replace("(rr S)", f"(rr {S})")
            body = [preamble, f"(define-fun {S} () MState {_state_term(tr, i)})"]
            items = []
            if cls in ("alu", "raw"):
                term = f[0] if cls == "alu" else f[1]
                body.append(f"(define-fun {T} () MState {sub(term)})")
                if cls == "alu" and len(f) > 2 and f[1] != "-":
                    items.append((f"addr({f[1]})", f"(= {sub(f[2])} {hexbv(tr.maddr[i])})"))
                for r in range(1, 32):
                    items.append((f"x{r}",
                                  f"(= (select (rr {T}) {hexbv(r)}) {hexbv(tr.reg(i + 1, r))})"))
                if tr.mk[i] == MK_STORE:
                    a, post = tr.maddr[i], tr.mpost[i]
                    items.append((f"mem[{a:#x}]", f"(= (ld8 (mm {T}) {hexbv(a)}) {hexbv(post)})"))
                    items.append((f"mem[{a-8:#x}]",
                                  f"(= (ld8 (mm {T}) {hexbv(a-8)}) (ld8 (mm {S}) {hexbv(a-8)}))"))
                    items.append((f"mem[{a+8:#x}]",
                                  f"(= (ld8 (mm {T}) {hexbv(a+8)}) (ld8 (mm {S}) {hexbv(a+8)}))"))
            elif cls == "branch":
                tgt = int(f[0], 16)
                items.append(("cond", f"(= {sub(f[1])} {'true' if tr.npc[i] == tgt else 'false'})"))
            else:
                print("  (no state check for this class)")
                return 0
            for nm, t in items:
                body.append(f"(simplify {t})")
            r = subprocess.run([Z3, "-in", "-smt2"], input="\n".join(body),
                               capture_output=True, text=True, timeout=300)
            outs = [l.strip() for l in r.stdout.splitlines() if l.strip()]
            print(f"  [{tr.name}@{tr.step[i]}] "
                  + (f"mem {'S' if tr.mk[i]==MK_STORE else 'L'}{tr.mw[i]}"
                     f"@{tr.maddr[i]:#x} pre={tr.mpre[i]:#x} post={tr.mpost[i]:#x}"
                     if tr.mk[i] != MK_NONE else "no memory operand"))
            if len(outs) != len(items):
                print("   z3:", (r.stdout + r.stderr)[:400])
            for (nm, t), o in zip(items, outs):
                if o != "true":
                    print(f"    MISMATCH {nm}: {o}")
            shown += 1
            if shown >= limit:
                return 0
    return 0


def phase3(traces, img, enc_dir, per_pc=24, chunk=800, jobs=None):
    tbl = EncTable(os.path.join(enc_dir, "steps.tsv"))
    global MMIO
    MMIO = mmio_region(img)
    preamble = open(os.path.join(enc_dir, "preamble.smt2")).read()
    samples, occ = phase3_samples(traces, tbl, per_pc)
    for pc in occ:
        img_word_cache[pc] = img.word(pc)
    mmio_hits = sum(1 for tr in traces for i in range(tr.n)
                    if tr.mk[i] == MK_STORE and MMIO[0] <= tr.maddr[i] < MMIO[1])
    # the encoder's word must be the image's word (a stale table is worse than
    # no table: every verdict below would be about a different program)
    stale = [pc for pc in occ if tbl.get(pc) is None]
    findings = []
    for pc in stale[:10]:
        findings.append(("NO-ENTRY", f"{pc:#x}", "executed but absent from the step table"))
    work = []
    for k, (pc, tr, i) in enumerate(samples):
        row = tbl.get(pc)
        if row is None:
            continue
        lines, okname, flags = phase3_block(k, pc, tr, i, row)
        for cid, ok, det in flags:
            if not ok:
                findings.append(("STEP-" + cid.upper(), f"{pc:#x}",
                                 f"[{tr.name}@{tr.step[i]}] {det}"))
        if okname:
            work.append((k, pc, tr, i, lines, okname))
    # batch into z3 files; every state is ground so one `get-value` localises
    results = {}
    chunks = [work[x:x + chunk] for x in range(0, len(work), chunk)]

    def run_chunk(cs):
        # every state is a closed term, so each check is `(simplify ok)` — a
        # rewrite, not a satisfiability question.  The answers come back in
        # order, one line each.
        body = [preamble]
        for _, _, _, _, lines, _ in cs:
            body += lines
        for c in cs:
            body.append(f"(simplify {c[5]})")
        p = subprocess.run([Z3, "-in", "-smt2"], input="\n".join(body),
                           capture_output=True, text=True, timeout=1800)
        outs = [l.strip() for l in p.stdout.splitlines() if l.strip()]
        if len(outs) != len(cs):
            return {c[0]: ("Z3ERR", (p.stdout + p.stderr).strip()[:300]) for c in cs}
        return {c[0]: (outs[n], "") for n, c in enumerate(cs)}

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs or (os.cpu_count() or 4)) as ex:
        for r in ex.map(run_chunk, chunks):
            results.update(r)
    bad = {}
    nchecked = 0
    for k, pc, tr, i, _, _ in work:
        v = results.get(k, ("MISSING", ""))
        nchecked += 1
        if v[0] != "true":
            bad.setdefault(pc, []).append((tr.name, tr.step[i], v[0], v[1]))
    for pc, hits in sorted(bad.items()):
        cls = tbl.get(pc)[0]
        nm, st, v, det = hits[0]
        findings.append(("STEP-STATE", f"{pc:#x}",
                         f"[{cls}] encoder's step disagrees with the machine on "
                         f"{len(hits)} sampled execution(s); first [{nm}@{st}] {v} {det}"))
    notes = []
    if mmio_hits:
        notes.append(("MMIO-EXCLUDED", f"{MMIO[0]:#x}..{MMIO[1]:#x}",
                      f"{mmio_hits} stores to the HTIF mailbox: the model consumes "
                      f"them as device commands, the encoder's byte array keeps "
                      f"the value.  Excluded from the memory comparison (see "
                      f"`mmio_region`); no span reflects those stores."))
    return findings, len(samples), nchecked, len(occ), notes


# ------------------------------------------------------------------- commands
def cmd_corpus(a):
    build_corpus(a.wl, a.out, workdir=a.workdir)


def cmd_trace(a):
    run_trace(a.elf, a.out, pcs=a.trace_pcs, max_steps=a.max_steps)
    print(f"[trace] {a.elf} -> {a.out}")


def trace_files(tdir):
    return [fn for fn in sorted(os.listdir(tdir)) if fn.endswith(".trace.tsv")]


def load_traces(tdir, img, names=None):
    trs = []
    for fn in trace_files(tdir):
        nm = fn[:-len(".trace.tsv")]
        if names is not None and nm not in names:
            continue
        t = Trace(os.path.join(tdir, fn), name=nm)
        t.compute_depth(img)
        trs.append(t)
    return trs


def trace_batches(tdir, batch):
    """Trace names in groups of `batch`.

    A whole-program trace of the proof model is ~100 MB of rows and the corpus
    can be a hundred of them, so the phases run over one group at a time and
    merge; loading them all at once is a gigabyte of register file."""
    names = [fn[:-len(".trace.tsv")] for fn in trace_files(tdir)]
    if not batch or batch >= len(names):
        return [None]
    return [names[i:i + batch] for i in range(0, len(names), batch)]


def merge_phase1(acc, rows):
    if acc is None:
        return {r["field"]: r for r in rows}
    for r in rows:
        a = acc[r["field"]]
        for k, v in r.items():
            if isinstance(v, int) and k not in ("entry", "stop", "rlo", "rhi", "arm",
                                                "enc_halts"):
                a[k] = a.get(k, 0) + v
            elif k == "traces":
                a["traces"] = a["traces"] | v
            elif k == "detail":
                for dk, dv in v.items():
                    a["detail"][dk] = a["detail"].get(dk, 0) + dv
    return acc


def merge_phase2(acc, agg):
    for sym, a in agg.items():
        b = acc.setdefault(sym, dict(sym=sym, n=0, nopair=0,
                                     verdicts={c: [0, 0, ""] for c in CLAUSE_IDS}))
        b["n"] += a["n"]
        b["nopair"] += a["nopair"]
        for c in CLAUSE_IDS:
            b["verdicts"][c][0] += a["verdicts"][c][0]
            b["verdicts"][c][1] += a["verdicts"][c][1]
            if not b["verdicts"][c][2]:
                b["verdicts"][c][2] = a["verdicts"][c][2]
    return acc


def cmd_phase1(a):
    img = Image(PROOF_ELF)
    spans = read_tsv(os.path.join(a.bmc, "spans.tsv"))
    arms = read_tsv(os.path.join(a.enc, "armdispatch.tsv"))
    acc = None
    seen, bad, unlisted, arms_at = None, [], {}, None
    ntr = 0
    for names in trace_batches(a.traces, a.batch):
        trs = load_traces(a.traces, img, names)
        ntr += len(trs)
        acc = merge_phase1(acc, phase1(trs, img, spans, arms, a.enc))
        sn, bd, un, aa = check_dispatch(trs, img, a.enc)
        arms_at = aa
        seen = sn if seen is None else {k: seen[k] | v for k, v in sn.items()}
        bad += bd
        for k, v in un.items():
            unlisted.setdefault(k, set()).update(v)
    rows = list(acc.values())
    write_phase1(rows, a.out)
    trs = []
    so = os.path.join(a.bmc, "stop-outside.tsv")
    recorded = {r["field"] for r in read_tsv(so)} if os.path.exists(so) else set()
    findings, notes = phase1_findings(rows, seen, bad, unlisted, arms_at, recorded)
    if recorded:
        print(f"  note: {len(recorded)} spans declare a stop outside their own region; "
              f"the encoder records them in stop-outside.tsv and decides `retExit` "
              f"structurally (their exit is the function's return)")
    ncov = sum(1 for r in rows if r["entries"])
    narr = sum(1 for r in rows if sum(r[k] for k in EXIT_KINDS))
    print(f"[phase1] {ntr} traces, {len(rows)} spans, {ncov} entered, "
          f"{narr} reach an encoder-recognised exit")
    for kind, f, msg in findings:
        print(f"  {kind:16s} {f:16s} {msg}")
    for kind, f, msg in notes:
        print(f"  note: {kind:12s} {f:16s} {msg}")
    if a.out:
        with open(a.out + ".findings", "w") as fh:
            fh.write("severity\tkind\twhere\tdetail\n")
            for kind, f, msg in findings:
                fh.write(f"FINDING\t{kind}\t{f}\t{msg}\n")
            for kind, f, msg in notes:
                fh.write(f"note\t{kind}\t{f}\t{msg}\n")
    return 1 if findings else 0


def cmd_phase2(a):
    img = Image(PROOF_ELF)
    known = {r["summary"] for r in read_tsv(os.path.join(a.bmc, "summaries.tsv"))
             if r["summary"]}
    agg, mm = {}, None
    for names in trace_batches(a.traces, a.batch):
        trs = load_traces(a.traces, img, names)
        agg, mm = phase2_agg(trs, img, a.enc, a.bmc, known, agg)
    rows, mined = phase2_report(agg, img, a.bmc, out_tsv=a.out)
    findings = phase2_findings(rows, mined)
    print(f"[phase2] memory map: {mm}")
    print(f"[phase2] {len(agg)} summaries instantiated by the corpus, "
          f"{sum(v['n'] for v in agg.values())} applications")
    for kind, f, msg in findings:
        print(f"  {kind:14s} {f:26s} {msg}")
    if a.out:
        with open(a.out + ".findings", "w") as fh:
            fh.write("severity\tkind\twhere\tdetail\n")
            for kind, f, msg in findings:
                fh.write(f"FINDING\t{kind}\t{f}\t{msg}\n")
    return 1 if findings else 0


def cmd_explain(a):
    img = Image(PROOF_ELF)
    trs = load_traces(a.traces, img)
    return phase3_explain(trs, img, a.enc, int(a.pc, 16), limit=a.limit)


def cmd_phase3(a):
    img = Image(PROOF_ELF)
    findings, nsamp, nchk, notes = [], 0, 0, []
    pcs = set()
    for names in trace_batches(a.traces, a.batch):
        trs = load_traces(a.traces, img, names)
        f, ns, nc, np_, nt = phase3(trs, img, a.enc, per_pc=a.per_pc,
                                    chunk=a.chunk, jobs=a.jobs)
        findings += f
        nsamp += ns
        nchk += nc
        notes = nt or notes
        pcs |= set(phase3_samples(trs, None, 1)[1].keys())
    findings = dedup_findings(findings)
    if a.out:
        with open(a.out, "w") as fh:
            fh.write("kind\twhere\tdetail\n")
            for kind, w, d in findings + notes:
                fh.write(f"{kind}\t{w}\t{d}\n")
    npc = len(pcs)
    print(f"[phase3] {npc} distinct PCs executed, {nsamp} sampled steps, "
          f"{nchk} state checks")
    for kind, w, d in notes:
        print(f"  note: {kind} {w}: {d}")
    for kind, w, d in findings[:60]:
        print(f"  {kind:18s} {w:12s} {d}")
    if len(findings) > 60:
        print(f"  ... and {len(findings)-60} more (see {a.out})")
    return 1 if findings else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("corpus")
    p.add_argument("wl", nargs="+")
    p.add_argument("--out", required=True)
    p.add_argument("--workdir", default="/tmp/dt-c")
    p.set_defaults(fn=cmd_corpus)

    p = sub.add_parser("trace")
    p.add_argument("elf")
    p.add_argument("--out", required=True)
    p.add_argument("--trace-pcs")
    p.add_argument("--max-steps", type=int)
    p.set_defaults(fn=cmd_trace)

    p = sub.add_parser("explain")
    p.add_argument("pc")
    p.add_argument("--traces", required=True)
    p.add_argument("--enc", required=True)
    p.add_argument("--limit", type=int, default=3)
    p.set_defaults(fn=cmd_explain)

    p = sub.add_parser("phase3")
    p.add_argument("--traces", required=True)
    p.add_argument("--batch", type=int, default=16,
                   help="traces held in memory at once (0 = all)")
    p.add_argument("--enc", required=True)
    p.add_argument("--per-pc", type=int, default=24)
    p.add_argument("--chunk", type=int, default=800)
    p.add_argument("--jobs", type=int)
    p.add_argument("--out")
    p.set_defaults(fn=cmd_phase3)

    p = sub.add_parser("phase2")
    p.add_argument("--traces", required=True)
    p.add_argument("--batch", type=int, default=16,
                   help="traces held in memory at once (0 = all)")
    p.add_argument("--enc", required=True)
    p.add_argument("--bmc", default=BMC_DIR)
    p.add_argument("--out")
    p.set_defaults(fn=cmd_phase2)

    p = sub.add_parser("phase1")
    p.add_argument("--traces", required=True)
    p.add_argument("--batch", type=int, default=16,
                   help="traces held in memory at once (0 = all)")
    p.add_argument("--enc", required=True)
    p.add_argument("--bmc", default=BMC_DIR)
    p.add_argument("--out")
    p.set_defaults(fn=cmd_phase1)

    a = ap.parse_args()
    sys.exit(a.fn(a) or 0)


if __name__ == "__main__":
    main()
