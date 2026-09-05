#!/usr/bin/env python3
"""difftest.py — differentially test the BMC encoder against the proof model.

Subcommands:

    corpus   build one traceable ELF per `.wl` program (padded, in /tmp)
    trace    run an ELF under the emulator's traced loop
    phase1   do the declared spans exist? (span reachability over the traces)
    phase2   do the summary clauses hold on real call pairs?
    phase3   does the encoder's step semantics agree with the machine?
    errors   classify runtime-error PCs and semantic constructor paths
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
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from difftest_lib import (ROOT, PROOF_ELF, BMC_DIR, Image, Trace, EncTable, decode,
                          is_call, is_ret, read_tsv, M64, MK_NONE, MK_LOAD, MK_STORE)

EMU = os.path.join(ROOT, "riscv-lean", "lean_emulator", ".lake", "build", "bin",
                   "lean_riscv_emulator")
REF_SCRIPT = os.path.join(ROOT, "c", "tests", "while.wl")
CODE_LO, CODE_HI = 0x80000000, 0x80018BE0


def campaign_provenance_files():
    """Tree files whose exact bytes define a residual campaign."""
    return {
        "ReflectSpan.lean": os.path.join(
            ROOT, "experiments", "smt", "ReflectSpan.lean"),
        "ReflectResiduals.lean": os.path.join(
            ROOT, "experiments", "smt", "ReflectResiduals.lean"),
        "NativeBodyAssert.lean": os.path.join(
            ROOT, "Vsa", "Sim", "rows", "NativeBodyAssert.lean"),
        "EvalCallNative2.lean": os.path.join(
            ROOT, "Vsa", "Sim", "EvalCallNative2.lean"),
        "SegEffect.lean": os.path.join(ROOT, "Vsa", "Sim", "SegEffect.lean"),
        "proof.elf": PROOF_ELF,
    }


def campaign_provenance_findings(directory):
    """Reject campaign bytes emitted from another tree or proof binary."""
    source_dir = os.path.join(directory, "src")
    if not os.path.isdir(source_dir):
        return [("PROVENANCE-MISSING", "campaign",
                 f"{directory} has no src/ provenance; re-emit before fuzzing")]
    required = campaign_provenance_files()
    missing = sorted(
        name for name in required
        if not os.path.isfile(os.path.join(source_dir, name)))
    if missing:
        return [("PROVENANCE-MISSING", "campaign",
                 "missing " + ",".join(missing))]
    stale = sorted(
        name for name, current in required.items()
        if open(os.path.join(source_dir, name), "rb").read()
        != open(current, "rb").read())
    if stale:
        return [("PROVENANCE-STALE", "campaign",
                 "campaign differs byte-for-byte from current "
                 + ",".join(stale))]
    return []


# --------------------------------------------------------------------- corpus
def build_corpus(wls, outdir, workdir="/tmp/dt-c", quiet=False):
    """Build one ELF per `.wl`, each padded to the proof script's length, in a
    /tmp copy of `c/`.  Returns [(name, elf_path)]."""
    ref = open(REF_SCRIPT, "rb").read()
    reflen = len(ref)
    if not os.path.isdir(workdir):
        parent = os.path.dirname(os.path.abspath(workdir))
        os.makedirs(parent, exist_ok=True)
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
    # A zero-step typed boundary is reached by the entry state itself.  Do not
    # execute the instruction after it merely to manufacture a nonempty span.
    if tr.pc[i] == stop:
        return ("at_stop", i, "")
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


def _arrived_from_call_dispatch(tr, row, depth):
    """Whether this eval frame reached the shared epilogue from call dispatch."""
    for index in range(row - 1, -1, -1):
        if tr.depth[index] > depth:
            continue
        if tr.depth[index] < depth:
            return False
        if tr.pc[index] == 0x80003254:
            return True
        if tr.pc[index] == 0x80003164:
            return False
    return False


def phase1(traces, img, spans, arms, enc_dir):
    armmap = {a["field"]: a for a in arms}
    noret = {int(r["target"], 16) for r in read_tsv(os.path.join(enc_dir, "noreturn.tsv"))}
    fstarts = {int(r["entry"], 16) for r in read_tsv(os.path.join(enc_dir, "funcstarts.tsv"))}
    dsites = read_tsv(os.path.join(enc_dir, "dispatchsites.tsv"))
    arms_at = {int(r["site"], 16): [int(x, 16) for x in r["arms"].split(",")] for r in dsites}
    res = {}
    for sp in spans:
        # Sequence queries have three tabled machine instances.  They are not
        # AST-dispatch arms and therefore have no `armdispatch.tsv` row.  Their
        # region and return convention are recorded by the BMC emitter itself.
        a = armmap.get(sp["field"])
        if a is None:
            a = dict(region_lo=sp["region_lo"], region_hi=sp["region_hi"],
                     arm=sp["entry"], dispatch="-", kind_reg="-", kind_idx="-",
                     ret_exit=sp["ret_exit"])
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

CLAUSE_IDS = ["inv_pres", "output_restore", "sp_restore", "ra_restore",
              "s0_restore", "s1_restore", "stack_or_arena", "above_sp"]
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
        if tr.mk[j] == MK_STORE and not _is_mmio_store(tr.maddr[j], tr.mw[j]):
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
        if tr.mk[j] == MK_STORE and not _is_mmio_store(tr.maddr[j], tr.mw[j]):
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
    """Evaluate each generic clause on one concrete `(pre, post)` pair.  Returns
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
    pre_out, pre_len, pre_known = _trace_output_state(tr, it.pre_row)
    post_out, post_len, post_known = _trace_output_state(tr, it.post_row)
    if pre_known and post_known:
        changed = _output_mismatches(
            St(None, None, post_out, post_len),
            St(None, None, pre_out, pre_len), limit=1)
        res["output_restore"] = (("HOLDS", "") if not changed else
                                 ("REFUTED", changed[0]))
    else:
        res["output_restore"] = ("NOPAIR", "trace lacks output observations")
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
    loop_invalid = {"ra_restore", "s0_restore", "s1_restore", "above_sp"}
    for sym, clauses in mined.items():
        if sym.startswith("loop_"):
            mined[sym] = [c for c in clauses if c not in loop_invalid]
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
CONST_BYTES = "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)"
MEM_POISON = "MEM_POISON"
MEM_POISON_DECL = "(declare-const MEM_POISON (Array (_ BitVec 64) (_ BitVec 8)))"


def _state_term(tr, i):
    """The entry state with every observed component made ground.

    Ground is the whole point.  Declaring `S` and constraining it with
    assertions makes every check a satisfiability question over a byte array,
    which bit-blasts (one chunk ran for twelve minutes at 400 MB).  The one
    exception is the symbolic fallback for unobserved memory: a correct
    instruction never reads it, while a stray read prevents the result from
    simplifying to `true`."""
    regs = CONST_REGS
    for r in range(1, 32):
        v = tr.reg(i, r)
        if v:
            regs = f"(store {regs} {hexbv(r)} {hexbv(v)})"
    # Leave every byte the trace did not observe symbolic.  A stray encoder
    # read must remain non-ground (and therefore fail the `simplify = true`
    # gate) instead of silently receiving zero.
    mem = MEM_POISON
    if tr.mk[i] != MK_NONE:
        a, pre = tr.maddr[i], tr.mpre[i]
        for j in range(8):
            b = (pre >> (8 * j)) & 0xFF
            mem = f"(store {mem} {hexbv(a + j)} #x%02x)" % b
    output, output_len, output_known = _trace_output_state(tr, i)
    out = CONST_BYTES
    if output_known:
        for index in range(output_len):
            byte = output.sel(index)
            if byte:
                out = f"(store {out} {hexbv(index)} #x{byte:02x})"
    return f"(mst {mem} {regs} {out} {hexbv(output_len)})"


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
    sub = lambda t: (t.replace("(mm S)", f"(mm {S})")
                     .replace("(rr S)", f"(rr {S})")
                     .replace("(oo S)", f"(oo {S})")
                     .replace("(ol S)", f"(ol {S})"))
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


def _is_mmio_store(address, width):
    """Whether an observed store is consumed by the HTIF mailbox, not RAM."""
    lo, hi = MMIO
    return lo < hi and address < hi and address + width > lo


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
            sub = lambda t: (t.replace("(mm S)", f"(mm {S})")
                             .replace("(rr S)", f"(rr {S})")
                             .replace("(oo S)", f"(oo {S})")
                             .replace("(ol S)", f"(ol {S})"))
            body = [preamble, MEM_POISON_DECL,
                    f"(define-fun {S} () MState {_state_term(tr, i)})"]
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
        # Every byte a correct step can read is ground.  `MEM_POISON` remains
        # only if the encoder reads outside the trace's observed operand; such
        # a check does not simplify to `true` and is reported as a mismatch.
        body = [preamble, MEM_POISON_DECL]
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


# -------------------------------------------------------------- phase 3 (span)
#
# The plan's phase 3, as it states it: take the entry state from the trace,
# assert it as `s0`, pin every summary application from its observed
# `(pre, post)` pair, read the exit register file out of `state_exit`, and
# compare against the trace at the stop.  Plus the direct write-log comparison the
# same section asks for: an address the encoder records and the machine never
# writes, the reverse, or a different final byte at a shared address is a bug;
# the footprint posts are where most of the VALIDs live.
#
# Everything is ground once `s0` and the summaries are pinned, so there is
# nothing to solve; `difftest_eval` evaluates the encoder's own emitted term
# directly, which additionally lets every intermediate state be checked and a
# disagreement named at the binding where it first appears.

from difftest_eval import Query, Ev, RA, MA, OA, St, EvalError, M64 as _M64, parse_all


def _memory_array_equal(left, right):
    """Decidable equality for finite updates over the same trace-memory base."""
    return (isinstance(right, MA) and left.base is right.base
            and left.d == right.d)


# difftest_eval deliberately models memory as finite updates over an opaque
# trace/ELF base.  Equality is decidable when both arrays retain that exact
# base; production postconditions use this case for direct store footprints.
MA.__eq__ = _memory_array_equal


def _register_array_equal(left, right):
    return isinstance(right, RA) and left.v == right.v


RA.__eq__ = _register_array_equal


# Independent concrete specifications for the projections implemented by
# houdini_summary.py.  Do not derive this table from residual_posts: that would
# let the producer and checker share the same wrong field offset or operation.
TERM_SEMANTIC_PROJECTION_FIELDS = {
    "hArgsCons", "hInt", "hStr", "hBool", "hNull", "hVar", "hAssign",
    "hNeg", "hNot",
    "hAndFalse", "hOrTrue", "hAndTrue", "hOrFalse",
    "hEq", "hNe", "hStrAddL", "hStrAddR",
    "hStrLt", "hStrLe", "hStrGt", "hStrGe", "hFn",
    "hCall", "hCallAssertOk", "hCallPrint", "hCallPrintln",
    "hIAdd", "hISub", "hIMul", "hIDiv", "hIMod",
    "hILt", "hILe", "hIGt", "hIGe", "hDivOv",
    "hSExpr", "hSBlock", "hSRet", "hSRetNull", "hSVarInit", "hSVarNull",
    "hSIfNone", "hSWhileFalse",
    "hSWhileBreak", "hSWhileRet", "hSWhileLoop",
    "hSBrk", "hSCont",
}

# Error projections use the same independent oracle machinery, but are not
# fields of TermResidualsCore.
INDEXED_ERROR_PROJECTION_FIELDS = {"hCallTooMany"}

# Retired term fields may remain useful machine-boundary regression checks.
# They are not semantic residual coverage.
MACHINE_BOUNDARY_PROJECTION_FIELDS = {"hArgsNil"}

SEMANTIC_PROJECTION_FIELDS = (
    TERM_SEMANTIC_PROJECTION_FIELDS | INDEXED_ERROR_PROJECTION_FIELDS)
PROJECTED_FIELDS = SEMANTIC_PROJECTION_FIELDS | MACHINE_BOUNDARY_PROJECTION_FIELDS

QUERY_CAPABILITIES = {
    "partial-projection",
    "machine-only",
    "indexed-error-projection",
    "machine-boundary",
}


def expected_query_capability(field):
    """The unique capability class for one emitted residual field."""
    if field in INDEXED_ERROR_PROJECTION_FIELDS:
        return "indexed-error-projection"
    if field in MACHINE_BOUNDARY_PROJECTION_FIELDS:
        return "machine-boundary"
    if field in TERM_SEMANTIC_PROJECTION_FIELDS:
        return "partial-projection"
    return "machine-only"


def query_capability_findings(query_caps):
    """Check both the capability vocabulary and each field's exact class."""
    findings = []
    for query, row in sorted(query_caps.items()):
        actual = row.get("capability", "")
        if actual not in QUERY_CAPABILITIES:
            findings.append(("CAPABILITY-INVALID", query,
                             f"unsupported capability label: {actual}"))
            continue
        field = row.get("field", "")
        expected = expected_query_capability(field)
        if actual != expected:
            findings.append(("CAPABILITY-CLASS", query,
                             f"{field}: expected {expected}, got {actual}"))
    return findings


_EFFECT_COLUMNS = (
    "query", "field", "register_writes", "direct_memory_writes",
    "direct_write_rows", "output", "theorem", "provenance",
)
_ZERO_STEP_EFFECT_QUERIES = {"hCallArgsToCall", "hCallCallToEpilogue"}
_ZERO_STEP_FRAME_THEOREM = "Vsa.Sim.FrameGuarantee.refl"
_ABI_ROUTE_FRAME_THEOREM = "Vsa.Sim.execWhileLoopRouteRow_framed"
_ABI_ROUTE_EFFECT_QUERIES = {
    "hSWhileRetBodyReturn", "hSWhileLoopBodyReturn",
}
_ABI_PRESERVED_GPRS = (2, 3, 4, 8, 9, *range(18, 28))


def query_effect_manifest(bmc_dir, query_caps):
    """Validate the conservative Lean-emitted effect classification.

    This ledger is not evidence that the SMT transformer equals Lean.  It
    certifies only zero-step frames and inventories the reflector's direct
    memory-write rows.  Dynamic register/output effects remain unsupported.
    """
    path = os.path.join(bmc_dir, "query-effects.tsv")
    if not os.path.isfile(path):
        return {}, [("EFFECT-MANIFEST", "campaign",
                     "missing query-effects.tsv")]
    with open(path) as fh:
        columns = tuple(fh.readline().rstrip("\n").split("\t"))
    if columns != _EFFECT_COLUMNS:
        return {}, [("EFFECT-COLUMNS", "campaign",
                     f"expected {_EFFECT_COLUMNS}, got {columns}")]
    rows = read_tsv(path)
    effects, findings = {}, []
    for row in rows:
        query = row.get("query", "")
        if query in effects:
            findings.append(("EFFECT-DUPLICATE", query, "duplicate row"))
            continue
        effects[query] = row
    expected = set(query_caps)
    for query in sorted(expected - set(effects)):
        findings.append(("EFFECT-MISSING", query, "no effect row"))
    for query in sorted(set(effects) - expected):
        findings.append(("EFFECT-EXTRA", query, "unknown effect row"))
    for query in sorted(expected & set(effects)):
        row = effects[query]
        if row["field"] != query_caps[query].get("field", ""):
            findings.append(("EFFECT-FIELD", query, row["field"]))
        zero = query in _ZERO_STEP_EFFECT_QUERIES
        abi_route = query in _ABI_ROUTE_EFFECT_QUERIES
        if zero:
            expected_values = {
                "register_writes": "none",
                "output": "preserved",
                "theorem": _ZERO_STEP_FRAME_THEOREM,
                "provenance": f"Lean:{_ZERO_STEP_FRAME_THEOREM}",
            }
        elif abi_route:
            expected_values = {
                "register_writes": "preserves-abi",
                "output": "preserved",
                "theorem": _ABI_ROUTE_FRAME_THEOREM,
                "provenance": f"Lean:{_ABI_ROUTE_FRAME_THEOREM}",
            }
        else:
            expected_values = {
                "register_writes": "unsupported-dynamic",
                "output": "unsupported-dynamic",
                "theorem": "-",
                "provenance": "Lean-emitted:Vsa.ReflectSpan.reflectBmcTopo",
            }
        for column, wanted in expected_values.items():
            if row[column] != wanted:
                findings.append(("EFFECT-WRONG", query,
                                 f"{column}: expected {wanted}, got {row[column]}"))
        try:
            declared = int(row["direct_write_rows"])
            if declared < 0:
                raise ValueError
        except ValueError:
            findings.append(("EFFECT-WRONG", query,
                             "direct_write_rows is not a natural number"))
            continue
        write_path = os.path.join(bmc_dir, "writes", query + ".tsv")
        if not os.path.isfile(write_path):
            findings.append(("EFFECT-WRITES-MISSING", query,
                             "missing direct write log"))
            continue
        try:
            actual = sum(int(item.get("width", "0")) != 0
                         for item in read_tsv(write_path))
        except ValueError:
            findings.append(("EFFECT-WRITES-MALFORMED", query,
                             "non-numeric direct write width"))
            continue
        wanted_mode = "none" if actual == 0 else "guarded-write-log"
        if declared != actual:
            findings.append(("EFFECT-WRITE-COUNT", query,
                             f"declared {declared}, emitted {actual}"))
        if row["direct_memory_writes"] != wanted_mode:
            findings.append(("EFFECT-WRONG", query,
                             "direct_memory_writes: expected " + wanted_mode))
    return effects, findings


def observed_effect_findings(effect, tr, entry_row, exit_row, machine_footprint):
    """Check only claims the effect manifest actually makes."""
    query = effect["query"]
    findings = []
    if effect["register_writes"] == "none":
        changed = [reg for reg in range(1, 32)
                   if tr.regs_at(entry_row)[reg] != tr.regs_at(exit_row)[reg]]
        if changed:
            findings.append(("EFFECT-REGISTERS", query,
                             "claimed no writes; changed x" +
                             ",x".join(map(str, changed))))
    elif effect["register_writes"] == "preserves-abi":
        changed = [reg for reg in _ABI_PRESERVED_GPRS
                   if tr.regs_at(entry_row)[reg] != tr.regs_at(exit_row)[reg]]
        if changed:
            findings.append(("EFFECT-REGISTERS", query,
                             "claimed ABI preservation; changed x" +
                             ",x".join(map(str, changed))))
    if effect["direct_memory_writes"] == "none" and machine_footprint:
        findings.append(("EFFECT-MEMORY", query,
                         f"claimed no direct writes; observed {len(machine_footprint)} bytes"))
    if effect["output"] == "preserved":
        before, before_len, before_known = _trace_output_state(tr, entry_row)
        after, after_len, after_known = _trace_output_state(tr, exit_row)
        if not before_known or not after_known:
            findings.append(("EFFECT-OUTPUT-UNKNOWN", query,
                             "preservation claim lacks trace observations"))
        elif before_len != after_len or before != after:
            findings.append(("EFFECT-OUTPUT", query,
                             "claimed preservation; trace output changed"))
    return findings


def _consistency_pin_blocked(findings):
    """Whether concrete encoder/machine/oracle disagreement forbids pins."""
    blocker_prefixes = ("EXIT-", "WRITE-", "EFFECT-")
    blocker_kinds = {
        "EVAL", "MEM-UNKNOWN", "PROJECTION-MACHINE", "PROJECTION-ENCODER",
    }
    return any(kind in blocker_kinds or kind.startswith(blocker_prefixes)
               for kind, _where, _detail in findings)

_ASSERT_OK_LEAN_CERTIFICATES = {
    ("hCallAssertOk", "abi_frame_x1"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x8"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x9"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x18"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
}
_ASSERT_OK_CERTIFICATE_MUTATIONS = {
    "x1": "abi_frame_x1",
    "x8": "abi_frame_x8",
    "x9": "abi_frame_x9",
    "x18": "abi_frame_x18",
}
_ASSERT_OK_MACHINE_MUTATIONS = {
    "null-kind", "null-payload", "x2", "output-array", "output-length",
}


def phase3b_lean_certificates(bmc_dir, verdict_paths):
    """Validate exact certificate identities and Lean-labelled verdict cells."""
    capability_path = os.path.join(bmc_dir, "query-capabilities.tsv")
    certificate_path = os.path.join(bmc_dir, "lean-certificates.tsv")
    findings = []
    if not os.path.exists(capability_path):
        return {}, [("CERTIFICATE-MANIFEST", "campaign",
                     "missing query-capabilities.tsv")]
    queries = {row["query"] for row in read_tsv(capability_path)}
    expected = (_ASSERT_OK_LEAN_CERTIFICATES
                if "hCallAssertOk" in queries else {})
    if not os.path.exists(certificate_path):
        if expected:
            findings.append(("CERTIFICATE-MANIFEST", "hCallAssertOk",
                             "missing lean-certificates.tsv"))
        return {}, findings
    rows = read_tsv(certificate_path)
    found = {}
    for row in rows:
        key = (row.get("residual", ""), row.get("post", ""))
        if key[0] not in queries:
            continue
        theorem = row.get("theorem", "")
        if key in found:
            findings.append(("CERTIFICATE-DUPLICATE", key[0], key[1]))
        elif key not in expected:
            findings.append(("CERTIFICATE-UNKNOWN", key[0], key[1]))
        elif theorem != expected[key]:
            findings.append(("CERTIFICATE-WRONG", key[0],
                             f"{key[1]}={theorem}"))
        else:
            found[key] = theorem
    missing = set(expected) - set(found)
    for query, post in sorted(missing):
        findings.append(("CERTIFICATE-MISSING", query, post))

    verdicts = {}
    for path in verdict_paths or ():
        if not os.path.exists(path):
            findings.append(("CERTIFICATE-VERDICT", "campaign",
                             f"missing {path}"))
            continue
        for row in read_tsv(path):
            query = row.get("query", "")
            prior = verdicts.setdefault(query, {})
            for column, value in row.items():
                old = prior.get(column, "")
                if old in ("", "N/A"):
                    prior[column] = value
                elif value not in ("", "N/A", old):
                    findings.append(("CERTIFICATE-VERDICT-CONFLICT", query,
                                     f"{column}: {old} != {value}"))
    if expected and not verdict_paths:
        findings.append(("CERTIFICATE-VERDICT", "hCallAssertOk",
                         "no --verdict supplied"))
    for key, theorem in sorted(found.items()):
        query, post = key
        want = f"VALID[Lean:{theorem}]"
        got = verdicts.get(query, {}).get(post, "")
        if got != want:
            findings.append(("CERTIFICATE-VERDICT", query,
                             f"{post}: expected {want}, got {got or '<missing>'}"))
    return (found if not findings else {}), findings

_STATUS_PROJECTION_FIELDS = {
    # field: (StmtKind, result status, nullable child offset, child is present,
    #         route PC required by the semantic constructor)
    "hSExpr": (0, 0, None, None, None),
    "hSRet": (6, 3, 8, True, None),
    "hSRetNull": (6, 3, 8, False, None),
    "hSVarInit": (1, 0, 16, True, None),
    "hSVarNull": (1, 0, 16, False, None),
    "hSIfNone": (3, 0, 24, False, 0x800042D4),
    "hSWhileFalse": (4, 0, None, None, 0x80004090),
    "hSBrk": (7, 1, None, None, None),
    "hSCont": (8, 2, None, None, None),
}

_BINARY_TOKENS = {
    "hIAdd": 11, "hISub": 12, "hIMul": 13, "hIDiv": 14,
    "hIMod": 15, "hILt": 20, "hILe": 21, "hIGt": 22, "hIGe": 23,
    "hDivOv": 14,
}

_PREMISE_BINARY_FIELDS = (
    "hIAdd", "hISub", "hIMul", "hIDiv", "hIMod",
    "hILt", "hILe", "hIGt", "hIGe", "hDivOv",
)
_BINARY_VALUE_POINT = "0x8000351c"
_UNARY_VALUE_POINT = "0x800035ec"
_EVAL_FRAME_BYTES = 1088
_BLOCK_QUERIES = {
    "hSBlock", "hSBlockIter", "hSBlockNormal", "hSBlockAbrupt",
}

_CALL_QUERY_FIELDS = {
    "hCallCallee": "hCall",
    "hCallTooMany": "hCallTooMany",
    "hCallCalleeToArgsNil": "hCall",
    "hCallCalleeToArgsCons": "hCall",
    "hCallArgsToCall": "hCall",
    "hCallCallToEpilogue": "hCall",
}
_CALL_QUERIES = set(_CALL_QUERY_FIELDS)
_CALL_CUTS = {
    # The first stage starts at EvalEntry so the dispatcher derives the arm;
    # armdispatch.tsv separately pins its selected arm to 0x800031b0.
    "hCallCallee": (0x80003164, 0x800031BC),
    "hCallTooMany": (0x800031C0, 0x80003FDC),
    "hCallCalleeToArgsNil": (0x800031C0, 0x800031D8),
    "hCallCalleeToArgsCons": (0x800031C0, 0x800031DC),
    "hCallArgsToCall": (0x80003254, 0x80003254),
    "hCallCallToEpilogue": (0x800033EC, 0x800033EC),
}

_WHILE_QUERY_FIELDS = {
    **{f"{field}{cut}": field
       for field in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop")
       for cut in ("CondSetup", "CondTruthy", "BodySetup", "Route")},
    "hSWhileRetBodyReturn": "hSWhileRet",
    "hSWhileLoopBodyReturn": "hSWhileLoop",
}
_WHILE_QUERIES = set(_WHILE_QUERY_FIELDS)
_WHILE_CUTS = {
    query: (
        (0x8000403C, 0x8000404C) if query.endswith("CondSetup") else
        (0x80004050, 0x80004074) if query.endswith("CondTruthy") else
        (0x80004074, 0x80004084) if query.endswith("BodySetup") else
        (0x80004088, 0x80004034) if query.endswith("BodyReturn") else
        ({"hSWhileBreak": 0x80004088,
          "hSWhileRet": 0x80004034,
          "hSWhileLoop": 0x80004034}[field],
         {"hSWhileBreak": 0x8000409C,
          "hSWhileRet": 0x80004150,
          "hSWhileLoop": 0x8000403C}[field]))
    for query, field in _WHILE_QUERY_FIELDS.items()
}


def _premise_schema():
    """Semantic premise names and machine checkpoints, independent of SMT.

    The offsets describe the concrete compiler frame visible at the two return
    points: eval_binary's left Value is at sp+120 and its right Value at
    sp+144; eval_expr's unary operand Value is at sp+144.  This inventory is a
    fuzzer oracle and is deliberately not derived from residual-extensions.tsv
    or houdini_summary.residual_pres.
    """
    schema = {}
    schema["hArgsNil"] = {
        "empty-argc": "entry",
        "empty-index": "entry",
    }
    schema["hArgsCons"] = {
        "index-nonnegative": "entry",
        "index-below-argc": "entry",
        "argc-bound": "entry",
        "pre-child-eval": "0x80003220",
        "post-child-eval": "0x80003224",
    }
    schema["hSBlock"] = {
        "execBlockA-x8-stmt": "0x8000418c",
        "execBlockA-x9-interp": "0x8000418c",
        "execBlockA-x19-env": "0x8000418c",
        "execBlockA-x18-ret": "0x8000418c",
        "pre-env-new": "0x80004190",
        "post-env-new": "0x80004194",
        "post-env-new-setup": "0x800041a0",
    }
    # These schemas are keyed by machine query, not Lean field.  The child
    # boundary accepts every first iteration; the one-instruction route queries
    # then distinguish normal from abrupt status.
    schema["hSBlockIter"] = {
        "index-nonnegative": "entry",
        "index-below-count": "entry",
        "pre-child-exec": "0x800041c4",
        "post-child-exec": "0x800041c8",
    }
    schema["hSBlockNormal"] = {"normal-child-status": "entry"}
    schema["hSBlockAbrupt"] = {"abrupt-child-status": "entry"}
    schema["hCallCallee"] = {
        "execBlockA-x8-expr": "0x800031b0",
        "execBlockA-x9-sret": "0x800031b0",
        "execBlockA-x18-interp": "0x800031b0",
        "execBlockA-x19-env": "0x800031b0",
        "callee-stack-window": "0x800031b0",
        "pre-callee-eval": "0x800031bc",
    }
    schema["hCallTooMany"] = {
        "call-node-kind": "entry",
        "argc-over-max": "entry",
        "argc-signed-nonnegative": "entry",
        "callee-return-stack-window": "entry",
        "callee-value-shadow": "entry",
    }
    schema["hCallCalleeToArgsNil"] = {
        "empty-argc": "entry",
        "callee-return-stack-window": "entry",
        "callee-value-shadow": "entry",
    }
    schema["hCallCalleeToArgsCons"] = {
        "nonempty-argc": "entry",
        "argc-bound": "entry",
        "callee-return-stack-window": "entry",
        "callee-value-shadow": "entry",
    }
    schema["hCallArgsToCall"] = {
        "argc-bound": "entry",
        "callee-value-shadow": "entry",
        "arg-vector-shadow": "entry",
    }
    schema["hCallCallToEpilogue"] = {
        "result-value-shadow": "entry",
    }
    schema["hCallAssertOk"] = {
        "assert-argc-one-or-two": "entry",
        "assert-first-value": "entry",
        "assert-first-truthy": "entry",
        "sret-above-htif": "entry",
        "sret-no-wrap": "entry",
        "sret-below-4g": "entry",
        "stack-frame-above-htif": "entry",
    }
    for field in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop"):
        schema[field + "CondTruthy"] = {
            "condition-truthy": "entry",
            "condition-bool-canonical": "entry",
            "stack-above-htif": "entry",
        }
    schema["hSWhileBreakRoute"] = {"body-break-status": "entry"}
    schema["hSWhileRetBodyReturn"] = {"body-return-status": "entry"}
    schema["hSWhileRetRoute"] = {"body-return-status": "entry"}
    schema["hSWhileLoopBodyReturn"] = {"body-loop-status": "entry"}
    schema["hSWhileLoopRoute"] = {"body-loop-status": "entry"}
    schema["hVar"] = {
        "post-env-get": "0x80003444",
    }
    schema["hAssign"] = {
        "post-rhs-eval": "0x8000348c",
        "pre-env-set": "0x800034b0",
        "post-env-set": "0x800034b4",
    }
    for field in ("hCallPrint", "hCallPrintln"):
        schema[field] = {
            "argc-bound": "entry",
            "sret-above-htif": "entry",
            "sret-no-wrap": "entry",
            "sret-below-4g": "entry",
            "stack-frame-above-htif": "entry",
        }
    for field in _PREMISE_BINARY_FIELDS:
        schema[field] = {
            "binop-token": "entry",
            "left-int": _BINARY_VALUE_POINT,
            "right-int": _BINARY_VALUE_POINT,
        }
    schema["hIDiv"].update({
        "nonzero-divisor": _BINARY_VALUE_POINT,
        "nonoverflow": _BINARY_VALUE_POINT,
    })
    schema["hIMod"]["nonzero-divisor"] = _BINARY_VALUE_POINT
    schema["hDivOv"].update({
        "min-dividend": _BINARY_VALUE_POINT,
        "minus-one-divisor": _BINARY_VALUE_POINT,
    })
    schema["hNeg"] = {
        "unop-token": "entry",
        "operand-int": _UNARY_VALUE_POINT,
    }
    schema.update({
        "hSRet": {"return-expr": "entry"},
        "hSRetNull": {"return-null": "entry"},
        "hSVarInit": {"initializer": "entry"},
        "hSVarNull": {"no-initializer": "entry"},
        "hSIfNone": {"no-else": "entry"},
    })
    return schema


def production_residual_posts(bmc_dir):
    """Read production formulas from a separate process, solely as test input."""
    producer = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "houdini_summary.py")
    proc = subprocess.run(
        [sys.executable, producer, bmc_dir, "--phase", "projections"],
        capture_output=True, text=True)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip().replace("\n", " ")
        return {}, [("PROJECTION-PRODUCER", "campaign", detail[:800])]
    try:
        posts = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {}, [("PROJECTION-PRODUCER", "campaign",
                     f"invalid JSON from production projection emitter: {exc}")]
    if not isinstance(posts, dict) or not all(
            isinstance(k, str) and isinstance(v, str) for k, v in posts.items()):
        return {}, [("PROJECTION-PRODUCER", "campaign",
                     "production projection emitter returned the wrong shape")]
    return posts, []


def production_residual_premises(bmc_dir):
    """Read production premises out of process, solely as test input."""
    producer = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "houdini_summary.py")
    proc = subprocess.run(
        [sys.executable, producer, bmc_dir, "--phase", "premises"],
        capture_output=True, text=True)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip().replace("\n", " ")
        return {}, [("PREMISE-PRODUCER", "campaign", detail[:800])]
    try:
        premises = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {}, [("PREMISE-PRODUCER", "campaign",
                     f"invalid JSON from production premise emitter: {exc}")]
    if not isinstance(premises, dict) or not all(
            isinstance(k, str) and isinstance(v, str)
            for k, v in premises.items()):
        return {}, [("PREMISE-PRODUCER", "campaign",
                     "production premise emitter returned the wrong shape")]
    return premises, []


def production_residual_suffixes(bmc_dir):
    """Read the production checkpoint contexts in a separate process.

    The production module is the subject under test.  In particular, this
    function does not import its arithmetic carry table into the fuzzer; slot
    addresses and words are reconstructed below from the proof ELF.
    """
    producer_dir = os.path.dirname(os.path.abspath(__file__))
    program = (
        "import json,sys; "
        f"sys.path.insert(0,{producer_dir!r}); "
        "import houdini_summary as producer; "
        "print(json.dumps({'suffixes': producer.residual_suffixes(sys.argv[1]), "
        "'posts': producer.residual_posts(sys.argv[1])}))"
    )
    proc = subprocess.run(
        [sys.executable, "-c", program, bmc_dir],
        capture_output=True, text=True)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip().replace("\n", " ")
        return {}, {}, [("SUFFIX-PRODUCER", "campaign", detail[:800])]
    try:
        subject = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {}, {}, [("SUFFIX-PRODUCER", "campaign",
                         f"invalid JSON from production suffix emitter: {exc}")]
    suffixes = subject.get("suffixes") if isinstance(subject, dict) else None
    posts = subject.get("posts") if isinstance(subject, dict) else None
    if not isinstance(suffixes, dict) or not all(
            isinstance(k, str) and isinstance(v, dict)
            for k, v in suffixes.items()):
        return {}, {}, [("SUFFIX-PRODUCER", "campaign",
                         "production suffix emitter returned the wrong shape")]
    if not isinstance(posts, dict) or not all(
            isinstance(k, str) and isinstance(v, str)
            for k, v in posts.items()):
        return {}, {}, [("SUFFIX-PRODUCER", "campaign",
                         "production suffix posts returned the wrong shape")]
    return suffixes, posts, []


_FALSE_ROUTE_SPECS = {
    # field: (loop header, required machine continuation, adversarial sibling)
    "hSIfNone": (0x8000401C, 0x800042D4, 0x80004090),
    "hSWhileFalse": (0x8000403C, 0x80004090, 0x80004150),
}


def _loop_exit_guards(query, header, target):
    """Find guards selecting one loop exit, independently of producer regexes."""
    symbol = f"loopexit_{header}"
    target_atom = f"#x{target:016x}"

    def selects(term):
        if not isinstance(term, list):
            return False
        if len(term) == 3 and term[0] == "=":
            for call, value in ((term[1], term[2]), (term[2], term[1])):
                if isinstance(call, list) and len(call) == 2 \
                        and call[0] == symbol and value == target_atom:
                    return True
        return any(selects(child) for child in term)

    return sorted(name for name, body in query.binds.items() if selects(body))


def _summary_input_term(query, result_state, symbol):
    """Follow parsed state aliases to one named summary application."""
    state, seen = result_state, set()
    while isinstance(state, str) and state not in seen:
        seen.add(state)
        term = query.binds.get(state)
        if isinstance(term, list) and len(term) == 2 and term[0] == symbol:
            return term[1]
        if not isinstance(term, str):
            return None
        state = term
    return None


def _environment_success_premise(query, residual, extensions):
    """Expected ground successful-lookup premise, parsed independently."""
    spec = {
        "hVar": ("post-env-get", "callee_2147494928"),
        "hAssign": ("post-env-set", "callee_2147495132"),
    }.get(residual)
    if spec is None:
        return None
    checkpoint_name, symbol = spec
    matches = [row.get("state") for row in extensions
               if row.get("name") == checkpoint_name]
    if len(matches) != 1:
        return None
    call_pre = _summary_input_term(query, matches[0], symbol)
    if call_pre is None:
        return None
    return [
        "lean_env_lookup_found",
        ["mm", call_pre],
        ["select", ["rr", call_pre], "#x000000000000000a"],
        ["select", ["rr", call_pre], "#x000000000000000b"],
    ]


def false_route_premise_audit(bmc_dir, production_premises, only=None):
    """Cross-check production false-route extraction against parsed query ASTs."""
    findings, killed = [], 0
    for field, (header, target, sibling) in _FALSE_ROUTE_SPECS.items():
        if only is not None and field not in only:
            continue
        path = os.path.join(bmc_dir, "queries", field + ".smt2")
        if not os.path.exists(path):
            findings.append(("FALSE-ROUTE-NO-QUERY", field,
                             "projected residual query is missing"))
            continue
        query = Query(open(path).read())
        expected = _loop_exit_guards(query, header, target)
        if len(expected) != 1:
            findings.append(("FALSE-ROUTE-NONUNIQUE", field,
                             f"expected one {header:#x}->{target:#x} guard, got {expected}"))
            continue
        try:
            forms = parse_all(production_premises.get(field, ""))
        except ValueError as exc:
            findings.append(("FALSE-ROUTE-PARSE", field, str(exc)))
            continue
        route_asserts = [form[1] for form in forms
                         if isinstance(form, list) and len(form) == 2
                         and form[0] == "assert" and isinstance(form[1], str)]
        if expected[0] not in route_asserts:
            findings.append(("FALSE-ROUTE-WRONG", field,
                             f"production premise omits guard {expected[0]}"))
            continue
        mutant = _loop_exit_guards(query, header, sibling)
        if not mutant or expected[0] in mutant:
            findings.append(("FALSE-ROUTE-MUTATION", field,
                             f"sibling {header:#x}->{sibling:#x} is not distinguishable"))
            continue
        killed += 1
    return findings, killed


def _load_le(mem, addr, width):
    return sum(mem.sel(addr + i) << (8 * i) for i in range(width))


def _signed64(value):
    return value - (1 << 64) if value & (1 << 63) else value


def _signed_div64(left, right):
    a, b = _signed64(left), _signed64(right)
    if b == 0:
        return _M64 if a >= 0 else 1
    quotient = abs(a) // abs(b)
    return (-quotient if (a < 0) != (b < 0) else quotient) & _M64


def _truthy_value(state, offset):
    sp = state.regs.sel(2)
    kind = _load_le(state.mem, sp + offset, 4)
    if kind == 1:
        return _load_le(state.mem, sp + offset + 8, 4) != 0
    if kind == 2:
        return _load_le(state.mem, sp + offset + 8, 8) != 0
    return kind in (3, 4, 5)


def _truthy_at(mem, address):
    """Lean `Value.truthy` on a concrete represented Value address."""
    kind = _load_le(mem, address, 4)
    if kind == 1:
        return _load_le(mem, address + 8, 4) != 0
    if kind == 2:
        return _load_le(mem, address + 8, 8) != 0
    return kind in (3, 4, 5)


def _value_at(state, offset):
    sp = state.regs.sel(2)
    return (_load_le(state.mem, sp + offset, 4),
            _load_le(state.mem, sp + offset + 8, 8))


def _projected_output_value(state, target, expected_kind):
    """Read only the payload width constrained by the represented value kind."""
    width = 4 if expected_kind == 1 else 8
    return (_load_le(state.mem, target, 4),
            _load_le(state.mem, target + 8, width))


def _value_shadow(mem, address):
    """Independent concrete portion of ValueRepr plus all three raw words."""
    kind = _load_le(mem, address, 4)
    payload = _load_le(mem, address + 8, 8)
    aux = _load_le(mem, address + 16, 8)
    valid = (
        kind in (0, 2)
        or (kind == 1 and _load_le(mem, address + 8, 4) in (0, 1))
        or (kind in (3, 4) and payload != 0)
        or (kind == 5 and payload != 0 and aux != 0)
    )
    if not valid:
        return None
    return (kind,
            _load_le(mem, address, 8), payload, aux)


def _arg_vector_shadow(state):
    count = state.regs.sel(15)
    base = (state.regs.sel(2) + 240) & _M64
    values = tuple(_value_shadow(state.mem, base + 24 * index)
                   for index in range(min(count, 32)))
    return None if any(value is None for value in values) else values


def _trace_output_state(tr, row):
    """Exact output prefix before `row`, when the trace records output events."""
    if row >= tr.n or not tr.out_known[row]:
        return OA(), 0, False
    events = getattr(tr, "_output_events", None)
    if events is None:
        events = []
        for k in range(tr.n):
            if tr.out_known[k] and tr.out_after[k] == tr.out_before[k] + 1 \
                    and tr.out_byte[k] <= 0xFF:
                events.append((k, tr.out_before[k], tr.out_byte[k]))
        tr._output_events = events
    out = OA()
    for event_row, index, byte in events:
        if event_row >= row:
            break
        out = out.store(index, byte)
    return out, tr.out_before[row], True


def trace_output_findings(tr):
    """Audit output observations independently of the SMT state transformer."""
    if not tr.n or not all(tr.out_known):
        return [("OUTPUT-UNOBSERVED", tr.name,
                 "trace predates output observations or mixes trace versions")]
    findings = []
    events = []
    for row in range(tr.n):
        before, after, byte = (tr.out_before[row], tr.out_after[row],
                               tr.out_byte[row])
        if row and before != tr.out_after[row - 1]:
            findings.append(("OUTPUT-CHAIN", tr.name,
                             f"row {row}: before={before}, previous after="
                             f"{tr.out_after[row - 1]}"))
            break
        if after == before:
            if byte != 256:
                findings.append(("OUTPUT-SPURIOUS-BYTE", tr.name,
                                 f"row {row}: unchanged length but byte={byte}"))
                break
        elif after == before + 1:
            if byte > 0xFF:
                findings.append(("OUTPUT-MISSING-BYTE", tr.name,
                                 f"row {row}: one chunk appended without one byte"))
                break
            events.append(byte)
        else:
            findings.append(("OUTPUT-DELTA", tr.name,
                             f"row {row}: chunk count {before}->{after}"))
            break
    stdout_path = tr.path + ".stdout"
    if os.path.exists(stdout_path):
        expected = "".join(chr(byte) for byte in events).encode("utf-8")
        observed = open(stdout_path, "rb").read()
        if expected != observed:
            findings.append(("OUTPUT-STDOUT", tr.name,
                             f"trace reconstructs {len(expected)} bytes; stdout has "
                             f"{len(observed)} bytes"))
    return findings


def _machine_state(tr, entry_mem, lo, row):
    """Concrete machine state before trace row `row`."""
    mem = entry_mem
    for k in range(lo, row):
        if tr.mk[k] != MK_STORE or _is_mmio_store(tr.maddr[k], tr.mw[k]):
            continue
        for byte in range(tr.mw[k]):
            mem = mem.store(tr.maddr[k] + byte,
                            (tr.mpost[k] >> (8 * byte)) & 0xFF)
    out, out_len, _ = _trace_output_state(tr, row)
    return St(mem, RA(tuple(tr.regs_at(row)) + (tr.pc[row],)), out, out_len)


def _checkpoint_states(tr, entry_mem, lo, hi, d0):
    """States at semantic checkpoints, selected from the trace, not SMT text."""
    wanted = {
        0x800033D0, 0x80003408, 0x80003414, 0x80003420, 0x8000342C,
        0x80003220, 0x80003224,
        # Strict hCall stages: arm entry/callee call, callee return and both
        # argument cursors, call dispatch, and epilogue handoff.
        0x800031B0, 0x800031BC, 0x800031C0, 0x800031D8, 0x800031DC,
        0x80003254, 0x800033EC,
        0x80003444, 0x8000348C, 0x800034B0, 0x800034B4,
        0x8000351C, 0x8000356C, 0x800035B0, 0x800035EC,
        0x800036BC, 0x800036C0, 0x80003720, 0x80003770,
        0x80003A10, 0x80003AC8, 0x80003AE4, 0x80003AF8, 0x80003B1C,
        # Block allocation and the first exact sequence-child boundary.
        0x8000418C, 0x80004190, 0x80004194, 0x800041A0,
        0x800041C4, 0x800041C8,
        # Constructor-specific false continuations.  Merely selecting the IF
        # or WHILE arm is insufficient: the corresponding Lean constructors
        # also say that the evaluated condition is false.
        0x800042D4, 0x80004090,
    }
    found = {}
    for row in range(lo, hi):
        pc = tr.pc[row]
        if pc in wanted and pc not in found and tr.depth[row] == d0:
            found[pc] = _machine_state(tr, entry_mem, lo, row)
    return found


def concrete_residual_projection(field, s0, checkpoints, query=None):
    """Return ``(applies, expected output)`` from an independent trace oracle.

    Value residuals return ``(kind, payload)``.  Fixed-status statement
    residuals return the status in ``a0``.  The statement path is deliberately
    decoded from the concrete input and trace before the expression decoder is
    touched; x12 is not an expression pointer at ``exec_stmt`` entry.
    """
    query = field if query is None else query

    if field == "hArgsNil":
        value = (s0.regs.sel(15), s0.regs.sel(16))
        return value == (0, 0), (0, 0)

    if field == "hArgsCons":
        # Independent machine oracle for the first iteration exposed by the
        # finite 0x800031dc..0x80003254 span.  This decodes no Lean Value or
        # expression list: the child result is exactly three opaque words.
        call_pre = checkpoints.get(0x80003220)
        child_ret = checkpoints.get(0x80003224)
        index = s0.regs.sel(16)
        argc = s0.regs.sel(15)
        sp = s0.regs.sel(2)
        call = s0.regs.sel(8)
        args_base = _load_le(s0.mem, (call + 16) & _M64, 8)
        arg = _load_le(s0.mem, (args_base + 8 * index) & _M64, 8)
        if call_pre is None or child_ret is None \
                or _signed64(index) < 0 \
                or _signed64(index) >= _signed64(argc) \
                or _signed64(argc) > 32:
            return False, None
        setup = (
            call_pre.regs.sel(2) == sp
            and call_pre.regs.sel(10) == ((sp + 64) & _M64)
            and call_pre.regs.sel(11) == s0.regs.sel(18)
            and call_pre.regs.sel(12) == arg
            and call_pre.regs.sel(13) == s0.regs.sel(13)
        )
        returned = _value_words(child_ret.mem, (sp + 64) & _M64)
        if not setup or returned is None:
            return False, None
        destination = (sp + 240 + 24 * index) & _M64
        return True, (argc, destination, returned)

    if field == "hCallAssertOk":
        argc = s0.regs.sel(12)
        args = s0.regs.sel(13)
        sret = s0.regs.sel(10)
        sret_end = (sret + 24) & _M64
        shadow = _value_shadow(s0.mem, args)
        if argc not in (1, 2) or shadow is None or not _truthy_at(s0.mem, args) \
                or sret < 0x8001AD10 or sret_end > 0x100000000 \
                or sret_end < sret or s0.regs.sel(2) - 80 < 0x8001AD10:
            return False, None
        return True, (
            sret, (0, 0), s0.regs.sel(2),
            tuple(s0.regs.sel(register) for register in (1, 8, 9, 18)),
            True,
        )

    if field == "hCallTooMany" and query == "hCallTooMany":
        sp = s0.regs.sel(2)
        node = s0.regs.sel(8)
        argc = _load_le(s0.mem, node + 24, 4)
        if _load_le(s0.mem, node, 4) != 9 \
                or argc <= 32 or argc >= (1 << 31) \
                or sp + 1016 < 0x8001AD10 \
                or _value_shadow(s0.mem, sp + 96) is None:
            return False, None
        return True, (
            s0.regs.sel(18),
            _sext32(_load_le(s0.mem, node + 4, 4)),
            0x80019470, 0, 0,
            tuple(s0.regs.sel(register)
                  for register in (1, 2, 8, 9, 18, 19, 20, 21, 22, 23)),
            tuple((offset, s0.regs.sel(register))
                  for register, offset in
                  ((19, 1048), (20, 1040), (21, 1032),
                   (22, 1024), (23, 1016))),
            True,
        )

    if field == "hCall" and query == "hCallCallee":
        arm = checkpoints.get(0x800031B0)
        call_pre = checkpoints.get(0x800031BC)
        expr = s0.regs.sel(12)
        if _load_le(s0.mem, expr, 4) != 9 or arm is None or call_pre is None:
            return False, None
        bridge = (
            arm.regs.sel(8) == expr
            and arm.regs.sel(9) == s0.regs.sel(10)
            and arm.regs.sel(18) == s0.regs.sel(11)
            and arm.regs.sel(19) == s0.regs.sel(13)
        )
        sp = arm.regs.sel(2)
        callee = _load_le(arm.mem, expr + 8, 8)
        expected = (
            sp, (sp + 96) & _M64, arm.regs.sel(18), callee,
            arm.regs.sel(19),
            tuple(arm.regs.sel(register)
                  for register in (1, 8, 9, 18, 19, 23)),
            tuple((arm.regs.sel(19) >> (8 * byte)) & 0xFF
                  for byte in range(8)),
            True,
        )
        return (True, expected) if bridge else (False, None)

    if field == "hCall" and query in (
            "hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
        sp = s0.regs.sel(2)
        node = s0.regs.sel(8)
        count = _load_le(s0.mem, node + 24, 4)
        is_nil = query.endswith("Nil")
        if count > 32 or (count == 0) != is_nil:
            return False, None
        shadow = _value_shadow(s0.mem, sp + 96)
        if shadow is None:
            return False, None
        return True, (
            count, 0, _load_le(s0.mem, sp, 8),
            tuple(s0.regs.sel(register)
                  for register in (1, 2, 8, 9, 10, 11, 12, 18, 19, 23)),
            tuple((s0.regs.sel(23) >> (8 * byte)) & 0xFF
                  for byte in range(8)),
            shadow, True,
        )

    if field == "hCall" and query == "hCallArgsToCall":
        callee = _value_shadow(s0.mem, s0.regs.sel(2) + 96)
        args = _arg_vector_shadow(s0)
        if s0.regs.sel(15) > 32 or callee is None or args is None:
            return False, None
        return True, (s0.regs.sel(15), callee, args, True, True)

    if field == "hCall" and query == "hCallCallToEpilogue":
        if "hCall-dispatch-route" not in checkpoints:
            return False, None
        result = _value_shadow(s0.mem, s0.regs.sel(9))
        if result is None:
            return False, None
        return True, (result, True, True)

    if field == "hSBlock" and query == "hSBlock":
        # Independent allocation-seam oracle.  The offsets come from Env's C
        # layout, not the production SMT formula: i32 count, i32 cap, then
        # names, vals, parent as three u64 words.
        env_pre = checkpoints.get(0x80004190)
        env_ret = checkpoints.get(0x80004194)
        setup = checkpoints.get(0x800041A0)
        arm = checkpoints.get(0x8000418C)
        stmt = s0.regs.sel(11)
        if _load_le(s0.mem, stmt, 4) != 2 \
                or arm is None or env_pre is None or env_ret is None \
                or setup is None:
            return False, None
        parent = s0.regs.sel(12)
        inner = env_ret.regs.sel(10)
        observed = (
            (arm.regs.sel(8), arm.regs.sel(9),
             arm.regs.sel(19), arm.regs.sel(18)),
            env_pre.regs.sel(10), inner,
            (_load_le(env_ret.mem, inner, 4),
             _load_le(env_ret.mem, inner + 4, 4),
             _load_le(env_ret.mem, inner + 8, 8),
             _load_le(env_ret.mem, inner + 16, 8),
             _load_le(env_ret.mem, inner + 24, 8)),
            (setup.regs.sel(19), setup.regs.sel(16),
             setup.regs.sel(8), setup.regs.sel(9), setup.regs.sel(18)),
            env_ret.out == env_pre.out and env_ret.out_len == env_pre.out_len,
            setup.out == env_ret.out and setup.out_len == env_ret.out_len,
            inner != 0 and inner & 7 == 0,
        )
        expected = (
            (s0.regs.sel(11), s0.regs.sel(10),
             s0.regs.sel(12), s0.regs.sel(13)),
            parent, inner, (0, 0, 0, 0, parent),
            (inner, 0, s0.regs.sel(11), s0.regs.sel(10), s0.regs.sel(13)),
            True, True, True,
        )
        return (True, expected) if observed == expected else (False, None)

    if field == "hSBlock" and query == "hSBlockIter":
        # Exact first-child boundary.  This applies to normal and abrupt child
        # returns alike; no terminal filter may hide call-setup defects.
        call_pre = checkpoints.get(0x800041C4)
        if call_pre is None:
            return False, None
        index = s0.regs.sel(16)
        node = s0.regs.sel(8)
        count = _signed64(_sext32(_load_le(s0.mem, node + 16, 4)))
        signed_index = _signed64(index)
        if signed_index < 0 or signed_index >= count:
            return False, None
        stmts = _load_le(s0.mem, node + 8, 8)
        stmt = _load_le(s0.mem, stmts + 8 * index, 8)
        expected = (
            (s0.regs.sel(2), s0.regs.sel(9), stmt,
             s0.regs.sel(19), s0.regs.sel(18)),
        )
        return True, expected

    if field == "hSBlock" and query in ("hSBlockNormal", "hSBlockAbrupt"):
        status = s0.regs.sel(10)
        normal = query == "hSBlockNormal"
        if (status == 0) != normal:
            return False, None
        # 0x41c8 -> 0x41cc and 0x41c8 -> 0x409c are each one conditional
        # branch.  They preserve every GPR, every memory byte, and all output.
        return True, (status, True, True)

    if field in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop") \
            and _WHILE_QUERY_FIELDS.get(query) == field:
        # These four cuts mirror the proof's recursive boundaries.  They say
        # nothing about the child relation: setup stops before the call, and
        # the next cut starts from the independently observed return state.
        abi = tuple(s0.regs.sel(register)
                    for register in (1, 2, 8, 9, 18, 19))
        sp = s0.regs.sel(2)
        node = s0.regs.sel(8)
        if query.endswith("CondSetup"):
            expected = (
                (sp + 80) & _M64,
                s0.regs.sel(9),
                _load_le(s0.mem, node + 8, 8),
                s0.regs.sel(19),
                abi, True, True,
            )
            return True, expected
        if query.endswith("CondTruthy"):
            if not _truthy_value(s0, 80):
                return False, None
            copied = tuple(_load_le(s0.mem, sp + offset, 8)
                           for offset in (80, 88, 96))
            # value_truthy writes no memory.  The surrounding code copies the
            # complete 24-byte Value from sp+80 to sp+16.
            return True, (
                1, copied,
                tuple(s0.regs.sel(register)
                      for register in (2, 8, 9, 18, 19)),
                True,
            )
        if query.endswith("BodySetup"):
            expected = (
                s0.regs.sel(9),
                _load_le(s0.mem, node + 16, 8),
                s0.regs.sel(19),
                s0.regs.sel(18),
                abi, True, True,
            )
            return True, expected
        status = s0.regs.sel(10)
        if field == "hSWhileBreak":
            if status != 1:
                return False, None
            final_status = 0
        elif field == "hSWhileRet":
            if status != 3:
                return False, None
            final_status = 3
        else:
            if status not in (0, 2):
                return False, None
            final_status = status
        return True, (final_status, abi, True, True)

    if field in ("hCallPrint", "hCallPrintln"):
        argc = s0.regs.sel(12)
        args_base = s0.regs.sel(13)
        if argc > 32:
            return False, None
        args = [_value_display_semantics(s0.mem, args_base + 24 * index)
                for index in range(argc)]
        if any(value is None for value in args):
            return False, None
        rendered = b" ".join(args)
        if field == "hCallPrintln":
            rendered += b"\n"
        return True, (rendered, (0, 0))

    if field == "hVar":
        expr = s0.regs.sel(12)
        if _load_le(s0.mem, expr, 4) != 4:
            return False, None
        name = _load_le(s0.mem, expr + 8, 8)
        env = s0.regs.sel(13)
        slot = _env_lookup_slot_semantics(s0.mem, env, name)
        link = checkpoints.get(0x80003444)
        if slot in (None, 0) or link is None:
            return False, None
        words = _value_words(s0.mem, slot)
        if words is None:
            return False, None
        # `s0` is eval_expr's function entry, before its 1088-byte prologue.
        # env_get writes the temporary Value at lowered-sp+240, not at
        # entry-sp+240.  The shared tail beginning at 0x80003448 subsequently
        # copies this temporary into the caller's sret buffer.
        destination = (s0.regs.sel(2) - _EVAL_FRAME_BYTES + 240) & _M64
        return True, (1, destination, words)

    if field == "hAssign":
        expr = s0.regs.sel(12)
        call_pre = checkpoints.get(0x800034B0)
        link = checkpoints.get(0x800034B4)
        if _load_le(s0.mem, expr, 4) != 5 or call_pre is None or link is None:
            return False, None
        env = call_pre.regs.sel(10)
        name = call_pre.regs.sel(11)
        value = call_pre.regs.sel(12)
        slot = _env_lookup_slot_semantics(call_pre.mem, env, name)
        words = _value_words(call_pre.mem, value)
        if slot in (None, 0) or words is None:
            return False, None
        return True, (1, slot, words)

    if field in _STATUS_PROJECTION_FIELDS:
        kind, status, child_offset, child_present, route_pc = \
            _STATUS_PROJECTION_FIELDS[field]
        stmt = s0.regs.sel(11)
        stmt_kind = _load_le(s0.mem, stmt, 4)
        applies = stmt_kind == kind
        if child_offset is not None:
            child = _load_le(s0.mem, stmt + child_offset, 8)
            applies = applies and ((child != 0) == child_present)
        if route_pc is not None:
            applies = applies and route_pc in checkpoints
        return applies, status

    expr = s0.regs.sel(12)
    expr_kind = _load_le(s0.mem, expr, 4)
    token = _load_le(s0.mem, expr + 8, 4)

    leaf = {
        "hInt": (0, 2, _load_le(s0.mem, expr + 8, 8)),
        "hStr": (1, 3, _load_le(s0.mem, expr + 8, 8)),
        "hBool": (2, 1, int(_load_le(s0.mem, expr + 8, 4) != 0)),
        "hNull": (3, 0, 0),
    }
    if field in leaf:
        required_kind, result_kind, payload = leaf[field]
        return expr_kind == required_kind, (result_kind, payload)

    if field in ("hNeg", "hNot"):
        state = checkpoints.get(0x800035EC)
        if state is None or expr_kind != 8 or token != {"hNeg": 12, "hNot": 16}[field]:
            return False, None
        kind, payload = _value_at(state, 144)
        if field == "hNeg":
            return kind == 2, (2, (-payload) & _M64)
        return kind <= 5, (1, int(not _truthy_value(state, 144)))

    if field in ("hAndFalse", "hAndTrue", "hOrTrue", "hOrFalse"):
        left_state = checkpoints.get(0x8000356C)
        required_token = 24 if field.startswith("hAnd") else 25
        if left_state is None or expr_kind != 7 or token != required_token:
            return False, None
        left_kind, _ = _value_at(left_state, 120)
        if left_kind > 5:
            return False, None
        left_truthy = _truthy_value(left_state, 120)
        if field == "hAndFalse":
            return not left_truthy, (1, 0)
        if field == "hOrTrue":
            return left_truthy, (1, 1)
        point, offset = ((0x800035B0, 240) if field == "hAndTrue"
                         else (0x80003A10, 144))
        right_state = checkpoints.get(point)
        if right_state is None or left_truthy != (field == "hAndTrue"):
            return False, None
        right_kind, _ = _value_at(right_state, offset)
        return right_kind <= 5, (1, int(_truthy_value(right_state, offset)))

    if field in ("hEq", "hNe"):
        point = 0x80003720 if field == "hEq" else 0x80003770
        state = checkpoints.get(point)
        values = checkpoints.get(0x8000351C)
        required_token = 19 if field == "hEq" else 17
        if state is None or values is None or expr_kind != 6 \
                or token != required_token:
            return False, None
        sp = values.regs.sel(2)
        equal_result = _value_equal_semantics(
            values.mem, sp + 120, sp + 144)
        if equal_result is None:
            return False, None
        return True, (1, int(not equal_result if field == "hNe" else equal_result))

    if field in ("hStrAddL", "hStrAddR"):
        state = checkpoints.get(0x80003AC8)
        values = checkpoints.get(0x8000351C)
        if state is None or values is None or expr_kind != 6 or token != 11:
            return False, None
        left_kind, _ = _value_at(values, 120)
        right_kind, _ = _value_at(values, 144)
        applies = left_kind == 3 if field == "hStrAddL" \
            else left_kind != 3 and right_kind == 3
        return applies, (3, state.regs.sel(8))

    if field in ("hStrLt", "hStrLe", "hStrGt", "hStrGe"):
        point = {
            "hStrLt": 0x800036C0, "hStrLe": 0x80003AF8,
            "hStrGt": 0x80003AE4, "hStrGe": 0x800036BC,
        }[field]
        state = checkpoints.get(point)
        values = checkpoints.get(0x8000351C)
        required_token = {
            "hStrLt": 20, "hStrLe": 21, "hStrGt": 22, "hStrGe": 23,
        }[field]
        if state is None or values is None or expr_kind != 6 \
                or token != required_token:
            return False, None
        if _value_at(values, 120)[0] != 3 or _value_at(values, 144)[0] != 3:
            return False, None
        sp = values.regs.sel(2)
        left_ptr = _try_load_le(values.mem, sp + 128, 8)
        right_ptr = _try_load_le(values.mem, sp + 152, 8)
        if left_ptr is None or right_ptr is None:
            return False, None
        result = _strcmp_semantics(values.mem, left_ptr, right_ptr)
        if result is None:
            return False, None
        truth = {
            "hStrLt": result < 0, "hStrLe": result <= 0,
            "hStrGt": result > 0, "hStrGe": result >= 0,
        }[field]
        return True, (1, int(truth))

    if field == "hFn":
        state = checkpoints.get(0x800033D0)
        saved_expr = state.regs.sel(8) if state is not None else 0
        if state is None or _load_le(state.mem, saved_expr, 4) != 10 \
                or state.regs.sel(10) == 0:
            return False, None
        return True, (4, state.regs.sel(10))

    if field in _BINARY_TOKENS:
        state = checkpoints.get(0x8000351C)
        if state is None or expr_kind != 6 or token != _BINARY_TOKENS[field]:
            return False, None
        left_kind, left = _value_at(state, 120)
        right_kind, right = _value_at(state, 144)
        if left_kind != 2 or right_kind != 2:
            return False, None
        overflow = left == 1 << 63 and right == _M64
        if field == "hDivOv":
            return overflow, (2, 1 << 63)
        if field == "hIDiv" and (right == 0 or overflow):
            return False, None
        if field == "hIMod" and right == 0:
            return False, None
        if field == "hIAdd":
            return True, (2, (left + right) & _M64)
        if field == "hISub":
            return True, (2, (left - right) & _M64)
        if field == "hIMul":
            return True, (2, (left * right) & _M64)
        if field == "hIDiv":
            return True, (2, _signed_div64(left, right))
        if field == "hIMod":
            quotient = _signed64(_signed_div64(left, right))
            return True, (2, (_signed64(left) - quotient * _signed64(right)) & _M64)
        comparison = {
            "hILt": _signed64(left) < _signed64(right),
            "hILe": _signed64(left) <= _signed64(right),
            "hIGt": _signed64(left) > _signed64(right),
            "hIGe": _signed64(left) >= _signed64(right),
        }[field]
        return True, (1, int(comparison))

    return False, None


def _store_le(mem, address, width, value):
    """Store one little-endian scalar into an independent concrete memory."""
    for byte in range(width):
        mem = mem.store(address + byte, (value >> (8 * byte)) & 0xFF)
    return mem


_ARITHMETIC_SUFFIX_FIELDS = set(_PREMISE_BINARY_FIELDS) | {"hNeg"}

_NONARITHMETIC_SUFFIX_POINTS = {
    "hInt": 0x80003408, "hStr": 0x80003414,
    "hBool": 0x80003420, "hNull": 0x8000342C,
    "hNot": 0x800035EC,
    "hAndFalse": 0x8000356C, "hOrTrue": 0x8000356C,
    "hAndTrue": 0x800035B0, "hOrFalse": 0x80003A10,
    "hEq": 0x80003720, "hNe": 0x80003770,
    "hStrAddL": 0x80003AC8, "hStrAddR": 0x80003AC8,
    "hStrLt": 0x80003B1C, "hStrLe": 0x80003B1C,
    "hStrGt": 0x80003B1C, "hStrGe": 0x80003B1C,
    "hFn": 0x800033D0,
}
_NONARITHMETIC_SUFFIX_FIELDS = set(_NONARITHMETIC_SUFFIX_POINTS)


def _binary_jump_slot(img, token):
    """Derive eval_expr's integer-binop slot from independently decoded code.

    The production checker has a per-field carry table.  The fuzzer instead
    decodes the index origin, scale, and PC-relative table base from the proof
    binary.  Thus a copied wrong table cannot make producer and oracle agree.
    """
    index = decode(0x80003528, img.word(0x80003528))
    shift_left = decode(0x80003538, img.word(0x80003538))
    shift_right = decode(0x8000353C, img.word(0x8000353C))
    upper = decode(0x80003540, img.word(0x80003540))
    lower = decode(0x80003544, img.word(0x80003544))
    table_load = decode(0x8000354C, img.word(0x8000354C))
    dispatch = decode(0x80003558, img.word(0x80003558))
    shape = (
        index.kind == "addiw" and index.rd == 15 and index.rs1 == 12,
        shift_left.kind == "slli" and shift_left.rd == 14
        and shift_left.rs1 == 15 and shift_left.imm == 32,
        shift_right.kind == "srli" and shift_right.rd == 15
        and shift_right.rs1 == 14 and shift_right.imm == 30,
        upper.kind == "auipc" and upper.rd == 14,
        lower.kind == "addi" and lower.rd == 14 and lower.rs1 == 14,
        table_load.kind == "lw" and table_load.rd == 15
        and table_load.rs1 == 15 and table_load.imm == 0,
        dispatch.kind == "jalr" and dispatch.rd == 0
        and dispatch.rs1 == 15,
    )
    if not all(shape):
        raise ValueError("integer-binop jump-table sequence changed shape")
    origin = -index.imm
    scaled_index = token - origin
    if not 0 <= scaled_index <= 12:
        raise ValueError(f"operator token {token} is outside the jump table")
    table_base = (upper.pc + upper.imm + lower.imm) & _M64
    return (table_base + 4 * scaled_index) & _M64


def _assertion_bodies(text):
    forms = parse_all(text)
    if any(not isinstance(form, list) or len(form) != 2 or form[0] != "assert"
           for form in forms):
        raise ValueError("suffix context contains a non-assert top-level form")
    return [form[1] for form in forms]


def _one_term(text):
    forms = parse_all(text)
    if len(forms) != 1:
        raise ValueError("expected one SMT term")
    return forms[0]


def _suffix_expected_assertions(field, state_name, img):
    """The checkpoint contract reconstructed without production carry data."""
    state = state_name
    sp = f"(select (rr {state}) #x0000000000000002)"
    mem = f"(mm {state})"
    sret = f"(select (rr {state}) #x0000000000000009)"

    def load(offset, width=8):
        return f"(ld{width} {mem} (bvadd {sp} #x{offset:016x}))"

    expected = {
        "sret-disjoint": (
            f"(or (bvule (bvadd {sret} #x0000000000000018) {sp}) "
            f"(bvule (bvadd {sp} #x0000000000000440) {sret}))"),
        "sp-lower": f"(bvule #x0000000080000000 {sp})",
        "sp-upper": f"(bvule {sp} #x00000000fffffbc0)",
        "sret-lower": f"(bvule #x0000000080000000 {sret})",
        "sret-upper": f"(bvule {sret} #x00000000ffffffe8)",
        "machine-invariant": f"(INV {state})",
    }
    x8 = f"(select (rr {state}) #x0000000000000008)"
    if field == "hNeg":
        expected.update({
            "operand-kind": f"(= {load(144, 4)} #x0000000000000002)",
            "checkpoint-op-token": (
                f"(= (ld4 {mem} (bvadd {x8} #x0000000000000008)) "
                "#x000000000000000c)"),
        })
        return {name: _one_term(term) for name, term in expected.items()}

    token = _BINARY_TOKENS[field]
    slot = _binary_jump_slot(img, token)
    word = img.word(slot)
    left = load(128)
    right = load(152)
    expected.update({
        "left-kind": f"(= {load(120, 4)} #x0000000000000002)",
        "right-kind": f"(= {load(144, 4)} #x0000000000000002)",
        "x19-left-payload": (
            f"(= (select (rr {state}) #x0000000000000013) {left})"),
        "respilled-left-kind": f"(= (ld8 {mem} {sp}) #x0000000000000002)",
        "checkpoint-op-token": (
            f"(= (ld4 {mem} (bvadd {x8} #x0000000000000008)) "
            f"#x{token:016x})"),
        "jump-slot-word": f"(= (ld4 {mem} #x{slot:016x}) #x{word:016x})",
    })
    if field in ("hIDiv", "hIMod"):
        expected["nonzero-divisor"] = \
            f"(not (= {right} #x0000000000000000))"
    if field == "hIDiv":
        expected["nonoverflow"] = (
            f"(not (and (= {left} #x8000000000000000) "
            f"(= {right} #xffffffffffffffff)))")
    if field == "hDivOv":
        expected.update({
            "min-dividend": f"(= {left} #x8000000000000000)",
            "minus-one-divisor": f"(= {right} #xffffffffffffffff)",
        })
    return {name: _one_term(term) for name, term in expected.items()}


def _with_mem_value(state, address, width, value):
    return St(_store_le(state.mem, address, width, value), state.regs,
              state.out, state.out_len)


def _with_reg_value(state, register, value):
    return St(state.mem, state.regs.store(register, value),
              state.out, state.out_len)


def _with_output_byte(state, index, value):
    return St(state.mem, state.regs, state.out.store(index, value),
              state.out_len)


def _while_fixture(query, premise_mutation=None):
    """Independent state pair for one finite while projection."""
    if query not in _WHILE_QUERIES:
        raise ValueError(f"not a while projection: {query}")
    sp, node = 0x80020000, 0x4000
    if premise_mutation == "stack-above-htif":
        sp = 0x8001ACF0
    regs = [0] * 33
    regs[1], regs[2] = 0x1111, sp
    regs[8], regs[9] = node, 0x2222
    regs[18], regs[19] = 0x3333, 0x4444
    mem = MA({}, lambda _address: 0, set())
    mem = _store_le(mem, node + 8, 8, 0x5000)
    mem = _store_le(mem, node + 16, 8, 0x6000)
    mem = _store_le(mem, sp + 80, 4, 1)
    mem = _store_le(mem, sp + 88, 4, 1)
    mem = _store_le(mem, sp + 96, 8, 0xA5A5)
    out = OA().store(0, 0x51)
    s0 = St(mem, RA(tuple(regs)), out, 1)
    exit_state = s0
    if query.endswith("CondSetup"):
        exit_state = _with_reg_value(exit_state, 10, sp + 80)
        exit_state = _with_reg_value(exit_state, 11, regs[9])
        exit_state = _with_reg_value(exit_state, 12, 0x5000)
        exit_state = _with_reg_value(exit_state, 13, regs[19])
    elif query.endswith("CondTruthy"):
        if premise_mutation == "condition-bool-canonical":
            s0 = _with_mem_value(s0, sp + 88, 4, 2)
            exit_state = s0
        if premise_mutation == "condition-truthy":
            s0 = _with_mem_value(s0, sp + 80, 4, 0)
            exit_state = s0
        else:
            for destination, source in ((16, 80), (24, 88), (32, 96)):
                exit_state = _with_mem_value(
                    exit_state, sp + destination, 8,
                    _load_le(s0.mem, sp + source, 8))
            kind = _load_le(s0.mem, sp + 80, 4)
            truthy_result = (_sext32(_load_le(s0.mem, sp + 88, 4))
                             if kind == 1 else int(_truthy_value(s0, 80)))
            exit_state = _with_reg_value(exit_state, 10, truthy_result)
    elif query.endswith("BodySetup"):
        exit_state = _with_reg_value(exit_state, 10, regs[9])
        exit_state = _with_reg_value(exit_state, 11, 0x6000)
        exit_state = _with_reg_value(exit_state, 12, regs[19])
        exit_state = _with_reg_value(exit_state, 13, regs[18])
    else:
        field = _WHILE_QUERY_FIELDS[query]
        status = {"hSWhileBreak": 1, "hSWhileRet": 3,
                  "hSWhileLoop": 0}[field]
        if premise_mutation is not None:
            status = 0 if field != "hSWhileLoop" else 1
        s0 = _with_reg_value(s0, 10, status)
        exit_state = s0
        if field == "hSWhileBreak" and not premise_mutation:
            exit_state = _with_reg_value(exit_state, 10, 0)
    return s0, exit_state


def _while_post_mutants(query, s0, exit_state):
    """One concrete result mutation for every post conjunct."""
    register_mutations = []
    if query.endswith("CondSetup") or query.endswith("BodySetup"):
        registers = (10, 11, 12, 13, 1, 2, 8, 9, 18, 19)
    elif query.endswith("CondTruthy"):
        registers = (10, 2, 8, 9, 18, 19)
    else:
        registers = (10, 1, 2, 8, 9, 18, 19)
    for register in registers:
        register_mutations.append((
            f"x{register}",
            _with_reg_value(
                exit_state, register, exit_state.regs.sel(register) ^ 1)))
    memory_mutations = []
    if query.endswith("CondTruthy"):
        sp = s0.regs.sel(2)
        for offset in (16, 24, 32):
            memory_mutations.append((
                f"copy+{offset}",
                _with_mem_value(
                    exit_state, sp + offset, 8,
                    _load_le(exit_state.mem, sp + offset, 8) ^ 1)))
    else:
        memory_mutations.append((
            "memory", _with_mem_value(exit_state, 0x80004088, 1,
                                      exit_state.mem.sel(0x80004088) ^ 1)))
    output_mutations = [
        ("output-array", _with_output_byte(
            exit_state, exit_state.out_len,
            exit_state.out.sel(exit_state.out_len) ^ 1)),
        ("output-length", St(
            exit_state.mem, exit_state.regs, exit_state.out,
            exit_state.out_len + 1)),
    ]
    return register_mutations + memory_mutations + output_mutations


def _call_fixture(query):
    """Independent concrete input/output pair for one strict hCall cut."""
    if query not in _CALL_QUERIES:
        raise ValueError(f"not an hCall projection: {query}")
    s0, points = _premise_fixture(query)
    checkpoints = {}
    if query == "hCallCallee":
        arm = points["0x800031b0"]
        sp = arm.regs.sel(2)
        expr = arm.regs.sel(8)
        exit_state = _with_reg_value(arm, 10, (sp + 96) & _M64)
        exit_state = _with_reg_value(
            exit_state, 12, _load_le(arm.mem, expr + 8, 8))
        exit_state = _with_mem_value(
            exit_state, sp, 8, arm.regs.sel(13))
        checkpoints = {0x800031B0: arm, 0x800031BC: exit_state}
    elif query == "hCallTooMany":
        sp = s0.regs.sel(2)
        node = s0.regs.sel(8)
        exit_state = _with_reg_value(s0, 10, s0.regs.sel(18))
        exit_state = _with_reg_value(
            exit_state, 11,
            _sext32(_load_le(s0.mem, node + 4, 4)))
        exit_state = _with_reg_value(exit_state, 12, 0x80019470)
        exit_state = _with_reg_value(exit_state, 13, 0)
        exit_state = _with_reg_value(exit_state, 14, 0)
        for register, offset in ((19, 1048), (20, 1040), (21, 1032),
                                 (22, 1024), (23, 1016)):
            exit_state = _with_mem_value(
                exit_state, sp + offset, 8, s0.regs.sel(register))
    elif query in ("hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
        sp = s0.regs.sel(2)
        count = _load_le(s0.mem, s0.regs.sel(8) + 24, 4)
        exit_state = _with_reg_value(s0, 15, count)
        exit_state = _with_reg_value(exit_state, 16, 0)
        exit_state = _with_reg_value(
            exit_state, 13, _load_le(s0.mem, sp, 8))
        exit_state = _with_mem_value(
            exit_state, sp + 1016, 8, s0.regs.sel(23))
    else:
        exit_state = s0
        if query == "hCallCallToEpilogue":
            checkpoints["hCall-dispatch-route"] = s0
    return s0, exit_state, checkpoints


def _call_post_mutants(query, s0, exit_state, checkpoints):
    """Independent mutations of every observable class in an hCall post."""
    if query == "hCallTooMany":
        mutants = [
            (f"x{register}", "state_exit",
             _with_reg_value(
                 exit_state, register, exit_state.regs.sel(register) ^ 1))
            for register in
            (10, 11, 12, 13, 14, 1, 2, 8, 9, 18, 19, 20, 21, 22, 23)
        ]
        sp = s0.regs.sel(2)
        for register, offset in ((19, 1048), (20, 1040), (21, 1032),
                                 (22, 1024), (23, 1016)):
            address = sp + offset
            mutants.append((
                f"spill-x{register}", "state_exit",
                _with_mem_value(
                    exit_state, address, 1,
                    exit_state.mem.sel(address) ^ 1)))
        mutants.extend([
            ("unexpected-memory", "state_exit",
             _with_mem_value(
                 exit_state, s0.regs.sel(8) + 32, 1,
                 exit_state.mem.sel(s0.regs.sel(8) + 32) ^ 1)),
            ("output-array", "state_exit",
             _with_output_byte(
                 exit_state, exit_state.out_len,
                 exit_state.out.sel(exit_state.out_len) ^ 1)),
            ("output-length", "state_exit",
             St(exit_state.mem, exit_state.regs, exit_state.out,
                exit_state.out_len + 1)),
        ])
        return mutants

    if query == "hCallCallee":
        call_pre = checkpoints[0x800031BC]
        mutants = [
            (f"pre-x{register}", "state_exit",
             _with_reg_value(
                 call_pre, register, call_pre.regs.sel(register) ^ 1))
            for register in (2, 10, 11, 12, 13, 1, 8, 9, 18, 19, 23)
        ]
        sp = checkpoints[0x800031B0].regs.sel(2)
        mutants.extend([
            ("env-spill", "state_exit",
             _with_mem_value(
                 call_pre, sp, 1, call_pre.mem.sel(sp) ^ 1)),
            ("output-array", "state_exit",
             _with_output_byte(
                 call_pre, call_pre.out_len,
                 call_pre.out.sel(call_pre.out_len) ^ 1)),
            ("output-length", "state_exit",
             St(call_pre.mem, call_pre.regs, call_pre.out,
                call_pre.out_len + 1)),
        ])
        return mutants

    if query in ("hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
        mutants = [
            (f"x{register}", "state_exit",
             _with_reg_value(
                 exit_state, register, exit_state.regs.sel(register) ^ 1))
            for register in (15, 16, 13, 1, 2, 8, 9, 10, 11, 12, 18, 19, 23)
        ]
        sp = s0.regs.sel(2)
        mutants.extend([
            ("s7-spill", "state_exit",
             _with_mem_value(
                 exit_state, sp + 1016, 1,
                 exit_state.mem.sel(sp + 1016) ^ 1)),
            ("callee-shadow", "state_exit",
             _with_mem_value(exit_state, sp + 96, 4, 6)),
            ("output-array", "state_exit",
             _with_output_byte(
                 exit_state, exit_state.out_len,
                 exit_state.out.sel(exit_state.out_len) ^ 1)),
            ("output-length", "state_exit",
             St(exit_state.mem, exit_state.regs, exit_state.out,
                exit_state.out_len + 1)),
        ])
        return mutants

    if query == "hCallArgsToCall":
        sp = s0.regs.sel(2)
        return [
            ("register-array", "state_exit",
             _with_reg_value(exit_state, 1, exit_state.regs.sel(1) ^ 1)),
            ("memory-array", "state_exit",
             _with_mem_value(
                 exit_state, 0x80003254, 1,
                 exit_state.mem.sel(0x80003254) ^ 1)),
            ("callee-shadow", "state_exit",
             _with_mem_value(exit_state, sp + 96, 4, 6)),
            ("arg-vector-shadow", "state_exit",
             _with_mem_value(exit_state, sp + 240, 4, 6)),
            ("output-array", "state_exit",
             _with_output_byte(
                 exit_state, exit_state.out_len,
                 exit_state.out.sel(exit_state.out_len) ^ 1)),
            ("output-length", "state_exit",
             St(exit_state.mem, exit_state.regs, exit_state.out,
                exit_state.out_len + 1)),
        ]

    result = s0.regs.sel(9)
    return [
        ("register-array", "state_exit",
         _with_reg_value(exit_state, 1, exit_state.regs.sel(1) ^ 1)),
        ("memory-array", "state_exit",
         _with_mem_value(
             exit_state, 0x800033EC, 1,
             exit_state.mem.sel(0x800033EC) ^ 1)),
        ("result-shadow", "state_exit",
         _with_mem_value(exit_state, result, 4, 6)),
        ("output-array", "state_exit",
         _with_output_byte(
             exit_state, exit_state.out_len,
             exit_state.out.sel(exit_state.out_len) ^ 1)),
        ("output-length", "state_exit",
         St(exit_state.mem, exit_state.regs, exit_state.out,
            exit_state.out_len + 1)),
    ]


def _assert_ok_post_mutants(s0, exit_state):
    """Independent mutations for every conjunct of the assert-success post."""
    sret = s0.regs.sel(10)
    mutants = [
        ("null-kind", _with_mem_value(exit_state, sret, 4, 1)),
        ("null-payload", _with_mem_value(exit_state, sret + 8, 8, 1)),
    ]
    mutants.extend(
        (f"x{register}", _with_reg_value(
            exit_state, register, exit_state.regs.sel(register) ^ 1))
        for register in (2, 1, 8, 9, 18)
    )
    mutants.extend([
        ("output-array", _with_output_byte(
            exit_state, exit_state.out_len,
            exit_state.out.sel(exit_state.out_len) ^ 1)),
        ("output-length", St(
            exit_state.mem, exit_state.regs, exit_state.out,
            exit_state.out_len + 1)),
    ])
    return mutants


def _concrete_layout_witness(stack, allocation):
    """Choose legal concrete SL/A intervals for evaluating an abstract INV.

    `allocation` is only a useful hint when a0 actually contains an address;
    arithmetic checkpoints commonly contain the small result payload instead.
    """
    stack_lo, stack_hi = stack - 0x2000, stack + 0x2000
    arena_lo, arena_hi = 0x10000, 0x12000
    if 0x10000 <= allocation < 0xFFFFFFFF:
        candidate_lo = allocation & ~0xFFF
        candidate_hi = min(max(candidate_lo + 0x2000,
                                allocation + 0x1000), 0xFFFFFFFF)
        if candidate_hi < stack_lo or candidate_lo > stack_hi:
            arena_lo, arena_hi = candidate_lo, candidate_hi
    return {
        "SL_lo": stack_lo,
        "SL_hi": stack_hi,
        "A_lo": arena_lo,
        "A_hi": arena_hi,
    }


def _eval_suffix_term(query, s0, state_name, checkpoint, term, exit_state=None,
                      layout_state=None):
    def reject_summary(*_args):
        raise EvalError("suffix predicate unexpectedly invokes a summary")

    ev = Ev(query, s0, reject_summary)
    ev.env[state_name] = checkpoint
    # INV intentionally leaves the stack and allocation intervals symbolic.
    # Supply one independently constructed witness around this concrete stack
    # pointer so its predicate can be exercised by the concrete evaluator.
    anchor = checkpoint if layout_state is None else layout_state
    stack = anchor.regs.sel(2)
    allocation = anchor.regs.sel(10)
    ev.env.update(_concrete_layout_witness(stack, allocation))
    if exit_state is not None:
        ev.env["state_exit"] = exit_state
    return bool(ev.ev(term))


def _write_projected_value(state, target, kind, payload):
    mem = _store_le(state.mem, target, 4, kind)
    width = 4 if kind == 1 else 8
    mem = _store_le(mem, target + 8, width, payload)
    return St(mem, state.regs, state.out, state.out_len)


def _nonarithmetic_suffix_expected_assertions(field, state_name):
    """Checkpoint facts reconstructed independently of the production table."""
    state = state_name
    reg = lambda n: f"(select (rr {state}) #x{n:016x})"
    sp = reg(2)
    mem = f"(mm {state})"

    def load_reg(register, offset, width=4):
        return (f"(ld{width} {mem} (bvadd {reg(register)} "
                f"#x{offset:016x}))")

    def load_sp(offset, width=4):
        return f"(ld{width} {mem} (bvadd {sp} #x{offset:016x}))"

    def truthy(offset):
        kind = load_sp(offset, 4)
        bool_value = load_sp(offset + 8, 4)
        int_value = load_sp(offset + 8, 8)
        return (f"(or (and (= {kind} #x0000000000000001) "
                f"(not (= {bool_value} #x0000000000000000))) "
                f"(and (= {kind} #x0000000000000002) "
                f"(not (= {int_value} #x0000000000000000))) "
                f"(= {kind} #x0000000000000003) "
                f"(= {kind} #x0000000000000004) "
                f"(= {kind} #x0000000000000005))")

    def falsy(offset):
        kind = load_sp(offset, 4)
        bool_value = load_sp(offset + 8, 4)
        int_value = load_sp(offset + 8, 8)
        return (f"(or (= {kind} #x0000000000000000) "
                f"(and (= {kind} #x0000000000000001) "
                f"(= {bool_value} #x0000000000000000)) "
                f"(and (= {kind} #x0000000000000002) "
                f"(= {int_value} #x0000000000000000)))")

    def sret_window():
        target = reg(9)
        end = f"(bvadd {target} #x0000000000000018)"
        return {
            "sret-above-htif": f"(bvule #x000000008001ad10 {target})",
            "sret-no-wrap": f"(bvule {target} {end})",
            "sret-below-4g": f"(bvule {end} #x0000000100000000)",
        }

    expected = {}
    leaf_kinds = {"hInt": 0, "hStr": 1, "hBool": 2, "hNull": 3}
    if field in leaf_kinds:
        expected = {
            "leaf-arm-kind": (
                f"(= {load_reg(12, 0)} #x{leaf_kinds[field]:016x})"),
            "sret-register": f"(= {reg(10)} {reg(9)})",
        }
    elif field == "hNot":
        expected = {
            "checkpoint-op-token": (
                f"(= {load_reg(8, 8)} #x0000000000000010)"),
            "operand-value": (
                f"(bvule {load_sp(144, 4)} #x0000000000000005)"),
        }
    elif field in ("hAndFalse", "hOrTrue"):
        token = 24 if field == "hAndFalse" else 25
        expected = {
            "checkpoint-op-token": f"(= {load_reg(8, 8)} #x{token:016x})",
            "left-falsy" if field == "hAndFalse" else "left-truthy":
                falsy(120) if field == "hAndFalse" else truthy(120),
        }
    elif field in ("hAndTrue", "hOrFalse"):
        token = 24 if field == "hAndTrue" else 25
        offset = 240 if field == "hAndTrue" else 144
        expected = {
            "checkpoint-op-token": f"(= {load_reg(8, 8)} #x{token:016x})",
            "right-value": (
                f"(bvule {load_sp(offset, 4)} #x0000000000000005)"),
            "left-truthy" if field == "hAndTrue" else "left-falsy":
                truthy(120) if field == "hAndTrue" else falsy(120),
        }
    elif field in ("hEq", "hNe"):
        expected = {
            "equal-left-value": (
                f"(bvule {load_sp(64, 4)} #x0000000000000005)"),
            "equal-right-value": (
                f"(bvule {load_sp(32, 4)} #x0000000000000005)"),
            "value-equal-relation": (
                f"(= {reg(10)} (lean_value_equal {mem} "
                f"(bvadd {sp} #x0000000000000040) "
                f"(bvadd {sp} #x0000000000000020)))"),
        }
        expected.update(sret_window())
    elif field in ("hStrLt", "hStrLe", "hStrGt", "hStrGe"):
        token = {"hStrLt": 20, "hStrLe": 21,
                 "hStrGt": 22, "hStrGe": 23}[field]
        expected = {
            "checkpoint-op-token": (
                f"(= (ld4 {mem} {sp}) #x{token:016x})"),
            "left-str": f"(= {load_sp(120, 4)} #x0000000000000003)",
            "right-str": f"(= {load_sp(144, 4)} #x0000000000000003)",
            "strcmp-relation": (
                f"(= (sign3 {reg(10)}) "
                f"(lean_cstring_cmp3 {mem} {reg(19)} {reg(17)}))"),
        }
        expected.update(sret_window())
    elif field in ("hStrAddL", "hStrAddR"):
        expected = {}
        if field == "hStrAddL":
            expected["left-str"] = (
                f"(= {load_sp(120, 4)} #x0000000000000003)")
        else:
            expected.update({
                "right-str": f"(= {load_sp(144, 4)} #x0000000000000003)",
                "left-not-str": (
                    f"(not (= {load_sp(120, 4)} #x0000000000000003))"),
            })
    elif field == "hFn":
        target = reg(9)
        target_end = f"(bvadd {target} #x0000000000000018)"
        closure = reg(10)
        closure_end = f"(bvadd {closure} #x0000000000000010)"
        expected = {
            "inv-layout": f"(INV {state})",
            "fn-kind": f"(= {load_reg(8, 0)} #x000000000000000a)",
            "malloc-success": (
                f"(not (= {reg(10)} #x0000000000000000))"),
            "sret-stack-low": f"(bvule SL_lo {target})",
            "sret-stack-high": f"(bvule {target_end} SL_hi)",
            "sret-above-htif": f"(bvule #x000000008001ad10 {target})",
            "malloc-arena-low": f"(bvule A_lo {closure})",
            "malloc-no-wrap": f"(bvule {closure} {closure_end})",
            "malloc-arena-high": f"(bvule {closure_end} A_hi)",
            "malloc-htif-disjoint": (
                f"(or (bvule {closure_end} #x000000008001ad00) "
                f"(bvule #x000000008001ad10 {closure}))"),
        }
    else:
        raise KeyError(field)
    return {name: _one_term(term) for name, term in expected.items()}


def _localize_suffix_post(post, suffix, state_name):
    entry_target = "(select (rr s0) #x000000000000000a)"
    local_target = f"(select (rr {state_name}) #x0000000000000009)"
    post = (post or "").replace(entry_target, local_target)
    for old, new in suffix.get("post_replacements", {}).items():
        post = post.replace(old, new)
    return post


def nonarithmetic_suffix_audit(query, field, s0, checkpoints, machine_exit,
                               suffix, production_post):
    """Validate a non-arithmetic checkpoint suffix and targeted mutations."""
    pc = _NONARITHMETIC_SUFFIX_POINTS[field]
    checkpoint = checkpoints.get(pc)
    if checkpoint is None:
        return [("SUFFIX-CHECKPOINT", field,
                 f"trace has no same-frame checkpoint at {pc:#x}")], 0, 0
    state_name = suffix.get("state")
    if not isinstance(state_name, str):
        return [("SUFFIX-SHAPE", field,
                 "production suffix has no state name")], 0, 0
    try:
        actual = _assertion_bodies(suffix.get("pre", ""))
        expected = _nonarithmetic_suffix_expected_assertions(field, state_name)
    except (KeyError, ValueError) as exc:
        return [("SUFFIX-SHAPE", field, str(exc))], 0, 0
    findings = []
    missing = [name for name, term in expected.items() if term not in actual]
    extra = [term for term in actual if term not in expected.values()]
    if missing:
        findings.append(("SUFFIX-PREMISE-MISSING", field, ",".join(missing)))
    if extra:
        findings.append(("SUFFIX-PREMISE-EXTRA", field,
                         f"{len(extra)} assertion(s) outside the independent schema"))
    for name, term in expected.items():
        if term not in actual:
            continue
        try:
            if not _eval_suffix_term(query, s0, state_name, checkpoint, term):
                findings.append(("SUFFIX-TRACE-PREMISE", field,
                                 f"concrete checkpoint violates {name}"))
        except EvalError as exc:
            findings.append(("SUFFIX-PREMISE-EVAL", field, f"{name}: {exc}"))

    sp = checkpoint.regs.sel(2)
    x8 = checkpoint.regs.sel(8)
    mutations = {}
    for name in expected:
        if name in ("leaf-arm-kind", "fn-kind"):
            base = checkpoint.regs.sel(12) if name == "leaf-arm-kind" else x8
            mutations[name] = _with_mem_value(
                checkpoint, base, 4,
                _load_le(checkpoint.mem, base, 4) ^ 1)
        elif name == "sret-register":
            mutations[name] = _with_reg_value(
                checkpoint, 10, checkpoint.regs.sel(9) ^ 0x100)
        elif name == "checkpoint-op-token":
            if field in ("hStrLt", "hStrLe", "hStrGt", "hStrGe"):
                mutations[name] = _with_mem_value(
                    checkpoint, sp, 4, _load_le(checkpoint.mem, sp, 4) ^ 1)
            else:
                mutations[name] = _with_mem_value(
                    checkpoint, x8 + 8, 4,
                    _load_le(checkpoint.mem, x8 + 8, 4) ^ 1)
        elif name in ("operand-value", "right-value"):
            offset = 240 if field == "hAndTrue" else 144
            mutations[name] = _with_mem_value(checkpoint, sp + offset, 4, 6)
        elif name == "left-truthy":
            mutations[name] = _with_mem_value(checkpoint, sp + 120, 4, 0)
        elif name == "left-falsy":
            mutations[name] = _with_mem_value(checkpoint, sp + 120, 4, 3)
        elif name == "left-str":
            mutations[name] = _with_mem_value(checkpoint, sp + 120, 4, 2)
        elif name == "right-str":
            mutations[name] = _with_mem_value(checkpoint, sp + 144, 4, 2)
        elif name == "left-not-str":
            mutations[name] = _with_mem_value(checkpoint, sp + 120, 4, 3)
        elif name == "malloc-success":
            mutations[name] = _with_reg_value(checkpoint, 10, 0)
        elif name == "inv-layout":
            # Force the stack pointer below the minimum legal StackLayout
            # address.  The concrete INV witness cannot repair this.
            mutations[name] = _with_reg_value(checkpoint, 2, 0x1000)
        elif name == "sret-stack-low":
            mutations[name] = _with_reg_value(
                checkpoint, 9, checkpoint.regs.sel(2) - 0x2001)
        elif name == "sret-stack-high":
            mutations[name] = _with_reg_value(
                checkpoint, 9, checkpoint.regs.sel(2) + 0x2000)
        elif name == "malloc-arena-low":
            mutations[name] = _with_reg_value(checkpoint, 10, 0xFFFF)
        elif name == "malloc-no-wrap":
            mutations[name] = _with_reg_value(checkpoint, 10, _M64 - 7)
        elif name == "malloc-arena-high":
            original = checkpoint.regs.sel(10)
            arena_hi = max((original & ~0xFFF) + 0x2000,
                           original + 0x1000)
            mutations[name] = _with_reg_value(checkpoint, 10, arena_hi)
        elif name == "malloc-htif-disjoint":
            mutations[name] = _with_reg_value(checkpoint, 10, 0x8001AD00)
        elif name == "equal-left-value":
            mutations[name] = _with_mem_value(checkpoint, sp + 64, 4, 6)
        elif name == "equal-right-value":
            mutations[name] = _with_mem_value(checkpoint, sp + 32, 4, 6)
        elif name == "value-equal-relation":
            mutations[name] = _with_reg_value(checkpoint, 10, 2)
        elif name == "strcmp-relation":
            raw = checkpoint.regs.sel(10)
            mutations[name] = _with_reg_value(
                checkpoint, 10, 0 if _signed64(raw) < 0 else _M64)
        elif name == "sret-above-htif":
            mutations[name] = _with_reg_value(
                checkpoint, 9, 0x8001AD00)
        elif name == "sret-no-wrap":
            mutations[name] = _with_reg_value(checkpoint, 9, _M64 - 7)
        elif name == "sret-below-4g":
            mutations[name] = _with_reg_value(
                checkpoint, 9, 0x0000000100000000)

    killed = 0
    for name, mutant in mutations.items():
        term = expected[name]
        if term not in actual:
            continue
        try:
            if _eval_suffix_term(query, s0, state_name, mutant, term,
                                 layout_state=checkpoint):
                findings.append(("SUFFIX-MUTANT-SURVIVED", field, name))
            else:
                killed += 1
        except EvalError as exc:
            findings.append(("SUFFIX-MUTATION-EVAL", field, f"{name}: {exc}"))

    try:
        localized_post = _localize_suffix_post(
            production_post, suffix, state_name)
        post_forms = _assertion_bodies(localized_post)
    except ValueError as exc:
        findings.append(("SUFFIX-POST-SHAPE", field, str(exc)))
        return findings, killed, len(expected)
    if len(post_forms) != 1:
        findings.append(("SUFFIX-POST-SHAPE", field,
                         f"expected one negated result assertion, got {len(post_forms)}"))
        return findings, killed, len(expected)
    bad_post = post_forms[0]
    applies, expected_value = concrete_residual_projection(field, s0, checkpoints)
    if not applies:
        findings.append(("SUFFIX-ORACLE-SCOPE", field,
                         "concrete oracle rejects the selected suffix instance"))
        return findings, killed, len(expected)
    try:
        if _eval_suffix_term(
                query, s0, state_name, checkpoint, bad_post, machine_exit):
            findings.append(("SUFFIX-POST", field,
                             "production relation rejects the concrete machine result"))
        target = checkpoint.regs.sel(9)
        kind, payload = expected_value
        output_mutants = {
            "result-kind": _write_projected_value(
                machine_exit, target, kind ^ 1, payload),
            "result-payload": _write_projected_value(
                machine_exit, target, kind, payload ^ 1),
        }
        for name, mutant in output_mutants.items():
            if _eval_suffix_term(
                    query, s0, state_name, checkpoint, bad_post, mutant):
                killed += 1
            else:
                findings.append(("SUFFIX-MUTANT-SURVIVED", field, name))
    except EvalError as exc:
        findings.append(("SUFFIX-POST-EVAL", field, str(exc)))
    if field == "hFn":
        # This is deliberately an independent concrete check, not part of the
        # symbolic projection.  At 0x33d0 a3 is still malloc-clobbered; the
        # environment that the tail restores and writes is the spill at 0(sp).
        closure = checkpoint.regs.sel(10)
        fn_expr = checkpoint.regs.sel(8)
        env = _load_le(checkpoint.mem, checkpoint.regs.sel(2), 8)

        def layout_ok(state):
            return (_load_le(state.mem, closure, 8) == fn_expr
                    and _load_le(state.mem, closure + 8, 8) == env)

        if not layout_ok(machine_exit):
            findings.append(("SUFFIX-MACHINE-LAYOUT", field,
                             "concrete closure header differs from fn/env inputs"))
        for name, address, value in (
                ("closure-fn-expr", closure, fn_expr ^ 1),
                ("closure-env", closure + 8, env ^ 1)):
            mutant = _with_mem_value(machine_exit, address, 8, value)
            if layout_ok(mutant):
                findings.append(("SUFFIX-MUTANT-SURVIVED", field, name))
            else:
                killed += 1
    if field in ("hStrAddL", "hStrAddR"):
        values = checkpoints.get(0x8000351C)
        if values is None:
            findings.append(("SUFFIX-MACHINE-CONCAT", field,
                             "operand checkpoint is absent"))
        else:
            sp = values.regs.sel(2)
            left = _cat_display_semantics(values.mem, sp + 120)
            right = _cat_display_semantics(values.mem, sp + 144)
            result_ptr = checkpoint.regs.sel(8)
            actual = _cstring_bytes(machine_exit.mem, result_ptr)
            if left is None or right is None or actual != left + right:
                findings.append(("SUFFIX-MACHINE-CONCAT", field,
                                 "result CString differs from Lean catDisplay concatenation"))
            elif actual:
                mutant = _with_mem_value(machine_exit, result_ptr, 1, actual[0] ^ 1)
                if _cstring_bytes(mutant.mem, result_ptr) == left + right:
                    findings.append(("SUFFIX-MUTANT-SURVIVED", field,
                                     "concat-result-byte"))
                else:
                    killed += 1
    return findings, killed, len(expected)


def arithmetic_suffix_audit(query, field, s0, checkpoints, machine_exit, img,
                            suffix, production_post):
    """Validate one post-child arithmetic context and kill targeted mutants."""
    pc = 0x800035EC if field == "hNeg" else 0x8000351C
    checkpoint = checkpoints.get(pc)
    if checkpoint is None:
        return [("SUFFIX-CHECKPOINT", field,
                 f"trace has no same-frame checkpoint at {pc:#x}")], 0, 0
    state_name = suffix.get("state")
    if not isinstance(state_name, str):
        return [("SUFFIX-SHAPE", field, "production suffix has no state name")], 0, 0
    try:
        actual = _assertion_bodies(suffix.get("pre", ""))
        expected = _suffix_expected_assertions(field, state_name, img)
    except (KeyError, ValueError) as exc:
        return [("SUFFIX-SHAPE", field, str(exc))], 0, 0
    findings = []
    missing = [name for name, term in expected.items() if term not in actual]
    expected_terms = list(expected.values())
    extra = [term for term in actual if term not in expected_terms]
    if missing:
        findings.append(("SUFFIX-PREMISE-MISSING", field, ",".join(missing)))
    if extra:
        findings.append(("SUFFIX-PREMISE-EXTRA", field,
                         f"{len(extra)} assertion(s) outside the independent schema"))
    for name, term in expected.items():
        if term not in actual:
            continue
        try:
            if not _eval_suffix_term(query, s0, state_name, checkpoint, term):
                findings.append(("SUFFIX-TRACE-PREMISE", field,
                                 f"concrete checkpoint violates {name}"))
        except EvalError as exc:
            findings.append(("SUFFIX-PREMISE-EVAL", field, f"{name}: {exc}"))

    sp = checkpoint.regs.sel(2)
    x8 = checkpoint.regs.sel(8)
    mutations = {}
    if field == "hNeg":
        mutations = {
            "operand-kind": _with_mem_value(checkpoint, sp + 144, 4, 3),
            "checkpoint-op-token": _with_mem_value(checkpoint, x8 + 8, 4, 13),
        }
    else:
        token = _BINARY_TOKENS[field]
        slot = _binary_jump_slot(img, token)
        mutations = {
            "left-kind": _with_mem_value(checkpoint, sp + 120, 4, 3),
            "right-kind": _with_mem_value(checkpoint, sp + 144, 4, 3),
            "x19-left-payload": _with_reg_value(
                checkpoint, 19, checkpoint.regs.sel(19) ^ 1),
            "respilled-left-kind": _with_mem_value(checkpoint, sp, 8, 3),
            "checkpoint-op-token": _with_mem_value(
                checkpoint, x8 + 8, 4, token ^ 1),
            "jump-slot-word": _with_mem_value(
                checkpoint, slot, 4, img.word(slot) ^ 1),
        }
        if field in ("hIDiv", "hIMod"):
            mutations["nonzero-divisor"] = _with_mem_value(
                checkpoint, sp + 152, 8, 0)
        if field == "hIDiv":
            nonoverflow = _with_mem_value(checkpoint, sp + 128, 8, 1 << 63)
            nonoverflow = _with_mem_value(nonoverflow, sp + 152, 8, _M64)
            mutations["nonoverflow"] = nonoverflow
        if field == "hDivOv":
            left = _with_mem_value(checkpoint, sp + 128, 8, (1 << 63) ^ 1)
            left = _with_reg_value(left, 19, (1 << 63) ^ 1)
            mutations["min-dividend"] = left
            mutations["minus-one-divisor"] = _with_mem_value(
                checkpoint, sp + 152, 8, _M64 ^ 1)

    killed = 0
    for name, mutant in mutations.items():
        term = expected.get(name)
        if term is None or term not in actual:
            continue
        try:
            if _eval_suffix_term(query, s0, state_name, mutant, term):
                findings.append(("SUFFIX-MUTANT-SURVIVED", field, name))
            else:
                killed += 1
        except EvalError as exc:
            findings.append(("SUFFIX-MUTATION-EVAL", field, f"{name}: {exc}"))

    try:
        post_forms = _assertion_bodies(production_post or "")
    except ValueError as exc:
        findings.append(("SUFFIX-POST-SHAPE", field, str(exc)))
        return findings, killed, len(expected)
    if len(post_forms) != 1:
        findings.append(("SUFFIX-POST-SHAPE", field,
                         f"expected one negated result assertion, got {len(post_forms)}"))
        return findings, killed, len(expected)
    bad_post = post_forms[0]
    target = s0.regs.sel(10)
    applies, expected_value = concrete_residual_projection(field, s0, checkpoints)
    if not applies:
        findings.append(("SUFFIX-ORACLE-SCOPE", field,
                         "concrete oracle rejects the selected suffix instance"))
        return findings, killed, len(expected)
    try:
        if _eval_suffix_term(
                query, s0, state_name, checkpoint, bad_post, machine_exit):
            findings.append(("SUFFIX-POST", field,
                             "production relation rejects the concrete machine result"))
        kind, payload = expected_value
        output_mutants = {
            "result-kind": _write_projected_value(
                machine_exit, target, kind ^ 1, payload),
            "result-payload": _write_projected_value(
                machine_exit, target, kind, payload ^ 1),
        }
        for name, mutant in output_mutants.items():
            if _eval_suffix_term(query, s0, state_name, checkpoint, bad_post, mutant):
                killed += 1
            else:
                findings.append(("SUFFIX-MUTANT-SURVIVED", field, name))
    except EvalError as exc:
        findings.append(("SUFFIX-POST-EVAL", field, str(exc)))

    # Change each semantic payload while leaving the real output untouched.
    # If the result relation reads the right checkpoint slot, it must notice
    # whenever the independent semantic result changes.
    offsets = (152,) if field == "hNeg" else (128, 152)
    for offset in offsets:
        old = _load_le(checkpoint.mem, sp + offset, 8)
        other_offset = 128 if offset == 152 else 152
        other = _load_le(checkpoint.mem, sp + other_offset, 8)
        chosen = None
        candidates = (
            old ^ 1, other, (other - 1) & _M64, (other + 1) & _M64,
            0, 1, 2, 7, _M64, (1 << 63) - 1, 1 << 63,
        )
        for value in candidates:
            if value == old:
                continue
            mutant = _with_mem_value(checkpoint, sp + offset, 8, value)
            mutant_points = dict(checkpoints)
            mutant_points[pc] = mutant
            mutant_applies, mutant_value = concrete_residual_projection(
                field, s0, mutant_points)
            if mutant_applies and mutant_value != expected_value:
                chosen = mutant
                break
        if chosen is None:
            # hDivOv fixes both payloads in its premise and has a constant
            # result, so neither payload can vary inside this constructor.
            if field != "hDivOv":
                findings.append(("SUFFIX-PAYLOAD-MUTATION", field,
                                 f"could not vary checkpoint payload +{offset}"))
            continue
        try:
            if _eval_suffix_term(
                    query, s0, state_name, chosen, bad_post, machine_exit):
                killed += 1
            else:
                findings.append(("SUFFIX-MUTANT-SURVIVED", field,
                                 f"input-payload+{offset}"))
        except EvalError as exc:
            findings.append(("SUFFIX-POST-EVAL", field,
                             f"input-payload+{offset}: {exc}"))
    return findings, killed, len(expected)


def _premise_fixture(field, mutation=None):
    if field == "hArgsNil":
        if mutation not in (None, "empty-argc", "empty-index"):
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        regs = [0] * 33
        regs[15] = 1 if mutation == "empty-argc" else 0
        regs[16] = 1 if mutation == "empty-index" else 0
        state = St(MA({}, lambda _address: 0, set()), RA(tuple(regs)))
        return state, {"entry": state}

    if field == "hArgsCons":
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        regs = [0] * 33
        regs[15], regs[16] = 2, 1
        if mutation == "index-nonnegative":
            regs[16] = 1 << 63
        elif mutation == "index-below-argc":
            regs[16] = 2
        elif mutation == "argc-bound":
            regs[15] = 33
        state = St(MA({}, lambda _address: 0, set()), RA(tuple(regs)))
        points = {point: state for point in names.values()}
        if mutation in ("pre-child-eval", "post-child-eval"):
            points.pop(names[mutation])
        return state, points

    if field == "hSBlock":
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        entry_regs = [0] * 33
        entry_regs[10:14] = [0x1100, 0x2200, 0x3300, 0x4400]
        state = St(MA({}, lambda _address: 0, set()), RA(tuple(entry_regs)))
        arm_regs = list(entry_regs)
        arm_regs[8], arm_regs[9], arm_regs[19], arm_regs[18] = (
            entry_regs[11], entry_regs[10], entry_regs[12], entry_regs[13])
        bridge_regs = {
            "execBlockA-x8-stmt": 8,
            "execBlockA-x9-interp": 9,
            "execBlockA-x19-env": 19,
            "execBlockA-x18-ret": 18,
        }
        if mutation in bridge_regs:
            register = bridge_regs[mutation]
            arm_regs[register] ^= 1
        arm = St(state.mem, RA(tuple(arm_regs)))
        points = {point: arm for point in set(names.values())}
        if mutation is not None and mutation not in bridge_regs:
            points.pop(names[mutation])
        return state, points

    if field == "hSBlockIter":
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        node = 0x1000
        regs = [0] * 33
        regs[8], regs[16] = node, 1
        mem = MA({}, lambda _address: 0, set())
        mem = _store_le(mem, node + 16, 4, 2)
        if mutation == "index-nonnegative":
            regs[16] = 1 << 63
        elif mutation == "index-below-count":
            regs[16] = 2
        state = St(mem, RA(tuple(regs)))
        points = {point: state for point in names.values()}
        if mutation in ("pre-child-exec", "post-child-exec"):
            points.pop(names[mutation])
        return state, points

    if field in ("hSBlockNormal", "hSBlockAbrupt"):
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        regs = [0] * 33
        regs[10] = 0 if field == "hSBlockNormal" else 3
        if mutation is not None:
            regs[10] = 3 if field == "hSBlockNormal" else 0
        state = St(MA({}, lambda _address: 0, set()), RA(tuple(regs)))
        return state, {"entry": state}

    if field in _CALL_QUERIES:
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        mem = MA({}, lambda _address: 0, set())
        regs = [0] * 33
        regs[1], regs[2] = 0x1111, 0x80020000
        regs[8], regs[9] = 0x4000, 0x9000
        regs[10:14] = [0x9000, 0xA000, 0x4000, 0x5000]
        regs[18], regs[19], regs[23] = 0xA000, 0x5000, 0x7777
        if field == "hCallCallee" and mutation == "callee-stack-window":
            regs[2] = 0x8001AD00 + _EVAL_FRAME_BYTES
        mem = _store_le(mem, 0x4000, 4, 9)
        mem = _store_le(mem, 0x4008, 8, 0x4100)
        if field == "hCallCallee":
            state = St(mem, RA(tuple(regs)))
            arm_regs = list(regs)
            arm_regs[2] = (regs[2] - _EVAL_FRAME_BYTES) & _M64
            arm_regs[8], arm_regs[9] = regs[12], regs[10]
            arm_regs[18], arm_regs[19] = regs[11], regs[13]
            bridge_regs = {
                "execBlockA-x8-expr": 8,
                "execBlockA-x9-sret": 9,
                "execBlockA-x18-interp": 18,
                "execBlockA-x19-env": 19,
            }
            if mutation in bridge_regs:
                arm_regs[bridge_regs[mutation]] ^= 1
            arm = St(mem, RA(tuple(arm_regs)))
            points = {"0x800031b0": arm, "0x800031bc": arm,
                      "entry": state}
            if mutation == "pre-callee-eval":
                points.pop("0x800031bc")
            return state, points

        if mutation == "callee-return-stack-window":
            # Place the final s7 spill exactly on `tohost`.  Rebuild every
            # stack-relative fixture byte below from this mutated base so the
            # other premises remain true.
            regs[2] = (0x8001AD00 - 1016) & _M64
        sp = regs[2]
        mem = _store_le(mem, sp, 8, regs[19])
        mem = _store_le(mem, sp + 96, 4, 2)
        mem = _store_le(mem, sp + 104, 8, 7)
        mem = _store_le(mem, sp + 112, 8, 0xAB)
        if field == "hCallTooMany":
            mem = _store_le(mem, regs[8] + 4, 4, 7)
            mem = _store_le(mem, regs[8] + 24, 4, 33)
            if mutation == "call-node-kind":
                mem = _store_le(mem, regs[8], 4, 8)
            elif mutation == "argc-over-max":
                mem = _store_le(mem, regs[8] + 24, 4, 32)
            elif mutation == "argc-signed-nonnegative":
                mem = _store_le(mem, regs[8] + 24, 4, 0x80000021)
            elif mutation == "callee-value-shadow":
                mem = _store_le(mem, sp + 96, 4, 6)
            state = St(mem, RA(tuple(regs)))
            return state, {"entry": state}
        if field == "hCallCalleeToArgsNil":
            count = 0
        else:
            count = 2
        regs[15] = count
        mem = _store_le(mem, regs[8] + 24, 4, count)
        for index, (kind, payload, aux) in enumerate(
                ((0, 0xDEAD, 0xBEEF), (3, 0x6000, 0xCAFE))):
            address = sp + 240 + 24 * index
            mem = _store_le(mem, address, 4, kind)
            mem = _store_le(mem, address + 8, 8, payload)
            mem = _store_le(mem, address + 16, 8, aux)
        if mutation == "empty-argc":
            mem = _store_le(mem, regs[8] + 24, 4, 1)
        elif mutation == "nonempty-argc":
            mem = _store_le(mem, regs[8] + 24, 4, 0)
        elif mutation == "argc-bound":
            if field == "hCallArgsToCall":
                regs[15] = 33
            else:
                mem = _store_le(mem, regs[8] + 24, 4, 33)
        elif mutation == "callee-value-shadow":
            mem = _store_le(mem, sp + 96, 4, 6)
        elif mutation == "arg-vector-shadow":
            mem = _store_le(mem, sp + 240, 4, 6)
        elif mutation == "result-value-shadow":
            mem = _store_le(mem, regs[9], 4, 6)
        if field == "hCallCallToEpilogue" and mutation is None:
            mem = _store_le(mem, regs[9], 4, 2)
            mem = _store_le(mem, regs[9] + 8, 8, 99)
            mem = _store_le(mem, regs[9] + 16, 8, 0x55)
        state = St(mem, RA(tuple(regs)))
        return state, {"entry": state}

    if field in _WHILE_QUERIES:
        names = _premise_schema().get(field, {})
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        state, _exit = _while_fixture(field, premise_mutation=mutation)
        return state, {"entry": state}

    if field == "hCallAssertOk":
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        regs = [0] * 33
        regs[1], regs[8], regs[9], regs[18] = 0x800039F8, 0x1111, 0x2222, 0x3333
        regs[2], regs[10], regs[12], regs[13] = (
            0x80400000, 0x80020000, 1, 0x80021000)
        mem = MA({}, lambda _address: 0, set())
        mem = _store_le(mem, regs[13], 4, 1)
        mem = _store_le(mem, regs[13] + 8, 4, 1)
        if mutation == "assert-argc-one-or-two":
            regs[12] = 0
        elif mutation == "assert-first-value":
            # Non-canonical Boolean: rejected by ValueRepr, but still truthy.
            mem = _store_le(mem, regs[13] + 8, 4, 2)
        elif mutation == "assert-first-truthy":
            mem = _store_le(mem, regs[13] + 8, 4, 0)
        elif mutation == "sret-above-htif":
            regs[10] = 0x8001AD00
        elif mutation == "sret-no-wrap":
            regs[10] = _M64 - 7
        elif mutation == "sret-below-4g":
            regs[10] = 0x100000000
        elif mutation == "stack-frame-above-htif":
            regs[2] = 0x8001AD0F + 80
        state = St(mem, RA(tuple(regs)))
        return state, {"entry": state}

    if field in ("hCallPrint", "hCallPrintln"):
        if mutation not in (None, "argc-bound", "sret-above-htif",
                            "sret-no-wrap", "sret-below-4g",
                            "stack-frame-above-htif"):
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        regs = [0] * 33
        regs[10] = 0x80020000
        regs[12] = 0
        regs[2] = 0x80400000
        if mutation == "argc-bound":
            regs[12] = 33
        elif mutation == "sret-above-htif":
            regs[10] = 0x8001AD00
        elif mutation == "sret-no-wrap":
            regs[10] = _M64 - 7
        elif mutation == "sret-below-4g":
            regs[10] = 0x100000000
        elif mutation == "stack-frame-above-htif":
            frame = 48 if field == "hCallPrint" else 16
            regs[2] = 0x8001AD0F + frame
        state = St(MA({}, lambda _address: 0, set()), RA(tuple(regs)))
        return state, {"entry": state}

    if field in ("hVar", "hAssign"):
        names = _premise_schema()[field]
        if mutation is not None and mutation not in names:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        state = St(MA({}, lambda _address: 0, set()), RA(tuple([0] * 33)))
        points = {point: state for point in names.values()}
        if mutation is not None:
            points.pop(names[mutation])
        return state, points

    """Build a valid semantic premise fixture, optionally killing one premise.

    Mutations change the source-level discriminator or one represented Value,
    rather than rewriting SMT text.  Every mutation is chosen so all sibling
    premises remain true; this catches conjunctions which accidentally omit a
    premise as well as predicates which read a neighbouring frame slot.
    """
    if field in {"hSRet", "hSRetNull", "hSVarInit", "hSVarNull", "hSIfNone"}:
        stmt = 0x1000
        spec = {
            "hSRet": (6, 8, "return-expr", True),
            "hSRetNull": (6, 8, "return-null", False),
            "hSVarInit": (1, 16, "initializer", True),
            "hSVarNull": (1, 16, "no-initializer", False),
            "hSIfNone": (3, 24, "no-else", False),
        }[field]
        kind, offset, premise, present = spec
        if mutation is not None and mutation != premise:
            raise ValueError(f"no independent premise mutation for {field}/{mutation}")
        pointer = 0x5000 if present else 0
        if mutation == premise:
            pointer = 0 if present else 0x5000
        mem = MA({}, lambda _address: 0, set())
        mem = _store_le(mem, stmt, 4, kind)
        mem = _store_le(mem, stmt + offset, 8, pointer)
        regs = [0] * 33
        regs[11] = stmt
        state = St(mem, RA(tuple(regs)))
        return state, {"entry": state}

    expr, sp = 0x1000, 0x2000
    token = _BINARY_TOKENS.get(field, 12)
    left_kind = right_kind = operand_kind = 2
    left, right = (1 << 63, _M64) if field == "hDivOv" else (7, 3)

    if mutation == "binop-token" or mutation == "unop-token":
        token ^= 1
    elif mutation == "left-int":
        left_kind = 3
    elif mutation == "right-int":
        right_kind = 3
    elif mutation == "nonzero-divisor":
        right = 0
    elif mutation == "nonoverflow":
        left, right = 1 << 63, _M64
    elif mutation == "min-dividend":
        left = 7
    elif mutation == "minus-one-divisor":
        right = 3
    elif mutation == "operand-int":
        operand_kind = 3
    elif mutation is not None:
        raise ValueError(f"no independent premise mutation for {field}/{mutation}")

    mem = MA({}, lambda _address: 0, set())
    mem = _store_le(mem, expr + 8, 4, token)
    mem = _store_le(mem, sp + 120, 4, left_kind)
    mem = _store_le(mem, sp + 128, 8, left)
    mem = _store_le(mem, sp + 144, 4,
                    operand_kind if field == "hNeg" else right_kind)
    mem = _store_le(mem, sp + 152, 8, right)
    regs = [0] * 33
    regs[2], regs[12] = sp, expr
    state = St(mem, RA(tuple(regs)))
    points = {
        "entry": state,
        _BINARY_VALUE_POINT: state,
        _UNARY_VALUE_POINT: state,
    }
    return state, points


def concrete_residual_premises(field, s0, checkpoints):
    """Evaluate semantic premises without consulting their emitted formulas."""
    schema = _premise_schema().get(field)
    if schema is None:
        return None
    if field == "hArgsNil":
        return {
            "empty-argc": s0.regs.sel(15) == 0,
            "empty-index": s0.regs.sel(16) == 0,
        }
    if field == "hArgsCons":
        return {
            "index-nonnegative": _signed64(s0.regs.sel(16)) >= 0,
            "index-below-argc": (
                _signed64(s0.regs.sel(16)) < _signed64(s0.regs.sel(15))),
            "argc-bound": _signed64(s0.regs.sel(15)) <= 32,
            "pre-child-eval": "0x80003220" in checkpoints,
            "post-child-eval": "0x80003224" in checkpoints,
        }
    if field == "hSBlock":
        arm = checkpoints.get("0x8000418c")
        return {
            "execBlockA-x8-stmt": (
                arm is not None and arm.regs.sel(8) == s0.regs.sel(11)),
            "execBlockA-x9-interp": (
                arm is not None and arm.regs.sel(9) == s0.regs.sel(10)),
            "execBlockA-x19-env": (
                arm is not None and arm.regs.sel(19) == s0.regs.sel(12)),
            "execBlockA-x18-ret": (
                arm is not None and arm.regs.sel(18) == s0.regs.sel(13)),
            "pre-env-new": "0x80004190" in checkpoints,
            "post-env-new": "0x80004194" in checkpoints,
            "post-env-new-setup": "0x800041a0" in checkpoints,
        }
    if field == "hSBlockIter":
        node = s0.regs.sel(8)
        count = _signed64(_sext32(_load_le(s0.mem, node + 16, 4)))
        index = _signed64(s0.regs.sel(16))
        return {
            "index-nonnegative": index >= 0,
            "index-below-count": index < count,
            "pre-child-exec": "0x800041c4" in checkpoints,
            "post-child-exec": "0x800041c8" in checkpoints,
        }
    if field == "hSBlockNormal":
        return {"normal-child-status": s0.regs.sel(10) == 0}
    if field == "hSBlockAbrupt":
        return {"abrupt-child-status": s0.regs.sel(10) != 0}
    if field == "hCallCallee":
        arm = checkpoints.get("0x800031b0")
        return {
            "execBlockA-x8-expr": (
                arm is not None and arm.regs.sel(8) == s0.regs.sel(12)),
            "execBlockA-x9-sret": (
                arm is not None and arm.regs.sel(9) == s0.regs.sel(10)),
            "execBlockA-x18-interp": (
                arm is not None and arm.regs.sel(18) == s0.regs.sel(11)),
            "execBlockA-x19-env": (
                arm is not None and arm.regs.sel(19) == s0.regs.sel(13)),
            "callee-stack-window": (
                arm is not None and arm.regs.sel(2) >= 0x8001AD10),
            "pre-callee-eval": "0x800031bc" in checkpoints,
        }
    if field == "hCallTooMany":
        node = s0.regs.sel(8)
        argc = _load_le(s0.mem, node + 24, 4)
        return {
            "call-node-kind": _load_le(s0.mem, node, 4) == 9,
            "argc-over-max": argc > 32,
            "argc-signed-nonnegative": argc < (1 << 31),
            "callee-return-stack-window": (
                s0.regs.sel(2) + 1016 >= 0x8001AD10),
            "callee-value-shadow": (
                _value_shadow(s0.mem, s0.regs.sel(2) + 96) is not None),
        }
    if field in ("hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
        count = _load_le(s0.mem, s0.regs.sel(8) + 24, 4)
        shadow = _value_shadow(s0.mem, s0.regs.sel(2) + 96)
        spill = (s0.regs.sel(2) + 1016) & _M64
        if field.endswith("Nil"):
            return {
                "empty-argc": count == 0,
                "callee-return-stack-window": spill >= 0x8001AD10,
                "callee-value-shadow": shadow is not None,
            }
        return {
            "nonempty-argc": count > 0,
            "argc-bound": count <= 32,
            "callee-return-stack-window": spill >= 0x8001AD10,
            "callee-value-shadow": shadow is not None,
        }
    if field == "hCallArgsToCall":
        return {
            "argc-bound": s0.regs.sel(15) <= 32,
            "callee-value-shadow": (
                _value_shadow(s0.mem, s0.regs.sel(2) + 96) is not None),
            "arg-vector-shadow": _arg_vector_shadow(s0) is not None,
        }
    if field == "hCallCallToEpilogue":
        return {
            "result-value-shadow": (
                _value_shadow(s0.mem, s0.regs.sel(9)) is not None),
        }
    if field == "hCallAssertOk":
        args = s0.regs.sel(13)
        sret = s0.regs.sel(10)
        sret_end = (sret + 24) & _M64
        return {
            "assert-argc-one-or-two": s0.regs.sel(12) in (1, 2),
            "assert-first-value": _value_shadow(s0.mem, args) is not None,
            "assert-first-truthy": _truthy_at(s0.mem, args),
            "sret-above-htif": sret >= 0x8001AD10,
            "sret-no-wrap": sret <= sret_end,
            "sret-below-4g": sret_end <= 0x100000000,
            "stack-frame-above-htif": s0.regs.sel(2) - 80 >= 0x8001AD10,
        }
    if field in _WHILE_QUERIES:
        if field.endswith("CondTruthy"):
            sp = s0.regs.sel(2)
            kind = _load_le(s0.mem, sp + 80, 4)
            boolean = _load_le(s0.mem, sp + 88, 4)
            return {
                "condition-truthy": _truthy_value(s0, 80),
                "condition-bool-canonical": (
                    kind != 1 or boolean in (0, 1)),
                "stack-above-htif": s0.regs.sel(2) >= 0x8001AD10,
            }
        status = s0.regs.sel(10)
        if field == "hSWhileBreakRoute":
            return {"body-break-status": status == 1}
        if field in ("hSWhileRetBodyReturn", "hSWhileRetRoute"):
            return {"body-return-status": status == 3}
        if field in ("hSWhileLoopBodyReturn", "hSWhileLoopRoute"):
            return {"body-loop-status": status in (0, 2)}
        return None
    if field in ("hVar", "hAssign"):
        return {name: point in checkpoints
                for name, point in schema.items()}
    if field in ("hCallPrint", "hCallPrintln"):
        sret = s0.regs.sel(10)
        sret_end = (sret + 24) & _M64
        frame = 48 if field == "hCallPrint" else 16
        return {
            "argc-bound": s0.regs.sel(12) <= 32,
            "sret-above-htif": sret >= 0x8001AD10,
            "sret-no-wrap": sret <= sret_end,
            "sret-below-4g": sret_end <= 0x100000000,
            "stack-frame-above-htif": ((s0.regs.sel(2) - frame) & _M64)
                >= 0x8001AD10,
        }
    if field in {"hSRet", "hSRetNull", "hSVarInit", "hSVarNull", "hSIfNone"}:
        stmt = s0.regs.sel(11)
        name, offset, present = {
            "hSRet": ("return-expr", 8, True),
            "hSRetNull": ("return-null", 8, False),
            "hSVarInit": ("initializer", 16, True),
            "hSVarNull": ("no-initializer", 16, False),
            "hSIfNone": ("no-else", 24, False),
        }[field]
        pointer = _load_le(s0.mem, stmt + offset, 8)
        return {name: (pointer != 0) == present}
    expr = s0.regs.sel(12)
    actual_token = _load_le(s0.mem, expr + 8, 4)
    if field == "hNeg":
        operand = checkpoints.get(_UNARY_VALUE_POINT)
        if operand is None:
            return None
        return {
            "unop-token": actual_token == 12,
            "operand-int": _value_at(operand, 144)[0] == 2,
        }

    values = checkpoints.get(_BINARY_VALUE_POINT)
    if values is None:
        return None
    left_kind, left = _value_at(values, 120)
    right_kind, right = _value_at(values, 144)
    premises = {
        "binop-token": actual_token == _BINARY_TOKENS[field],
        "left-int": left_kind == 2,
        "right-int": right_kind == 2,
    }
    if field in ("hIDiv", "hIMod"):
        premises["nonzero-divisor"] = right != 0
    if field == "hIDiv":
        premises["nonoverflow"] = not (left == 1 << 63 and right == _M64)
    if field == "hDivOv":
        premises["min-dividend"] = left == 1 << 63
        premises["minus-one-divisor"] = right == _M64
    return premises


def _eval_manifest_predicate(query, row, state, entry_state=None):
    """Evaluate one emitted premise formula on a supplied semantic state."""
    def reject_summary(*_args):
        raise EvalError("premise unexpectedly invokes a machine summary")

    forms = parse_all(row["predicate"])
    if len(forms) != 1:
        raise EvalError("premise predicate is not one SMT term")
    ev = Ev(query, state if entry_state is None else entry_state, reject_summary)
    ev.env[row["state"]] = state
    return bool(ev.ev(forms[0]))


def _eval_manifest_term(ev, text):
    forms = parse_all(text)
    if len(forms) != 1:
        raise EvalError("manifest cell is not one SMT term")
    return ev.ev(forms[0])


def _selected_state_binding(ev, text):
    """Leaf binding selected by one concrete checkpoint-state expression."""
    forms = parse_all(text)
    if len(forms) != 1:
        raise EvalError("checkpoint state is not one SMT term")
    term = forms[0]
    while isinstance(term, list) and term and term[0] == "ite":
        term = term[2] if ev.ev(term[1]) else term[3]
    if not isinstance(term, str):
        raise EvalError("checkpoint state does not select a named binding")
    return term


def premise_mutation_audit(bmc_dir, by_query, only=None):
    """Kill every projected semantic premise in the production manifest."""
    schema = _premise_schema()
    findings = []
    killed = 0
    for query_name, expected in schema.items():
        residual = ("hSBlock" if query_name in _BLOCK_QUERIES
                    else _CALL_QUERY_FIELDS.get(
                        query_name, _WHILE_QUERY_FIELDS.get(
                            query_name, query_name)))
        if only is not None and residual not in only and query_name not in only:
            continue
        rows = by_query.get(query_name, [])
        actual = {row["name"]: row for row in rows}
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        if missing:
            findings.append(("PREMISE-MISSING", query_name, ",".join(missing)))
        if extra:
            findings.append(("PREMISE-EXTRA", query_name, ",".join(extra)))
        query_path = os.path.join(bmc_dir, "queries", query_name + ".smt2")
        if not os.path.exists(query_path):
            continue
        query = Query(open(query_path).read())
        for name, point in expected.items():
            row = actual.get(name)
            if row is None:
                continue
            if row["point"].lower() != point:
                findings.append(("PREMISE-POINT", query_name,
                                 f"{name}: expected {point}, got {row['point']}"))
            valid, valid_points = _premise_fixture(query_name)
            mutant, mutant_points = _premise_fixture(query_name, name)
            valid_oracle = concrete_residual_premises(
                query_name, valid, valid_points)
            mutant_oracle = concrete_residual_premises(
                query_name, mutant, mutant_points)
            if valid_oracle is None or not valid_oracle.get(name, False):
                findings.append(("PREMISE-ORACLE", query_name,
                                 f"{name}: valid fixture rejected by independent oracle"))
                continue
            if mutant_oracle is None or mutant_oracle.get(name, True):
                findings.append(("PREMISE-ORACLE", query_name,
                                 f"{name}: adversarial fixture accepted by independent oracle"))
                continue
            siblings = set(expected) - {name}
            if any(not mutant_oracle.get(sibling, False) for sibling in siblings):
                findings.append(("PREMISE-MUTATION", query_name,
                                 f"{name}: mutation also kills a sibling premise"))
                continue
            valid_state = valid_points.get(point)
            if valid_state is None:
                findings.append(("PREMISE-FIXTURE", query_name,
                                 f"{name}: valid fixture has no {point} checkpoint"))
                continue
            try:
                valid_value = _eval_manifest_predicate(
                    query, row, valid_state, valid)
            except (EvalError, ValueError) as exc:
                findings.append(("PREMISE-EVAL", query_name, f"{name}: {exc}"))
                continue
            if not valid_value:
                findings.append(("PREMISE-VALID-REJECTED", query_name,
                                 f"{name}: emitted predicate rejects valid fixture"))
                continue
            mutant_state = mutant_points.get(point)
            if mutant_state is None:
                # Checkpoint-existence premises (`hVar`/`hAssign`) deliberately
                # carry predicate `true`: their content is that the named,
                # guarded machine state exists.  Removing the point is the
                # independent mutation, so there is no state on which to
                # evaluate the predicate.  Require the production row to be
                # guarded; an unguarded `true` would not encode existence.
                if point == "entry" or row["guard"] == "true":
                    findings.append(("PREMISE-MUTANT-SURVIVED", query_name,
                                     f"{name}: missing checkpoint is not guarded"))
                else:
                    killed += 1
                continue
            try:
                mutant_value = _eval_manifest_predicate(
                    query, row, mutant_state, mutant)
            except (EvalError, ValueError) as exc:
                findings.append(("PREMISE-EVAL", query_name, f"{name}: {exc}"))
                continue
            if mutant_value:
                findings.append(("PREMISE-MUTANT-SURVIVED", query_name,
                                 f"{name}: emitted predicate accepts targeted mutation"))
            else:
                killed += 1
    return findings, killed


def _selfcheck_campaign_metadata():
    """Mutation checks for capability classes and byte provenance."""
    representatives = {
        "partial": {
            "query": "hInt", "field": "hInt",
            "capability": "partial-projection",
        },
        "machine": {
            "query": "hSIfTrue", "field": "hSIfTrue",
            "capability": "machine-only",
        },
        "indexed": {
            "query": "hCallTooMany", "field": "hCallTooMany",
            "capability": "indexed-error-projection",
        },
        "boundary": {
            "query": "hArgsNil", "field": "hArgsNil",
            "capability": "machine-boundary",
        },
    }
    assert not query_capability_findings(representatives)
    labels = sorted(QUERY_CAPABILITIES)
    for query, row in representatives.items():
        mutated = {name: dict(value)
                   for name, value in representatives.items()}
        wrong = labels[(labels.index(row["capability"]) + 1) % len(labels)]
        mutated[query]["capability"] = wrong
        findings = query_capability_findings(mutated)
        assert len(findings) == 1
        assert findings[0][:2] == ("CAPABILITY-CLASS", query)
    invalid = {name: dict(value) for name, value in representatives.items()}
    invalid["partial"]["capability"] = "semantic"
    assert query_capability_findings(invalid)[0][:2] == (
        "CAPABILITY-INVALID", "partial")

    with tempfile.TemporaryDirectory() as directory:
        assert campaign_provenance_findings(directory)[0][0] == \
            "PROVENANCE-MISSING"
        source_dir = os.path.join(directory, "src")
        os.makedirs(source_dir)
        required = campaign_provenance_files()
        for name, current in required.items():
            shutil.copyfile(current, os.path.join(source_dir, name))
        assert not campaign_provenance_findings(directory)
        for name, current in required.items():
            copied = os.path.join(source_dir, name)
            with open(copied, "ab") as fh:
                fh.write(b"\x00")
            findings = campaign_provenance_findings(directory)
            assert len(findings) == 1
            assert findings[0][0] == "PROVENANCE-STALE"
            assert name in findings[0][2]
            shutil.copyfile(current, copied)
        missing = os.path.join(source_dir, "ReflectSpan.lean")
        os.remove(missing)
        findings = campaign_provenance_findings(directory)
        assert len(findings) == 1
        assert findings[0][0] == "PROVENANCE-MISSING"
        assert "ReflectSpan.lean" in findings[0][2]


def _selfcheck_effect_manifest():
    """Fail-closed mutations for every effect column and query identity."""
    zero = "hCallArgsToCall"
    abi_route = "hSWhileLoopBodyReturn"
    dynamic = "hInt"
    caps = {
        zero: {"field": "hCall"},
        abi_route: {"field": "hSWhileLoop"},
        dynamic: {"field": "hInt"},
    }
    rows = [
        {
            "query": zero, "field": "hCall", "register_writes": "none",
            "direct_memory_writes": "none", "direct_write_rows": "0",
            "output": "preserved", "theorem": _ZERO_STEP_FRAME_THEOREM,
            "provenance": f"Lean:{_ZERO_STEP_FRAME_THEOREM}",
        },
        {
            "query": abi_route, "field": "hSWhileLoop",
            "register_writes": "preserves-abi",
            "direct_memory_writes": "none", "direct_write_rows": "0",
            "output": "preserved", "theorem": _ABI_ROUTE_FRAME_THEOREM,
            "provenance": f"Lean:{_ABI_ROUTE_FRAME_THEOREM}",
        },
        {
            "query": dynamic, "field": "hInt",
            "register_writes": "unsupported-dynamic",
            "direct_memory_writes": "guarded-write-log",
            "direct_write_rows": "1", "output": "unsupported-dynamic",
            "theorem": "-",
            "provenance": "Lean-emitted:Vsa.ReflectSpan.reflectBmcTopo",
        },
    ]

    with tempfile.TemporaryDirectory() as directory:
        os.makedirs(os.path.join(directory, "writes"))

        def write_effects(current):
            with open(os.path.join(directory, "query-effects.tsv"), "w") as fh:
                fh.write("\t".join(_EFFECT_COLUMNS) + "\n")
                for row in current:
                    fh.write("\t".join(row[column]
                                       for column in _EFFECT_COLUMNS) + "\n")

        with open(os.path.join(directory, "writes", zero + ".tsv"), "w") as fh:
            fh.write("guard\twidth\taddr\n")
        with open(os.path.join(directory, "writes", abi_route + ".tsv"), "w") as fh:
            fh.write("guard\twidth\taddr\n")
        with open(os.path.join(directory, "writes", dynamic + ".tsv"), "w") as fh:
            fh.write("guard\twidth\taddr\ntrue\t8\t#x0000000000001000\n")
        write_effects(rows)
        effects, findings = query_effect_manifest(directory, caps)
        assert set(effects) == set(caps) and not findings

        for row_index in (0, 1):
            for column in ("register_writes", "direct_memory_writes",
                           "direct_write_rows", "output", "theorem", "provenance"):
                mutated = [dict(row) for row in rows]
                mutated[row_index][column] = "wrong"
                write_effects(mutated)
                assert query_effect_manifest(directory, caps)[1]
        write_effects(rows[:-1])
        assert any(item[0] == "EFFECT-MISSING"
                   for item in query_effect_manifest(directory, caps)[1])
        extra = dict(rows[1], query="extra")
        write_effects(rows + [extra])
        assert any(item[0] == "EFFECT-EXTRA"
                   for item in query_effect_manifest(directory, caps)[1])
        write_effects(rows + [dict(rows[0])])
        assert any(item[0] == "EFFECT-DUPLICATE"
                   for item in query_effect_manifest(directory, caps)[1])

    # Certificate and mutation-audit failures must not suppress a concrete
    # consistency witness.  Actual encoder/machine/oracle failures must.
    assert not _consistency_pin_blocked([
        ("CERTIFICATE-VERDICT", zero, "missing solver verdict"),
        ("PROJECTION-ASSERT-MUTANT-SURVIVED", zero, "x1"),
    ])
    for kind in ("EXIT-REGS", "WRITE-VALUE", "PROJECTION-MACHINE",
                 "PROJECTION-ENCODER", "EFFECT-OUTPUT"):
        assert _consistency_pin_blocked([(kind, zero, "mutation")])


def cmd_selfcheck(_args):
    # Helper theorem availability is a separate exact artifact.  Missing,
    # duplicate, and misnamed theorem rows must fail closed and must not become
    # SMT/fuzzer coverage merely because semantic-helpers.tsv is present.
    _selfcheck_effect_manifest()
    with tempfile.TemporaryDirectory() as helper_dir:
        helper_rows = [
            {
                "target": f"0x{target:x}",
                "name": name,
                "mode": "ground-semantic-post",
                "relation": relation,
                "lean_basis": theorem,
            }
            for target, (name, relation, theorem) in
            SEMANTIC_HELPER_CALLEES.items()
        ]

        def write_helper_rows(path, columns, rows):
            with open(os.path.join(helper_dir, path), "w") as fh:
                fh.write("\t".join(columns) + "\n")
                for row in rows:
                    fh.write("\t".join(row[column] for column in columns) + "\n")

        write_helper_rows(
            "semantic-helpers.tsv",
            ("target", "name", "mode", "relation", "lean_basis"),
            helper_rows)
        certificate_rows = list(SEMANTIC_HELPER_CERTIFICATES.values())
        certificate_columns = ("target", "name", "relation", "theorem")
        certificate_path = "semantic-helper-certificates.tsv"
        write_helper_rows(certificate_path, certificate_columns, certificate_rows)
        targets, findings = semantic_helper_manifest(helper_dir)
        assert targets == set(SEMANTIC_HELPER_CALLEES) and not findings

        write_helper_rows(
            certificate_path, certificate_columns, certificate_rows[:-1])
        targets, findings = semantic_helper_manifest(helper_dir)
        assert not targets
        assert any(kind == "SEMANTIC-HELPER-CERTIFICATE-SET"
                   for kind, _where, _detail in findings)

        write_helper_rows(
            certificate_path, certificate_columns,
            certificate_rows + [certificate_rows[0]])
        targets, findings = semantic_helper_manifest(helper_dir)
        assert not targets
        assert any(kind == "SEMANTIC-HELPER-CERTIFICATE-DUPLICATE"
                   for kind, _where, _detail in findings)

        wrong_theorem = [dict(row) for row in certificate_rows]
        wrong_theorem[0]["theorem"] = "Vsa.Sim.not_the_manifest_theorem"
        write_helper_rows(
            certificate_path, certificate_columns, wrong_theorem)
        targets, findings = semantic_helper_manifest(helper_dir)
        assert not targets
        assert any(kind == "SEMANTIC-HELPER-CERTIFICATE-IDENTITY"
                   for kind, _where, _detail in findings)

    _selfcheck_campaign_metadata()

    # The >32-argument route is ordered after a successful callee return and
    # before any argument evaluation.  These fixtures are independent of the
    # production error-site and SMT formulas.
    max_args_route = [
        0x800031BC, 0x80003000, 0x800031C0, 0x800031C4,
        0x800031C8, 0x80003FB0, 0x80003FDC,
    ]
    max_args_depth = [7, 8, 7, 7, 7, 7, 7]
    assert _too_many_call_order(max_args_route, max_args_depth) is None
    assert _too_many_call_order(max_args_route[1:], max_args_depth[1:]) is not None
    assert _too_many_call_order(
        [pc for pc in max_args_route if pc != 0x800031C0],
        [depth for pc, depth in zip(max_args_route, max_args_depth)
         if pc != 0x800031C0]) is not None
    wrong_edge = list(max_args_route)
    wrong_edge[5] = 0x800031CC
    assert _too_many_call_order(wrong_edge, max_args_depth) is not None
    evaluated_arg = max_args_route[:5] + [0x80003220] + max_args_route[5:]
    evaluated_depth = max_args_depth[:5] + [7] + max_args_depth[5:]
    assert _too_many_call_order(evaluated_arg, evaluated_depth) is not None
    assert _call_argc_guard_problem(33, 33) is None
    assert _call_argc_guard_problem(32, 32) is not None
    assert _call_argc_guard_problem(33, 34) is not None
    negative_word = 0x80000021
    assert _call_argc_guard_problem(
        negative_word, negative_word | 0xFFFFFFFF00000000) is not None

    # Trace output observations are versioned by an `O` suffix.  Exercise both
    # a new no-memory row and a legacy row so adding output does not silently
    # reinterpret the old optional memory columns.
    regs = "\t".join(["0"] * 31)
    with tempfile.NamedTemporaryFile("w", delete=False) as tf:
        tf.write(f"T\t0\t1\t2\t{regs}\tO\t0\t1\t10\n")
        tf.write(f"T\t1\t2\t3\t{regs}\tO\t1\t1\t256\n")
        trace_path = tf.name
    try:
        parsed = Trace(trace_path, name="output-selfcheck")
        assert parsed.mk[0] == MK_NONE and parsed.out_known[0] == 1
        assert (parsed.out_before[0], parsed.out_after[0], parsed.out_byte[0]) \
            == (0, 1, 10)
        parsed_out, parsed_len, known = _trace_output_state(parsed, 1)
        assert known and parsed_len == 1 and parsed_out.sel(0) == 10
        assert not trace_output_findings(parsed)
        parsed.out_before[1] = 0
        assert trace_output_findings(parsed)[0][0] == "OUTPUT-CHAIN"
        parsed.out_before[1] = 1
        parsed.out_after[1] = 3
        assert trace_output_findings(parsed)[0][0] == "OUTPUT-DELTA"
        parsed.out_after[1] = 1
        parsed.out_byte[1] = 10
        assert trace_output_findings(parsed)[0][0] == "OUTPUT-SPURIOUS-BYTE"
        parsed.out_byte[1] = 256
        parsed.out_byte[0] = 256
        assert trace_output_findings(parsed)[0][0] == "OUTPUT-MISSING-BYTE"
        parsed.out_byte[0] = 10
    finally:
        os.remove(trace_path)

    # The concrete SMT evaluator must preserve and append the same byte stream.
    output_query = Query("""
      (define-fun state_exit () MState
        (mst (mm s0) (rr s0)
             (store (oo s0) (ol s0) #x0a)
             (bvadd (ol s0) #x0000000000000001)))
    """)
    empty_mem = MA({}, lambda _address: 0, set())
    output_s0 = St(empty_mem, RA(tuple([0] * 33)), OA({0: 65}), 1)
    output_exit = Ev(output_query, output_s0, lambda *_args: output_s0).ev(
        output_query.state_exit)
    output_machine = St(empty_mem, output_s0.regs, OA({0: 65, 1: 10}), 2)
    assert not _output_mismatches(output_exit, output_machine)
    assert _output_mismatches(
        St(empty_mem, output_s0.regs, output_s0.out, 1), output_machine)
    assert _output_mismatches(
        St(empty_mem, output_s0.regs, OA({0: 65, 1: 11}), 2), output_machine)
    assert _output_mismatches(
        St(empty_mem, output_s0.regs, OA({0: 10, 1: 65}), 2), output_machine)
    assert _output_mismatches(
        St(empty_mem, output_s0.regs, OA({0: 65, 1: 10, 2: 10}), 3),
        output_machine)

    # Phase 3 must not turn an unobserved memory byte into zero.  The symbolic
    # fallback stays unresolved, while an explicitly observed zero simplifies
    # to true.  This is the fail-closed distinction the step checker relies on.
    poison_probe = "\n".join([
        MEM_POISON_DECL,
        "(simplify (= (select MEM_POISON #x0000000000001000) #x00))",
        "(simplify (= (select (store MEM_POISON #x0000000000001000 #x00) "
        "#x0000000000001000) #x00))",
    ])
    poison_run = subprocess.run(
        [Z3, "-in", "-smt2"], input=poison_probe,
        capture_output=True, text=True, timeout=30)
    poison_lines = [line.strip() for line in poison_run.stdout.splitlines()
                    if line.strip()]
    assert len(poison_lines) == 2
    assert poison_lines[0] != "true" and poison_lines[1] == "true"

    # A small arithmetic result in a0 is not an allocator address.  The
    # concrete witness must still be a well-formed arena below the live stack;
    # a real malloc result, by contrast, is enclosed when it is disjoint.
    arithmetic_layout = _concrete_layout_witness(0x88000000, 2)
    assert (0x10000 <= arithmetic_layout["A_lo"]
            < arithmetic_layout["A_hi"]
            < arithmetic_layout["SL_lo"])
    closure_layout = _concrete_layout_witness(0x88000000, 0x8001C4F0)
    assert (closure_layout["A_lo"] <= 0x8001C4F0
            < closure_layout["A_hi"]
            < closure_layout["SL_lo"])

    # `lean_print_args_same` compares only the Value/display footprint.  An
    # unrelated byte change is accepted; a Value payload or referenced CString
    # change is rejected.  The long-string case guards against accidentally
    # turning the executable oracle into a finite-string abstraction.
    def output_put(mem, address, width, value):
        for byte in range(width):
            mem = mem.store(address + byte, (value >> (8 * byte)) & 0xFF)
        return mem

    args = 0x4000
    string = 0x5000
    base_mem = output_put(empty_mem, args, 4, 3)
    base_mem = output_put(base_mem, args + 8, 8, string)
    long_text = b"x" * 70000
    long_bytes = dict(base_mem.d)
    long_bytes.update((string + offset, byte)
                      for offset, byte in enumerate(long_text + b"\0"))
    base_mem = MA(long_bytes, base_mem.base, base_mem.unknown)
    unrelated_mem = base_mem.store(0x900000, 0xA5)
    changed_mem = base_mem.store(string + 69999, ord("y"))
    same_query = Query("""
      (define-fun state_exit () MState s0)
    """)
    same_ev = Ev(same_query, output_s0, lambda *_args: output_s0)
    same_ev.env.update({"left_mem": base_mem, "right_mem": unrelated_mem})
    same_term = parse_all(
        "(lean_print_args_same left_mem right_mem "
        "#x0000000000004000 #x0000000000000001)")[0]
    assert same_ev.ev(same_term)
    same_ev.env["right_mem"] = changed_mem
    assert not same_ev.ev(same_term)

    # The output-loop contract is independently executable.  Each preserved
    # register and the final index is necessary; changing any one kills it.
    loop_mem = output_put(empty_mem, args, 4, 2)
    loop_mem = output_put(loop_mem, args + 8, 8, 7)
    loop_mem = output_put(loop_mem, args + 24, 4, 2)
    loop_mem = output_put(loop_mem, args + 32, 8, 8)
    loop_regs = [0] * 33
    loop_regs[2] = 0x80400000
    loop_regs[8] = args
    loop_regs[9] = 0
    loop_regs[18] = 0x8001B000
    loop_regs[19] = 2
    loop_regs[20] = 0x803FFFF0
    loop_pre = St(loop_mem, RA(tuple(loop_regs)), OA({0: ord(">")}), 1)
    loop_post_regs = list(loop_regs)
    loop_post_regs[9] = 2
    loop_post_regs[8] += 24
    loop_post = St(loop_mem, RA(tuple(loop_post_regs)),
                   OA({0: ord(">"), 1: ord("7"), 2: ord(" "), 3: ord("8")}), 4)
    assert _output_loop_relation(loop_pre, loop_post)
    for register in _OUTPUT_LOOP_PRESERVED:
        assert not _output_loop_relation(
            loop_pre, _with_reg_value(
                loop_post, register, loop_post.regs.sel(register) ^ 1))
    assert not _output_loop_relation(
        loop_pre, _with_reg_value(loop_post, 9, 1))
    assert not _output_loop_relation(
        loop_pre, _with_reg_value(loop_post, 8, loop_regs[8]))
    assert not _output_loop_relation(
        loop_pre, St(loop_mem, loop_post.regs,
                     OA({0: ord(">"), 1: ord("7"), 2: ord(" "), 3: ord("9")}), 4))
    assert not _output_loop_relation(
        loop_pre, St(loop_mem, loop_post.regs, loop_post.out, 3))

    """Focused regressions for the independent semantic oracle."""
    def put(mem, address, width, value):
        for byte in range(width):
            mem = mem.store(address + byte, (value >> (8 * byte)) & 0xFF)
        return mem

    def state(expr_kind, token=0, left=7, right=9):
        expr, sp = 0x1000, 0x2000
        mem = MA({}, lambda _address: 0, set())
        mem = put(mem, expr, 4, expr_kind)
        mem = put(mem, expr + 8, 8, token)
        mem = put(mem, sp + 120, 4, 2)
        mem = put(mem, sp + 128, 8, left)
        mem = put(mem, sp + 144, 4, 2)
        mem = put(mem, sp + 152, 8, right)
        regs = [0] * 33
        regs[2], regs[10], regs[12] = sp, 0x3000, expr
        return St(mem, RA(tuple(regs)))

    proof = Image(PROOF_ELF)
    for tokens in (range(11, 16), range(20, 24)):
        slots = [_binary_jump_slot(proof, token) for token in tokens]
        assert all(right - left == 4
                   for left, right in zip(slots, slots[1:]))
    assert len(_suffix_expected_assertions("hIAdd", "checkpoint", proof)) == 12
    assert len(_suffix_expected_assertions("hIDiv", "checkpoint", proof)) == 14
    assert len(_suffix_expected_assertions("hDivOv", "checkpoint", proof)) == 14
    assert len(_suffix_expected_assertions("hNeg", "checkpoint", proof)) == 8
    expected_nonarith_facts = {
        "hInt": 2, "hStr": 2, "hBool": 2, "hNull": 2,
        "hNot": 2,
        "hAndFalse": 2, "hOrTrue": 2,
        "hAndTrue": 3, "hOrFalse": 3,
        "hEq": 6, "hNe": 6,
        "hStrAddL": 1, "hStrAddR": 2,
        "hStrLt": 7, "hStrLe": 7, "hStrGt": 7, "hStrGe": 7,
        "hFn": 10,
    }
    assert set(expected_nonarith_facts) == _NONARITHMETIC_SUFFIX_FIELDS
    for field, count in expected_nonarith_facts.items():
        assert len(_nonarithmetic_suffix_expected_assertions(
            field, "checkpoint")) == count

    add = state(6, 11)
    args_nil, _ = _premise_fixture("hArgsNil")
    assert concrete_residual_projection("hArgsNil", args_nil, {}) == \
        (True, (0, 0))
    assert concrete_residual_projection(
        "hArgsNil", _with_reg_value(args_nil, 15, 1), {}) == (False, (0, 0))
    args_sp, call_node, args_base, arg_node = 0x8000, 0x4000, 0x5000, 0x6000
    args_mem = MA({}, lambda _address: 0, set())
    args_mem = put(args_mem, call_node + 16, 8, args_base)
    args_mem = put(args_mem, args_base + 8, 8, arg_node)
    args_regs = [0] * 33
    args_regs[2], args_regs[8], args_regs[13] = args_sp, call_node, 0x7000
    args_regs[15], args_regs[16], args_regs[18] = 3, 1, 9
    args_entry = St(args_mem, RA(tuple(args_regs)))
    call_regs = list(args_regs)
    call_regs[10], call_regs[11] = args_sp + 64, 9
    call_regs[12], call_regs[13] = arg_node, 0x7000
    call_pre = St(args_mem, RA(tuple(call_regs)))
    child_mem = put(args_mem, args_sp + 64, 8, 0x11)
    child_mem = put(child_mem, args_sp + 72, 8, 0x22)
    child_mem = put(child_mem, args_sp + 80, 8, 0x33)
    child_ret = St(child_mem, RA(tuple(call_regs)))
    args_points = {0x80003220: call_pre, 0x80003224: child_ret}
    assert concrete_residual_projection(
        "hArgsCons", args_entry, args_points) == (
            True, (3, args_sp + 264, (0x11, 0x22, 0x33)))
    assert concrete_residual_projection(
        "hArgsCons", args_entry,
        {**args_points, 0x80003220: _with_reg_value(call_pre, 12, arg_node ^ 1)}) \
        == (False, None)
    assert concrete_residual_projection(
        "hArgsCons", args_entry, {0x80003220: call_pre}) == (False, None)
    assert concrete_residual_projection(
        "hIAdd", add, {0x8000351C: add}) == (True, (2, 16))
    sub = state(6, 12)
    assert concrete_residual_projection(
        "hISub", sub, {0x8000351C: sub}) == (True, (2, (-2) & _M64))
    div = state(6, 14, (-7) & _M64, 3)
    assert concrete_residual_projection(
        "hIDiv", div, {0x8000351C: div}) == (True, (2, (-2) & _M64))
    overflow = state(6, 14, 1 << 63, _M64)
    assert concrete_residual_projection(
        "hDivOv", overflow, {0x8000351C: overflow}) == (True, (2, 1 << 63))
    wrong_token = state(6, 12)
    assert concrete_residual_projection(
        "hIAdd", wrong_token, {0x8000351C: wrong_token}) == (False, None)

    # Post-helper suffix projections: the oracle reads the helper return from
    # the named checkpoint and independently enforces the source discriminator.
    eq = state(6, 19, 7, 7)
    eqret = _with_reg_value(eq, 10, 7)
    assert concrete_residual_projection(
        "hEq", eq, {0x8000351C: eq, 0x80003720: eqret}) == (True, (1, 1))
    assert concrete_residual_projection(
        "hEq", state(6, 17), {0x8000351C: eq, 0x80003720: eqret}) == (False, None)
    ne = state(6, 17, 7, 9)
    neret = _with_reg_value(ne, 10, 1)
    assert concrete_residual_projection(
        "hNe", ne, {0x8000351C: ne, 0x80003770: neret}) == (True, (1, 1))

    cmp_input = state(6, 20)
    cmp_input = _with_mem_value(cmp_input, cmp_input.regs.sel(2) + 120, 4, 3)
    cmp_input = _with_mem_value(cmp_input, cmp_input.regs.sel(2) + 144, 4, 3)
    cmp_input = _with_mem_value(cmp_input, cmp_input.regs.sel(2) + 128, 8, 0x5100)
    cmp_input = _with_mem_value(cmp_input, cmp_input.regs.sel(2) + 152, 8, 0x5200)
    cmp_input = _with_mem_value(cmp_input, 0x5100, 2, ord("a"))
    cmp_input = _with_mem_value(cmp_input, 0x5200, 2, ord("b"))
    cmpret = _with_reg_value(cmp_input, 11, _M64)
    cmpret = _with_reg_value(cmpret, 12, 20)
    assert concrete_residual_projection(
        "hStrLt", cmp_input,
        {0x8000351C: cmp_input, 0x800036C0: cmpret}) == (True, (1, 1))
    bad_cmp = _with_mem_value(cmp_input, cmp_input.regs.sel(2) + 144, 4, 2)
    assert concrete_residual_projection(
        "hStrLt", bad_cmp,
        {0x8000351C: bad_cmp, 0x800036C0: cmpret}) == (False, None)

    concat = state(6, 11)
    concat = _with_mem_value(concat, concat.regs.sel(2) + 120, 4, 3)
    concat_tail = _with_reg_value(concat, 8, 0x7000)
    assert concrete_residual_projection(
        "hStrAddL", concat,
        {0x8000351C: concat, 0x80003AC8: concat_tail}) == (True, (3, 0x7000))

    fn = state(10)
    fn_tail = _with_reg_value(fn, 8, fn.regs.sel(12))
    fn_tail = _with_reg_value(fn_tail, 10, 0x7100)
    assert concrete_residual_projection(
        "hFn", fn, {0x800033D0: fn_tail}) == (True, (4, 0x7100))
    assert concrete_residual_projection(
        "hFn", fn,
        {0x800033D0: _with_reg_value(fn_tail, 10, 0)}) == (False, None)
    brk = state(0)
    brk.regs = brk.regs.store(11, 0x4000)
    brk.mem = put(brk.mem, 0x4000, 4, 7)
    assert concrete_residual_projection("hSBrk", brk, {}) == (True, 1)
    assert concrete_residual_projection("hSCont", brk, {}) == (False, 2)
    cont = state(0)
    cont.regs = cont.regs.store(11, 0x4000)
    cont.mem = put(cont.mem, 0x4000, 4, 8)
    assert concrete_residual_projection("hSCont", cont, {}) == (True, 2)

    def statement(kind, offset=None, pointer=0):
        stmt = 0x4000
        st = state(0)
        st.regs = st.regs.store(11, stmt)
        st.mem = put(st.mem, stmt, 4, kind)
        if offset is not None:
            st.mem = put(st.mem, stmt + offset, 8, pointer)
        return st

    sexpr = statement(0)
    assert concrete_residual_projection("hSExpr", sexpr, {}) == (True, 0)
    sret = statement(6, 8, 0x5000)
    assert concrete_residual_projection("hSRet", sret, {}) == (True, 3)
    assert concrete_residual_projection("hSRetNull", sret, {}) == (False, 3)
    sretnull = statement(6, 8, 0)
    assert concrete_residual_projection("hSRetNull", sretnull, {}) == (True, 3)
    svar = statement(1, 16, 0x5000)
    assert concrete_residual_projection("hSVarInit", svar, {}) == (True, 0)
    assert concrete_residual_projection("hSVarNull", svar, {}) == (False, 0)
    svarnull = statement(1, 16, 0)
    assert concrete_residual_projection("hSVarNull", svarnull, {}) == (True, 0)
    sifnone = statement(3, 24, 0)
    assert concrete_residual_projection(
        "hSIfNone", sifnone, {0x800042D4: sifnone}) == (True, 0)
    assert concrete_residual_projection("hSIfNone", sifnone, {}) == (False, 0)
    swhile = statement(4)
    assert concrete_residual_projection(
        "hSWhileFalse", swhile, {0x80004090: swhile}) == (True, 0)
    assert concrete_residual_projection("hSWhileFalse", swhile, {}) == (False, 0)

    # Parse and execute every production while post on independently built
    # states.  Then kill every individual post conjunct with a concrete state
    # mutation.  This catches malformed formulas and wrong offsets even when no
    # external trace happens to exercise one status route.
    with tempfile.TemporaryDirectory() as while_dir:
        with open(os.path.join(while_dir, "residual-extensions.tsv"), "w") as fh:
            fh.write("query\tfield\tname\tpoint\tguard\tstate\tpredicate\n")
        _suffixes, while_posts, while_findings = \
            production_residual_suffixes(while_dir)
        assert not while_findings
        assert _WHILE_QUERIES <= set(while_posts)
        empty_query = Query(
            "(define-fun ld8 ((m Mem) (a BV64)) BV64 "
            "(concat (select m (bvadd a #x0000000000000007)) "
            "(select m (bvadd a #x0000000000000006)) "
            "(select m (bvadd a #x0000000000000005)) "
            "(select m (bvadd a #x0000000000000004)) "
            "(select m (bvadd a #x0000000000000003)) "
            "(select m (bvadd a #x0000000000000002)) "
            "(select m (bvadd a #x0000000000000001)) (select m a)))\n"
            "(define-fun state_exit () MState s0)")
        while_mutations = 0
        for query_name in sorted(_WHILE_QUERIES):
            s0_while, exit_while = _while_fixture(query_name)
            forms = parse_all(while_posts[query_name])
            assert len(forms) == 1 and forms[0][0] == "assert"
            ev_while = Ev(empty_query, s0_while, lambda *_args: None)
            ev_while.env["state_exit"] = exit_while
            assert not ev_while.ev(forms[0][1])
            for _name, mutant in _while_post_mutants(
                    query_name, s0_while, exit_while):
                ev_while.env["state_exit"] = mutant
                assert ev_while.ev(forms[0][1])
                while_mutations += 1
        assert while_mutations == 161
        loop_s0, _loop_exit = _while_fixture("hSWhileLoopRoute")
        loop_cont = _with_reg_value(loop_s0, 10, 2)
        assert concrete_residual_premises(
            "hSWhileLoopRoute", loop_cont, {"entry": loop_cont}) == {
                "body-loop-status": True}
        assert concrete_residual_projection(
            "hSWhileLoop", loop_cont, {}, "hSWhileLoopRoute")[0]

    # Exercise all four typed hCall stages from independently constructed
    # states.  The two zero-step stages must transport the concrete Value and
    # ArgVec shadows, not merely happen to have identical PCs.
    with tempfile.TemporaryDirectory() as call_dir:
        with open(os.path.join(call_dir, "residual-extensions.tsv"), "w") as fh:
            fh.write("query\tfield\tname\tpoint\tguard\tstate\tpredicate\n")
            fh.write("hCallCallee\thCall\texecBlockA-x8-expr\t"
                     "0x800031b0\ttrue\tcall_arm\ttrue\n")
            fh.write("hCallCallee\thCall\tpre-callee-eval\t"
                     "0x800031bc\ttrue\tcall_pre\ttrue\n")
        _suffixes, call_posts, call_findings = \
            production_residual_suffixes(call_dir)
        assert not call_findings
        assert _CALL_QUERIES <= set(call_posts)
        call_query = Query(
            "(define-fun ld4 ((m Mem) (a BV64)) BV64 "
            "((_ zero_extend 32) (concat "
            "(select m (bvadd a #x0000000000000003)) "
            "(select m (bvadd a #x0000000000000002)) "
            "(select m (bvadd a #x0000000000000001)) (select m a))))\n"
            "(define-fun ld4s ((m Mem) (a BV64)) BV64 "
            "((_ sign_extend 32) (concat "
            "(select m (bvadd a #x0000000000000003)) "
            "(select m (bvadd a #x0000000000000002)) "
            "(select m (bvadd a #x0000000000000001)) (select m a))))\n"
            "(define-fun ld8 ((m Mem) (a BV64)) BV64 "
            "(concat (select m (bvadd a #x0000000000000007)) "
            "(select m (bvadd a #x0000000000000006)) "
            "(select m (bvadd a #x0000000000000005)) "
            "(select m (bvadd a #x0000000000000004)) "
            "(select m (bvadd a #x0000000000000003)) "
            "(select m (bvadd a #x0000000000000002)) "
            "(select m (bvadd a #x0000000000000001)) (select m a)))\n"
            "(define-fun state_exit () MState s0)")
        call_mutations = 0
        for query_name in sorted(_CALL_QUERIES):
            s0_call, exit_call, call_points = _call_fixture(query_name)
            applies, _expected = concrete_residual_projection(
                _CALL_QUERY_FIELDS[query_name], s0_call, call_points,
                query_name)
            assert applies
            forms = parse_all(call_posts[query_name])
            assert len(forms) == 1 and forms[0][0] == "assert"
            ev_call = Ev(call_query, s0_call, lambda *_args: None)
            originals = {"state_exit": exit_call}
            targets = {"state_exit": "state_exit"}
            if query_name == "hCallCallee":
                originals.update({
                    "call_arm": call_points[0x800031B0],
                    "call_pre": call_points[0x800031BC],
                })
            ev_call.env.update(originals)
            if ev_call.ev(forms[0][1]):
                conjunction = forms[0][1][1]
                failed = [index for index, clause in enumerate(conjunction[1:])
                          if not ev_call.ev(clause)]
                raise AssertionError((query_name, failed))
            for _name, target, mutant in _call_post_mutants(
                    query_name, s0_call, exit_call, call_points):
                ev_call.env.update(originals)
                ev_call.env[targets[target]] = mutant
                assert ev_call.ev(forms[0][1]), (query_name, _name)
                call_mutations += 1
        assert call_mutations == 82

    # Native assert success: independently exercise the truthy/arity premises,
    # the null result, callee-saved register restoration, and unchanged output.
    assert_s0, _ = _premise_fixture("hCallAssertOk")
    assert_sret = assert_s0.regs.sel(10)
    assert_exit = _with_mem_value(assert_s0, assert_sret, 4, 0)
    assert_exit = _with_mem_value(assert_exit, assert_sret + 8, 8, 0)
    assert concrete_residual_projection(
        "hCallAssertOk", assert_s0, {}) == (
            True,
            (assert_sret, (0, 0), assert_s0.regs.sel(2),
             tuple(assert_s0.regs.sel(register)
                   for register in (1, 8, 9, 18)), True))
    false_assert, _ = _premise_fixture(
        "hCallAssertOk", "assert-first-truthy")
    assert concrete_residual_projection(
        "hCallAssertOk", false_assert, {}) == (False, None)
    with tempfile.TemporaryDirectory() as assert_dir:
        with open(os.path.join(assert_dir, "residual-extensions.tsv"), "w") as fh:
            fh.write("query\tfield\tname\tpoint\tguard\tstate\tpredicate\n")
        _suffixes, assert_posts, assert_findings = \
            production_residual_suffixes(assert_dir)
        assert not assert_findings
        form = parse_all(assert_posts["hCallAssertOk"])
        assert len(form) == 1 and form[0][0] == "assert"
        ev_assert = Ev(call_query, assert_s0, lambda *_args: None)
        ev_assert.env["state_exit"] = assert_exit
        assert not ev_assert.ev(form[0][1])
        assert_mutations = set()
        certificate_mutations = set()
        for name, mutant in _assert_ok_post_mutants(assert_s0, assert_exit):
            ev_assert.env["state_exit"] = mutant
            if name in _ASSERT_OK_CERTIFICATE_MUTATIONS:
                assert not ev_assert.ev(form[0][1]), name
                certificate_mutations.add(name)
            else:
                assert ev_assert.ev(form[0][1]), name
                assert_mutations.add(name)
        assert assert_mutations == _ASSERT_OK_MACHINE_MUTATIONS
        assert certificate_mutations == set(_ASSERT_OK_CERTIFICATE_MUTATIONS)
        with open(os.path.join(assert_dir, "query-capabilities.tsv"), "w") as fh:
            fh.write("query\tfield\tinstance\tcapability\n")
            fh.write("hCallAssertOk\thCallAssertOk\tsingle\tpartial-projection\n")
        with open(os.path.join(assert_dir, "lean-certificates.tsv"), "w") as fh:
            fh.write("residual\tpost\ttheorem\n")
            for (query, post), theorem in sorted(
                    _ASSERT_OK_LEAN_CERTIFICATES.items()):
                fh.write(f"{query}\t{post}\t{theorem}\n")
        certificate_verdict = os.path.join(assert_dir, "verdicts.tsv")
        certificate_posts = sorted(
            post for query, post in _ASSERT_OK_LEAN_CERTIFICATES
            if query == "hCallAssertOk")
        with open(certificate_verdict, "w") as fh:
            fh.write("query\t" + "\t".join(certificate_posts) + "\n")
            fh.write("hCallAssertOk\t" + "\t".join(
                "VALID[Lean:Vsa.Sim.nativeAssertInternalAbi_closed]"
                for _post in certificate_posts) + "\n")
        certificates, certificate_findings = phase3b_lean_certificates(
            assert_dir, [certificate_verdict])
        assert certificates == _ASSERT_OK_LEAN_CERTIFICATES
        assert not certificate_findings
        with open(certificate_verdict, "w") as fh:
            fh.write("query\t" + "\t".join(certificate_posts) + "\n")
            fh.write("hCallAssertOk\t" + "\t".join(
                "VALID-MACHINE" for _post in certificate_posts) + "\n")
        certificates, certificate_findings = phase3b_lean_certificates(
            assert_dir, [certificate_verdict])
        assert not certificates
        assert len(certificate_findings) == 4

    # hSBlock has separate allocation, child-boundary, and status-route queries.
    block = statement(2)
    block.regs = block.regs.store(10, 0x1110).store(12, 0x2220) \
        .store(13, 0x3330)
    arm_regs = block.regs.store(8, block.regs.sel(11)).store(9, 0x1110) \
        .store(19, 0x2220).store(18, 0x3330)
    arm = St(block.mem, arm_regs)
    env_pre = _with_reg_value(block, 10, 0x2220)
    inner = 0x8000
    env_mem = _store_le(block.mem, inner, 8, 0)
    env_mem = _store_le(env_mem, inner + 8, 8, 0)
    env_mem = _store_le(env_mem, inner + 16, 8, 0)
    env_mem = _store_le(env_mem, inner + 24, 8, 0x2220)
    env_ret = St(env_mem, env_pre.regs.store(10, inner))
    setup_regs = env_ret.regs.store(19, inner).store(16, 0) \
        .store(8, block.regs.sel(11)).store(9, 0x1110).store(18, 0x3330)
    setup = St(env_mem, setup_regs)
    applies, block_expected = concrete_residual_projection(
        "hSBlock", block,
        {0x8000418C: arm, 0x80004190: env_pre,
         0x80004194: env_ret, 0x800041A0: setup},
        "hSBlock")
    assert applies and block_expected[3] == (0, 0, 0, 0, 0x2220)
    bad_parent = _with_mem_value(env_ret, inner + 24, 8, 0x2221)
    assert concrete_residual_projection(
        "hSBlock", block,
        {0x8000418C: arm, 0x80004190: env_pre, 0x80004194: bad_parent,
         0x800041A0: setup}, "hSBlock") == (False, None)

    node, stmts, child = 0x4000, 0x5000, 0x6000
    iter_mem = _store_le(block.mem, node + 8, 8, stmts)
    iter_mem = _store_le(iter_mem, node + 16, 4, 1)
    iter_mem = _store_le(iter_mem, stmts, 8, child)
    iter_regs = [0] * 33
    iter_regs[2], iter_regs[8], iter_regs[9] = 0x9000, node, 0x1110
    iter_regs[18], iter_regs[19], iter_regs[16] = 0x3330, inner, 0
    iter_entry = St(iter_mem, RA(tuple(iter_regs)))
    child_pre_regs = list(iter_regs)
    child_pre_regs[10:14] = [0x1110, child, inner, 0x3330]
    child_pre = St(iter_mem, RA(tuple(child_pre_regs)))
    child_ret = _with_reg_value(child_pre, 10, 0)
    applies, iter_expected = concrete_residual_projection(
        "hSBlock", iter_entry,
        {0x800041C4: child_pre, 0x800041C8: child_ret}, "hSBlockIter")
    assert applies and iter_expected == (
        (0x9000, 0x1110, child, inner, 0x3330),)
    assert concrete_residual_projection(
        "hSBlock", child_ret, {}, "hSBlockNormal") == (
            True, (0, True, True))
    abrupt_ret = _with_reg_value(child_ret, 10, 3)
    assert concrete_residual_projection(
        "hSBlock", abrupt_ret, {}, "hSBlockAbrupt") == (
            True, (3, True, True))
    assert concrete_residual_projection(
        "hSBlock", abrupt_ret, {}, "hSBlockNormal") == (False, None)

    # A Boolean value writes and represents only four payload bytes.  Garbage
    # in the untouched upper word must not refute the semantic projection.
    bool_mem = put(cont.mem, 0x3000, 4, 1)
    bool_mem = put(bool_mem, 0x3008, 4, 1)
    bool_mem = put(bool_mem, 0x300C, 4, 0xDEADBEEF)
    bool_state = St(bool_mem, cont.regs)
    assert _projected_output_value(bool_state, 0x3000, 1) == (1, 1)
    assert _value_shadow(bool_mem, 0x3000) is not None
    bad_bool_mem = put(bool_mem, 0x3008, 4, 2)
    assert _value_shadow(bad_bool_mem, 0x3000) is None

    # Exact-helper detector mutations: a missing payload write, a wrong tag,
    # and a clobbered caller register must each be observable.  These test the
    # checker itself, independently of the emitted transformer.
    hmem = MA({}, lambda _address: 0, set())
    hregs = [0] * 32
    hregs[1], hregs[10], hregs[11], hregs[20] = 0x9004, 0x5000, 0x1234, 0xCAFE
    post, stores = _exact_helper_expected(0x8000280C, hregs, hmem)
    assert not _helper_observation_errors(0x8000280C, hregs, hmem, post, stores)
    assert _helper_observation_errors(0x8000280C, hregs, hmem, post, stores[:-1])
    wrong_tag = list(stores); wrong_tag[-1] = (wrong_tag[-1][0], 4, 3)
    assert _helper_observation_errors(0x8000280C, hregs, hmem, post, wrong_tag)
    clobbered = list(post); clobbered[20] ^= 1
    assert _helper_observation_errors(0x8000280C, hregs, hmem, clobbered, stores)

    # Compiler-runtime arithmetic contracts use a separately implemented RV64
    # oracle.  Cover zero, both units, signed truncation, remainder sign,
    # MIN/-1, and wrapping multiplication; then mutate each promised effect.
    arithmetic_edges = {
        0x80004640: [
            (0, 0, 0), (7, 1, 7), (7, _M64, (-7) & _M64),
            (1 << 63, 2, 0), (_M64, _M64, 1),
        ],
        0x800046A4: [
            (7, 0, _M64), (7, 1, 7), (7, _M64, (-7) & _M64),
            ((-7) & _M64, 3, (-2) & _M64),
            (7, (-3) & _M64, (-2) & _M64),
            ((-7) & _M64, (-3) & _M64, 2),
            (1 << 63, _M64, 1 << 63),
        ],
        0x80004728: [
            (7, 0, 7), (7, 1, 0), (7, _M64, 0),
            ((-7) & _M64, 3, _M64),
            (7, (-3) & _M64, 1),
            ((-7) & _M64, (-3) & _M64, _M64),
            (1 << 63, _M64, 0),
        ],
    }
    for target, cases in arithmetic_edges.items():
        for left, right, expected in cases:
            assert _arithmetic_helper_result(target, left, right) == expected
        aregs = [0x1000 + reg for reg in range(32)]
        aregs[10], aregs[11] = cases[-1][:2]
        apost = list(aregs)
        apost[10] = _arithmetic_helper_result(target, aregs[10], aregs[11])
        assert not _arithmetic_helper_observation_errors(
            target, aregs, apost, [])
        wrong_result = list(apost); wrong_result[10] ^= 1
        assert _arithmetic_helper_observation_errors(
            target, aregs, wrong_result, [])
        wrong_preserved = list(apost); wrong_preserved[20] ^= 1
        assert _arithmetic_helper_observation_errors(
            target, aregs, wrong_preserved, [])
        assert _arithmetic_helper_observation_errors(
            target, aregs, apost, [(0xDEAD, 8, 1)])

    # env_new's modular helper relation.  Allocator metadata may also change;
    # the independent oracle checks only the returned 32-byte Env and ABI.
    nmem = MA({}, lambda _address: 0, set())
    nregs = [0x3000 + reg for reg in range(32)]
    nregs[10] = 0x4440
    npost = list(nregs)
    npost[10] = 0x8000
    nstores = [
        (0x8000, 8, 0), (0x8008, 8, 0), (0x8010, 8, 0),
        (0x8018, 8, 0x4440),
    ]
    assert not _semantic_helper_observation_errors(
        0x800029FC, nregs, nmem, npost, nstores)
    bad_parent = list(nstores)
    bad_parent[-1] = (0x8018, 8, 0x4441)
    assert _semantic_helper_observation_errors(
        0x800029FC, nregs, nmem, npost, bad_parent)
    unaligned = list(npost); unaligned[10] = 0x8001
    assert _semantic_helper_observation_errors(
        0x800029FC, nregs, nmem, unaligned, nstores)

    # Decode helper inputs independently from memory.  Cover every Value kind
    # and kill wrong-result, wrong-sign, memory-effect, and frame mutants.
    smem = MA({}, lambda _address: None, set())
    def sm_put(addr, width, value):
        nonlocal smem
        smem = put(smem, addr, width, value)
    left, right = 0x7000, 0x7020
    sm_put(left, 4, 0); sm_put(right, 4, 0)
    assert _value_equal_semantics(smem, left, right) == 1
    for kind, width, offset in ((1, 4, 8), (2, 8, 8), (4, 8, 8), (5, 8, 16)):
        sm_put(left, 4, kind); sm_put(right, 4, kind)
        sm_put(left + offset, width, 0x1234); sm_put(right + offset, width, 0x1234)
        assert _value_equal_semantics(smem, left, right) == 1
        sm_put(right + offset, width, 0x1235)
        assert _value_equal_semantics(smem, left, right) == 0
    sa, sb = 0x7100, 0x7120
    sm_put(left, 4, 3); sm_put(right, 4, 3)
    sm_put(left + 8, 8, sa); sm_put(right + 8, 8, sb)
    for i, byte in enumerate(b"abc\0"):
        sm_put(sa + i, 1, byte); sm_put(sb + i, 1, byte)
    assert _value_equal_semantics(smem, left, right) == 1
    sm_put(sb + 2, 1, ord("d"))
    assert _value_equal_semantics(smem, left, right) == 0
    assert _strcmp_semantics(smem, sa, sb) == -1
    sregs = [0x2000 + reg for reg in range(32)]
    sregs[1], sregs[10], sregs[11] = 0x9004, left, right
    spost = list(sregs); spost[10] = 0
    assert not _semantic_helper_observation_errors(
        0x8000285C, sregs, smem, spost, [])
    wrong = list(spost); wrong[10] = 1
    assert _semantic_helper_observation_errors(
        0x8000285C, sregs, smem, wrong, [])
    sregs[10], sregs[11] = sa, sb
    spost = list(sregs); spost[10] = _M64
    assert not _semantic_helper_observation_errors(
        0x80006EA0, sregs, smem, spost, [])
    assert _semantic_helper_observation_errors(
        0x80006EA0, sregs, smem, spost, [(0xDEAD, 1, 0)])
    wrong = list(spost); wrong[10] = 1
    assert _semantic_helper_observation_errors(
        0x80006EA0, sregs, smem, wrong, [])
    wrong = list(spost); wrong[20] ^= 1
    assert _semantic_helper_observation_errors(
        0x80006EA0, sregs, smem, wrong, [])

    # Decode one represented Env independently and check the two mutable
    # environment helpers in both directions.  env_get copies slot -> out;
    # env_set copies input -> the first matching slot.
    env, names, values = 0x7300, 0x7340, 0x7380
    stored_name, query_name = 0x73C0, 0x73D0
    get_out, set_value = 0x7400, 0x7440
    sm_put(env, 4, 1)
    sm_put(env + 4, 4, 1)
    sm_put(env + 8, 8, names)
    sm_put(env + 16, 8, values)
    sm_put(env + 24, 8, 0)
    sm_put(names, 8, stored_name)
    for base in (stored_name, query_name):
        for i, byte in enumerate(b"x\0"):
            sm_put(base + i, 1, byte)
    old_words = (0x0000000000000002, 17, 0xA5A5)
    new_words = (0x0000000000000002, 23, 0x5A5A)
    for offset, word in zip((0, 8, 16), old_words):
        sm_put(values + offset, 8, word)
    for offset, word in zip((0, 8, 16), new_words):
        sm_put(set_value + offset, 8, word)
    assert _env_lookup_slot_semantics(smem, env, query_name) == values

    eregs = [0x3000 + reg for reg in range(32)]
    eregs[2] = 0x9000
    eregs[10], eregs[11], eregs[12] = env, query_name, get_out
    epost = list(eregs); epost[10] = 1
    get_stores = [(get_out + offset, 8, word)
                  for offset, word in zip((0, 8, 16), old_words)]
    assert not _semantic_helper_observation_errors(
        0x80002C10, eregs, smem, epost, get_stores)
    wrong_get = list(get_stores); wrong_get[1] = (get_out + 8, 8, 18)
    assert _semantic_helper_observation_errors(
        0x80002C10, eregs, smem, epost, wrong_get)

    eregs[12] = set_value
    epost = list(eregs); epost[10] = 1
    set_stores = [(values + offset, 8, word)
                  for offset, word in zip((0, 8, 16), new_words)]
    assert not _semantic_helper_observation_errors(
        0x80002CDC, eregs, smem, epost, set_stores)
    wrong_set = list(set_stores); wrong_set[2] = (values + 16, 8, 0)
    assert _semantic_helper_observation_errors(
        0x80002CDC, eregs, smem, epost, wrong_set)

    # Exercise the SMT evaluator's independent meaning for the two ground
    # environment symbols.  This is the path used when phase 3b evaluates the
    # production hVar/hAssign post, not the helper-observation path above.
    env_query = Query(
        "(declare-const s0 MState)\n"
        "(define-fun state_exit () MState s0)\n")
    env_state = St(smem, RA(tuple(eregs)))
    env_ev = Ev(env_query, env_state, lambda *_args: env_state)
    slot_term = parse_all(
        f"(lean_env_lookup_slot (mm s0) #x{env:016x} "
        f"#x{query_name:016x})")[0]
    found_term = parse_all(
        f"(lean_env_lookup_found (mm s0) #x{env:016x} "
        f"#x{query_name:016x})")[0]
    assert env_ev.ev(slot_term) == values
    assert env_ev.ev(found_term)

    # The per-residual oracle uses the caller states, not the helper manifest.
    expr = 0x7480
    sm_put(expr, 4, 4)
    sm_put(expr + 8, 8, query_name)
    vregs = [0] * 33
    vregs[2], vregs[12], vregs[13] = 0x7600, expr, env
    var_entry = St(smem, RA(tuple(vregs)))
    var_link_regs = list(vregs); var_link_regs[10] = 1
    var_out = (vregs[2] - _EVAL_FRAME_BYTES + 240) & _M64
    var_stores = [(var_out + offset, 8, word)
                  for offset, word in zip((0, 8, 16), old_words)]
    var_link_mem = _memory_after_stores(smem, var_stores)
    var_link = St(var_link_mem, RA(tuple(var_link_regs)))
    applies, var_expected = concrete_residual_projection(
        "hVar", var_entry, {0x80003444: var_link})
    assert applies and var_expected == (1, var_out, old_words)
    assert _value_words(var_link.mem, var_out) == old_words
    assert _value_words(
        _with_mem_value(var_link, var_out + 8, 8, old_words[1] ^ 1).mem,
        var_out) != old_words

    sm_put(expr, 4, 5)
    assign_entry = St(smem, RA(tuple(vregs)))
    call_regs = list(vregs)
    call_regs[10], call_regs[11], call_regs[12] = env, query_name, set_value
    call_pre = St(smem, RA(tuple(call_regs)))
    assign_link_regs = list(call_regs); assign_link_regs[10] = 1
    assign_link = St(
        _memory_after_stores(smem, set_stores), RA(tuple(assign_link_regs)))
    applies, assign_expected = concrete_residual_projection(
        "hAssign", assign_entry,
        {0x800034B0: call_pre, 0x800034B4: assign_link})
    assert applies and assign_expected == (1, values, new_words)
    assert _value_words(assign_link.mem, values) == new_words
    assert _value_words(
        _with_mem_value(assign_link, values + 16, 8, new_words[2] ^ 1).mem,
        values) != new_words

    displays = []
    sm_put(left, 4, 0); displays.append(_cat_display_semantics(smem, left))
    sm_put(left, 4, 1); sm_put(left + 8, 4, 1)
    displays.append(_cat_display_semantics(smem, left))
    sm_put(left, 4, 2); sm_put(left + 8, 8, (-17) & _M64)
    displays.append(_cat_display_semantics(smem, left))
    sm_put(left, 4, 3); sm_put(left + 8, 8, sa)
    displays.append(_cat_display_semantics(smem, left))
    closure, fn_expr, name = 0x7200, 0x7220, 0x7240
    sm_put(left, 4, 4); sm_put(left + 8, 8, closure)
    sm_put(closure, 8, fn_expr); sm_put(fn_expr + 8, 8, name)
    for i, byte in enumerate(b"f\0"):
        sm_put(name + i, 1, byte)
    displays.append(_cat_display_semantics(smem, left))
    sm_put(left, 4, 5)
    displays.append(_cat_display_semantics(smem, left))
    assert displays == [b"null", b"true", b"-17", b"abc", b"<fn f>",
                        b"<native fn>"]
    sm_put(left + 8, 8, name)
    assert _value_display_semantics(smem, left) == b"<native fn f>"

    # Both closure-print branches are semantic obligations.  A null name
    # pointer selects fwrite("<fn>"); a non-null pointer selects fprintf with
    # the represented CString.  Mutating either selector or name bytes must
    # change the independent oracle's result.
    sm_put(left, 4, 4); sm_put(left + 8, 8, closure)
    sm_put(fn_expr + 8, 8, name)
    assert _value_display_semantics(smem, left) == b"<fn f>"
    sm_put(name, 1, ord("g"))
    assert _value_display_semantics(smem, left) == b"<fn g>"
    sm_put(name, 1, ord("f")); sm_put(fn_expr + 8, 8, 0)
    assert _value_display_semantics(smem, left) == b"<fn>"
    sm_put(fn_expr + 8, 8, name + 0x1000)
    assert _value_display_semantics(smem, left) is None
    sm_put(fn_expr + 8, 8, name); sm_put(left + 8, 8, 0)
    assert _value_display_semantics(smem, left) is None
    sm_put(left + 8, 8, closure)

    # Summary observations are keyed by the memory bytes they read as well as
    # by registers.  Mutating one spilled byte while keeping every register the
    # same must prevent the old trace return from being selected.
    sig_addr = 0x6200
    sig = {sig_addr: 0x34}
    sig_regs = RA(tuple([0] * 33))
    good_mem = MA({sig_addr: 0x34}, lambda _address: None, set())
    bad_mem = MA({sig_addr: 0x35}, lambda _address: None, set())
    picker = Oracle.__new__(Oracle)
    candidate = [(10, 20, tuple(sig_regs.sel(r) for r in range(32)), sig)]
    assert picker._pick(candidate, St(good_mem, sig_regs), "callee_1", "b0", False) \
        == (10, 20, [], [], False)
    picked = picker._pick(
        candidate, St(bad_mem, sig_regs), "callee_1", "b0", False)
    assert picked[:2] == (10, 20) and picked[2] == [] \
        and picked[3] == [sig_addr]

    class OutputTrace:
        pass
    picker.tr = OutputTrace()
    picker.tr.n = 21
    picker.tr.out_known = [1] * 21
    picker.tr.out_before = [0] * 21
    picker.tr.out_after = [0] * 21
    picker.tr.out_byte = [256] * 21
    picker.tr.out_after[5] = 1
    picker.tr.out_byte[5] = 65
    for row in range(6, 21):
        picker.tr.out_before[row] = 1
        picker.tr.out_after[row] = 1
    matching_output = St(good_mem, sig_regs, OA({0: 65}), 1)
    assert picker._pick(candidate, matching_output, "callee_1", "b0", False) \
        == (10, 20, [], [], False)
    wrong_output = St(good_mem, sig_regs, OA({0: 66}), 1)
    assert picker._pick(candidate, wrong_output, "callee_1", "b0", False)[4]

    # Address-only footprint equality used to accept this mutation.  Equal
    # write locations with a changed final byte must now be reported.
    machine_mem = MA({sig_addr: 0xA5}, lambda _address: None, set())
    encoded_mem = MA({sig_addr: 0xA4}, lambda _address: None, set())
    machine_state = St(machine_mem, sig_regs)
    encoded_state = St(encoded_mem, sig_regs)
    assert _written_byte_mismatches(
        encoded_state, machine_state, {sig_addr}) == [(sig_addr, 0xA4, 0xA5)]

    # Each semantic premise gets a single-fault mutant.  The independent
    # oracle must reject exactly that premise and keep every sibling true.
    premise_mutations = 0
    for field, names in _premise_schema().items():
        valid, valid_points = _premise_fixture(field)
        valid_result = concrete_residual_premises(field, valid, valid_points)
        assert valid_result is not None and all(valid_result.values())
        for name in names:
            mutant, mutant_points = _premise_fixture(field, name)
            mutant_result = concrete_residual_premises(
                field, mutant, mutant_points)
            assert mutant_result is not None and not mutant_result[name]
            assert all(value for sibling, value in mutant_result.items()
                       if sibling != name), (field, name, mutant_result)
            premise_mutations += 1
    assert premise_mutations == sum(len(names) for names in _premise_schema().values())
    print("[selfcheck] independent residual, exact-helper, and semantic-helper oracles: ok "
          f"({premise_mutations} premise mutations; 8 output-loop mutations; "
          "4 closure-output mutations; 2 environment-helper mutations; "
          "2 environment-residual mutations; 82 hCall-family-post mutations; "
          "5 assert-success machine mutations; 4 exact Lean exclusions; "
          "161 while-post mutations)")


def residual_extensions(bmc_dir, only=None):
    """Load and structurally check the premises emitted into each query."""
    path = os.path.join(bmc_dir, "residual-extensions.tsv")
    if not os.path.exists(path):
        return {}, [("NO-EXTENSIONS", "campaign",
                     "residual-extensions.tsv is missing")], 0
    by_field = {}
    findings = []
    for row in read_tsv(path):
        query = row.get("query", row["field"])
        by_field.setdefault(query, []).append(row)
    for field, rows in by_field.items():
        query_path = os.path.join(bmc_dir, "queries", field + ".smt2")
        if not os.path.exists(query_path):
            findings.append(("EXT-NO-QUERY", field,
                             "extensions exist but the query is missing"))
            continue
        q = Query(open(query_path).read())
        for row in rows:
            try:
                predicate = parse_all(row["predicate"])
            except ValueError as exc:
                findings.append(("EXT-PARSE", field,
                                 f'{row["name"]}: {exc}'))
                continue
            if len(predicate) != 1 or predicate[0] not in q.plain:
                findings.append(("EXT-NOT-EMITTED", field,
                                 f'{row["name"]}: predicate absent from query'))
            guard = row["guard"]
            guard_term = parse_all(guard)[0] if guard != "true" else "true"
            if guard != "true" and guard_term not in q.plain:
                findings.append(("EXT-GUARD-MISSING", field,
                                 f'{row["name"]}: checkpoint guard {guard} absent'))
    for field, kind in (("hSBrk", 7), ("hSCont", 8)):
        rows = by_field.get(field, [])
        stmt_rows = [row for row in rows if row["name"] == "stmt-kind"]
        expected = ("(= (ld4 (mm s0) (bvadd (select (rr s0) "
                    "#x000000000000000b) #x0000000000000000)) "
                    f"#x{kind:016x})")
        if len(stmt_rows) != 1 or stmt_rows[0]["point"] != "entry" \
                or stmt_rows[0]["guard"] != "true" \
                or stmt_rows[0]["predicate"] != expected:
            findings.append(("STMT-PIN-WRONG", field,
                             f"expected exactly one entry x11 statement-kind {kind} pin"))
    mutation_findings, killed = premise_mutation_audit(
        bmc_dir, by_field, only=only)
    return by_field, findings + mutation_findings, killed


def residual_routes(bmc_dir, enc_dir):
    """Check every emitted arm-route pin against the independent arm table.

    In particular, hSBrk and hSCont have the same result ABI; a swapped route
    still executes and can satisfy the other field's post.  The selected guard,
    all sibling exclusions, arm address, and statement-kind index therefore
    have to agree independently, not merely occur somewhere in the query.
    """
    path = os.path.join(bmc_dir, "residual-routes.tsv")
    if not os.path.exists(path):
        return [("NO-ROUTES", "campaign", "residual-routes.tsv is missing")]
    arms = {row["field"]: row for row in
            read_tsv(os.path.join(enc_dir, "armdispatch.tsv"))}
    rows = {row["query"]: row for row in read_tsv(path)}
    findings = []
    for field, arm in arms.items():
        query_path = os.path.join(bmc_dir, "queries", field + ".smt2")
        if not os.path.exists(query_path) or arm["kind_reg"] == "-":
            continue
        row = rows.get(field)
        if row is None:
            findings.append(("ROUTE-MISSING", field,
                             "query has an arm dispatch but no route manifest row"))
            continue
        if row["field"] != field or row["arm"].lower() != arm["arm"].lower() \
                or row["site"].lower() != arm["dispatch"].lower():
            findings.append(("ROUTE-WRONG", field,
                             "route manifest disagrees with independent armdispatch.tsv"))
        q = Query(open(query_path).read())
        selected = parse_all(row["selected_guard"])[0]
        if selected not in q.plain:
            findings.append(("ROUTE-SELECT-MISSING", field,
                             f"selected guard {row['selected_guard']} is not asserted"))
        for guard in filter(None, row["excluded_guards"].split(",")):
            negated = ["not", parse_all(guard)[0]]
            if negated not in q.plain:
                findings.append(("ROUTE-EXCLUDE-MISSING", field,
                                 f"sibling guard {guard} is not excluded"))
        if field in ("hSBrk", "hSCont"):
            expected_kind = "7" if field == "hSBrk" else "8"
            if arm["kind_reg"] != "11" or arm["kind_idx"] != expected_kind:
                findings.append(("STMT-DISCRIMINATOR", field,
                                 f"expected x11 kind {expected_kind}, got "
                                 f"x{arm['kind_reg']} kind {arm['kind_idx']}"))
    return findings


EXACT_VALUE_CALLEES = {
    0x800027EC: "value_null",
    0x800027F8: "value_bool",
    0x8000280C: "value_int",
    0x8000281C: "value_str",
    0x8000282C: "value_truthy",
}

ARITH_FUNCTIONAL_CALLEES = {
    0x80004640: ("__muldi3", "bvmul(a0,a1)", {10, 11, 12, 13}),
    0x800046A4: ("__divdi3", "bvsdiv(a0,a1)", {1, 5, 10, 11, 12, 13}),
    0x80004728: ("__moddi3", "bvsrem(a0,a1)", {1, 5, 10, 11, 12, 13}),
}

SEMANTIC_HELPER_CALLEES = {
    0x800029FC: ("env_new", "empty 32-byte Env with parent link",
                 "Vsa.Sim.env_new_spec"),
    0x8000285C: ("value_equal", "Lean Value.equal",
                 "Vsa.Sim.value_equal_spec_full"),
    0x80006EA0: ("strcmp", "Lean string lexicographic sign",
                 "Vsa.Sim.strcmp_full_spec"),
    0x80002C10: ("env_get", "Lean Store.get? successful Value words",
                 "Vsa.Sim.env_get_found_uncond''"),
    0x80002CDC: ("env_set", "Lean Store.set? successful first binding update",
                 "Vsa.Sim.env_set_from_entry"),
}

# This is theorem-identity evidence only.  It does not establish that the SMT
# summary in `semantic-helpers.tsv` is equivalent to the theorem's relation.
SEMANTIC_HELPER_CERTIFICATES = {
    target: {
        "target": f"0x{target:x}",
        "name": name,
        "relation": relation,
        "theorem": theorem,
    }
    for target, (name, relation, theorem) in SEMANTIC_HELPER_CALLEES.items()
}

NATIVE_OUTPUT_CALLEES = {
    0x80002ED4: ("native_print", False),
    0x80002F7C: ("native_println", True),
}


def exact_callee_manifest(bmc_dir):
    """Validate the exact-inline contract inventory and return its targets."""
    path = os.path.join(bmc_dir, "exact-callees.tsv")
    if not os.path.exists(path):
        return set(), [("NO-EXACT-CALLEES", "campaign",
                        "exact-callees.tsv is missing")]
    rows = read_tsv(path)
    got = {int(row["target"], 16): row for row in rows}
    findings = []
    if set(got) != set(EXACT_VALUE_CALLEES):
        findings.append(("EXACT-CALLEE-SET", "campaign",
                         f"expected={sorted(EXACT_VALUE_CALLEES)} got={sorted(got)}"))
    for target, name in EXACT_VALUE_CALLEES.items():
        row = got.get(target)
        if row is None:
            continue
        if row["name"] != name or row["mode"] != "inline-exact" \
                or not row["lean_basis"].startswith("Vsa.Sim."):
            findings.append(("EXACT-CALLEE-BASIS", name,
                             "name, mode, or Lean proof dependency is missing"))
        sym = f"callee_{target}"
        for query in os.listdir(os.path.join(bmc_dir, "queries")):
            if query.endswith(".smt2") and sym in open(
                    os.path.join(bmc_dir, "queries", query)).read():
                findings.append(("EXACT-CALLEE-OPAQUE", query[:-5],
                                 f"{name} still occurs as {sym}"))
    return set(got), findings


def arithmetic_callee_manifest(bmc_dir):
    """Validate the independently tested ground functional-post inventory."""
    path = os.path.join(bmc_dir, "functional-callees.tsv")
    if not os.path.exists(path):
        return set(), [("NO-FUNCTIONAL-CALLEES", "campaign",
                        "functional-callees.tsv is missing")]
    rows = read_tsv(path)
    got = {int(row["target"], 16): row for row in rows}
    findings = []
    if set(got) != set(ARITH_FUNCTIONAL_CALLEES):
        findings.append(("FUNCTIONAL-CALLEE-SET", "campaign",
                         f"expected={sorted(ARITH_FUNCTIONAL_CALLEES)} "
                         f"got={sorted(got)}"))
    for target, (name, result, _clobbered) in ARITH_FUNCTIONAL_CALLEES.items():
        row = got.get(target)
        if row is None:
            continue
        if row.get("name") != name \
                or row.get("mode") != "ground-functional-post" \
                or row.get("result") != result \
                or row.get("memory") != "read-only":
            findings.append(("FUNCTIONAL-CALLEE-BASIS", name,
                             "name, mode, result, or memory effect is wrong"))
    return set(got), findings


def semantic_helper_certificate_manifest(bmc_dir):
    """Validate exact kernel-backed helper theorem identities.

    Passing this check proves only that a fresh Lean emitter named the expected
    theorem.  Summary/Lean relation agreement is checked independently.
    """
    path = os.path.join(bmc_dir, "semantic-helper-certificates.tsv")
    if not os.path.exists(path):
        return set(), [("NO-SEMANTIC-HELPER-CERTIFICATES", "campaign",
                        "semantic-helper-certificates.tsv is missing")]
    rows = read_tsv(path)
    findings = []
    got = {}
    for index, row in enumerate(rows, 2):
        if set(row) != {"target", "name", "relation", "theorem"}:
            findings.append(("SEMANTIC-HELPER-CERTIFICATE-SCHEMA", "campaign",
                             f"line {index}: expected target/name/relation/theorem"))
            continue
        try:
            target = int(row["target"], 16)
        except ValueError:
            findings.append(("SEMANTIC-HELPER-CERTIFICATE-TARGET", "campaign",
                             f"line {index}: invalid target {row['target']!r}"))
            continue
        if target in got:
            findings.append(("SEMANTIC-HELPER-CERTIFICATE-DUPLICATE",
                             row.get("name", "campaign"),
                             f"duplicate target {target:#x}"))
            continue
        got[target] = row
    if set(got) != set(SEMANTIC_HELPER_CERTIFICATES):
        findings.append(("SEMANTIC-HELPER-CERTIFICATE-SET", "campaign",
                         f"expected={sorted(SEMANTIC_HELPER_CERTIFICATES)} "
                         f"got={sorted(got)}"))
    for target, expected in SEMANTIC_HELPER_CERTIFICATES.items():
        row = got.get(target)
        if row is not None and row != expected:
            findings.append(("SEMANTIC-HELPER-CERTIFICATE-IDENTITY",
                             expected["name"],
                             "target, name, relation, or theorem is wrong"))
    return (set() if findings else set(got)), findings


def semantic_helper_manifest(bmc_dir):
    """Validate helper summaries and their separate theorem identities."""
    path = os.path.join(bmc_dir, "semantic-helpers.tsv")
    if not os.path.exists(path):
        return set(), [("NO-SEMANTIC-HELPERS", "campaign",
                        "semantic-helpers.tsv is missing")]
    rows = read_tsv(path)
    findings = []
    got = {}
    for row in rows:
        try:
            target = int(row["target"], 16)
        except (KeyError, ValueError):
            findings.append(("SEMANTIC-HELPER-TARGET", "campaign",
                             f"invalid target {row.get('target')!r}"))
            continue
        if target in got:
            findings.append(("SEMANTIC-HELPER-DUPLICATE",
                             row.get("name", "campaign"),
                             f"duplicate target {target:#x}"))
            continue
        got[target] = row
    if set(got) != set(SEMANTIC_HELPER_CALLEES):
        findings.append(("SEMANTIC-HELPER-SET", "campaign",
                         f"expected={sorted(SEMANTIC_HELPER_CALLEES)} "
                         f"got={sorted(got)}"))
    for target, (name, relation, lean_basis) in SEMANTIC_HELPER_CALLEES.items():
        row = got.get(target)
        if row is None:
            continue
        if row.get("name") != name or row.get("mode") != "ground-semantic-post" \
                or row.get("relation") != relation \
                or row.get("lean_basis") != lean_basis:
            findings.append(("SEMANTIC-HELPER-BASIS", name,
                             "name, mode, relation, or Lean theorem is wrong"))
    certified, certificate_findings = semantic_helper_certificate_manifest(bmc_dir)
    findings.extend(certificate_findings)
    # Both manifests must agree exactly before trace checks may use a helper.
    if certified and certified != set(got):
        findings.append(("SEMANTIC-HELPER-CERTIFICATE-SET", "campaign",
                         "summary and certificate target sets differ"))
    return (set() if findings else set(got)), findings


def _sext32(value):
    value &= 0xFFFFFFFF
    return value | (0xFFFFFFFF00000000 if value & 0x80000000 else 0)


def _exact_helper_expected(target, regs, mem):
    """Independent ABI/memory oracle for one value helper invocation."""
    out = list(regs)
    buf, payload = regs[10], regs[11]
    stores = []
    if target == 0x800027EC:              # value_null
        stores = [(buf, 4, 0), (buf + 8, 8, 0)]
    elif target == 0x800027F8:            # value_bool
        out[11] = int(payload != 0)
        out[15] = 1
        stores = [(buf + 8, 4, out[11]), (buf, 4, 1)]
    elif target == 0x8000280C:            # value_int
        out[15] = 2
        stores = [(buf + 8, 8, payload), (buf, 4, 2)]
    elif target == 0x8000281C:            # value_str
        out[15] = 3
        stores = [(buf + 8, 8, payload), (buf, 4, 3)]
    elif target == 0x8000282C:            # value_truthy
        kind = _sext32(_load_le(mem, buf, 4))
        out[15] = kind
        out[14] = 1 if kind == 1 else 2
        if kind == 1:
            out[10] = _sext32(_load_le(mem, buf + 8, 4))
        elif kind == 2:
            out[10] = int(_load_le(mem, buf + 8, 8) != 0)
        else:
            out[10] = int(kind != 0)
    else:
        raise ValueError(f"not an exact value helper: {target:#x}")
    return out, [(a & _M64, w, v & ((1 << (8 * w)) - 1))
                 for a, w, v in stores]


def _helper_observation_errors(target, pre_regs, mem, post_regs, stores):
    """Compare one observed return against the independent helper oracle."""
    want_regs, want_stores = _exact_helper_expected(target, pre_regs, mem)
    errors = []
    bad_regs = [r for r in range(1, 32)
                if (post_regs[r] & _M64) != (want_regs[r] & _M64)]
    if bad_regs:
        errors.append("registers " + ",".join(f"x{r}" for r in bad_regs[:8]))
    got_stores = [(a & _M64, w, v & ((1 << (8 * w)) - 1))
                  for a, w, v in stores]
    if got_stores != want_stores:
        errors.append(f"stores expected {want_stores}, got {got_stores}")
    return errors


def _try_load_le(mem, addr, width):
    bytes_ = []
    for i in range(width):
        address = (addr + i) & _M64
        byte = mem.sel(address)
        if address not in mem.d and address in mem.unknown:
            return None
        bytes_.append(byte)
    if any(byte is None for byte in bytes_):
        return None
    return sum(byte << (8 * i) for i, byte in enumerate(bytes_))


def _cstring_bytes(mem, ptr):
    """Decode an observed C string without inventing unknown bytes."""
    out = bytearray()
    for offset in range(_M64 + 1):
        address = (ptr + offset) & _M64
        byte = mem.sel(address)
        if address not in mem.d and address in mem.unknown:
            return None
        if byte is None:
            return None
        if byte == 0:
            return bytes(out)
        if not 0 <= byte <= 0xFF:
            return None
        out.append(byte)
    return None


def _value_words(mem, ptr):
    """Read the three complete machine words copied for one C Value."""
    words = tuple(_try_load_le(mem, ptr + offset, 8)
                  for offset in (0, 8, 16))
    return None if any(word is None for word in words) else words


def _env_lookup_slot_semantics(mem, env, name_ptr):
    """Independently decode the first matching slot in an Env parent chain.

    This follows the concrete 32-byte Env layout.  It does not consult the SMT
    symbols or the production summary clauses.  Cycles and implausibly large
    counts are rejected as malformed observations rather than guessed through.
    """
    name = _cstring_bytes(mem, name_ptr)
    if name is None:
        return None
    seen = set()
    while env != 0:
        if env in seen:
            return None
        seen.add(env)
        count = _try_load_le(mem, env, 4)
        capacity = _try_load_le(mem, env + 4, 4)
        names = _try_load_le(mem, env + 8, 8)
        values = _try_load_le(mem, env + 16, 8)
        parent = _try_load_le(mem, env + 24, 8)
        if None in (count, capacity, names, values, parent) \
                or count > capacity or count > 4096:
            return None
        for index in range(count):
            candidate_ptr = _try_load_le(mem, names + 8 * index, 8)
            if candidate_ptr is None:
                return None
            candidate = _cstring_bytes(mem, candidate_ptr)
            if candidate is None:
                return None
            if candidate == name:
                return (values + 24 * index) & _M64
        env = parent
    return 0


def _memory_after_stores(mem, stores):
    """Replay an observed ordered store log into independent memory."""
    post = mem
    for address, width, value in stores:
        post = _store_le(post, address & _M64, width, value)
    return post


_OUTPUT_LOOP_PRESERVED = (2, 18, 19, 20)


def _output_loop_relation(pre, post):
    """Independent concrete oracle for native_print's loop summary."""
    index = pre.regs.sel(9)
    argc = pre.regs.sel(19)
    if index > argc or argc > 32:
        return False
    rendered = [
        _value_display_semantics(pre.mem, pre.regs.sel(8) + 24 * offset)
        for offset in range(argc - index)
    ]
    if any(value is None for value in rendered):
        return False
    expected = ((b" " if index > 0 and index < argc else b"")
                + b" ".join(rendered))
    expected_out = pre.out
    for offset, byte in enumerate(expected):
        expected_out = expected_out.store(pre.out_len + offset, byte)
    return (
        all(post.regs.sel(register) == pre.regs.sel(register)
            for register in _OUTPUT_LOOP_PRESERVED)
        and post.regs.sel(9) == argc
        and post.regs.sel(8) == (
            pre.regs.sel(8) + (24 * (argc - index - 1)
                               if index < argc else 0)) & _M64
        and post.out_len == (pre.out_len + len(expected)) & _M64
        and post.out == expected_out
    )


def _value_equal_semantics(mem, left_ptr, right_ptr):
    """Independent executable reading of While.Value.equal on two C Values."""
    left_kind = _try_load_le(mem, left_ptr, 4)
    right_kind = _try_load_le(mem, right_ptr, 4)
    if left_kind not in range(6) or right_kind not in range(6):
        return None
    if left_kind != right_kind:
        return 0
    if left_kind == 0:
        return 1
    if left_kind == 1:
        left = _try_load_le(mem, left_ptr + 8, 4)
        right = _try_load_le(mem, right_ptr + 8, 4)
    elif left_kind in (2, 4):
        left = _try_load_le(mem, left_ptr + 8, 8)
        right = _try_load_le(mem, right_ptr + 8, 8)
    elif left_kind == 3:
        left_addr = _try_load_le(mem, left_ptr + 8, 8)
        right_addr = _try_load_le(mem, right_ptr + 8, 8)
        if left_addr is None or right_addr is None:
            return None
        left = _cstring_bytes(mem, left_addr)
        right = _cstring_bytes(mem, right_addr)
    else:
        # VAL_NATIVE equality compares the function pointer, not its name.
        left = _try_load_le(mem, left_ptr + 16, 8)
        right = _try_load_le(mem, right_ptr + 16, 8)
    return None if left is None or right is None else int(left == right)


def _strcmp_semantics(mem, left_ptr, right_ptr):
    left = _cstring_bytes(mem, left_ptr)
    right = _cstring_bytes(mem, right_ptr)
    if left is None or right is None:
        return None
    return (left > right) - (left < right)


def _cat_display_semantics(mem, value_ptr):
    """Decode the C representation of Lean Value.catDisplay."""
    kind = _try_load_le(mem, value_ptr, 4)
    if kind == 0:
        return b"null"
    if kind == 1:
        value = _try_load_le(mem, value_ptr + 8, 4)
        return None if value is None else (b"true" if value else b"false")
    if kind == 2:
        value = _try_load_le(mem, value_ptr + 8, 8)
        return None if value is None else str(_signed64(value)).encode("ascii")
    if kind == 3:
        ptr = _try_load_le(mem, value_ptr + 8, 8)
        return None if ptr is None else _cstring_bytes(mem, ptr)
    if kind == 4:
        closure = _try_load_le(mem, value_ptr + 8, 8)
        if closure is None:
            return None
        fn_expr = _try_load_le(mem, closure, 8)
        if fn_expr is None:
            return None
        name_ptr = _try_load_le(mem, fn_expr + 8, 8)
        if name_ptr is None:
            return None
        if name_ptr == 0:
            return b"<fn>"
        name = _cstring_bytes(mem, name_ptr)
        return None if name is None else b"<fn " + name + b">"
    if kind == 5:
        return b"<native fn>"
    return None


def _value_display_semantics(mem, value_ptr):
    """Decode the C representation of Lean Value.display."""
    kind = _try_load_le(mem, value_ptr, 4)
    if kind != 5:
        return _cat_display_semantics(mem, value_ptr)
    name_ptr = _try_load_le(mem, value_ptr + 8, 8)
    if name_ptr is None:
        return None
    name = _cstring_bytes(mem, name_ptr)
    return None if name is None else b"<native fn " + name + b">"


def _trace_output_segment(tr, lo, hi):
    out = bytearray()
    for row in range(lo, hi):
        if not tr.out_known[row]:
            return None
        before, after, byte = (tr.out_before[row], tr.out_after[row],
                               tr.out_byte[row])
        if after == before:
            if byte != 256:
                return None
        elif after == before + 1 and byte <= 0xFF:
            out.append(byte)
        else:
            return None
    return bytes(out)


def _semantic_helper_observation_errors(target, pre_regs, mem, post_regs, stores):
    """Check a helper result against an independent Lean-level relation."""
    errors = []
    if target == 0x800029FC:
        post_mem = _memory_after_stores(mem, stores)
        inner = post_regs[10] & _M64
        parent = pre_regs[10] & _M64
        if inner == 0:
            errors.append("returned null on the successful path")
        elif inner & 7:
            errors.append(f"returned unaligned Env {inner:#x}")
        else:
            fields = (
                _try_load_le(post_mem, inner, 4),
                _try_load_le(post_mem, inner + 4, 4),
                _try_load_le(post_mem, inner + 8, 8),
                _try_load_le(post_mem, inner + 16, 8),
                _try_load_le(post_mem, inner + 24, 8),
            )
            expected = (0, 0, 0, 0, parent)
            if fields != expected:
                errors.append(f"Env fields expected {expected}, got {fields}")
        # malloc may update allocator metadata, so only the returned Env bytes
        # are constrained.  env_new otherwise follows the ordinary RV64 ABI.
        clobbered = {1, 5, 6, 7, *range(10, 18), 28, 29, 30, 31}
    elif target == 0x8000285C:
        expected = _value_equal_semantics(mem, pre_regs[10], pre_regs[11])
        if expected is None:
            errors.append("input Value or string bytes are unobserved")
        elif (post_regs[10] & _M64) != expected:
            errors.append(f"a0 expected {expected}, got {post_regs[10] & _M64}")
        # The string arm owns a 16-byte frame and spills ra at entry-sp+8.
        # Other arms are leaf paths.  Reject any semantic-memory write while
        # allowing that real frame spill.
        frame_lo, frame_hi = ((pre_regs[2] - 16) & _M64, pre_regs[2] & _M64)
        bad_stores = [(address, width) for address, width, _value in stores
                      if not (frame_lo <= address and address + width <= frame_hi)]
        if bad_stores:
            errors.append(f"writes outside helper frame: {bad_stores[:3]}")
        clobbered = {1, 2, 5, 6, 7, 10, 11, 12, 13, 14, 15}
    elif target == 0x80006EA0:
        expected = _strcmp_semantics(mem, pre_regs[10], pre_regs[11])
        actual = (_signed64(post_regs[10]) > 0) - (_signed64(post_regs[10]) < 0)
        if expected is None:
            errors.append("input string bytes are unobserved")
        elif actual != expected:
            errors.append(f"sign(a0) expected {expected}, got {actual}")
        if stores:
            errors.append(f"expected read-only memory, got {len(stores)} stores")
        clobbered = {5, 6, 7, 10, 11, 12, 13, 14, 15}
    elif target in (0x80002C10, 0x80002CDC):
        slot = _env_lookup_slot_semantics(mem, pre_regs[10], pre_regs[11])
        if slot is None:
            errors.append("environment chain or binding bytes are unobserved")
        else:
            expected_found = int(slot != 0)
            if (post_regs[10] & _M64) != expected_found:
                errors.append(
                    f"a0 expected {expected_found}, got {post_regs[10] & _M64}")
            if expected_found:
                post_mem = _memory_after_stores(mem, stores)
                if target == 0x80002C10:
                    source, destination = slot, pre_regs[12]
                else:
                    source, destination = pre_regs[12], slot
                expected_words = _value_words(mem, source)
                actual_words = _value_words(post_mem, destination)
                if expected_words is None:
                    errors.append("source Value words are unobserved")
                elif actual_words != expected_words:
                    errors.append(
                        f"Value words expected {expected_words}, got {actual_words}")
        # Ordinary RV64 ABI calls.  The helper bodies may use every
        # caller-saved register and their own stack frames.
        clobbered = {1, 5, 6, 7, *range(10, 18), 28, 29, 30, 31}
    else:
        raise ValueError(f"not a semantic helper: {target:#x}")
    bad_regs = [reg for reg in range(1, 32) if reg not in clobbered
                and (post_regs[reg] & _M64) != (pre_regs[reg] & _M64)]
    if bad_regs:
        errors.append("preserved registers " +
                      ",".join(f"x{reg}" for reg in bad_regs[:8]))
    return errors


def _signed64(value):
    value &= _M64
    return value - (1 << 64) if value & (1 << 63) else value


def _rv64_sdiv(left, right):
    """RISC-V signed division: truncation toward zero plus defined edge cases."""
    left, right = _signed64(left), _signed64(right)
    if right == 0:
        return _M64
    if left == -(1 << 63) and right == -1:
        return 1 << 63
    magnitude = abs(left) // abs(right)
    quotient = -magnitude if (left < 0) != (right < 0) else magnitude
    return quotient & _M64


def _rv64_srem(left, right):
    """RISC-V signed remainder, whose sign follows the dividend."""
    signed_left, signed_right = _signed64(left), _signed64(right)
    if signed_right == 0:
        return signed_left & _M64
    quotient = _signed64(_rv64_sdiv(signed_left, signed_right))
    return (signed_left - quotient * signed_right) & _M64


def _arithmetic_helper_result(target, left, right):
    if target == 0x80004640:
        return (left * right) & _M64
    if target == 0x800046A4:
        return _rv64_sdiv(left, right)
    if target == 0x80004728:
        return _rv64_srem(left, right)
    raise ValueError(f"not an arithmetic functional helper: {target:#x}")


def _arithmetic_helper_observation_errors(target, pre_regs, post_regs, stores):
    """Check only the exact functional/footprint facts asserted by Houdini."""
    _name, _result, clobbered = ARITH_FUNCTIONAL_CALLEES[target]
    errors = []
    want = _arithmetic_helper_result(target, pre_regs[10], pre_regs[11])
    if (post_regs[10] & _M64) != want:
        errors.append(f"a0 expected {want:#018x}, got {post_regs[10] & _M64:#018x}")
    if stores:
        errors.append(f"expected no stores, got {len(stores)}")
    bad_regs = [reg for reg in range(32) if reg not in clobbered
                and (post_regs[reg] & _M64) != (pre_regs[reg] & _M64)]
    if bad_regs:
        errors.append("preserved registers " +
                      ",".join(f"x{reg}" for reg in bad_regs[:8]))
    return errors


def exact_helper_findings(tr, img, targets):
    """Check every concrete call/return pair for the exact-inline helpers."""
    findings, checked = [], 0
    for k in range(tr.n):
        p = tr.pc[k]
        ins = decode(p, img.word(p))
        if not is_call(ins) or ins.kind != "jal" or ins.target not in targets:
            continue
        d0 = tr.depth[k]
        j = k + 1
        while j < tr.n and tr.depth[j] > d0:
            j += 1
        if j >= tr.n:
            findings.append(("HELPER-NORETURN", EXACT_VALUE_CALLEES[ins.target],
                             f"{tr.name}@{tr.step[k]} has no caller continuation"))
            continue
        pre_regs = list(tr.regs_at(k))
        pre_regs[1] = (p + 4) & _M64
        mem = entry_memory(tr, img, k + 1, j)
        stores = [(tr.maddr[i], tr.mw[i], tr.mpost[i])
                  for i in range(k + 1, j) if tr.mk[i] == MK_STORE]
        errors = _helper_observation_errors(
            ins.target, pre_regs, mem, list(tr.regs_at(j)), stores)
        if errors:
            findings.append(("HELPER-CONTRACT", EXACT_VALUE_CALLEES[ins.target],
                             f"{tr.name}@{tr.step[k]}: " + "; ".join(errors)))
        checked += 1
    return findings, checked


def arithmetic_helper_findings(tr, img, targets):
    """Check observed calls against the independent RV64 arithmetic oracle."""
    findings, checked = [], 0
    for k in range(tr.n):
        p = tr.pc[k]
        ins = decode(p, img.word(p))
        if not is_call(ins) or ins.kind != "jal" or ins.target not in targets:
            continue
        d0 = tr.depth[k]
        j = k + 1
        while j < tr.n and tr.depth[j] > d0:
            j += 1
        if j >= tr.n:
            findings.append(("ARITH-HELPER-NORETURN",
                             ARITH_FUNCTIONAL_CALLEES[ins.target][0],
                             f"{tr.name}@{tr.step[k]} has no caller continuation"))
            continue
        pre_regs = list(tr.regs_at(k))
        pre_regs[1] = (p + 4) & _M64
        stores = [(tr.maddr[i], tr.mw[i], tr.mpost[i])
                  for i in range(k + 1, j) if tr.mk[i] == MK_STORE]
        errors = _arithmetic_helper_observation_errors(
            ins.target, pre_regs, list(tr.regs_at(j)), stores)
        if errors:
            findings.append(("ARITH-HELPER-CONTRACT",
                             ARITH_FUNCTIONAL_CALLEES[ins.target][0],
                             f"{tr.name}@{tr.step[k]}: " + "; ".join(errors)))
        checked += 1
    return findings, checked


def semantic_helper_findings(tr, img, targets):
    """Check every observed helper call against its Lean-level relation."""
    findings, checked = [], 0
    for k in range(tr.n):
        p = tr.pc[k]
        ins = decode(p, img.word(p))
        if not is_call(ins) or ins.kind != "jal" or ins.target not in targets:
            continue
        d0 = tr.depth[k]
        j = k + 1
        while j < tr.n and tr.depth[j] > d0:
            j += 1
        name = SEMANTIC_HELPER_CALLEES[ins.target][0]
        if j >= tr.n:
            findings.append(("SEMANTIC-HELPER-NORETURN", name,
                             f"{tr.name}@{tr.step[k]} has no caller continuation"))
            continue
        pre_regs = list(tr.regs_at(k))
        pre_regs[1] = (p + 4) & _M64
        mem = entry_memory(tr, img, k + 1, j)
        stores = [(tr.maddr[i], tr.mw[i], tr.mpost[i])
                  for i in range(k + 1, j) if tr.mk[i] == MK_STORE]
        errors = _semantic_helper_observation_errors(
            ins.target, pre_regs, mem, list(tr.regs_at(j)), stores)
        if ins.target == 0x800029FC:
            pre_out, pre_len, pre_known = _trace_output_state(tr, k)
            post_out, post_len, post_known = _trace_output_state(tr, j)
            if not pre_known or not post_known:
                errors.append("output stream is unobserved")
            elif pre_out != post_out or pre_len != post_len:
                errors.append("successful env_new changed the output stream")
        if errors:
            findings.append(("SEMANTIC-HELPER-CONTRACT", name,
                             f"{tr.name}@{tr.step[k]}: " + "; ".join(errors)))
        checked += 1
    return findings, checked


def concat_relation_findings(tr, img):
    """Check each concrete string-add path against Lean Value.catDisplay."""
    findings, checked = [], 0
    for k in range(tr.n):
        if tr.pc[k] != 0x8000351C:
            continue
        d0 = tr.depth[k]
        j = k + 1
        while j < tr.n and tr.depth[j] >= d0:
            if tr.depth[j] == d0 and tr.pc[j] == 0x80003AC8:
                break
            j += 1
        if j >= tr.n or tr.depth[j] < d0:
            continue
        mem = entry_memory(tr, img, k, j + 1)
        inputs = _machine_state(tr, mem, k, k)
        expr = inputs.regs.sel(8)
        if _try_load_le(inputs.mem, expr + 8, 4) != 11:
            continue
        sp = inputs.regs.sel(2)
        left_kind = _try_load_le(inputs.mem, sp + 120, 4)
        right_kind = _try_load_le(inputs.mem, sp + 144, 4)
        if left_kind != 3 and right_kind != 3:
            continue
        left = _cat_display_semantics(inputs.mem, sp + 120)
        right = _cat_display_semantics(inputs.mem, sp + 144)
        output = _machine_state(tr, mem, k, j)
        actual = _cstring_bytes(output.mem, output.regs.sel(8))
        if left is None or right is None:
            findings.append(("CONCAT-INPUT-UNOBSERVED", tr.name,
                             f"step {tr.step[k]} has undecodable Value bytes"))
        elif actual != left + right:
            findings.append(("CONCAT-LEAN-RELATION", tr.name,
                             f"step {tr.step[k]} expected {(left + right)!r}, "
                             f"got {actual!r}"))
        checked += 1
    return findings, checked


def native_output_findings(tr, img):
    """Check native print calls against Lean printArgs and the output trace."""
    findings, checked, loop_checked = [], 0, 0
    for k in range(tr.n):
        ins = decode(tr.pc[k], img.word(tr.pc[k]))
        if not is_call(ins):
            continue
        target = ins.target if ins.kind == "jal" else tr.npc[k]
        if target not in NATIVE_OUTPUT_CALLEES:
            continue
        d0 = tr.depth[k]
        j = k + 1
        while j < tr.n and tr.depth[j] > d0:
            j += 1
        name, newline = NATIVE_OUTPUT_CALLEES[target]
        if j >= tr.n:
            findings.append(("NATIVE-OUTPUT-NORETURN", name,
                             f"{tr.name}@{tr.step[k]} has no continuation"))
            continue
        mem = entry_memory(tr, img, k + 1, j)
        argc = tr.reg(k, 12) & 0xFFFFFFFF
        args_base = tr.reg(k, 13)
        args = [_value_display_semantics(mem, args_base + 24 * index)
                for index in range(argc)]
        actual = _trace_output_segment(tr, k + 1, j)
        if any(arg is None for arg in args):
            findings.append(("NATIVE-OUTPUT-INPUT", name,
                             f"{tr.name}@{tr.step[k]} has undecodable argument bytes"))
        else:
            expected = b" ".join(args) + (b"\n" if newline else b"")
            if actual != expected:
                findings.append(("NATIVE-OUTPUT-RELATION", name,
                                 f"{tr.name}@{tr.step[k]} expected {expected!r}, "
                                 f"got {actual!r}"))
        post = _machine_state(tr, mem, k + 1, j)
        sret = tr.reg(k, 10)
        if _try_load_le(post.mem, sret, 4) != 0 \
                or _try_load_le(post.mem, sret + 8, 8) != 0:
            findings.append(("NATIVE-OUTPUT-SRET", name,
                             f"{tr.name}@{tr.step[k]} did not return Value.null"))
        if not newline and argc > 0:
            header = next((row for row in range(k + 1, j)
                           if tr.pc[row] == 0x80002F1C), None)
            exit_row = (next((row for row in range(header + 1, j)
                              if tr.pc[row] == 0x80002F50
                              and tr.depth[row] == tr.depth[header]), None)
                        if header is not None else None)
            if header is None or exit_row is None:
                findings.append(("NATIVE-OUTPUT-LOOP-COVERAGE", name,
                                 f"{tr.name}@{tr.step[k]} has nonzero argc but "
                                 "no complete output-loop observation"))
            else:
                loop_pre = _machine_state(tr, mem, k + 1, header)
                loop_post = _machine_state(tr, mem, k + 1, exit_row)
                if not _output_loop_relation(loop_pre, loop_post):
                    findings.append(("NATIVE-OUTPUT-LOOP", name,
                                     f"{tr.name}@{tr.step[k]} violates the "
                                     "printed-prefix/control-state relation"))
                loop_checked += 1
        checked += 1
    return findings, checked, loop_checked


def _memory_signature_diff(mem, expected):
    """Addresses where a symbolic state disagrees with observed input bytes.

    Unknown bytes do not count as zero.  ``MA.sel`` records an unknown fallback
    in-place, so inspect that record after reading while allowing an explicit
    array-store override to make the byte known again.
    """
    different = []
    for address, value in expected.items():
        actual = mem.sel(address)
        unknown = address not in mem.d and address in mem.unknown
        if unknown or actual != value:
            different.append(address)
    return different


class Oracle:
    """Resolves the encoder's uninterpreted symbols from one real execution.

    CONTENT-ADDRESSED, not sequential.  `state_exit` is a guarded merge, so
    deciding which guard is true forces evaluation of states on paths the machine
    did NOT take, and those paths apply summaries at states that never occurred.
    A cursor walked through the trace in order would hand them somebody else's
    observation and the answer would be fiction.  So an application of
    `callee_T` is matched to the call to `T` whose register file EQUALS the state
    the encoder hands it, and if none does the result is marked TAINTED.

    Taint is the honest reading of the plan's own construction.  Pinning
    `(callee_X pre) = post` from observed pairs leaves the callee unconstrained
    everywhere else, so a guard that depends on an unobserved application is
    undetermined rather than false, and a `get-value` through Z3 would have had
    exactly the same gap with no way to see it.  Here it is visible: a guard is
    only believed when nothing tainted feeds it."""

    def __init__(self, tr, img, lo, hi, d0, exits_of):
        self.tr, self.img, self.d0 = tr, img, d0
        self.lo, self.hi = lo, hi
        self.exits_of = exits_of
        self.tainted = set()      # bindings whose value is not determined by the trace
        self.problems = []
        self.resolved = []
        # Each observation also records the bytes read before their first write
        # by the summary.  Register equality alone is not enough to identify a
        # call state: two states can have identical argument registers but
        # different spilled Values / heap objects, and returning the trace result
        # for the wrong memory would hide exactly the data-flow bugs phase 3b is
        # meant to find.
        self.calls = {}           # target -> [(row, ret_row, regs_with_ra, reads)]
        self.icalls = []
        self.loops = {}           # header -> [(row, exit_row, regs, reads)]
        self._index()

    def _input_reads(self, a, b, include_entry=False):
        """Bytes whose entry values an observed summary can depend on.

        A byte first written inside the summary and only read afterwards is not
        part of its input.  A load before the first write is.  The trace records
        the pre-value of every data-memory access, so this is independent of the
        SMT transformer's load/store expressions.
        """
        reads, written = {}, set()
        start = a if include_entry else a + 1
        for k in range(start, b):
            if self.tr.mk[k] == MK_NONE:
                continue
            addr, width = self.tr.maddr[k], self.tr.mw[k]
            if self.tr.mk[k] == MK_LOAD:
                for byte in range(width):
                    address = (addr + byte) & M64
                    if address not in written and address not in reads:
                        reads[address] = (self.tr.mpre[k] >> (8 * byte)) & 0xFF
            if self.tr.mk[k] == MK_STORE:
                for byte in range(width):
                    written.add((addr + byte) & M64)
        return reads

    def _index(self):
        tr, d = self.tr, self.tr.depth
        for k in range(self.lo, self.hi):
            if d[k] != self.d0:
                continue
            p = tr.pc[k]
            ins = decode(p, self.img.word(p))
            if is_call(ins):
                j = k + 1
                while j < tr.n and d[j] > self.d0:
                    j += 1
                if j >= tr.n:
                    continue
                regs = list(tr.regs_at(k))
                regs[1] = (p + 4) & M64          # the encoder's `ra{k}` bind
                key = tuple(regs)
                if ins.kind == "jal":
                    self.calls.setdefault(ins.target, []).append(
                        (k, j, key, self._input_reads(k, j)))
                else:
                    self.icalls.append((k, j, key, self._input_reads(k, j)))
            if p in self.exits_of:
                ex = self.exits_of[p]
                j = k + 1
                while j < self.hi and not (d[j] == self.d0 and tr.pc[j] in ex):
                    j += 1
                self.loops.setdefault(p, []).append(
                    (k, min(j, self.hi - 1), tuple(tr.regs_at(k)),
                     self._input_reads(k, min(j, self.hi - 1),
                                       include_entry=True)))

    def _apply_stores(self, mem, a, b, include_entry=False):
        """Apply summary-owned writes before continuation row `b`."""
        d = dict(mem.d)
        start = a if include_entry else a + 1
        for k in range(start, b):
            if self.tr.mk[k] == MK_STORE and not _is_mmio_store(
                    self.tr.maddr[k], self.tr.mw[k]):
                post, addr, w = self.tr.mpost[k], self.tr.maddr[k], self.tr.mw[k]
                for j in range(w):
                    d[(addr + j) & M64] = (post >> (8 * j)) & 0xFF
        return MA(d, mem.base, mem.unknown, mem.reads)

    def _state_at(self, row, mem):
        # The encoder reserves rr[32] for the control PC.  Summary results use
        # it to select one loop exit, so concrete oracle states must carry it.
        out, out_len, _ = _trace_output_state(self.tr, row)
        return St(mem, RA(tuple(self.tr.regs_at(row)) + (self.tr.pc[row],)),
                  out, out_len)

    def _pick(self, cands, arg, sym, binding, use_ra):
        """The observation matching both registers and read-relevant memory."""
        want = tuple(arg.regs.sel(r) for r in range(32))
        best, best_score = None, None
        for row, ret, key, reads in cands:
            reg_diff = [r for r in range(1, 32) if key[r] != want[r]]
            mem_diff = _memory_signature_diff(arg.mem, reads)
            trace_out, trace_out_len, output_known = (
                _trace_output_state(self.tr, row) if hasattr(self, "tr")
                else (OA(), 0, False))
            output_diff = output_known and bool(_output_mismatches(
                arg, St(arg.mem, arg.regs, trace_out, trace_out_len), limit=1))
            if not reg_diff and not mem_diff and not output_diff:
                return (row, ret, [], [], False)
            score = len(reg_diff) + len(mem_diff) + int(output_diff)
            if best_score is None or score < best_score:
                best, best_score = (row, ret, reg_diff, mem_diff, output_diff), score
        return best if best else (None, None, None, None, False)

    def __call__(self, sym, arg, binding):
        if sym.startswith("callee_"):
            tgt = int(sym[len("callee_"):])
            cands = self.calls.get(tgt, [])
            return self._resolve(sym, arg, binding, cands, f"call to {tgt:#x}")
        if sym.startswith("icall_"):
            return self._resolve(sym, arg, binding, self.icalls, "indirect call")
        if sym.startswith("loopexit_"):
            # the PC the loop actually left at: the encoder's per-loop exit
            # selector, answered from the trace
            h = int(sym[len("loopexit_"):])
            cands = self.loops.get(h, [])
            if not cands:
                self.tainted.add(binding)
                return 0
            row, ret, reg_diff, mem_diff, output_diff = self._pick(
                cands, arg, sym, binding, False)
            if reg_diff or mem_diff or output_diff:
                self.tainted.add(binding)
                return 0
            p = self.tr.pc[ret]
            return p if (self.lo <= ret < self.hi) else 0
        if sym.startswith("loop_"):
            h = int(sym[len("loop_"):])
            return self._resolve(sym, arg, binding, self.loops.get(h, []),
                                 f"loop header {h:#x}")
        # an unlisted computed goto or an unmodelled word: nothing to match
        self.tainted.add(binding)
        return arg

    def _resolve(self, sym, arg, binding, cands, what):
        if not cands:
            self.tainted.add(binding)
            self.problems.append(("SUMMARY-NOSITE", binding,
                                  f"{sym}: no {what} in this instance"))
            return arg
        row, ret, reg_diff, mem_diff, output_diff = self._pick(
            cands, arg, sym, binding, True)
        if reg_diff or mem_diff or output_diff:
            self.tainted.add(binding)
            details = []
            if reg_diff:
                details.append("registers " + ", ".join(
                    f"x{r}" for r in reg_diff[:6]) +
                    (f" (+{len(reg_diff)-6})" if len(reg_diff) > 6 else ""))
            if mem_diff:
                details.append("input bytes " + ", ".join(
                    f"{a:#x}" for a in mem_diff[:6]) +
                    (f" (+{len(mem_diff)-6})" if len(mem_diff) > 6 else ""))
            if output_diff:
                details.append("output prefix")
            self.problems.append(("SUMMARY-ARG", binding,
                f"{sym} applied to a state no {what} in this instance is in; "
                f"nearest is step {self.tr.step[row]}, differing in " +
                "; ".join(details)))
            return self._state_at(
                ret, self._apply_stores(
                    arg.mem, row, ret, include_entry=sym.startswith("loop_")))
        self.resolved.append((sym, row, ret))
        return self._state_at(
            ret, self._apply_stores(
                arg.mem, row, ret, include_entry=sym.startswith("loop_")))


def entry_memory(tr, img, lo, hi):
    """The machine's memory at row `lo`, over the addresses this instance reads.

    Built from the trace's own observations: the first time the instance touches
    an address, the `pre` bytes ARE the entry value, unless the instance has
    already written it.  Anything never touched falls back to the ELF image, and
    an address neither knows is recorded as unknown rather than defaulted to
    zero — a zero default would let a load of uninitialised memory agree with the
    encoder by accident."""
    # Heap ASTs are built before the evaluated span.  Replay prior stores so
    # residual premises may read fields the span itself does not load on this
    # branch (for example an absent `else` pointer).
    known, written = {}, set()
    for k in range(lo):
        if tr.mk[k] != MK_STORE or _is_mmio_store(tr.maddr[k], tr.mw[k]):
            continue
        for j in range(tr.mw[k]):
            known[(tr.maddr[k] + j) & _M64] = (tr.mpost[k] >> (8 * j)) & 0xFF
    for k in range(lo, hi):
        if tr.mk[k] == MK_NONE:
            continue
        a, pre, w = tr.maddr[k], tr.mpre[k], tr.mw[k]
        for j in range(8):
            addr = (a + j) & _M64
            if addr not in written and addr not in known:
                known[addr] = (pre >> (8 * j)) & 0xFF
        if tr.mk[k] == MK_STORE and not _is_mmio_store(a, w):
            for j in range(w):
                written.add((a + j) & _M64)
    def base(addr):
        if addr in known:
            return known[addr]
        return img.byte(addr) if img.mapped(addr) else None
    return MA({}, base, set())


def exit_guard_shape(q, a):
    """Is this plain assertion the exit-guard disjunction?

    The emitter writes `(assert {exitG})` immediately after the binding chain,
    and `exitG` is either an `or` of guarded terms or one guarded term.  Everything
    else the query asserts is a PIN — the AST-kind word and which arm of the
    dispatch it selects — and a pin is a precondition of the span, not a claim
    about it."""
    def mentions_guard(t):
        if isinstance(t, str):
            return t.startswith("g") and t in q.binds
        return isinstance(t, list) and any(mentions_guard(x) for x in t)

    if isinstance(a, list) and a and a[0] == "or" \
            and all(mentions_guard(x) for x in a[1:]):
        return list(a[1:])
    if mentions_guard(a):
        return [a]
    return None


def ite_chain(q):
    """`state_exit`'s guarded merge as [(guard, state), …], ALL arms.

    `reflectBmc` folds the exits into `ite g1 s1 (ite g2 s2 … sN)`, so the LAST
    arrival's guard is not in the term — it is the fallthrough.  Its guard is in
    the exit-guard assertion the emitter writes after the chain
    (`(assert (or g1 … gN))`), and without it a span with a single exit looks
    like a span with no true guard at all."""
    t, out = q.state_exit, []
    while isinstance(t, list) and t and t[0] == "ite":
        out.append(t[2])
        t = t[3]
    out.append(t)
    gs = None
    for a in reversed(q.plain):
        if exit_guard_shape(q, a) is not None:
            gs = exit_guard_shape(q, a)
            break
    if gs is None or len(gs) != len(out):
        # fall back to the guards the term itself carries; the fallthrough is
        # then unguarded, which is what the term literally says
        t, gs = q.state_exit, []
        while isinstance(t, list) and t and t[0] == "ite":
            gs.append(t[1])
            t = t[3]
        gs.append("true")
    return list(zip(gs, out))


def _concrete_consistency_pins(q, ev, s0, orc, tr, lo, chosen):
    """A stronger, concrete model slice for an SMT consistency check.

    Phase 3b has already evaluated the emitted term against a real execution
    and rejected unknown memory, tainted selected exits, and machine/encoder
    disagreement.  Pinning those observed values cannot manufacture
    satisfiability: SAT of ``query ∧ pins`` is a witness for SAT of ``query``.
    The pins are emitted as a separate artifact so the production encoder and
    this independent evaluator remain distinct implementations.
    """
    lines = [
        f"; trace={tr.name} step={tr.step[lo]}",
        "; concrete phase3b consistency witness; append before (check-sat)",
    ]
    addresses = sorted(s0.mem.reads)

    def pin_state(name, state, pin_memory):
        for register in range(33):
            lines.append(
                f"(assert (= (select (rr {name}) #x{register:016x}) "
                f"#x{state.regs.sel(register):016x}))")
        lines.append(f"(assert (= (ol {name}) #x{state.out_len:016x}))")
        for index, byte in sorted(state.out.d.items()):
            lines.append(
                f"(assert (= (select (oo {name}) #x{index:016x}) "
                f"#x{byte:02x}))")
        if pin_memory:
            for address in addresses:
                lines.append(
                    f"(assert (= (select (mm {name}) #x{address:016x}) "
                    f"#x{state.mem.sel(address):02x}))")

    # The entry memory is the source of every direct instruction state.
    pin_state("s0", s0, True)

    # Fix every trace-determined path guard.  Guards fed by an unobserved
    # summary remain deliberately unconstrained.
    for name in q.order:
        if q.sorts.get(name) != "Bool" \
                or term_deps(q, name) & orc.tainted:
            continue
        try:
            value = ev.get(name)
        except EvalError:
            continue
        lines.append(f"(assert {name})" if value
                     else f"(assert (not {name}))")

    # Register/output pins for determined intermediate states remove model
    # search without equating whole arrays.  Pin finite memory support only on
    # the selected exit; intermediate memories remain governed by the emitted
    # store equations.
    selected = ev.ev(chosen)
    selected_name = chosen if isinstance(chosen, str) else None
    if selected_name is not None:
        pin_state(selected_name, selected, True)
    return "\n".join(lines) + "\n"


def phase3b_instance(q, tr, img, sp, lo, hi, d0, exits_of, exit_row,
                     extensions=(), residual=None, production_post=None,
                     production_premise=None, write_rows=(), exact_targets=(),
                     production_suffix=None, production_suffix_post=None,
                     suffix_audit=None, projection_audit=None,
                     consistency_pins=None):
    """One span instance, driven end to end.

    Returns (findings, chain footprint, summaries resolved, emitted footprint)."""
    mem = entry_memory(tr, img, lo, hi)
    entry_out, entry_out_len, _ = _trace_output_state(tr, lo)
    s0 = St(mem, RA(tuple(tr.regs_at(lo)) + (tr.pc[lo],)),
            entry_out, entry_out_len)

    def unknown_memory(stage):
        if not mem.unknown:
            return None
        first = min(mem.unknown)
        return ([
            ("MEM-UNKNOWN", sp["field"],
             f"[{tr.name}@{tr.step[lo]}] {stage} read "
             f"{len(mem.unknown)} byte(s) the trace and image leave undefined "
             f"(first {first:#x})")
        ], [], 0, set(), [])

    orc = Oracle(tr, img, lo, hi, d0, exits_of)
    ev = Ev(q, s0, orc)
    out = []
    projection = residual in PROJECTED_FIELDS
    checkpoints = _checkpoint_states(tr, mem, lo, hi, d0) if projection else {}
    if sp["field"] == "hCallCallToEpilogue" \
            and _arrived_from_call_dispatch(tr, lo, d0):
        checkpoints["hCall-dispatch-route"] = s0
    applies, expected = concrete_residual_projection(
        residual, s0, checkpoints, sp["field"]) if projection else (False, None)
    unknown = unknown_memory("the independent residual oracle")
    if unknown is not None:
        return unknown
    if projection and not applies:
        return None, [], 0, set(), []
    # Evaluate the manifest, not merely the anonymous query assertions.  This
    # makes residual scoping visible and ensures every accepted witness reaches
    # each named internal checkpoint.
    for ext in extensions:
        try:
            if ext["guard"] != "true" \
                    and not _eval_manifest_term(ev, ext["guard"]):
                if projection:
                    out.append(("PROJECTION-PREMISE", sp["field"],
                                f"[{tr.name}@{tr.step[lo]}] production checkpoint "
                                f"guard for {ext['name']} rejects an independent instance"))
                    continue
                unknown = unknown_memory("a residual checkpoint guard")
                if unknown is not None:
                    return unknown
                return None, [], 0, set(), []
            pred = parse_all(ext["predicate"])
            if len(pred) != 1 or not ev.ev(pred[0]):
                if projection:
                    out.append(("PROJECTION-PREMISE", sp["field"],
                                f"[{tr.name}@{tr.step[lo]}] production predicate "
                                f"{ext['name']} rejects an independent instance"))
                    continue
                unknown = unknown_memory("a residual checkpoint predicate")
                if unknown is not None:
                    return unknown
                return None, [], 0, set(), []
        except (EvalError, ValueError) as exc:
            if projection:
                out.append(("PROJECTION-PREMISE", sp["field"],
                            f"[{tr.name}@{tr.step[lo]}] {ext['name']}: {exc}"))
                continue
            return None, [], 0, set(), []
    # IS THIS EXECUTION IN THE SPAN'S SCOPE AT ALL?
    #
    # The residual is selected by the query's PINS — the AST kind word and the
    # dispatch arm it makes true — not by reaching the arm's address.  Those are
    # different things: `exec_stmt`'s `if` arm reaches into the `block` arm's
    # code, so an `if` statement passes through 0x8000418c at the span's own
    # depth while the kind word says 3 and `hSBlock` pins 2.  Filtering on the
    # address instead of on the pins put fifty out-of-scope executions into the
    # comparison, where the encoder is under no obligation to agree with
    # anything.
    for a in q.plain:
        if exit_guard_shape(q, a) is not None:
            continue
        try:
            if not ev.ev(a) and not (term_deps(q, a) & orc.tainted):
                if projection:
                    out.append(("PROJECTION-SCOPE", sp["field"],
                                f"[{tr.name}@{tr.step[lo]}] production query pins "
                                "reject an independent residual instance"))
                    continue
                unknown = unknown_memory("a residual scope predicate")
                if unknown is not None:
                    return unknown
                return None, [], 0, set(), []
        except EvalError:
            if projection:
                out.append(("PROJECTION-SCOPE", sp["field"],
                            f"[{tr.name}@{tr.step[lo]}] production query pin "
                            "cannot be evaluated on an independent residual instance"))
                continue
            return None, [], 0, set(), []
    if residual in ("hVar", "hAssign"):
        try:
            expected_premise = _environment_success_premise(
                q, residual, extensions)
            forms = parse_all(production_premise or "")
            bodies = [form[1] for form in forms
                      if isinstance(form, list) and len(form) == 2
                      and form[0] == "assert"]
            if expected_premise is None or bodies != [expected_premise]:
                out.append(("PROJECTION-ENV-PREMISE", sp["field"],
                            "production premise is not the independently parsed "
                            "successful first-match helper relation"))
            elif not ev.ev(expected_premise):
                out.append(("PROJECTION-ENV-PREMISE", sp["field"],
                            f"[{tr.name}@{tr.step[lo]}] successful lookup premise "
                            "rejects the independently selected execution"))
        except (EvalError, ValueError) as exc:
            out.append(("PROJECTION-ENV-PREMISE", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] {exc}"))
    if residual in _FALSE_ROUTE_SPECS:
        try:
            forms = parse_all(production_premise or "")
            route_asserts = [form[1] for form in forms
                             if isinstance(form, list) and len(form) == 2
                             and form[0] == "assert"
                             and isinstance(form[1], str)]
            header, target, _ = _FALSE_ROUTE_SPECS[residual]
            expected_guards = _loop_exit_guards(q, header, target)
            if len(expected_guards) != 1 or expected_guards[0] not in route_asserts:
                out.append(("PROJECTION-ROUTE", sp["field"],
                            "production premise does not select the independently "
                            "identified false continuation"))
            elif not ev.ev(expected_guards[0]):
                out.append(("PROJECTION-ROUTE", sp["field"],
                            f"[{tr.name}@{tr.step[lo]}] false-route guard "
                            f"{expected_guards[0]} rejects the concrete route"))
        except (EvalError, ValueError) as exc:
            out.append(("PROJECTION-ROUTE", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] {exc}"))
    arms = ite_chain(q)
    live, undet = [], 0
    for g, st in arms:
        try:
            v = ev.ev(g)
        except EvalError as e:
            out.append(("EVAL", sp["field"], f"guard: {e}"))
            return out, [], 0, set(), []
        # a guard fed by an unobserved summary application is UNDETERMINED, not
        # false: the trace pins a summary only where it was applied for real
        if term_deps(q, g) & orc.tainted:
            undet += 1
            continue
        if v:
            live.append((g, st))
    if not live:
        if undet == 0:
            out.append(("EXIT-UNCOVERED", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] no exit guard of the merge is true "
                        f"for a real execution, and none is undetermined; `state_exit` "
                        f"falls through to the last arrival, a state the machine is "
                        f"not in"))
        else:
            out.append(("EXIT-UNDETERMINED", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] no exit guard is determinedly true "
                        f"({undet} of {len(arms)} depend on a summary application this "
                        f"execution never made)"))
        return out, [], len(orc.resolved), set(), []
    if len(live) > 1:
        # ambiguity only matters if the arms disagree: several arrivals at the
        # same exit PC with the same state is a merge, not a race
        rs = []
        for _, st in live:
            try:
                v = ev.ev(st)
                rs.append(tuple(v.regs.sel(r) for r in range(32)))
            except EvalError:
                rs.append(None)
        if len({r for r in rs if r is not None}) > 1:
            out.append(("EXIT-AMBIGUOUS", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] {len(live)} exit guards are true at "
                        f"once AND the arms disagree; the `ite` merge silently takes the "
                        f"first, so the exit state depends on emission order; guards="
                        + ",".join(str(g) for g, _ in live)))
    chosen = live[0][1]
    if term_deps(q, chosen) & orc.tainted:
        out.append(("EXIT-TAINTED", sp["field"],
                    f"[{tr.name}@{tr.step[lo]}] the selected exit state is fed by a "
                    f"summary application this execution never made: "
                    + "; ".join(m for _, _, m in orc.problems[:2])))
        return out, [], len(orc.resolved), set(), []
    try:
        exit_st = ev.ev(chosen)
    except EvalError as e:
        out.append(("EVAL", sp["field"], str(e)))
        return out, [], len(orc.resolved), set(), []
    machine_exit = _machine_state(tr, mem, lo, exit_row)
    suffix_snapshot = None
    if suffix_audit is not None:
        suffix_snapshot = {
            "fields": set(suffix_audit["fields"]),
            "facts": suffix_audit["facts"],
            "results": suffix_audit["results"],
            "mutations": suffix_audit["mutations"],
        }
    suffix_fields = _ARITHMETIC_SUFFIX_FIELDS | _NONARITHMETIC_SUFFIX_FIELDS
    if residual in suffix_fields and production_suffix \
            and suffix_audit is not None \
            and residual not in suffix_audit["fields"]:
        if residual in _ARITHMETIC_SUFFIX_FIELDS:
            suffix_findings, killed, facts = arithmetic_suffix_audit(
                q, residual, s0, checkpoints, machine_exit, img,
                production_suffix, production_suffix_post)
        else:
            suffix_findings, killed, facts = nonarithmetic_suffix_audit(
                q, residual, s0, checkpoints, machine_exit,
                production_suffix, production_suffix_post)
        # Some concrete inputs are algebraically insensitive to one operand
        # (for example `0 * x` or `x % 1`).  Such an execution can validate the
        # machine state but cannot demonstrate that the candidate result
        # relation depends on every semantic payload.  Do not freeze the
        # per-field mutation audit on that first occurrence: discard this
        # attempt and let phase3b select a later, discriminating execution.  If
        # the corpus has none, the ordinary NO-INSTANCE gate remains fail-closed.
        if suffix_findings and all(
                kind == "SUFFIX-PAYLOAD-MUTATION"
                for kind, _where, _detail in suffix_findings):
            suffix_audit.clear()
            suffix_audit.update(suffix_snapshot)
            return None, [], 0, set(), []
        out += suffix_findings
        suffix_audit["fields"].add(residual)
        suffix_audit["mutations"] += killed
        suffix_audit["facts"] += facts
        if not any(kind.startswith("SUFFIX-POST")
                   for kind, _where, _detail in suffix_findings):
            suffix_audit["results"] += 1
    if projection:
        if residual == "hArgsNil":
            machine_value = (machine_exit.regs.sel(15), machine_exit.regs.sel(16))
            encoder_value = (exit_st.regs.sel(15), exit_st.regs.sel(16))
        elif residual == "hArgsCons":
            _argc, destination, _returned = expected
            machine_value = (
                machine_exit.regs.sel(16), destination,
                _value_words(machine_exit.mem, destination))
            encoder_value = (
                exit_st.regs.sel(16), destination,
                _value_words(exit_st.mem, destination))
        elif residual == "hSBlock":
            state_names = {row["name"]: row["state"] for row in extensions}

            def encoded_checkpoint(name):
                state_name = state_names.get(name)
                return ev.ev(state_name) if state_name is not None else None

            if sp["field"] == "hSBlock":
                machine_arm = checkpoints.get(0x8000418C)
                machine_pre = checkpoints.get(0x80004190)
                machine_ret = checkpoints.get(0x80004194)
                machine_setup = checkpoints.get(0x800041A0)
                encoded_arm = encoded_checkpoint("execBlockA-x8-stmt")
                encoded_pre = encoded_checkpoint("pre-env-new")
                encoded_ret = encoded_checkpoint("post-env-new")
                encoded_setup = encoded_checkpoint("post-env-new-setup")

                def allocation_observation(arm, pre, ret, setup):
                    if arm is None or pre is None or ret is None or setup is None:
                        return None
                    inner = ret.regs.sel(10)
                    return (
                        (arm.regs.sel(8), arm.regs.sel(9),
                         arm.regs.sel(19), arm.regs.sel(18)),
                        pre.regs.sel(10), inner,
                        (_load_le(ret.mem, inner, 4),
                         _load_le(ret.mem, inner + 4, 4),
                         _load_le(ret.mem, inner + 8, 8),
                         _load_le(ret.mem, inner + 16, 8),
                         _load_le(ret.mem, inner + 24, 8)),
                        (setup.regs.sel(19), setup.regs.sel(16),
                         setup.regs.sel(8), setup.regs.sel(9),
                         setup.regs.sel(18)),
                        ret.out == pre.out and ret.out_len == pre.out_len,
                        setup.out == ret.out and setup.out_len == ret.out_len,
                        inner != 0 and inner & 7 == 0,
                    )

                machine_value = allocation_observation(
                    machine_arm, machine_pre, machine_ret, machine_setup)
                encoder_value = allocation_observation(
                    encoded_arm, encoded_pre, encoded_ret, encoded_setup)
            elif sp["field"] == "hSBlockIter":
                machine_pre = checkpoints.get(0x800041C4)
                encoded_pre = encoded_checkpoint("pre-child-exec")
                index = s0.regs.sel(16)
                node = s0.regs.sel(8)
                stmts = _load_le(s0.mem, node + 8, 8)
                stmt = _load_le(s0.mem, stmts + 8 * index, 8)

                def iteration_observation(pre, ret):
                    if pre is None or ret is None:
                        return None
                    return (
                        (pre.regs.sel(2), pre.regs.sel(10),
                         pre.regs.sel(11), pre.regs.sel(12),
                         pre.regs.sel(13)),
                    )

                machine_value = iteration_observation(
                    machine_pre, machine_exit)
                encoder_value = iteration_observation(
                    encoded_pre, exit_st)
            else:
                machine_value = (
                    machine_exit.regs.sel(10),
                    machine_exit.mem is s0.mem,
                    machine_exit.out == s0.out
                    and machine_exit.out_len == s0.out_len,
                )
                encoder_value = (
                    exit_st.regs.sel(10),
                    exit_st.mem is s0.mem,
                    exit_st.out == s0.out
                    and exit_st.out_len == s0.out_len,
                )
        elif residual == "hCallTooMany":
            sp0 = s0.regs.sel(2)

            def too_many_observation(end):
                return (
                    end.regs.sel(10), end.regs.sel(11), end.regs.sel(12),
                    end.regs.sel(13), end.regs.sel(14),
                    tuple(end.regs.sel(register)
                          for register in
                          (1, 2, 8, 9, 18, 19, 20, 21, 22, 23)),
                    tuple((offset, _load_le(end.mem, sp0 + offset, 8))
                          for offset in (1048, 1040, 1032, 1024, 1016)),
                    end.out == s0.out and end.out_len == s0.out_len,
                )

            machine_value = too_many_observation(machine_exit)
            encoder_value = too_many_observation(exit_st)
        elif residual == "hCall":
            query_name = sp["field"]
            state_names = {row["name"]: row["state"] for row in extensions}

            def encoded_checkpoint(name):
                state_name = state_names.get(name)
                return ev.ev(state_name) if state_name is not None else None

            if query_name == "hCallCallee":
                machine_arm = checkpoints.get(0x800031B0)
                encoded_arm = encoded_checkpoint("execBlockA-x8-expr")

                def callee_observation(arm, end):
                    if arm is None:
                        return None
                    sp_arm = arm.regs.sel(2)
                    return (
                        end.regs.sel(2), end.regs.sel(10), end.regs.sel(11),
                        end.regs.sel(12), end.regs.sel(13),
                        tuple(end.regs.sel(register)
                              for register in (1, 8, 9, 18, 19, 23)),
                        tuple(end.mem.sel(sp_arm + byte) for byte in range(8)),
                        end.out == arm.out and end.out_len == arm.out_len,
                    )

                machine_value = callee_observation(machine_arm, machine_exit)
                encoder_value = callee_observation(encoded_arm, exit_st)
            elif query_name in (
                    "hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
                sp0 = s0.regs.sel(2)

                def to_args_observation(end):
                    return (
                        end.regs.sel(15), end.regs.sel(16), end.regs.sel(13),
                        tuple(end.regs.sel(register)
                              for register in
                              (1, 2, 8, 9, 10, 11, 12, 18, 19, 23)),
                        tuple(end.mem.sel(sp0 + 1016 + byte)
                              for byte in range(8)),
                        _value_shadow(end.mem, sp0 + 96),
                        end.out == s0.out and end.out_len == s0.out_len,
                    )

                machine_value = to_args_observation(machine_exit)
                encoder_value = to_args_observation(exit_st)
            elif query_name == "hCallArgsToCall":
                def args_to_call_observation(end):
                    return (
                        end.regs.sel(15),
                        _value_shadow(end.mem, end.regs.sel(2) + 96),
                        _arg_vector_shadow(end),
                        end.mem is s0.mem,
                        end.out == s0.out and end.out_len == s0.out_len,
                    )

                machine_value = args_to_call_observation(machine_exit)
                encoder_value = args_to_call_observation(exit_st)
            else:
                def call_to_epilogue_observation(end):
                    return (
                        _value_shadow(end.mem, end.regs.sel(9)),
                        end.mem is s0.mem,
                        end.out == s0.out and end.out_len == s0.out_len,
                    )

                machine_value = call_to_epilogue_observation(machine_exit)
                encoder_value = call_to_epilogue_observation(exit_st)
        elif residual in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop"):
            query_name = sp["field"]

            def while_observation(exit_state):
                abi6 = tuple(exit_state.regs.sel(register)
                             for register in (1, 2, 8, 9, 18, 19))
                if query_name.endswith("CondSetup"):
                    return (
                        exit_state.regs.sel(10), exit_state.regs.sel(11),
                        exit_state.regs.sel(12), exit_state.regs.sel(13),
                        abi6, exit_state.mem is s0.mem,
                        exit_state.out == s0.out
                        and exit_state.out_len == s0.out_len,
                    )
                if query_name.endswith("CondTruthy"):
                    copied = tuple(
                        _load_le(exit_state.mem, s0.regs.sel(2) + offset, 8)
                        for offset in (16, 24, 32))
                    abi5 = tuple(exit_state.regs.sel(register)
                                 for register in (2, 8, 9, 18, 19))
                    return (
                        exit_state.regs.sel(10), copied, abi5,
                        exit_state.out == s0.out
                        and exit_state.out_len == s0.out_len,
                    )
                if query_name.endswith("BodySetup"):
                    return (
                        exit_state.regs.sel(10), exit_state.regs.sel(11),
                        exit_state.regs.sel(12), exit_state.regs.sel(13),
                        abi6, exit_state.mem is s0.mem,
                        exit_state.out == s0.out
                        and exit_state.out_len == s0.out_len,
                    )
                return (
                    exit_state.regs.sel(10), abi6,
                    exit_state.mem is s0.mem,
                    exit_state.out == s0.out
                    and exit_state.out_len == s0.out_len,
                )

            machine_value = while_observation(machine_exit)
            encoder_value = while_observation(exit_st)
        elif residual in _STATUS_PROJECTION_FIELDS:
            machine_value = machine_exit.regs.sel(10)
            encoder_value = exit_st.regs.sel(10)
        elif residual == "hCallAssertOk":
            sret = s0.regs.sel(10)

            def assert_ok_observation(end):
                return (
                    sret,
                    (_load_le(end.mem, sret, 4),
                     _load_le(end.mem, sret + 8, 8)),
                    end.regs.sel(2),
                    tuple(end.regs.sel(register)
                          for register in (1, 8, 9, 18)),
                    end.out == s0.out and end.out_len == s0.out_len,
                )

            machine_value = assert_ok_observation(machine_exit)
            encoder_value = assert_ok_observation(exit_st)
        elif residual in ("hCallPrint", "hCallPrintln"):
            start = s0.out_len
            machine_bytes = bytes(
                machine_exit.out.sel(index)
                for index in range(start, machine_exit.out_len))
            encoder_bytes = bytes(
                exit_st.out.sel(index)
                for index in range(start, exit_st.out_len))
            sret = s0.regs.sel(10)
            machine_value = (
                machine_bytes,
                (_load_le(machine_exit.mem, sret, 4),
                 _load_le(machine_exit.mem, sret + 8, 8)))
            encoder_value = (
                encoder_bytes,
                (_load_le(exit_st.mem, sret, 4),
                 _load_le(exit_st.mem, sret + 8, 8)))
        elif residual in ("hVar", "hAssign"):
            _success, destination, _words = expected
            machine_value = (
                machine_exit.regs.sel(10), destination,
                _value_words(machine_exit.mem, destination))
            encoder_value = (
                exit_st.regs.sel(10), destination,
                _value_words(exit_st.mem, destination))
        else:
            target = s0.regs.sel(10)
            machine_value = _projected_output_value(
                machine_exit, target, expected[0])
            encoder_value = _projected_output_value(
                exit_st, target, expected[0])
        if machine_value != expected:
            out.append(("PROJECTION-MACHINE", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] independent oracle expects "
                        f"{expected}, machine exits with {machine_value}"))
        if encoder_value != expected:
            out.append(("PROJECTION-ENCODER", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] independent oracle expects "
                        f"{expected}, encoded state_exit has {encoder_value}"))
    # A suffix audit evaluates hFn's observable closure bytes after replacing
    # only the MallocContract ghost transition with its named checkpoint seam.
    # The full post still contains allocator ghost state, which a byte trace
    # cannot execute; evaluating it again would report a fake fuzzer failure.
    if production_post and not (residual == "hFn" and production_suffix):
        try:
            form = parse_all(production_post)
            # Test the production formula against the real machine exit.  If
            # both the encoder and its formula share an error, this still fails.
            ev.env["state_exit"] = machine_exit
            if len(form) != 1 or len(form[0]) != 2 or form[0][0] != "assert":
                raise EvalError("malformed residual post")
            if ev.ev(form[0][1]):
                out.append(("PROJECTION-SMT", sp["field"],
                            f"[{tr.name}@{tr.step[lo]}] the concrete execution "
                            "violates the production SMT projection"))
            if residual in ("hVar", "hAssign"):
                _success, destination, words = expected
                mutants = {
                    "success-result": _with_reg_value(machine_exit, 10, 0),
                    "value-word": _with_mem_value(
                        machine_exit, destination + 8, 8, words[1] ^ 1),
                    "output-length": St(
                        machine_exit.mem, machine_exit.regs, machine_exit.out,
                        machine_exit.out_len + 1),
                }
                for name, mutant in mutants.items():
                    ev.env["state_exit"] = mutant
                    if not ev.ev(form[0][1]):
                        out.append(("PROJECTION-ENV-MUTANT-SURVIVED",
                                    sp["field"], name))
                ev.env["state_exit"] = machine_exit
            elif residual == "hCallAssertOk" \
                    and projection_audit is not None \
                    and sp["field"] not in projection_audit["fields"]:
                killed = []
                excluded = []
                for name, mutant in _assert_ok_post_mutants(s0, machine_exit):
                    certificate_post = _ASSERT_OK_CERTIFICATE_MUTATIONS.get(name)
                    if certificate_post is not None:
                        theorem = projection_audit["lean_certificates"].get(
                            (sp["field"], certificate_post))
                        if theorem is not None:
                            excluded.append((name, certificate_post, theorem))
                            continue
                    ev.env["state_exit"] = mutant
                    if ev.ev(form[0][1]):
                        killed.append(name)
                        projection_audit["assert_mutations"] += 1
                    else:
                        out.append(("PROJECTION-ASSERT-MUTANT-SURVIVED",
                                    sp["field"], name))
                ev.env["state_exit"] = machine_exit
                found_machine = set(killed)
                if found_machine != _ASSERT_OK_MACHINE_MUTATIONS:
                    out.append((
                        "PROJECTION-ASSERT-MUTATION-SET", sp["field"],
                        f"expected {sorted(_ASSERT_OK_MACHINE_MUTATIONS)}, "
                        f"found {sorted(found_machine)}"))
                projection_audit["mutation_summary"][sp["field"]] = {
                    "mutations_expected": len(_ASSERT_OK_MACHINE_MUTATIONS),
                    "mutations_killed": len(killed),
                    "certificates_excluded": len(excluded),
                }
                for name in killed:
                    projection_audit["mutation_rows"].append({
                        "field": sp["field"],
                        "post": "residual_relation",
                        "mutation": name,
                        "provenance": "independent-trace-oracle",
                        "result": "killed",
                    })
                for name, post, theorem in excluded:
                    projection_audit["mutation_rows"].append({
                        "field": sp["field"],
                        "post": post,
                        "mutation": name,
                        "provenance": theorem,
                        "result": "excluded-lean-certificate",
                    })
                projection_audit["fields"].add(sp["field"])
            elif residual == "hArgsCons" and projection_audit is not None \
                    and residual not in projection_audit["fields"]:
                states = {row["name"]: row["state"] for row in extensions}
                pre_name = states.get("pre-child-eval")
                ret_name = states.get("post-child-eval")
                call_pre = checkpoints.get(0x80003220)
                child_ret = checkpoints.get(0x80003224)
                if not pre_name or not ret_name or call_pre is None \
                        or child_ret is None:
                    out.append(("PROJECTION-ARGS-MUTATION", sp["field"],
                                "missing named child-call checkpoint"))
                else:
                    _argc, destination, returned = expected
                    mutations = []
                    for register, name in (
                            (2, "call-sp"), (10, "call-sret"),
                            (11, "call-depth"), (12, "call-arg"),
                            (13, "call-env")):
                        mutations.append((
                            name, pre_name,
                            _with_reg_value(
                                call_pre, register,
                                call_pre.regs.sel(register) ^ 1)))
                    source = (s0.regs.sel(2) + 64) & _M64
                    for word, offset in enumerate((0, 8, 16)):
                        mutations.append((
                            f"child-word-{word}", ret_name,
                            _with_mem_value(
                                child_ret, source + offset, 8,
                                returned[word] ^ 1)))
                    mutations.append((
                        "final-counter", "state_exit",
                        _with_reg_value(
                            machine_exit, 16,
                            machine_exit.regs.sel(16) ^ 1)))
                    for word, offset in enumerate((0, 8, 16)):
                        mutations.append((
                            f"final-word-{word}", "state_exit",
                            _with_mem_value(
                                machine_exit, destination + offset, 8,
                                returned[word] ^ 1)))
                    originals = {
                        pre_name: call_pre,
                        ret_name: child_ret,
                        "state_exit": machine_exit,
                    }
                    for name, state_name, mutant in mutations:
                        ev.env.update(originals)
                        ev.env[state_name] = mutant
                        if ev.ev(form[0][1]):
                            projection_audit["mutations"] += 1
                        else:
                            out.append(("PROJECTION-ARGS-MUTANT-SURVIVED",
                                        sp["field"], name))
                    ev.env.update(originals)
                    projection_audit["fields"].add(residual)
            elif residual in ("hCall", "hCallTooMany") \
                    and projection_audit is not None \
                    and sp["field"] not in projection_audit["fields"]:
                query_name = sp["field"]
                state_names = {row["name"]: row["state"]
                               for row in extensions}
                originals = {"state_exit": machine_exit}
                target_names = {"state_exit": "state_exit"}
                if query_name == "hCallCallee":
                    call_pre_name = state_names.get("pre-callee-eval")
                    call_pre = checkpoints.get(0x800031BC)
                    if call_pre_name is None or call_pre is None:
                        out.append(("PROJECTION-CALL-MUTATION", query_name,
                                    "missing callee-call checkpoint"))
                    else:
                        selected_name = _selected_state_binding(
                            ev, call_pre_name)
                        originals[selected_name] = call_pre
                        target_names["pre-callee-eval"] = selected_name
                if (query_name != "hCallCallee"
                        or "pre-callee-eval" in target_names):
                    for name, target, mutant in _call_post_mutants(
                            query_name, s0, machine_exit, checkpoints):
                        ev.env.update(originals)
                        ev.env[target_names[target]] = mutant
                        if ev.ev(form[0][1]):
                            projection_audit["call_mutations"] += 1
                        else:
                            out.append(("PROJECTION-CALL-MUTANT-SURVIVED",
                                        query_name, name))
                    ev.env.update(originals)
                    projection_audit["fields"].add(query_name)
            elif residual == "hSBlock" and projection_audit is not None \
                    and sp["field"] not in projection_audit["fields"]:
                states = {row["name"]: row["state"] for row in extensions}
                if sp["field"] == "hSBlock":
                    pre_name = states.get("pre-env-new")
                    ret_name = states.get("post-env-new")
                    setup_name = states.get("post-env-new-setup")
                    call_pre = checkpoints.get(0x80004190)
                    env_ret = checkpoints.get(0x80004194)
                    setup = checkpoints.get(0x800041A0)
                    if not all((pre_name, ret_name, setup_name, call_pre,
                                env_ret, setup)):
                        out.append(("PROJECTION-BLOCK-MUTATION", sp["field"],
                                    "missing env_new checkpoint"))
                    else:
                        inner = env_ret.regs.sel(10)
                        mutations = [
                            ("parent-abi", pre_name,
                             _with_reg_value(call_pre, 10,
                                             call_pre.regs.sel(10) ^ 1)),
                            ("returned-inner", ret_name,
                             _with_reg_value(env_ret, 10, inner ^ 1)),
                            ("count", ret_name,
                             _with_mem_value(env_ret, inner, 4, 1)),
                            ("cap", ret_name,
                             _with_mem_value(env_ret, inner + 4, 4, 1)),
                            ("names", ret_name,
                             _with_mem_value(env_ret, inner + 8, 8, 1)),
                            ("vals", ret_name,
                             _with_mem_value(env_ret, inner + 16, 8, 1)),
                            ("parent", ret_name,
                             _with_mem_value(
                                 env_ret, inner + 24, 8,
                                 s0.regs.sel(12) ^ 1)),
                            ("setup-inner", setup_name,
                             _with_reg_value(setup, 19,
                                             setup.regs.sel(19) ^ 1)),
                            ("setup-index", setup_name,
                             _with_reg_value(setup, 16, 1)),
                            ("setup-stmt", setup_name,
                             _with_reg_value(setup, 8,
                                             setup.regs.sel(8) ^ 1)),
                            ("setup-interp", setup_name,
                             _with_reg_value(setup, 9,
                                             setup.regs.sel(9) ^ 1)),
                            ("setup-ret", setup_name,
                             _with_reg_value(setup, 18,
                                             setup.regs.sel(18) ^ 1)),
                            ("helper-output-length", ret_name,
                             St(env_ret.mem, env_ret.regs, env_ret.out,
                                env_ret.out_len + 1)),
                            ("helper-output-byte", ret_name,
                             _with_output_byte(
                                 env_ret, env_ret.out_len,
                                 env_ret.out.sel(env_ret.out_len) ^ 1)),
                            ("setup-output-length", setup_name,
                             St(setup.mem, setup.regs, setup.out,
                                setup.out_len + 1)),
                            ("setup-output-byte", setup_name,
                             _with_output_byte(
                                 setup, setup.out_len,
                                 setup.out.sel(setup.out_len) ^ 1)),
                        ]
                        originals = {
                            pre_name: call_pre,
                            ret_name: env_ret,
                            setup_name: setup,
                            "state_exit": machine_exit,
                        }
                        for name, state_name, mutant in mutations:
                            ev.env.update(originals)
                            ev.env[state_name] = mutant
                            if ev.ev(form[0][1]):
                                projection_audit["block_mutations"] += 1
                            else:
                                out.append((
                                    "PROJECTION-BLOCK-MUTANT-SURVIVED",
                                    sp["field"], name))
                        ev.env.update(originals)
                        projection_audit["fields"].add(sp["field"])
                elif sp["field"] == "hSBlockIter":
                    pre_name = states.get("pre-child-exec")
                    call_pre = checkpoints.get(0x800041C4)
                    if not all((pre_name, call_pre)):
                        out.append(("PROJECTION-BLOCK-MUTATION", sp["field"],
                                    "missing recursive-child checkpoint"))
                    else:
                        mutations = []
                        for register, name in (
                                (2, "call-sp"), (10, "call-interp"),
                                (11, "call-stmt"), (12, "call-env"),
                                (13, "call-ret")):
                            mutations.append((
                                name, pre_name,
                                _with_reg_value(
                                    call_pre, register,
                                    call_pre.regs.sel(register) ^ 1)))
                        originals = {
                            pre_name: call_pre,
                            "state_exit": machine_exit,
                        }
                        for name, state_name, mutant in mutations:
                            ev.env.update(originals)
                            ev.env[state_name] = mutant
                            if ev.ev(form[0][1]):
                                projection_audit["block_mutations"] += 1
                            else:
                                out.append((
                                    "PROJECTION-BLOCK-MUTANT-SURVIVED",
                                    sp["field"], name))
                        ev.env.update(originals)
                        projection_audit["fields"].add(sp["field"])
                else:
                    # Each status query contains one branch and no memory or
                    # output instruction.  Mutate each transported component
                    # independently.  Unlike the child-boundary audit, these
                    # slots are consumed only by the matching terminal route.
                    address = 0x800041C8
                    mutations = (
                        ("route-status", _with_reg_value(
                            machine_exit, 10,
                            machine_exit.regs.sel(10) ^ 1)),
                        ("route-memory-byte", _with_mem_value(
                            machine_exit, address, 1,
                            machine_exit.mem.sel(address) ^ 1)),
                        ("route-output-length", St(
                            machine_exit.mem, machine_exit.regs,
                            machine_exit.out, machine_exit.out_len + 1)),
                        ("route-output-byte", _with_output_byte(
                            machine_exit, machine_exit.out_len,
                            machine_exit.out.sel(machine_exit.out_len) ^ 1)),
                    )
                    original = machine_exit
                    for name, mutant in mutations:
                        ev.env["state_exit"] = mutant
                        if ev.ev(form[0][1]):
                            projection_audit["block_mutations"] += 1
                        else:
                            out.append((
                                "PROJECTION-BLOCK-MUTANT-SURVIVED",
                                sp["field"], name))
                    ev.env["state_exit"] = original
                    projection_audit["fields"].add(sp["field"])
            elif residual in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop") \
                    and projection_audit is not None \
                    and sp["field"] not in projection_audit["fields"]:
                original = machine_exit
                for name, mutant in _while_post_mutants(
                        sp["field"], s0, machine_exit):
                    ev.env["state_exit"] = mutant
                    if ev.ev(form[0][1]):
                        projection_audit["while_mutations"] += 1
                    else:
                        out.append((
                            "PROJECTION-WHILE-MUTANT-SURVIVED",
                            sp["field"], name))
                ev.env["state_exit"] = original
                projection_audit["fields"].add(sp["field"])
        except (EvalError, ValueError) as exc:
            out.append(("PROJECTION-SMT-EVAL", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] {exc}"))
    bad = []
    for r in range(1, 32):
        want, got = tr.reg(exit_row, r), exit_st.regs.sel(r)
        if want != got:
            bad.append(f"x{r}: encoder {got:#x} machine {want:#x}")
    if bad:
        out.append(("EXIT-REGS", sp["field"],
                    f"[{tr.name}@{tr.step[lo]}] state_exit disagrees with the machine "
                    f"at {tr.pc[exit_row]:#x}: " + "; ".join(bad[:6])
                    + (f" (+{len(bad)-6} more)" if len(bad) > 6 else "")))
    _, _, output_known = _trace_output_state(tr, exit_row)
    if output_known:
        output_bad = _output_mismatches(exit_st, machine_exit)
        if output_bad:
            out.append(("EXIT-OUTPUT", sp["field"],
                        f"[{tr.name}@{tr.step[lo]}] state_exit output disagrees "
                        "with the machine: " + "; ".join(output_bad)))
    if mem.unknown:
        # A suffix audit may have evaluated several candidate terms before the
        # unknown byte became visible.  Do not report those attempts as tested
        # facts or killed mutants.
        if suffix_snapshot is not None:
            suffix_audit.clear()
            suffix_audit.update(suffix_snapshot)
        out.append(("MEM-UNKNOWN", sp["field"],
                    f"[{tr.name}@{tr.step[lo]}] the term read {len(mem.unknown)} byte(s) "
                    f"the trace and the image both leave undefined "
                    f"(first {sorted(mem.unknown)[0]:#x})"))
    # Use the emitter's guarded write manifest.  Recording evaluator side
    # effects while probing guards also records stores from rejected branches.
    dep = term_deps(q, chosen)
    fp, skipped = emitted_footprint(q, ev, write_rows)
    if skipped:
        out.append(("WRITE-EVAL", sp["field"],
                    f"[{tr.name}@{tr.step[lo]}] {skipped} emitted write rows "
                    "could not be evaluated"))
    bad_bytes = _written_byte_mismatches(exit_st, machine_exit, fp)
    if bad_bytes:
        address, encoded_byte, machine_byte = bad_bytes[0]
        out.append(("WRITE-VALUE", sp["field"],
                    f"[{tr.name}@{tr.step[lo]}] {len(bad_bytes)} byte(s) at "
                    "the encoder's direct write footprint have wrong final values; "
                    f"first {address:#x}: encoder {encoded_byte:#04x}, "
                    f"machine {machine_byte:#04x}"))
    covered = list(orc.resolved)
    # Consistency witnesses depend only on the concrete encoder/machine/oracle
    # agreement.  Certificate availability, production-post parsing, and
    # mutation-audit findings must not create a circular prerequisite for the
    # pins used to obtain a solver verdict.
    if consistency_pins is not None and not _consistency_pin_blocked(out):
        consistency_pins[sp["field"]] = _concrete_consistency_pins(
            q, ev, s0, orc, tr, lo, chosen)
    return out, sorted(fp), len(orc.resolved), dep, covered


def term_deps(q, t, acc=None):
    """Every binding a term transitively depends on."""
    acc = set() if acc is None else acc
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, str):
            if x in q.binds and x not in acc:
                acc.add(x)
                stack.append(q.binds[x])
        elif isinstance(x, list):
            stack.extend(x)
    return acc


def machine_footprint(tr, img, lo, hi, d0, covered=(), exact_targets=()):
    """Every byte the SPAN ITSELF writes.

    Stores at the span's own depth, minus the rows a summary covers.  A CALLEE's
    stores are at a deeper depth and drop out on their own, but a LOOP summary's
    body runs at the span's depth and its stores belong to the summary, not to
    the chain: `loop_0x800031dc` is the argument-marshalling loop, and its 24
    spilled bytes are exactly the ones the encoder was accused of missing."""
    skip = set()
    for sym, a, b in covered:
        skip.update(range(a if sym.startswith("loop_") else a + 1, b))
    # Exact-inline helper bodies are represented instruction-for-instruction in
    # the query, so their deeper call rows belong to the encoder footprint too.
    inline_rows = set()
    for k in range(lo, hi):
        if tr.depth[k] != d0:
            continue
        ins = decode(tr.pc[k], img.word(tr.pc[k]))
        if not is_call(ins) or ins.kind != "jal" or ins.target not in exact_targets:
            continue
        j = k + 1
        while j < hi and tr.depth[j] > d0:
            inline_rows.add(j)
            j += 1
    out = set()
    for k in range(lo, hi):
        if k in skip:
            continue
        if (tr.depth[k] == d0 or k in inline_rows) and tr.mk[k] == MK_STORE \
                and not _is_mmio_store(tr.maddr[k], tr.mw[k]):
            for j in range(tr.mw[k]):
                out.add((tr.maddr[k] + j) & M64)
    return out


def emitted_footprint(q, ev, wr_rows):
    """`<bmc>/writes/<field>.tsv` evaluated on this execution: the addresses the
    encoder RECORDS as its store footprint, which is the table the campaign's
    frame, StoreRepr and code-preservation posts are all decided against."""
    from difftest_eval import parse_all
    out, skipped = set(), 0
    for r in wr_rows:
        g, w, a = r.get("guard", ""), r.get("width", "0"), r.get("addr", "")
        if not a or not w.isdigit() or int(w) == 0:
            continue
        try:
            if g and g in q.binds and not ev.ev(g):
                continue
            base = ev.ev(parse_all(a)[0] if a.startswith("(") else a)
        except Exception:
            skipped += 1
            continue
        for j in range(int(w)):
            out.add((base + j) & M64)
    return out, skipped


def _written_byte_mismatches(encoded, machine, addresses):
    """Written addresses whose encoded and observed final bytes disagree."""
    out = []
    for address in sorted(set(addresses)):
        encoded_byte = encoded.mem.sel(address)
        machine_byte = machine.mem.sel(address)
        if encoded_byte != machine_byte:
            out.append((address, encoded_byte, machine_byte))
    return out


def _output_mismatches(encoded, machine, limit=6):
    """Length and byte disagreements between encoded and observed output."""
    out = []
    if encoded.out_len != machine.out_len:
        out.append(f"length: encoder {encoded.out_len} machine {machine.out_len}")
    for index in range(min(encoded.out_len, machine.out_len)):
        encoded_byte = encoded.out.sel(index)
        machine_byte = machine.out.sel(index)
        if encoded_byte != machine_byte:
            out.append(
                f"byte {index}: encoder {encoded_byte:#x} machine {machine_byte:#x}")
            if len(out) >= limit:
                break
    return out


def phase3b(traces, img, enc_dir, bmc_dir, per_span=8, only=None, counts=None,
            extensions=None, production_posts=None, production_premises=None,
            exact_targets=(), production_suffixes=None,
            production_suffix_posts=None, suffix_audit=None,
            projection_audit=None, consistency_pins=None, query_effects=None):
    spans = read_tsv(os.path.join(bmc_dir, "spans.tsv"))
    arms = {a["field"]: a for a in read_tsv(os.path.join(enc_dir, "armdispatch.tsv"))}
    loops = read_tsv(os.path.join(enc_dir, "loops.tsv"))
    exits_of = {int(r["header"], 16): {int(x, 16) for x in r["exits"].split(",") if x}
                for r in loops}
    noret = {int(r["target"], 16) for r in read_tsv(os.path.join(enc_dir, "noreturn.tsv"))}
    fstarts = {int(r["entry"], 16) for r in read_tsv(os.path.join(enc_dir, "funcstarts.tsv"))}
    dsites = read_tsv(os.path.join(enc_dir, "dispatchsites.tsv"))
    arms_at = {int(r["site"], 16): [int(x, 16) for x in r["arms"].split(",")] for r in dsites}
    findings, rows = [], []
    extensions = extensions or {}
    production_posts = production_posts or {}
    production_premises = production_premises or {}
    production_suffixes = production_suffixes or {}
    production_suffix_posts = production_suffix_posts or {}
    query_effects = query_effects or {}
    for sp in spans:
        f = sp["field"]
        residual = sp.get("residual", f)
        if only and f not in only and residual not in only:
            continue
        qp = os.path.join(bmc_dir, "queries", f + ".smt2")
        if not os.path.exists(qp):
            findings.append(("NO-QUERY", f, "the encoder wrote no query for this span"))
            continue
        a = arms.get(f)
        entry, stop = int(sp["entry"], 16), int(sp["stop"], 16)
        if a is None:
            rlo, rhi = int(sp["region_lo"], 16), int(sp["region_hi"], 16)
            arm = entry
            ret_exit = sp["ret_exit"].lower() == "true"
        else:
            rlo, rhi = int(a["region_lo"], 16), int(a["region_hi"], 16)
            arm, ret_exit = int(a["arm"], 16), a["ret_exit"].lower() == "true"
        if counts is not None and counts.get(f, 0) >= per_span:
            continue
        q = Query(open(qp).read())
        wr_rows = read_tsv(os.path.join(bmc_dir, "writes", f + ".tsv")) \
            if os.path.exists(os.path.join(bmc_dir, "writes", f + ".tsv")) else []
        done = counts.get(f, 0) if counts is not None else 0
        fp_ok = fp_bad = 0
        for tr in traces:
            if done >= per_span:
                break
            for i in range(tr.n):
                if done >= per_span:
                    break
                if tr.pc[i] != entry:
                    continue
                d0 = tr.depth[i]
                kind, j, _ = walk_span(tr, img, i, d0, rlo, rhi, stop, ret_exit,
                                       noret, fstarts, arms_at)
                if kind not in EXIT_KINDS:
                    continue
                if arm != entry:
                    k, on = i, False
                    while k <= j:
                        if tr.depth[k] == d0 and tr.pc[k] == arm:
                            on = True
                            break
                        k += 1
                    if not on:
                        continue
                try:
                    fs, fp, nres, dep, cov = phase3b_instance(
                        q, tr, img, sp, i, j + 1, d0, exits_of, j,
                        extensions.get(f, ()), residual,
                        production_posts.get(f, production_posts.get(residual)),
                        production_premises.get(f, production_premises.get(residual)),
                        wr_rows, exact_targets,
                        production_suffixes.get(f, production_suffixes.get(residual)),
                        production_suffix_posts.get(
                            f, production_suffix_posts.get(residual)), suffix_audit,
                        projection_audit, consistency_pins)
                except (EvalError, RecursionError) as e:
                    fs, fp, nres, dep, cov = [("EVAL", f, f"[{tr.name}@{tr.step[i]}] {e}")], [], 0, set(), []
                if fs is None:      # out of the span's scope: not an instance
                    continue
                instance_findings = list(fs)
                findings += instance_findings
                mfp = machine_footprint(tr, img, i, j + 1, d0, cov, exact_targets)
                efp = set(fp)
                # a footprint is only comparable when the exit state was
                # determined; a tainted path has no path to compare
                extra, missing = (sorted(efp - mfp), sorted(mfp - efp)) if dep else ([], [])
                if extra or missing:
                    fp_bad += 1
                    footprint_finding = ("FOOTPRINT", f,
                        f"[{tr.name}@{tr.step[i]}] the chain's stores differ from the "
                        f"machine's: {len(extra)} address(es) the encoder writes and the "
                        f"machine does not"
                        + (f" (first {extra[0]:#x})" if extra else "")
                        + f", {len(missing)} the machine writes and the encoder does not"
                        + (f" (first {missing[0]:#x})" if missing else ""))
                    findings.append(footprint_finding)
                    instance_findings.append(footprint_finding)
                    if consistency_pins is not None:
                        consistency_pins.pop(f, None)
                else:
                    fp_ok += 1
                effect = query_effects.get(f)
                if effect is not None:
                    effect_findings = observed_effect_findings(
                        effect, tr, i, j, mfp)
                    findings += effect_findings
                    instance_findings += effect_findings
                    if effect_findings and consistency_pins is not None:
                        consistency_pins.pop(f, None)
                row_ok = not instance_findings
                if row_ok:
                    done += 1
                mutation_summary = (
                    projection_audit.get("mutation_summary", {}).get(f, {})
                    if projection_audit is not None else {})
                rows.append(dict(field=f, trace=tr.name, step=tr.step[i], exit=kind,
                                 summaries=nres, enc_writes=len(efp),
                                 machine_writes=len(mfp),
                                 extensions=len(extensions.get(f, ())),
                                 residual_post="yes" if residual in PROJECTED_FIELDS else "n/a",
                                 agree="yes" if row_ok else "no",
                                 mutations_expected=mutation_summary.get(
                                     "mutations_expected", 0),
                                 mutations_killed=mutation_summary.get(
                                     "mutations_killed", 0),
                                 certificates_excluded=mutation_summary.get(
                                     "certificates_excluded", 0)))
        if counts is not None:
            counts[f] = done
    return findings, rows


# ---------------------------------------------------------- error-family audit
# This is an independent inventory of the actual proof ELF.  It is deliberately
# not generated from m5_error_routing.tsv: that table is one of the subjects
# checked below.  The two parser-unconstructible fallback sites are still part
# of the 19-site machine inventory.
_ERROR_JAL_SITES = {
    0x80002E90: "assert-arity",
    0x80002EBC: "assert-falsy",
    0x800034E4: "assignment-unbound",
    0x80003950: "unknown-binary-operator",
    0x80003B54: "unknown-expression-kind",
    0x80003B9C: "minus-or-neg-non-int",
    0x80003BC8: "modulo-by-zero",
    0x80003C10: "modulo-non-int",
    0x80003C7C: "multiply-non-int",
    0x80003CC4: "call-depth",
    0x80003CE8: "closure-break-or-continue",
    0x80003D14: "division-by-zero",
    0x80003D5C: "addition-non-int",
    0x80003DA0: "closure-arity",
    0x80003DE8: "not-callable",
    0x80003E98: "comparison-non-int",
    0x80003F58: "division-non-int",
    0x80003FAC: "undefined-variable",
    0x80003FDC: "more-than-32-call-arguments",
}

_UNCONSTRUCTIBLE_ERROR_SITES = {
    0x80003950: "the parser cannot construct an unknown BinOp token",
    0x80003B54: "the parser cannot construct an unknown Expr kind",
}

# A trace name determines the test's semantic derivation context; the terminal
# PC is separately checked against the machine.  Keeping this table in Python,
# as well as a human-readable tag in each .wl file, makes either side drifting a
# test failure rather than silently changing the oracle.
_ERROR_CASE_SITES = {
    "dt_err_assert_arity": 0x80002E90,
    "dt_err_assert_fail": 0x80002EBC,
    "dt_err_assign_unbound": 0x800034E4,
    "dt_err_minus_type": 0x80003B9C,
    "dt_err_minus_rhs_type": 0x80003B9C,
    "dt_err_neg_type": 0x80003B9C,
    "dt_err_mod_zero": 0x80003BC8,
    "dt_err_mod_lhs_type": 0x80003C10,
    "dt_err_mod_rhs_type": 0x80003C10,
    "dt_err_mul_type": 0x80003C7C,
    "dt_err_mul_rhs_type": 0x80003C7C,
    "dt_err_depth": 0x80003CC4,
    "dt_err_escape": 0x80003CE8,
    "dt_err_div_zero": 0x80003D14,
    "dt_err_plus_type": 0x80003D5C,
    "dt_err_plus_rhs_type": 0x80003D5C,
    "dt_err_arity": 0x80003DA0,
    "dt_err_not_callable": 0x80003DE8,
    "dt_err_cmp_type": 0x80003E98,
    "dt_err_cmp_rhs_type": 0x80003E98,
    "dt_err_div_lhs_type": 0x80003F58,
    "dt_err_div_rhs_type": 0x80003F58,
    "dt_err_too_many_args": 0x80003FDC,
}

for _error_case in (
        "and_lhs", "and_rhs", "assign_rhs", "binary_lhs", "binary_rhs",
        "block", "call_arg_head", "call_arg_tail", "call_body", "call_callee",
        "for_body", "for_cond", "for_init", "for_loop", "for_step", "if_cond",
        "if_else", "if_then", "or_lhs", "or_rhs", "return_expr",
        "unary_operand", "var_init", "var_undef", "while_body", "while_cond",
        "while_loop"):
    _ERROR_CASE_SITES["dt_err_" + _error_case] = 0x80003FAC
_ERROR_CASE_SITES["dt_err_top_abrupt"] = None

_ERROR_CASE_PREMISES = {
    "dt_err_assert_arity": ("hAssertArity", "hCallC", "hExpr", "hSeqHead"),
    "dt_err_assert_fail": ("hAssertFail", "hCallC", "hExpr", "hSeqHead"),
    "dt_err_assign_unbound": ("hAssignUnbound", "hExpr", "hSeqHead"),
    "dt_err_neg_type": ("hNegType", "hExpr", "hSeqHead"),
    "dt_err_not_callable": ("hNotCallable", "hCallC", "hExpr", "hSeqHead"),
    "dt_err_arity": ("hArity", "hCallC", "hExpr", "hSeqTail"),
    "dt_err_depth": ("hDepth", "hCallC", "hBody", "hRet", "hSeqHead", "hSeqTail"),
    "dt_err_escape": ("hEscape", "hCallC", "hExpr", "hSeqTail"),
    "dt_err_var_undef": ("hVarUndef", "hExpr", "hSeqHead"),
    "dt_err_assign_rhs": ("hVarUndef", "hAssignE", "hExpr", "hSeqTail"),
    "dt_err_binary_lhs": ("hVarUndef", "hBinaryL", "hExpr", "hSeqHead"),
    "dt_err_binary_rhs": ("hVarUndef", "hBinaryR", "hExpr", "hSeqHead"),
    "dt_err_or_lhs": ("hVarUndef", "hOrL", "hExpr", "hSeqHead"),
    "dt_err_or_rhs": ("hVarUndef", "hOrR", "hExpr", "hSeqHead"),
    "dt_err_and_lhs": ("hVarUndef", "hAndL", "hExpr", "hSeqHead"),
    "dt_err_and_rhs": ("hVarUndef", "hAndR", "hExpr", "hSeqHead"),
    "dt_err_unary_operand": ("hVarUndef", "hUnaryE", "hExpr", "hSeqHead"),
    "dt_err_call_callee": ("hVarUndef", "hCallF", "hExpr", "hSeqHead"),
    "dt_err_call_arg_head": (
        "hVarUndef", "hArgsHead", "hCallArgs", "hExpr", "hSeqHead"),
    "dt_err_call_arg_tail": (
        "hVarUndef", "hArgsHead", "hArgsTail", "hCallArgs", "hExpr", "hSeqHead"),
    "dt_err_call_body": (
        "hVarUndef", "hExpr", "hSeqHead", "hBody", "hCallC", "hSeqTail"),
    "dt_err_var_init": ("hVarUndef", "hVarInit", "hSeqHead"),
    "dt_err_block": ("hVarUndef", "hExpr", "hSeqHead", "hBlock"),
    "dt_err_if_cond": ("hVarUndef", "hIfCond", "hSeqHead"),
    "dt_err_if_then": ("hVarUndef", "hExpr", "hIfThen", "hSeqHead"),
    "dt_err_if_else": ("hVarUndef", "hExpr", "hIfElse", "hSeqHead"),
    "dt_err_while_cond": ("hVarUndef", "hWhileCond", "hSeqHead"),
    "dt_err_while_body": ("hVarUndef", "hExpr", "hWhileBody", "hSeqHead"),
    "dt_err_while_loop": (
        "hVarUndef", "hOrR", "hWhileCond", "hWhileLoop", "hSeqTail"),
    "dt_err_for_init": ("hVarUndef", "hExpr", "hForInit", "hSeqHead"),
    "dt_err_for_cond": ("hVarUndef", "hFlCond", "hForLoop", "hSeqHead"),
    "dt_err_for_body": (
        "hVarUndef", "hExpr", "hFlBody", "hForLoop", "hSeqHead"),
    "dt_err_for_step": ("hVarUndef", "hFlStep", "hForLoop", "hSeqHead"),
    "dt_err_for_loop": (
        "hVarUndef", "hExpr", "hFlBody", "hFlLoop", "hForLoop", "hSeqTail"),
    "dt_err_return_expr": (
        "hVarUndef", "hRet", "hSeqHead", "hBody", "hCallC", "hSeqTail"),
    "dt_err_top_abrupt": ("hTopAbrupt",),
}

for _binary_case in (
        "cmp_type", "cmp_rhs_type", "div_lhs_type", "div_rhs_type", "div_zero",
        "minus_type", "minus_rhs_type", "mod_lhs_type", "mod_rhs_type", "mod_zero",
        "mul_type", "mul_rhs_type", "plus_type", "plus_rhs_type"):
    _ERROR_CASE_PREMISES["dt_err_" + _binary_case] = (
        "hBinaryOp", "hExpr", "hSeqHead")
_ERROR_CASE_PREMISES["dt_err_too_many_args"] = ("hCallTooMany",)

_ERROR_INDEXED_PREMISES = {
    "hVarUndef", "hAssignE", "hAssignUnbound", "hBinaryL", "hBinaryR",
    "hBinaryOp", "hOrL", "hOrR", "hAndL", "hAndR", "hUnaryE", "hNegType",
    "hCallF", "hCallTooMany", "hCallArgs", "hCallC", "hArgsHead", "hArgsTail", "hNotCallable",
    "hBadClosure", "hArity", "hDepth", "hBody", "hEscape", "hAssertFail",
    "hAssertArity", "hExpr", "hVarInit", "hBlock", "hIfCond", "hIfThen",
    "hIfElse", "hWhileCond", "hWhileBody", "hWhileLoop", "hForInit", "hForLoop",
    "hRet", "hFlCond", "hFlBody", "hFlStep", "hFlLoop", "hSeqHead", "hSeqTail",
}


def _error_annotation(path):
    with open(path) as fh:
        first = fh.readline().strip()
    prefix = "// DIFFTEST-ERROR: "
    if not first.startswith(prefix):
        return None
    return tuple(x.strip() for x in first[len(prefix):].split(",") if x.strip())


def _too_many_call_order(pcs, depths):
    """Check the MAX_ARGS route independently of the error-site table.

    The callee must return before the 0x31c8 guard.  The guard must take its
    0x3fb0 error edge.  No argument-evaluation call may occur.
    """
    guards = [i for i, pc in enumerate(pcs) if pc == 0x800031C8]
    if not guards:
        return "missing 0x800031c8 MAX_ARGS guard"
    for guard in guards:
        arm_depth = depths[guard]
        callee = next((i for i in range(guard - 1, -1, -1)
                       if pcs[i] == 0x800031BC and depths[i] == arm_depth), None)
        returned = next((i for i in range((callee + 1) if callee is not None else guard, guard)
                         if pcs[i] == 0x800031C0 and depths[i] == arm_depth), None)
        edge = guard + 1 < len(pcs) and pcs[guard + 1] == 0x80003FB0 \
            and depths[guard + 1] == arm_depth
        end = next((i for i in range(guard + 1, len(pcs))
                    if pcs[i] == 0x80003FDC and depths[i] == arm_depth), len(pcs))
        arg_call = any(pcs[i] == 0x80003220 and depths[i] == arm_depth
                       for i in range((callee or 0), end))
        if callee is not None and returned is not None and edge and not arg_call:
            return None
    return ("expected callee call/return 0x31bc→0x31c0, taken "
            "0x31c8→0x3fb0 edge, and no 0x3220 argument call")


def _call_argc_guard_problem(raw32, loaded64):
    """Check the signed C-int value used by the MAX_ARGS guard.

    `ExprRepr.call` excludes words with bit 31 set.  Without that represented
    AST invariant, Nat length `> 32` does not imply the assembly's signed
    `blt 32, argc` branch.
    """
    raw32 &= 0xFFFFFFFF
    loaded64 &= M64
    expected = raw32 if raw32 < (1 << 31) \
        else raw32 | 0xFFFFFFFF00000000
    if loaded64 != expected:
        return (f"lw sign extension mismatch: raw={raw32:#x}, "
                f"x15={loaded64:#x}, expected={expected:#x}")
    if raw32 >= (1 << 31):
        return f"argc word {raw32:#x} is negative as a C int"
    if _signed64(loaded64) <= 32:
        return f"signed argc {_signed64(loaded64)} does not exceed MAX_ARGS"
    return None


def _too_many_call_guard_trace(tr):
    """Validate the concrete `lw argc; li 32; blt` boundary from a trace."""
    for guard in range(tr.n):
        if tr.pc[guard] != 0x800031C8:
            continue
        depth = tr.depth[guard]
        load = next((i for i in range(guard - 1, -1, -1)
                     if tr.depth[i] == depth and tr.pc[i] == 0x800031C0), None)
        if load is None:
            continue
        if tr.mk[load] != MK_LOAD or tr.mw[load] != 4:
            return "0x800031c0 is not recorded as a four-byte load"
        if tr.maddr[load] != ((tr.reg(load, 8) + 24) & M64):
            return "argc load address is not s0+24"
        return _call_argc_guard_problem(tr.mpre[load], tr.reg(guard, 15))
    return "missing 0x800031c8 MAX_ARGS guard"


def error_family_audit(trace_dir, source_dir, routing_path=None, out_tsv=None):
    """Classify error traces by stable jal PC and semantic constructor path.

    This does not encode hErrFam as a finite query.  A propagation constructor
    can lead to several terminal PCs, while badClosure has no executable C
    witness at all.  The audit records concrete witnesses for those dimensions.
    """
    img = Image(PROOF_ELF)
    findings, rows, premise_sites = [], [], {}
    reached, covered = set(), set()
    site_mutants = tag_mutants = 0

    # First verify that the machine inventory really is the complete set of
    # direct jal calls to runtime_error in the proof ELF.
    decoded = set()
    for pc in range(CODE_LO, CODE_HI, 4):
        ins = decode(pc, img.word(pc))
        if ins.kind == "jal" and ins.target == 0x80002DA8:
            decoded.add(pc)
    if decoded != set(_ERROR_JAL_SITES):
        findings.append(("ERROR-SITE-INVENTORY", "proof.elf",
                         f"oracle-only={sorted(set(_ERROR_JAL_SITES)-decoded)} "
                         f"elf-only={sorted(decoded-set(_ERROR_JAL_SITES))}"))

    for name, expected_site in sorted(_ERROR_CASE_SITES.items()):
        trace_path = os.path.join(trace_dir, name + ".trace.tsv")
        source_path = os.path.join(source_dir, name + ".wl")
        if not os.path.exists(trace_path):
            findings.append(("ERROR-NO-TRACE", name, "focused error trace is missing"))
            continue
        tr = Trace(trace_path, name=name)
        tr.compute_depth(img)
        hits = sorted(set(tr.pc) & set(_ERROR_JAL_SITES))
        if expected_site is None:
            stdout_path = trace_path + ".stdout"
            stdout = open(stdout_path).read() if os.path.exists(stdout_path) else ""
            if hits or "outside of a loop" not in stdout:
                findings.append(("TOP-ABRUPT", name,
                                 f"expected no jal and top-level abrupt diagnostic; hits={hits}"))
            site = None
        elif hits != [expected_site]:
            findings.append(("ERROR-PC", name,
                             f"expected {expected_site:#x}, observed "
                             + ",".join(hex(x) for x in hits)))
            site = hits[0] if len(hits) == 1 else None
        else:
            site = expected_site
            reached.add(site)
            # A swapped-site mutant must be rejected by the same exact check.
            wrong = next(p for p in _ERROR_JAL_SITES if p != expected_site)
            if hits != [wrong]:
                site_mutants += 1

        if name == "dt_err_too_many_args":
            order_problem = _too_many_call_order(tr.pc, tr.depth)
            if order_problem is not None:
                findings.append(("MAX-ARGS-ORDER", name, order_problem))
            guard_problem = _too_many_call_guard_trace(tr)
            if guard_problem is not None:
                findings.append(("MAX-ARGS-SIGNED", name, guard_problem))

        expected_tags = _ERROR_CASE_PREMISES.get(name)
        if expected_tags is None:
            findings.append(("ERROR-NO-TAGS", name, "no semantic premise path in oracle"))
            expected_tags = ()
        annotation = _error_annotation(source_path) if os.path.exists(source_path) else None
        if annotation != expected_tags:
            findings.append(("ERROR-TAG-DRIFT", name,
                             f"source={annotation} oracle={expected_tags}"))
        for tag in expected_tags:
            covered.add(tag)
            if site is not None and tag in _ERROR_INDEXED_PREMISES:
                premise_sites.setdefault(tag, set()).add(site)
            # Deleting this tag from the source annotation must be observable.
            if tuple(x for x in expected_tags if x != tag) != expected_tags:
                tag_mutants += 1
        rows.append(dict(case=name, pc="-" if site is None else f"0x{site:x}",
                         cause="top-level-abrupt" if site is None else
                               _ERROR_JAL_SITES.get(site, "unknown"),
                         premises=",".join(expected_tags)))

    # The old generated routing table assigns one fixed jal to every semantic
    # propagation constructor.  Concrete witnesses refute such an assignment
    # whenever their terminal site differs; a propagation rule has no unique PC.
    if routing_path and os.path.exists(routing_path):
        production = {}
        with open(routing_path) as fh:
            for line in fh:
                if not line.strip() or line.startswith("#"):
                    continue
                fl = line.rstrip("\n").split("\t")
                if len(fl) >= 3:
                    production[fl[0]] = int(fl[2], 16)
        for premise, sites in sorted(premise_sites.items()):
            declared = production.get(premise)
            if declared is not None and any(site != declared for site in sites):
                findings.append(("ERROR-ROUTING-REFUTED", premise,
                                 f"declares {declared:#x}; concrete witness sites="
                                 + ",".join(hex(x) for x in sorted(sites))))

    if out_tsv:
        with open(out_tsv, "w") as fh:
            fh.write("case\tstable_pc\tmachine_cause\tsemantic_premises\n")
            for row in rows:
                fh.write(f"{row['case']}\t{row['pc']}\t{row['cause']}\t"
                         f"{row['premises']}\n")

    indexed_covered = covered & _ERROR_INDEXED_PREMISES
    print(f"[errors] {len(rows)} focused traces; {len(reached)}/{len(_ERROR_JAL_SITES)} "
          f"physical jal sites reached; {len(indexed_covered)}/{len(_ERROR_INDEXED_PREMISES)} "
          "indexed Lean error premises witnessed")
    print(f"  top-level abrupt: {'covered' if 'hTopAbrupt' in covered else 'uncovered'}; "
          f"MAX_ARGS semantic error: {'covered' if 'hCallTooMany' in covered else 'uncovered'}")
    print(f"  mutations: {site_mutants}/{sum(v is not None for v in _ERROR_CASE_SITES.values())} "
          f"swapped-PC and {tag_mutants}/{sum(map(len, _ERROR_CASE_PREMISES.values()))} "
          "deleted-tag mutants killed")
    for pc in sorted(set(_ERROR_JAL_SITES) - reached):
        print(f"  unreachable: {pc:#x} {_ERROR_JAL_SITES[pc]}: "
              f"{_UNCONSTRUCTIBLE_ERROR_SITES.get(pc, 'no focused witness')}" )
    for premise in sorted(_ERROR_INDEXED_PREMISES - indexed_covered):
        why = "spec-only dangling closure; C closures are valid by construction" \
            if premise == "hBadClosure" else "no focused semantic witness"
        print(f"  unconstructible: {premise}: {why}")
    for kind, where, detail in findings:
        print(f"  {kind:24s} {where:18s} {detail}")
    return findings


# ------------------------------------------------------------------- commands
def cmd_corpus(a):
    build_corpus(a.wl, a.out, workdir=a.workdir)


def cmd_trace(a):
    run_trace(a.elf, a.out, pcs=a.trace_pcs, max_steps=a.max_steps)
    print(f"[trace] {a.elf} -> {a.out}")


def cmd_errors(a):
    findings = error_family_audit(a.traces, a.sources, a.routing, a.out)
    return 1 if findings else 0


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
    global MMIO
    MMIO = mmio_region(img)
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


def cmd_phase3b(a):
    provenance_findings = campaign_provenance_findings(a.bmc)
    if provenance_findings:
        for kind, where, detail in provenance_findings:
            print(f"  {kind:18s} {where:16s} {detail}")
        return 1
    img = Image(PROOF_ELF)
    global MMIO
    MMIO = mmio_region(img)
    only = set(a.only.split(",")) if a.only else None
    extensions, extension_findings, premise_mutations = residual_extensions(
        a.bmc, only=only)
    production_posts, producer_findings = production_residual_posts(a.bmc)
    production_premises, premise_producer_findings = \
        production_residual_premises(a.bmc)
    production_suffixes, production_suffix_posts, suffix_producer_findings = \
        production_residual_suffixes(a.bmc)
    false_route_findings, false_route_mutations = false_route_premise_audit(
        a.bmc, production_premises, only=only)
    exact_targets, exact_findings = exact_callee_manifest(a.bmc)
    arithmetic_targets, arithmetic_manifest_findings = \
        arithmetic_callee_manifest(a.bmc)
    semantic_targets, semantic_manifest_findings = semantic_helper_manifest(a.bmc)
    lean_certificates, certificate_findings = phase3b_lean_certificates(
        a.bmc, a.verdict)
    allf = (list(extension_findings) + producer_findings
            + premise_producer_findings + suffix_producer_findings
            + false_route_findings + exact_findings
            + arithmetic_manifest_findings
            + semantic_manifest_findings
            + certificate_findings
            + residual_routes(a.bmc, a.enc))
    if only is not None:
        structural_scope = set(only) | {
            "campaign", "machine_instances", "semantic_projection",
            "production_projection",
        }
        if "hSBlock" in only:
            structural_scope.update(_BLOCK_QUERIES)
        for residual in only:
            structural_scope.update(
                query for query, owner in _CALL_QUERY_FIELDS.items()
                if owner == residual)
        for field in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop"):
            if field in only:
                structural_scope.update(
                    query for query, owner in _WHILE_QUERY_FIELDS.items()
                    if owner == field)
        allf = [finding for finding in allf
                if finding[1] in structural_scope]
    allr, counts = [], {}
    helper_checked = 0
    arithmetic_checked = 0
    semantic_helper_checked = 0
    concat_checked = 0
    native_output_checked = 0
    output_loop_checked = 0
    suffix_audit = {
        "fields": set(), "facts": 0, "results": 0, "mutations": 0,
    }
    projection_audit = {"fields": set(), "mutations": 0,
                        "block_mutations": 0, "call_mutations": 0,
                        "while_mutations": 0, "assert_mutations": 0,
                        "lean_certificates": lean_certificates,
                        "mutation_summary": {}, "mutation_rows": []}
    consistency_pins = {} if a.consistency_pins else None
    query_effects = {}
    cap_path = os.path.join(a.bmc, "query-capabilities.tsv")
    residual_cap_path = os.path.join(a.bmc, "residual-capabilities.tsv")
    if not os.path.exists(cap_path) or not os.path.exists(residual_cap_path):
        allf.append(("NO-CAPABILITIES", "campaign",
                     "query/residual capability manifests are required"))
        query_caps, residual_caps = {}, []
    else:
        query_caps = {r["query"]: r for r in read_tsv(cap_path)}
        residual_caps = read_tsv(residual_cap_path)
        emitted_spans = read_tsv(os.path.join(a.bmc, "spans.tsv"))
        span_ids = {r["field"] for r in emitted_spans}
        if set(query_caps) != span_ids:
            allf.append(("CAPABILITY-MISMATCH", "machine_instances",
                         "query-capabilities.tsv does not identify exactly the emitted spans"))
        allf += query_capability_findings(query_caps)
        query_effects, effect_findings = query_effect_manifest(a.bmc, query_caps)
        allf += effect_findings
        advertised = {r["field"] for r in residual_caps
                      if r["semantic_projection"] == "yes"}
        independent = set(PROJECTED_FIELDS)
        if only is not None:
            advertised &= only
            independent &= only
        if advertised != independent:
            allf.append(("CAPABILITY-MISMATCH", "semantic_projection",
                         f"advertised-only={sorted(advertised - independent)} "
                         f"oracle-only={sorted(independent - advertised)}"))
        # Production posts are keyed by machine query.  Multiple queries may
        # project one Lean residual through four distinct machine instances.
        produced = {
            query_caps.get(query, {"field": query})["field"]
            for query in production_posts
        }
        if only is not None:
            produced &= only
        if advertised != produced:
            allf.append(("CAPABILITY-MISMATCH", "production_projection",
                         f"advertised-only={sorted(advertised - produced)} "
                         f"produced-only={sorted(produced - advertised)}"))
        spans_by_query = {row["field"]: row for row in emitted_spans}
        for query_name, (entry, stop) in _WHILE_CUTS.items():
            row = spans_by_query.get(query_name)
            if row is None:
                continue
            if int(row["entry"], 16) != entry or int(row["stop"], 16) != stop:
                allf.append((
                    "WHILE-CUT-WIDENED", query_name,
                    f"expected {entry:#x}->{stop:#x}, emitted "
                    f"{row['entry']}->{row['stop']}"))
        for query_name, (entry, stop) in _CALL_CUTS.items():
            row = spans_by_query.get(query_name)
            if row is None:
                continue
            if int(row["entry"], 16) != entry or int(row["stop"], 16) != stop:
                allf.append((
                    "CALL-CUT-WIDENED", query_name,
                    f"expected {entry:#x}->{stop:#x}, emitted "
                    f"{row['entry']}->{row['stop']}"))
        route_rows = {row["query"]: row for row in read_tsv(
            os.path.join(a.bmc, "residual-routes.tsv"))}
        call_arm = route_rows.get("hCallCallee")
        # A focused campaign need not contain the staged hCall query at all.
        # Enforce its arm identity exactly when that query was emitted; treating
        # absence from an unrelated focused campaign as a malformed hCall route
        # made otherwise-complete per-residual fuzz runs fail spuriously.
        if "hCallCallee" in query_caps and (
                call_arm is None or int(call_arm["arm"], 16) != 0x800031B0):
            allf.append(("CALL-ARM-WRONG", "hCallCallee",
                         "EvalEntry query does not select arm 0x800031b0"))
    for names in trace_batches(a.traces, a.batch):
        trs = load_traces(a.traces, img, names)
        for tr in trs:
            allf += trace_output_findings(tr)
            helper_findings, nchecked = exact_helper_findings(tr, img, exact_targets)
            allf += helper_findings
            helper_checked += nchecked
            arithmetic_findings, nchecked = arithmetic_helper_findings(
                tr, img, arithmetic_targets)
            allf += arithmetic_findings
            arithmetic_checked += nchecked
            semantic_findings, nchecked = semantic_helper_findings(
                tr, img, semantic_targets)
            allf += semantic_findings
            semantic_helper_checked += nchecked
            concat_findings, nchecked = concat_relation_findings(tr, img)
            allf += concat_findings
            concat_checked += nchecked
            native_findings, nchecked, nloops = native_output_findings(tr, img)
            allf += native_findings
            native_output_checked += nchecked
            output_loop_checked += nloops
        fs, rs = phase3b(trs, img, a.enc, a.bmc, per_span=a.per_span, only=only,
                         counts=counts, extensions=extensions,
                         production_posts=production_posts,
                         production_premises=production_premises,
                         exact_targets=exact_targets,
                         production_suffixes=production_suffixes,
                         production_suffix_posts=production_suffix_posts,
                         suffix_audit=suffix_audit,
                         projection_audit=projection_audit,
                         consistency_pins=consistency_pins,
                         query_effects=query_effects)
        allf += fs
        allr += rs
        if counts and min(counts.values()) >= a.per_span and \
                len(counts) == len(read_tsv(os.path.join(a.bmc, "spans.tsv"))):
            break
    span_rows = read_tsv(os.path.join(a.bmc, "spans.tsv"))
    selected_span_rows = [
        sp for sp in span_rows
        if only is None or sp["field"] in only
        or sp.get("residual", sp["field"]) in only
    ]
    for sp in span_rows:
        residual = sp.get("residual", sp["field"])
        if (only is None or sp["field"] in only or residual in only) \
                and not counts.get(sp["field"]):
            allf.append(("NO-INSTANCE", sp["field"],
                         "no trace runs this span's arm through to an exit"))
    if a.out:
        cols = ["field", "trace", "step", "exit", "summaries", "enc_writes",
                "machine_writes", "extensions", "residual_post", "agree",
                "mutations_expected", "mutations_killed",
                "certificates_excluded"]
        with open(a.out, "w") as fh:
            fh.write("\t".join(cols) + "\n")
            for r in allr:
                fh.write("\t".join(str(r[c]) for c in cols) + "\n")
        with open(a.out + ".findings", "w") as fh:
            fh.write("kind\twhere\tdetail\n")
            for k, w, d in allf:
                fh.write(f"{k}\t{w}\t{d}\n")
        mutation_cols = ("field", "post", "mutation", "provenance", "result")
        with open(a.out + ".mutations.tsv", "w") as fh:
            fh.write("\t".join(mutation_cols) + "\n")
            for row in projection_audit["mutation_rows"]:
                fh.write("\t".join(str(row[column])
                                   for column in mutation_cols) + "\n")
    if a.consistency_pins:
        os.makedirs(a.consistency_pins, exist_ok=True)
        for query, pins in sorted(consistency_pins.items()):
            with open(os.path.join(a.consistency_pins, query + ".smt2"), "w") as fh:
                fh.write(pins)
    nf = len({r["field"] for r in allr if r["agree"] == "yes"})
    ok = sum(1 for r in allr if r["agree"] == "yes")
    covered_extensions = sum(len(rows) for field, rows in extensions.items()
                             if counts.get(field))
    by_residual = {}
    for sp in span_rows:
        by_residual.setdefault(sp.get("residual", sp["field"]), []).append(sp["field"])
    hole_path = os.path.join(a.bmc, "residual-holes.tsv")
    holes = read_tsv(hole_path) if os.path.exists(hole_path) else []
    lean_residual_fields = {
        row["field"] for row in holes
        if row["dimension"] == "full-lean-proposition"
    }
    if only is not None:
        selected_residuals = {
            sp.get("residual", sp["field"]) for sp in selected_span_rows
        }
        holes = [row for row in holes
                 if row["field"] in only
                 or row["field"] in selected_residuals]
        residual_fields = lean_residual_fields & (
            set(only) | selected_residuals)
    else:
        residual_fields = lean_residual_fields
    covered_relations = sum(
        1 for field in SEMANTIC_PROJECTION_FIELDS
        if field in residual_fields
        if any(counts.get(q) for q in by_residual.get(field, ())))
    print(f"[phase3b] {nf}/{len(selected_span_rows)} machine instances, "
          f"{len(allr)} concrete runs driven end to end, "
          f"{ok} agree with the machine on every register of state_exit and on the "
          f"addresses and final bytes of the direct emitted stores; "
          f"{covered_extensions} residual premises and "
          f"{covered_relations}/{len(residual_fields)} Lean residual fields have a "
          "tested semantic projection")
    print(f"  exact helper contracts: {helper_checked} concrete call/return pairs checked")
    print(f"  arithmetic functional contracts: {arithmetic_checked} concrete "
          "call/return pairs checked")
    print(f"  helper-to-Lean relations: {semantic_helper_checked} concrete "
          "call/return pairs checked")
    print(f"  catDisplay concatenation relation: {concat_checked} concrete "
          "string-add paths checked")
    print(f"  native output relation: {native_output_checked} concrete "
          "print/println calls checked")
    print(f"  native output loop: {output_loop_checked} nonzero-argc "
          "printed-prefix/control-state runs checked; 8 independent mutants")
    print(f"  hArgsCons call/copy relation: "
          f"{int('hArgsCons' in projection_audit['fields'])} concrete relation "
          f"checked; {projection_audit['mutations']}/12 independent mutants killed")
    block_checked = sum(
        field in projection_audit["fields"]
        for field in _BLOCK_QUERIES)
    print(f"  hSBlock allocation/child/route relations: {block_checked}/4 concrete "
          f"relations checked; {projection_audit['block_mutations']}/29 "
          "independent mutants killed")
    call_scope = {
        query for query, owner in _CALL_QUERY_FIELDS.items()
        if only is None or query in only or owner in only
    }
    call_checked = sum(
        query in projection_audit["fields"] for query in call_scope)
    call_mutation_total = sum(
        len(_call_post_mutants(query, *_call_fixture(query)))
        for query in call_scope)
    print(f"  hCall staged machine/representation relations: "
          f"{call_checked}/{len(call_scope)} concrete relations checked; "
          f"{projection_audit['call_mutations']}/{call_mutation_total} "
          "independent mutants killed")
    assert_summary = projection_audit["mutation_summary"].get(
        "hCallAssertOk", {})
    print("  hCallAssertOk native success relation: "
          f"{projection_audit['assert_mutations']}/"
          f"{len(_ASSERT_OK_MACHINE_MUTATIONS)} independent machine mutants "
          f"killed; {assert_summary.get('certificates_excluded', 0)}/"
          f"{len(_ASSERT_OK_LEAN_CERTIFICATES)} ABI mutations excluded by exact "
          "Lean certificates")
    while_checked = sum(
        query in projection_audit["fields"] for query in _WHILE_QUERIES)
    print(f"  while condition/body/status cuts: {while_checked}/14 concrete "
          f"relations checked; {projection_audit['while_mutations']}/161 "
          "independent mutants killed")
    premise_total = sum(
        len(names) for query, names in _premise_schema().items()
        if only is None or query in only
        or (query in _BLOCK_QUERIES and "hSBlock" in only)
        or (_CALL_QUERY_FIELDS.get(query) in only)
        or (_WHILE_QUERY_FIELDS.get(query) in only))
    print(f"  semantic premise mutations: {premise_mutations}/"
          f"{premise_total} killed")
    false_route_total = sum(
        1 for field in _FALSE_ROUTE_SPECS if only is None or field in only)
    print(f"  false-route mutations: {false_route_mutations}/"
          f"{false_route_total} killed")
    suffix_fields = _ARITHMETIC_SUFFIX_FIELDS | _NONARITHMETIC_SUFFIX_FIELDS
    suffix_scope = suffix_fields if only is None else suffix_fields & only
    print(f"  candidate suffix contracts: {suffix_audit['facts']} premises and "
          f"{suffix_audit['results']} result relations checked for "
          f"{len(suffix_audit['fields'])}/{len(suffix_scope)} selected fields; "
          f"{suffix_audit['mutations']} targeted mutants killed")
    if producer_findings and production_suffix_posts:
        print("  note: suffix-only differential checks used direct production "
              "formulas from this 59-field campaign despite the tree-provenance "
              "mismatch; no current 61-field manifest claim is made")
    functional_gaps = {
        field: suffix["functional_gap"]
        for field, suffix in production_suffixes.items()
        if field in suffix_scope and "functional_gap" in suffix
    }
    if functional_gaps:
        print("  untested helper result summaries: " + "; ".join(
            f"{field}={gap[1]} ({gap[0]})"
            for field, gap in sorted(functional_gaps.items())))
    full_holes = [r for r in holes if r["dimension"] == "full-lean-proposition"]
    if full_holes:
        print(f"  unencoded: full Lean proposition for {len(full_holes)} residual fields")
    for row in holes:
        if row["dimension"] != "full-lean-proposition":
            print(f"  unencoded: {row['field']}/{row['dimension']}: {row['reason']}")
    no_relation = sorted(residual_fields - PROJECTED_FIELDS)
    if no_relation:
        print(f"  untested semantic relation: {len(no_relation)} residual fields: "
              + ",".join(no_relation))
    seen = set()
    for k, w, d in allf:
        if (k, w) in seen:
            continue
        seen.add((k, w))
        print(f"  {k:18s} {w:16s} {d}")
    return 1 if allf else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("selfcheck")
    p.set_defaults(fn=cmd_selfcheck)

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

    p = sub.add_parser("errors")
    p.add_argument("--traces", required=True)
    p.add_argument("--sources", default=os.path.join(ROOT, "c", "difftests"))
    p.add_argument("--routing", default=os.path.join(ROOT, "scripts", "m5_error_routing.tsv"))
    p.add_argument("--out")
    p.set_defaults(fn=cmd_errors)

    p = sub.add_parser("explain")
    p.add_argument("pc")
    p.add_argument("--traces", required=True)
    p.add_argument("--enc", required=True)
    p.add_argument("--limit", type=int, default=3)
    p.set_defaults(fn=cmd_explain)

    p = sub.add_parser("phase3b")
    p.add_argument("--traces", required=True)
    p.add_argument("--enc", required=True)
    p.add_argument("--bmc", default=BMC_DIR)
    p.add_argument("--batch", type=int, default=8)
    p.add_argument("--per-span", type=int, default=8)
    p.add_argument("--only")
    p.add_argument("--out")
    p.add_argument(
        "--verdict", action="append", default=[],
        help="scoped Houdini verdict TSV used to validate Lean certificate posts")
    p.add_argument(
        "--consistency-pins",
        help="write trace-derived SMT pins for clean instances into this directory")
    p.set_defaults(fn=cmd_phase3b)

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
