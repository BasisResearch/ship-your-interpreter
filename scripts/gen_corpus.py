#!/usr/bin/env python3
"""gen_corpus.py — the remaining-case machine corpus (ANALYSIS ONLY, no Lean).

Enumerates EVERY remaining proof target and emits one summary file per case
into experiments/corpus/, plus experiments/corpus/INDEX.md (one line per case
with a shape-cluster tag).  Sources of enumeration:

  * the NOT_FOUND fields of experiments/field-census.tsv, with the supplier
    notes of experiments/assembly_skeleton.tsv and the documented arm PCs
    (jump tables reproduced from Vsa/Sim/rows/Layout{JumpTable,StmtTable,VpTable}Gen.lean);
  * the io flush chain (__swbuf_r/_fflush_r/__sflush_r, the __sbprintf
    buffered arm, the _vfprintf_r pinned fmt paths — experiments/run1-brief.md);
  * the error segments (scripts/m5_error_routing.tsv, one case per distinct
    jal site);
  * the value_print jump-table arms (rows/LayoutVpTableGen.lean) that no
    census field names directly.

Per case: disasm slice, CFG (via scripts/gen_fn.py's build_cfg/classify_loop —
IMPORTED, not forked), terminator/loop classification, calls with
landed-summary status (grepped from Vsa/**.lean theorem names), a
register/memory outcome sketch, and the record field(s) that consume it.

Usage:  python3 scripts/gen_corpus.py [-o experiments/corpus]
"""

import argparse
import bisect
import os
import re
import sys
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_fn  # noqa: E402  (the analysis functions — import, don't fork)
from genseg import lib  # noqa: E402

ROOT = lib.ROOT

# Analysis-only: gen_fn's budgets guard EMISSION of Lean; for pure CFG analysis
# of large functions (eval_expr/exec_stmt/_vfprintf_r) we lift them.
gen_fn.MAX_INSTRS = 10 ** 9
gen_fn.MAX_BRANCHES = 10 ** 9

SLICE_BLOCK_CAP = 28          # reachable-closure cap per case
SLICE_DISASM_CAP = 90         # printed disasm lines cap per case

# --------------------------------------------------------------------------
# disasm / symbols
# --------------------------------------------------------------------------

DI = lib.parse_disasm()

SYMS = []  # (addr, name), address-sorted, duplicates kept
for line in open(os.path.join(ROOT, "experiments", "disasm.txt")):
    m = gen_fn.func_re.match(line)
    if m:
        SYMS.append((int(m.group(1), 16), m.group(2)))
SYMS.sort()
SYM_ADDRS = [a for a, _ in SYMS]


def sym_at(addr):
    """First symbol whose extent contains addr (address-based, duplicate-safe)."""
    i = bisect.bisect_right(SYM_ADDRS, addr) - 1
    if i < 0:
        return None, None, None
    start, name = SYMS[i]
    end = SYMS[i + 1][0] if i + 1 < len(SYMS) else None
    return name, start, end


def entry_of(name, prefer=None):
    """Entry PC of a symbol; `prefer` disambiguates duplicates (e.g. __sbprintf)."""
    hits = [a for a, n in SYMS if n == name]
    if not hits:
        raise SystemExit(f"symbol {name} not in disasm")
    if prefer is not None and prefer in hits:
        return prefer
    return hits[0]


# --------------------------------------------------------------------------
# CFG cache (whole containing function, gen_fn.build_cfg)
# --------------------------------------------------------------------------

_CFG_CACHE = {}


def fn_cfg(fn_entry):
    """(body, blocks) of the function whose disasm starts at fn_entry."""
    if fn_entry in _CFG_CACHE:
        return _CFG_CACHE[fn_entry]
    name, start, end = sym_at(fn_entry)
    # gen_fn.build_cfg keys extents by NAME; feed it a one-entry extent map so
    # duplicate symbols resolve to the address we actually want.
    body, blocks = gen_fn.build_cfg(name, start, DI, {name: (start, end)})
    _CFG_CACHE[fn_entry] = (name, start, end, body, blocks)
    return _CFG_CACHE[fn_entry]


def slice_from(blocks, pc, cap=SLICE_BLOCK_CAP):
    """Reachable-closure block slice from pc (jump-table arm entries may land
    mid-block: the head block is then viewed from pc onward).  Returns
    (ordered block list, truncated?, split_note)."""
    by_start = {b.start: b for b in blocks}
    head, note = None, None
    if pc in by_start:
        head = by_start[pc]
    else:
        for b in blocks:
            if b.start < pc <= b.term_addr:
                # arm entry splits a block (computed-jump target, not a
                # direct-branch leader): synthesize the suffix view.
                v = gen_fn.Block(pc)
                v.instrs = [i for i in b.instrs if i.addr >= pc]
                v.term, v.kind = b.term, b.kind
                v.succs, v.callee, v.callee_pc = b.succs, b.callee, b.callee_pc
                v.is_loop_head = False
                head = v
                note = (f"arm entry 0x{pc:x} is a computed-jump target inside "
                        f"block 0x{b.start:x} (suffix view)")
                break
    if head is None:
        return [], False, f"0x{pc:x} not inside any block"
    seen, order, work = {head.start}, [head], list(head.succs)
    truncated = False
    while work:
        if len(order) >= cap:
            truncated = True
            break
        a = work.pop(0)
        if a in seen or a not in by_start:
            continue
        seen.add(a)
        b = by_start[a]
        order.append(b)
        work.extend(b.succs)
    return order, truncated, note


# --------------------------------------------------------------------------
# landed-summary index (theorem/def names across Vsa/**.lean)
# --------------------------------------------------------------------------

_DECL_RE = re.compile(r"\b(?:theorem|def|abbrev|structure)\s+([A-Za-z0-9_.']+)")
_LANDED_HINT = re.compile(r"(spec|summary|contract|fold|closed|row)", re.I)


def build_decl_index():
    names = set()
    for dirpath, _, files in os.walk(os.path.join(ROOT, "Vsa")):
        for f in files:
            if not f.endswith(".lean"):
                continue
            try:
                text = open(os.path.join(dirpath, f), encoding="utf-8").read()
            except OSError:
                continue
            names.update(_DECL_RE.findall(text))
    return sorted(names)


DECLS = build_decl_index()
_DECLS_NORM = [(n, re.sub(r"[_.']", "", n).lower()) for n in DECLS]


def landed_status(callee):
    """Landed *_spec/*_summary/*Contract/*Fold theorems whose name mentions the
    callee (normalized).  Returns (status, [names])."""
    if not callee:
        return "?", []
    needle = re.sub(r"[_.']", "", callee).lower()
    if len(needle) < 4:
        return "NONE", []
    hits = [n for n, norm in _DECLS_NORM
            if needle in norm and _LANDED_HINT.search(n)]
    hits = sorted(set(hits), key=lambda n: (len(n), n))[:6]
    return ("LANDED" if hits else "NONE"), hits


# --------------------------------------------------------------------------
# census + skeleton notes
# --------------------------------------------------------------------------

def load_census():
    out = OrderedDict()
    path = os.path.join(ROOT, "experiments", "field-census.tsv")
    for i, line in enumerate(open(path)):
        if i == 0 or not line.strip():
            continue
        cols = line.rstrip("\n").split("\t")
        out[cols[0]] = cols[1]
    return out


def load_skeleton_notes():
    out = {}
    path = os.path.join(ROOT, "experiments", "assembly_skeleton.tsv")
    for i, line in enumerate(open(path)):
        if i == 0 or not line.strip():
            continue
        cols = line.rstrip("\n").split("\t")
        if len(cols) >= 3:
            out[cols[0]] = cols[2].strip().strip('"')
    return out


# --------------------------------------------------------------------------
# the documented arm PCs (sources cited; regenerable via scripts/gen_layout.py)
# --------------------------------------------------------------------------

# eval_expr ExprKind jump table @ 0x80019f58 (rows/LayoutJumpTableGen.lean)
EVAL_ARMS = OrderedDict([
    ("EX_INT", 0x80003408), ("EX_STR", 0x80003414), ("EX_BOOL", 0x80003420),
    ("EX_NULL", 0x8000342c), ("EX_VAR", 0x80003434), ("EX_ASSIGN", 0x8000347c),
    ("EX_BINARY", 0x800034e8), ("EX_LOGICAL", 0x8000355c),
    ("EX_UNARY", 0x800035e0), ("EX_CALL", 0x800031b0), ("EX_FN", 0x800033c4),
])
# exec_stmt StmtKind jump table @ 0x80019fb8 (rows/LayoutStmtTableGen.lean)
STMT_ARMS = OrderedDict([
    ("ST_EXPR", 0x80004170), ("ST_VAR", 0x800040d8), ("ST_BLOCK", 0x8000418c),
    ("ST_IF", 0x800041e8), ("ST_WHILE", 0x8000403c), ("ST_FOR", 0x80004234),
    ("ST_RETURN", 0x80004120), ("ST_BREAK", 0x80004098),
    ("ST_CONTINUE", 0x800040b8),
])
# value_print jump table @ 0x80019f10 (rows/LayoutVpTableGen.lean)
VP_ARMS = OrderedDict([
    ("VP_NULL", 0x8000295c), ("VP_BOOL", 0x80002974), ("VP_INT", 0x80002990),
    ("VP_STR", 0x800029a4), ("VP_CLOSURE", 0x80002928), ("VP_NATIVE", 0x80002948),
])
EVAL_ARGS_LOOP_PC = 0x800031dc   # Vsa/Sim/CallEntry.lean evalArgsLoopPC
EXEC_SEQ_LOOP_PC = 0x800041a4    # Vsa/Sim/ExecSeqLoop.lean execSeqLoopPC

# census field → (entry pc | None for pure oracles, seam note)
FIELD_PC = {
    "hStr": (EVAL_ARMS["EX_STR"], "leaf arm; residual = EvalEntryStrAstRegion payload premise (wave 47g/h)"),
    "hNeg": (EVAL_ARMS["EX_UNARY"], "unary arm, neg route; child eval seam via jal"),
    "hNot": (EVAL_ARMS["EX_UNARY"], "unary arm, not route"),
    "hOrTrue": (EVAL_ARMS["EX_LOGICAL"], "logical short-circuit, or/true route"),
    "hAndFalse": (EVAL_ARMS["EX_LOGICAL"], "logical short-circuit, and/false route"),
    "hOrFalse": (EVAL_ARMS["EX_LOGICAL"], "logical fall-through, or/false route (two children)"),
    "hAndTrue": (EVAL_ARMS["EX_LOGICAL"], "logical fall-through, and/true route (two children)"),
    "hVar": (EVAL_ARMS["EX_VAR"], "var arm; env_get call bridge (env_get_found_uncond'')"),
    "hAssign": (EVAL_ARMS["EX_ASSIGN"], "assign arm; child eval + env_define store-set"),
    "hArgsNil": (EVAL_ARGS_LOOP_PC, "args loop seg-identity evalArgsLoopPC→evalArgsContPC"),
    "hArgsCons": (EVAL_ARGS_LOOP_PC, "args loop per-iter body + back-edge (loopFromBody)"),
    "hCallPrint": (EVAL_ARMS["EX_CALL"], "native print route → value_print DAG"),
    "hCallPrintln": (EVAL_ARMS["EX_CALL"], "native println route → value_print DAG"),
    "hCallAssertOk": (EVAL_ARMS["EX_CALL"], "native assert route (ok arm)"),
    "hCall": (EVAL_ARMS["EX_CALL"], "call arm head: callee eval + args loop + dispatch"),
    "hFn": (EVAL_ARMS["EX_FN"], "closure-alloc arm + native-store repr"),
    "hCallClosure": (EVAL_ARMS["EX_CALL"], "CRUX: depth guard + env_new + body ExecSeq splice"),
    "hSExpr": (STMT_ARMS["ST_EXPR"], "exec expr arm"),
    "hSRet": (STMT_ARMS["ST_RETURN"], "exec return-with-value arm"),
    "hSRetNull": (STMT_ARMS["ST_RETURN"], "exec bare-return arm (value_null glue)"),
    "hSVarNull": (STMT_ARMS["ST_VAR"], "exec var-decl no-init arm (value_null + env_define)"),
    "hSVarInit": (STMT_ARMS["ST_VAR"], "exec var-decl init arm (env_define glue)"),
    "hSBrk": (STMT_ARMS["ST_BREAK"], "exec break arm"),
    "hSCont": (STMT_ARMS["ST_CONTINUE"], "exec continue arm"),
    "hSIfNone": (STMT_ARMS["ST_IF"], "exec if, no-else route"),
    "hSIfTrue": (STMT_ARMS["ST_IF"], "exec if, then route"),
    "hSIfFalse": (STMT_ARMS["ST_IF"], "exec if, else route"),
    "hSBlock": (STMT_ARMS["ST_BLOCK"], "exec block arm (allocFrame + seq)"),
    "hSForStart": (STMT_ARMS["ST_FOR"], "exec for arm (allocFrame + init/for loop)"),
    "hSWhileFalse": (STMT_ARMS["ST_WHILE"], "exec while, cond-false exit"),
    "hSWhileBreak": (STMT_ARMS["ST_WHILE"], "exec while, break exit (shared WhileResid)"),
    "hSeqNil": (EXEC_SEQ_LOOP_PC, "seq loop identity execSeqLoopPC→execSeqContPC"),
    "hSeqConsNormal": (EXEC_SEQ_LOOP_PC, "seq loop back-edge, normal status"),
    "hSeqConsAbrupt": (EXEC_SEQ_LOOP_PC, "seq loop abrupt-exit arm"),
    "hInitStore": (0x80004308, "interp_init store build + interp_run loop setup [0x8000442c,0x8000448c) (EntrySeams doc)"),
    "hEpilogueSpill": (0x80004514, "interpNormalExitPC epilogue restore block (s5=0 latch)"),
    "hDivCorr": (None, "DIVERGENCE oracle: per-load DivCorrFamily, progress-only skeleton over exec_stmt cases — no single machine span"),
}
# the 19 binary cells + overflow arm all enter at EX_BINARY; per-op seam noted
_BIN_SEAM = {
    "hIAdd": "int cell, inline addw path", "hISub": "int cell, inline subw path",
    "hIMul": "int cell, __muldi3 seam", "hIDiv": "int cell, __divdi3 seam (no-ovf guard)",
    "hIMod": "int cell, __moddi3/div-parity seam", "hILt": "int cmp cell (slt ladder)",
    "hILe": "int cmp cell", "hIGt": "int cmp cell", "hIGe": "int cmp cell (xori route)",
    "hEq": "eq cell, value_equal seam", "hNe": "ne cell, value_equal seam",
    "hStrAddL": "str + cell (left-str), strlen/malloc/memcpy concat seam",
    "hStrAddR": "str + cell (right-str), concat seam",
    "hStrLt": "str cmp cell, strcmp seam + sign tail", "hStrLe": "str cmp cell",
    "hStrGt": "str cmp cell", "hStrGe": "str cmp cell (ge fixup tail)",
    "hDivOv": "div overflow arm (INT64_MIN / -1 wraps)",
}
for f, seam in _BIN_SEAM.items():
    FIELD_PC[f] = (EVAL_ARMS["EX_BINARY"], "binary arm dispatch; " + seam)

# io flush chain (run1-brief.md DAG, bottom-up)
IO_CHAIN = [
    ("_write", None, "tohost byte loop (counted-loop template)"),
    ("_write_r", None, "reent shim over _write"),
    ("__swrite", None, "FILE-op shim over _write_r"),
    ("_putc_r", None, "putc core: fast path + __swbuf_r spill"),
    ("_fputc_r", None, "fputc shim over _putc_r"),
    ("_fputs_r", None, "fputs over __sfvwrite_r"),
    ("_fwrite_r", None, "fwrite over __sfvwrite_r"),
    ("__sfvwrite_r", None, "BOTH arms: unbuffered (real stdout) + buffered (only under __sbprintf synthetic FILE)"),
    ("__sbprintf", 0x8000dda8, "buffered-arm detour (57i; second copy at 0x8001688c)"),
    ("__swbuf_r", None, "buffer spill + flush trigger"),
    ("__sflush_r", None, "flush core"),
    ("_fflush_r", None, "flush shim"),
    ("fflush", None, "top flush entry"),
    ("_svfprintf_r", None, "snprintf-family fmt core (landed %lld specs live HERE)"),
    ("_vfprintf_r", None, "SEPARATE compilation: pinned fmt paths %lld + %s×2; sbprintf detour at +0x39c; digit loop re-instantiates at vfprintf-local PCs"),
    ("value_print", None, "value dispatch via vp jump table 0x80019f10"),
    ("snprintf", None, "ABI wrapper (landed snprintf_lld_spec; kept for cross-ref)"),
]

IO_CONSUMERS = ("TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk "
                "(native rows) via rows/ValuePrintContract's three contracts")


# --------------------------------------------------------------------------
# per-case emission
# --------------------------------------------------------------------------

def sketch(blocks_slice):
    """Register/memory outcome sketch of a block slice."""
    wrote, loads, stores, callees, terms = [], 0, 0, [], []
    NO_RD = {"sd", "sw", "sh", "sb", "j", "jr", "ret", "beq", "bne", "blt",
             "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz",
             "bgtz", "ble", "bgt", "bgtu", "bleu"}
    for b in blocks_slice:
        instrs = b.instrs + ([b.term] if b.term else [])
        for i in instrs:
            ops = [o.strip() for o in i.ops.split(",")] if i.ops else []
            if i.mnem.startswith("l") and "(" in i.ops:
                loads += 1
            if i.mnem in ("sd", "sw", "sh", "sb"):
                stores += 1
            if i.mnem not in NO_RD and ops and re.fullmatch(r"[a-z][a-z0-9]{1,3}", ops[0]) \
                    and ops[0] not in wrote and ops[0] != "zero":
                wrote.append(ops[0])
        if b.kind in ("jal", "tailj", "jalrcall") and b.callee:
            if b.callee not in callees:
                callees.append(b.callee)
        terms.append(b.kind)
    return wrote, loads, stores, callees, terms


def cluster_tag(kind, blocks_slice, callees, has_loop):
    if kind == "oracle":
        return "oracle-no-span"
    if kind == "errsite":
        return "error-jal-seam"
    seam = set(callees)
    if kind == "io":
        return "io-loop-fold" if has_loop else "io-fold"
    if {"__divdi3", "__muldi3", "__moddi3"} & seam:
        return "libgcc-seam"
    if {"strcmp", "strlen", "memcpy", "malloc", "strdup"} & seam:
        return "str-seam"
    if "value_equal" in seam:
        return "value-equal-seam"
    if {"env_get", "env_define", "env_new"} & seam:
        return "env-seam"
    if "eval_expr" in seam or "exec_stmt" in seam:
        return "loop-arm" if has_loop else "arm-child-seam"
    if {"value_int", "value_bool", "value_str", "value_null"} & seam:
        return "value-box-tail"
    if has_loop:
        return "loop"
    if not seam and len(blocks_slice) <= 3:
        return "leaf-slot"
    return "branchy-span" if len(blocks_slice) > 3 else "straight-span"


def disasm_lines(blocks_slice, cap=SLICE_DISASM_CAP):
    out, n = [], 0
    for b in blocks_slice:
        out.append(f"  -- block 0x{b.start:x} [{b.kind}]"
                   + (" LOOP-HEAD" if b.is_loop_head else ""))
        for i in b.instrs + ([b.term] if b.term else []):
            if n >= cap:
                out.append(f"  … (disasm capped at {cap} lines)")
                return out
            out.append(f"  {i.addr:x}: {i.mnem} {i.ops}")
            n += 1
    return out


def emit_case(outdir, case_id, kind, pc, note, consumers, extra=""):
    """Build one corpus summary file; returns the INDEX line dict."""
    lines = [f"# {case_id}", "",
             f"- kind: {kind}",
             f"- consumes/consumed-by: {consumers}",
             f"- note: {note}"]
    tag, nblocks, callee_report = "oracle-no-span", 0, []
    if pc is not None:
        fname, fstart, fend, body, blocks = fn_cfg(pc)
        loop = gen_fn.classify_loop(blocks)
        sl, truncated, split_note = slice_from(blocks, pc)
        has_loop = any(b.is_loop_head for b in sl) or any(
            s <= b.term_addr for b in sl for s in b.succs if s in {x.start for x in sl})
        wrote, loads, stores, callees, terms = sketch(sl)
        tag = cluster_tag(kind, sl, callees, has_loop)
        nblocks = len(sl)
        lines += [f"- entry: 0x{pc:x} (inside `{fname}` [0x{fstart:x}, "
                  + (f"0x{fend:x}" if fend else "?") + "))",
                  f"- containing-fn CFG: {len(blocks)} blocks, "
                  f"{sum(1 for b in blocks if b.kind == 'br')} branches, "
                  f"loop-template={'yes (' + loop['ptr'] + ')' if loop else 'no'}"]
        if split_note:
            lines.append(f"- {split_note}")
        lines += ["", f"## Case slice ({nblocks} blocks"
                  + (", truncated closure" if truncated else "") + ")", ""]
        for b in sl:
            lines.append(f"- {b!r}")
        lines += ["", "## Terminator/loop classification", "",
                  f"- terminators on slice: {', '.join(sorted(set(terms)))}",
                  f"- back-edge/loop on slice: {'YES' if has_loop else 'no'}",
                  "", "## Calls (landed-summary status)", ""]
        if callees:
            for cal in callees:
                st, hits = landed_status(cal)
                callee_report.append(f"{cal}:{st}")
                lines.append(f"- `{cal}` → {st}"
                             + (f" ({', '.join(hits)})" if hits else ""))
        else:
            lines.append("- (no call seams on slice)")
        lines += ["", "## Register/memory outcome sketch", "",
                  f"- regs written on slice: {', '.join(wrote) if wrote else '(none)'}",
                  f"- loads: {loads}, stores: {stores}",
                  "", "## Disasm slice", "", "```"]
        lines += disasm_lines(sl)
        lines.append("```")
    else:
        lines += ["", "No machine span: this residual is an ORACLE/family fact "
                  "(see note); its discharge is recursor/metatheorem work, not "
                  "a seg."]
    lines.append("")
    with open(os.path.join(outdir, f"{case_id}.md"), "w") as f:
        f.write("\n".join(lines))
    return {"id": case_id, "tag": tag, "pc": pc, "nblocks": nblocks,
            "callees": callee_report, "consumers": consumers}


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", "--outdir",
                    default=os.path.join(ROOT, "experiments", "corpus"))
    args = ap.parse_args()
    os.makedirs(args.outdir, exist_ok=True)

    census = load_census()
    notes = load_skeleton_notes()
    index = []

    # 1. census NOT_FOUND fields
    missing = [f for f, st in census.items() if st != "FOUND"]
    for f in missing:
        pc, seam = FIELD_PC.get(f, (None, "NO DOCUMENTED PC — flag for triage"))
        note = seam + (" | skeleton: " + notes[f] if f in notes else "")
        kind = "oracle" if pc is None else "field"
        index.append(emit_case(args.outdir, f, kind, pc, note,
                               f"TermResidualsCore.{f}"))

    # 2. io flush chain
    for name, prefer, note in IO_CHAIN:
        pc = entry_of(name, prefer)
        index.append(emit_case(args.outdir, f"io_{name.lstrip('_')}", "io",
                               pc, note, IO_CONSUMERS))

    # 3. error segments (one case per distinct jal site)
    sites = OrderedDict()
    for i, line in enumerate(open(os.path.join(HERE, "m5_error_routing.tsv"))):
        if line.startswith("#") or not line.strip():
            continue
        cols = line.rstrip("\n").split("\t")
        premise, site_pc = cols[0], int(cols[2], 16)
        sites.setdefault(site_pc, []).append(premise)
    for site_pc, premises in sites.items():
        index.append(emit_case(
            args.outdir, f"err_{site_pc:08x}", "errsite", site_pc,
            f"jal runtime_error site; errSite_{site_pc:8x} Triple rows landed "
            f"(rows/ErrSitesBatch*); residual = hsite caller linkage",
            "ErrWork/hErrFam premises: " + ", ".join(premises)))

    # 4. value_print jump-table arms (not census fields themselves)
    for tag_name, pc in VP_ARMS.items():
        index.append(emit_case(
            args.outdir, f"vparm_{tag_name}", "field", pc,
            f"value_print arm {tag_name} (vp table 0x80019f10)",
            "hCallPrint/hCallPrintln via rows/ValuePrintContract"))

    # INDEX.md
    by_tag = {}
    for row in index:
        by_tag.setdefault(row["tag"], []).append(row["id"])
    with open(os.path.join(args.outdir, "INDEX.md"), "w") as f:
        f.write("# Remaining-case corpus index\n\n")
        f.write(f"{len(index)} cases. Generated by scripts/gen_corpus.py — "
                "analysis only, regenerate at will.\n\n")
        f.write("## Cases\n\n")
        for row in index:
            pcs = f"0x{row['pc']:x}" if row["pc"] is not None else "-"
            f.write(f"- `{row['id']}` cluster={row['tag']} entry={pcs} "
                    f"blocks={row['nblocks']} "
                    f"calls=[{', '.join(row['callees'])}] "
                    f"→ {row['consumers']}\n")
        f.write("\n## Cluster table\n\n")
        for tag in sorted(by_tag):
            f.write(f"- **{tag}** ({len(by_tag[tag])}): "
                    + ", ".join(by_tag[tag]) + "\n")
    print(f"[gen_corpus] {len(index)} cases → {args.outdir}")
    for tag in sorted(by_tag):
        print(f"  {tag}: {len(by_tag[tag])}")


if __name__ == "__main__":
    main()
