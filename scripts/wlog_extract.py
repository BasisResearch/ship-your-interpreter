#!/usr/bin/env python3
"""
wlog_extract.py — MECHANICALLY read an exec-arm's write-log off block-reflection.

This closes the gap WRITELOG-SMT.md named as "the next step, not a barrier": the
write-log SMT probe (scripts/writelog_smt.py) HAND-transcribed the brk/cont arm's
five spill stores. Here we EVALUATE `wlogM`/`runGM` (Vsa/Sim/BlockMem.lean) via
`experiments/smt/WlogExtract.lean` (`#eval`, read-only `lake env lean`) and parse
the result into the SYMBOLIC store list that `gen_probe.wlog_stores` consumes.

The Lean side prints, per store, a row
    (dstReg, dstOff, width, dataReg, dataLit)
where a store address is `baseOf dstReg + dstOff` (dstReg = -1 ⇒ absolute) and
the data is entry-register `dataReg` (or literal dataLit if dataReg = -1). We
re-symbolise `dstReg`/`dataReg` back to SMT terms (e.g. reg 2 → `sp`) so the SMT
query is over the SYMBOLIC frame, exactly as the hand probe was — but now the
store list is PROVABLY the block-reflection `wlogM` output (a wrong transcription
cannot slip in; `wlogM` is the source of truth).

Public API (consumed by writelog_smt.py / autoprove.py):

    extract_wlog(tag) -> {"stores":[Store...], "regs":[Reg...], "raw":...}
      Store = {addr: SMT-Int-term, width: int, data: SMT-BV64-or-None}
        addr is symbolic in the register SMT names given by `reg_names`.
        data is None for a FRAME obligation (WHERE, not WHAT) — matching the
        probe policy — unless --with-data is set.

`tag` selects a `WLOG_BEGIN <tag>` / `WLOG_END` block in WlogExtract.lean; today
`brkCont` (the probe's known arm). Adding an arm = adding an MInstr list +
`#eval dumpWlog` block there, NO change here.
"""
import subprocess, os, re, sys, json, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LEAN = os.path.join(ROOT, "experiments", "smt", "WlogExtract.lean")

# Register-index -> SMT symbol used by the frame VC. The frame probe declares
# `sp` (and `sllo`); the spilled data registers are irrelevant to a FRAME goal
# so they map to fresh symbolic bytes. Extend as arms mention more regs.
REG_SMT = {2: "sp", 1: "ra", 8: "s0", 9: "s1", 18: "s2", 19: "s3"}


def _run_lean():
    """Run `lake env lean WlogExtract.lean`, return stdout (the #eval dumps)."""
    p = subprocess.run(["lake", "env", "lean", LEAN], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    if p.returncode != 0:
        raise RuntimeError("lake env lean WlogExtract.lean FAILED:\n"
                           + (p.stdout + p.stderr)[-2000:])
    return p.stdout


# The #eval prints Lean list-of-tuples, possibly wrapped across lines. We flatten
# and pull every top-level parenthesised tuple `( .. )` in order.
def _parse_tuples(block):
    flat = re.sub(r"\s+", " ", block).strip()
    # find the outer [ ... ]
    m = re.search(r"\[(.*)\]", flat)
    if not m:
        return []
    body = m.group(1)
    rows, depth, cur = [], 0, ""
    for ch in body:
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        if ch == ")":
            depth -= 1
            if depth == 0:
                rows.append([int(x.strip()) for x in cur.split(",")])
                continue
        if depth >= 1:
            cur += ch
    return rows


def _extract_block(out, kind, tag):
    """Grab the #eval output that follows the `-- {kind}_BEGIN {tag}` marker.
    The markers are Lean line-comments in WlogExtract.lean; `lake env lean` does
    NOT echo them, so we instead rely on the ORDER of #eval outputs. We split
    stdout into the successive #eval results (each starts with `[`)."""
    chunks = re.findall(r"\[[^\[\]]*(?:\[[^\]]*\][^\[\]]*)*\]", out, re.S)
    # WlogExtract.lean emits, per tag in file order: dumpWlog then dumpRegs.
    # For the single `brkCont` tag: chunk 0 = wlog, chunk 1 = regs.
    order = {"brkCont": (0, 1)}
    wi, ri = order.get(tag, (0, 1))
    idx = wi if kind == "WLOG" else ri
    if idx >= len(chunks):
        raise RuntimeError(f"no {kind} block #{idx} for tag {tag}; got {len(chunks)} chunks")
    return chunks[idx]


def _addr_smt(dst_reg, dst_off):
    if dst_reg == -1:
        return str(dst_off)               # absolute address literal
    base = REG_SMT.get(dst_reg, f"r{dst_reg}")
    if dst_off == 0:
        return base
    if dst_off < 0:
        return f"(- {base} {-dst_off})"
    return f"(+ {base} {dst_off})"


def _data_smt(data_reg, data_lit, with_data):
    if not with_data:
        return None                       # FRAME obligation: value irrelevant
    if data_reg == -1:
        return f"((_ int2bv 64) {data_lit})"
    return REG_SMT.get(data_reg, f"r{data_reg}")


def extract_wlog(tag="brkCont", with_data=False, _cached=None):
    out = _cached if _cached is not None else _run_lean()
    wl = _parse_tuples(_extract_block(out, "WLOG", tag))
    rg = _parse_tuples(_extract_block(out, "REGS", tag))
    stores = []
    for (dr, doff, w, datar, datal) in wl:
        stores.append({"addr": _addr_smt(dr, doff), "width": w,
                       "data": _data_smt(datar, datal, with_data),
                       "raw": {"dstReg": dr, "dstOff": doff, "dataReg": datar,
                               "dataLit": datal}})
    regs = [{"reg": n, "baseReg": br, "off": off, "lit": lit}
            for (n, br, off, lit) in rg]
    reg_names = sorted({REG_SMT[s["raw"]["dstReg"]]
                        for s in stores if s["raw"]["dstReg"] in REG_SMT})
    return {"stores": stores, "regs": regs, "reg_names": reg_names, "raw": out}


def main():
    ap = argparse.ArgumentParser(description="Extract an exec-arm write-log via block-reflection.")
    ap.add_argument("--tag", default="brkCont")
    ap.add_argument("--with-data", action="store_true",
                    help="thread spilled data values (default: FRAME-only, WHERE not WHAT)")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    r = extract_wlog(args.tag, with_data=args.with_data)
    if args.json:
        r.pop("raw", None)
        print(json.dumps(r, indent=2))
        return 0
    print(f"# write-log for arm '{args.tag}' (mechanically extracted from wlogM):")
    for s in r["stores"]:
        print(f"  store  addr={s['addr']:20}  width={s['width']}  "
              f"data={s['data'] if s['data'] else '(frame: fresh)'}")
    print(f"# reg outcome ({len(r['regs'])} regs); symbolic bases: {r['reg_names']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
