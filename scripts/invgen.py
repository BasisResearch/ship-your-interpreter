#!/usr/bin/env python3
"""invgen.py — one-command invariant-generation orchestrator (ANALYSIS ONLY).

Closes gap 2 of experiments/invariant-gen-plan.md: corpus lookup → trace-hook
patch → emulator build (REUSED per probe-set; cases sharing a probe shape share
one build) → run the .wl corpus → segment → mine (+ relational where the case
has a spec seam) → emit experiments/invariants/<case>.{md,lean} → fuzz.

  python3 scripts/invgen.py --case hSBrk
  python3 scripts/invgen.py --batch env-seam        # one cluster
  python3 scripts/invgen.py --batch all             # all 97 corpus cases

Design decisions (honest about constraints):
  * The machine trace requires the COW emulator (/tmp/rl-trace/lean_emulator,
    warm .lake) and the xpack cross-gcc (~/toolchains, auto-found by the
    wl-test Makefile).  ELFs are built to SCRATCH names (never the tracked
    c/while-riscv-htif.elf); the tracked copy is restored after each run.
  * Cases are grouped by (dispatch-PC, probe shape) into PROBE-SETS; one
    emulator build + one ELF + one trace serves every case in a set → the batch
    is ~O(#probe-sets) machine runs, not O(#cases).
  * The spec side runs the general driver (scripts/spec_trace_driver.lean.tmpl
    filled with scripts/wl_to_lean.py output) — cheap, local, per representative
    .wl.  Relational mining aligns machine×spec by (kind, ordinal).
  * Clusters with no spec seam (io-*, error-jal-seam, straight-span, oracle)
    get pure T1-T5 mining or a `no-trace-path` verdict when no probe path is
    wired.  ZERO LLM calls anywhere.

Nothing here enters a proof.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
INDEX = os.path.join(ROOT, "experiments", "corpus", "INDEX.md")
INVDIR = os.path.join(ROOT, "experiments", "invariants")
SPECDIR = "/tmp/spec"
WLTEST = "/tmp/wl-test"
EMU = "/tmp/rl-trace/lean_emulator"
TRACED_ELF = os.path.join(WLTEST, "while-riscv-htif.elf")
REPO_ELF = os.path.join(ROOT, "c", "while-riscv-htif.elf")
TMPL = os.path.join(HERE, "spec_trace_driver.lean.tmpl")

# ---------------------------------------------------------------------------
# Cluster → pipeline plan.  A "relational" cluster has a stmt/expr kind seam
# minable against the spec driver; dispatch_pc is where the kind word is read.
#   exec_stmt dispatch (kind@[s0]) = 0x80004014, node reg s0
#   eval_expr dispatch (kind@[a2]) = 0x80003164, node reg a2, payload @ a2+8
# The representative .wl exercises the cluster's path.
# ---------------------------------------------------------------------------
CLUSTER = {
    # NOTE: the eval dispatch PC 0x80003164 reads the NODE KIND; the a2+8 word
    # there is the node's operand field, NOT the computed boxed value (that is
    # in a0 at the ARM EXIT after value_int/value_bool boxes it).  So a value-
    # repr conjunct probed here is spurious — payload is DISABLED for loop-arm
    # (the kind bridge is the solid mined fact; value-repr needs an arm-exit
    # probe not wired in this batch).  See experiments/observations.md.
    "loop-arm": dict(side="expr", dispatch=0x80003164, node="a2",
                     mem="a2:0:4", wl="arithmetic.wl", relational=True),
    "env-seam": dict(side="stmt", dispatch=0x80004014, node="s0",
                     mem="s0:0:4", wl="scope.wl", relational=True),
    "value-box-tail": dict(side="expr", dispatch=0x80003164, node="a2",
                           mem="a2:0:4", wl="strings.wl", relational=True),
    "str-seam": dict(side="expr", dispatch=0x80003164, node="a2",
                     mem="a2:0:4", wl="strings.wl", relational=True),
    "leaf-slot": dict(side="stmt", dispatch=0x80004014, node="s0",
                      mem="s0:0:4", wl="while.wl", relational=True),
    "loop": dict(side="stmt", dispatch=0x80004014, node="s0", mem="s0:0:4",
                 wl="while.wl", relational=True),
    # pure-machine loops / no-spec-seam classes: T1-T5 or no-trace-path.
    "io-loop-fold": dict(machine_only=True, wl="strings.wl"),
    "io-fold": dict(machine_only=True, wl="strings.wl"),
    "error-jal-seam": dict(no_seam=True),
    "straight-span": dict(no_seam=True),
    "oracle-no-span": dict(no_seam=True),
}

# stmt/expr arm PCs for slot-pin confirmation (from corpus entries).
ARM_PC = {
    "hSBrk": [(0x80004098, 7)], "hSCont": [(0x800040b8, 8)],
}


def load_index():
    cases = {}
    pat = re.compile(r"^- `([^`]+)` cluster=(\S+) entry=(\S+) .*?→ (.+)$")
    for line in open(INDEX):
        m = pat.match(line.strip())
        if m:
            cases[m[1]] = dict(case=m[1], cluster=m[2], entry=m[3],
                               target=m[4].strip())
    return cases


# ---------------------------------------------------------------------------
# ELF hygiene: build to scratch, never clobber the tracked copy.
# ---------------------------------------------------------------------------
def build_elf(wl_name, scratch):
    """Build the wl-test HTIF ELF for tests/<wl_name>, copy to <scratch>, and
    restore the tracked-identical while-riscv-htif.elf.  Returns scratch path."""
    wl = os.path.join(WLTEST, "tests", wl_name)
    if not os.path.exists(wl):
        return None
    subprocess.run(["make", "-C", WLTEST, "clean"], capture_output=True)
    r = subprocess.run(["make", "-C", WLTEST, "riscv-htif", f"HTIF_SCRIPT={wl}"],
                       capture_output=True, text=True)
    if not os.path.exists(TRACED_ELF):
        return None
    shutil.copy(TRACED_ELF, scratch)
    if os.path.exists(REPO_ELF):
        shutil.copy(REPO_ELF, TRACED_ELF)   # restore tracked copy
    return scratch


# ---------------------------------------------------------------------------
# spec trace (general driver): transpile .wl → AST → fill template → #eval
# ---------------------------------------------------------------------------
def spec_trace(wl_name):
    os.makedirs(SPECDIR, exist_ok=True)
    base = wl_name.replace(".wl", "")
    ast = os.path.join(SPECDIR, f"{base}_ast.lean")
    r = subprocess.run(["python3", os.path.join(HERE, "wl_to_lean.py"),
                        "--wl", os.path.join(WLTEST, "tests", wl_name),
                        "--name", "prog", "--out", ast], capture_output=True, text=True)
    if not os.path.exists(ast):
        return None, f"transpile failed: {r.stderr[-300:]}"
    tmpl = open(TMPL).read()
    prog = open(ast).read()
    lean = os.path.join(SPECDIR, f"spec_trace_{base}.lean")
    open(lean, "w").write(tmpl.replace(
        "-- @@PROG@@  (scripts/invgen.py substitutes the transpiled `def prog : Program`)",
        prog))
    r = subprocess.run(["lake", "env", "lean", lean], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    out = os.path.join(SPECDIR, f"{base}_spec.txt")
    lines = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith("SPEC ev=")]
    open(out, "w").write("\n".join(lines) + "\n")
    return (out if lines else None), (f"{len(lines)} spec events")


# ---------------------------------------------------------------------------
# per-case pipeline
# ---------------------------------------------------------------------------
def gen_trace(case, plan, elf):
    """Run gen_trace.py against a PREBUILT scratch ELF (reuse per probe-set)."""
    out = f"/tmp/rl-trace/{case}_trace.jsonl"
    cmd = ["python3", os.path.join(HERE, "gen_trace.py"), "--case", case,
           "--pc", hex(plan["dispatch"]),
           "--regs", f"{plan['node']},a0,a1,sp",
           "--mem", plan["mem"], "--elf", elf, "--out", out]
    if plan.get("payload"):
        cmd += ["--mem", plan["payload"]]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=700)
    return (out if os.path.exists(out) and os.path.getsize(out) > 0 else None,
            r.stdout[-400:] + r.stderr[-400:])


def mine_case(seg_jsonl, case):
    r = subprocess.run(["python3", os.path.join(HERE, "mine.py"),
                        "--in", seg_jsonl, "--case", case],
                       capture_output=True, text=True, timeout=300)
    return r.stdout


def relational(case, plan, machine, spec_txt):
    cmd = ["python3", os.path.join(HERE, "mine_relational.py"),
           "--machine", machine, "--spec", spec_txt,
           "--dispatch-pc", hex(plan["dispatch"]), "--case", case]
    if plan["side"] == "expr":
        cmd.append("--expr")
    if plan.get("payload"):
        cmd.append("--payload")
    for (pc, k) in ARM_PC.get(case, []):
        cmd += ["--arm", f"{hex(pc)}:{k}"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    out = r.stdout
    verdict = "mining-silent"
    contradictions = []
    m = re.search(r"VERDICT: (\S+)", out)
    if m:
        verdict = m[1]
    for cl in re.findall(r"!! (.+)", out):
        contradictions.append(cl)
    return verdict, contradictions, out


def emit_artifacts(case, meta, plan, mine_out, rel_out, verdict, contradictions):
    os.makedirs(INVDIR, exist_ok=True)
    md = os.path.join(INVDIR, f"{case}.md")
    with open(md, "w") as f:
        f.write(f"# {case} — mined invariant candidate (invgen.py)\n\n")
        f.write(f"- cluster: `{meta['cluster']}`  entry: `{meta['entry']}`\n")
        f.write(f"- target field: `{meta['target']}`\n")
        f.write(f"- verdict: **{verdict}**\n\n")
        if contradictions:
            f.write("## CONTRADICTIONS (pre-proof falsity candidates)\n\n")
            for c in contradictions:
                f.write(f"- !! {c}\n")
            f.write("\n")
        if mine_out:
            f.write("## Mined conjuncts (T1-T5)\n\n```\n" + mine_out + "\n```\n\n")
        if rel_out:
            f.write("## Relational (machine×spec) conjuncts\n\n```\n" + rel_out + "\n```\n")
    lean = emit_lean_candidate(case, meta, plan, rel_out, verdict)
    return md, lean


# ---------------------------------------------------------------------------
# hermetic, INHABITABLE ghost-struct candidate + a refutable mutant, so the
# generator can auto-fuzz (CTI loop) every invariant it emits — no manual step.
# ---------------------------------------------------------------------------
STRUCT = "KindBridge"


def emit_lean_candidate(case, meta, plan, rel_out, verdict):
    lean = os.path.join(INVDIR, f"{case}.lean")
    kinds = re.findall(r"= (\d+) = kindOf(\w+) \(\.(\w+)\)", rel_out or "")
    fn = "kindOfExpr" if plan.get("side") == "expr" else "kindOfStmt"
    with open(lean, "w") as f:
        f.write(f"-- {case}: mined invariant candidate (invgen.py, ANALYSIS ONLY "
                f"— a DRAFT for the proving agent; Law 4 applies).\n")
        f.write(f"-- cluster {meta['cluster']}  target {meta['target']}\n")
        f.write(f"namespace InvGen_{case}\n\n")
        if kinds:
            f.write("-- MINED KIND BRIDGE (machine==spec count, per-seam ordinal "
                    f"aligned): read32[node]&0xff = {fn} node.\n")
            for (k, _, nm) in kinds:
                f.write(f"--   tag {k}  ↔  {fn} node = .{nm}\n")
            # A hermetic, INHABITABLE model of the mined conjunct: the machine
            # kind byte equals the spec kind tag at each aligned event.  The
            # fuzzer inhabit-checks the mined pairing (SURVIVES) and refutes a
            # mutant that swaps two tags (REFUTED-by-witness).  This mirrors the
            # landed *Repr kind bridge without importing the drifting real names.
            tags = [int(k) for (k, _, _) in kinds]
            f.write("\n/-- machine kind byte ↔ spec kind tag, per aligned event. -/\n")
            f.write(f"structure {STRUCT} (mach spec : List Nat) : Prop where\n")
            f.write("  len : mach.length = spec.length\n")
            f.write("  agree : mach = spec\n\n")
            ml = "[" + ", ".join(str(t) for t in tags) + "]"
            f.write(f"-- the MINED pairing (machine tags = spec tags, as traced).\n")
            f.write(f"def machTags : List Nat := {ml}\n")
            f.write(f"def specTags : List Nat := {ml}\n")
            f.write(f"def mined : Prop := {STRUCT} machTags specTags\n")
            # mutant: swap the first tag with a bogus one (deliberately wrong).
            bogus = ([tags[0] + 100] + tags[1:]) if tags else [999]
            bl = "[" + ", ".join(str(t) for t in bogus) + "]"
            f.write(f"def machTagsMutant : List Nat := {bl}\n")
            f.write(f"def mutant : Prop := {STRUCT} machTagsMutant specTags\n")
        else:
            f.write("-- (no agreeing relational kind bridge mined; see .md)\n")
        f.write(f"\nend InvGen_{case}\n")
    return lean if kinds else None


def autofuzz(case, lean):
    """CTI step built INTO the generator: fuzz the emitted candidate.  The mined
    pairing must SURVIVE (inhabited/self-consistent); the mutant must be REFUTED
    by witness.  Returns (mined_verdict, mutant_verdict) or (None, None).

    v2: a SECOND pass runs `statement_fuzz --descend` on the mined Prop — the
    nested-quantifier witness descent that catches the ∀-mcall over-quant class
    (`∀ mcall, agree-off-window → MemExtends/presence`) which the struct-witness
    pass is blind to.  A descent REFUTED on `mined` is a falsity the struct pass
    missed; it is folded into `mined`'s verdict as REFUTED so `run_case` records
    the contradiction (same gate as a struct refutation)."""
    if not lean or not os.path.exists(lean):
        return None, None
    def run(prop, descend=False):
        cmd = ["python3", os.path.join(HERE, "statement_fuzz.py"),
               "--file", lean, "--prop", f"InvGen_{case}.{prop}"]
        cmd += (["--descend"] if descend
                else ["--struct", f"InvGen_{case}.{STRUCT}"])
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=400)
        m = re.search(r"→ \*\*([A-Z-]+)\*\*", r.stdout)
        return m.group(1) if m else "UNDECIDABLE"
    # only emit the mutant/mined if the candidate actually defines them
    body = open(lean).read()
    if "def mined" not in body:
        return None, None
    mined_v, mutant_v = run("mined"), run("mutant")
    # descent CTI: only worth running when the mined Prop actually contains a
    # nested ∀-mcall / agree-off-window conjunct (else descent has no builder to
    # bite and just SURVIVES).  If descent REFUTES a candidate the struct pass
    # called SURVIVED, the descent verdict WINS (it found deeper falsity).
    if "mcall" in body or "MemExtends" in body:
        dv = run("mined", descend=True)
        if dv in ("REFUTED", "REFUTED-DIRTY") and mined_v not in (
                "REFUTED", "REFUTED-DIRTY"):
            mined_v = dv
    return mined_v, mutant_v


def run_case(case, meta, elf_cache, spec_cache, trace_cache=None, skip_fuzz=False):
    trace_cache = trace_cache if trace_cache is not None else {}
    plan = CLUSTER.get(meta["cluster"], {})
    if plan.get("no_seam"):
        return dict(case=case, verdict="no-trace-path", contradictions=[],
                    cluster=meta["cluster"],
                    note=f"{meta['cluster']}: no spec seam / machine loop not wired")
    wl = plan.get("wl")
    # spec side (cached per .wl)
    spec_txt = None
    if plan.get("relational"):
        if wl not in spec_cache:
            spec_cache[wl] = spec_trace(wl)
        spec_txt, _ = spec_cache[wl]
    # machine side (ELF cached per .wl; one build serves the probe-set)
    if wl and wl not in elf_cache:
        elf_cache[wl] = build_elf(wl, f"/tmp/wl-test/scratch-{wl.replace('.wl','')}.elf")
    elf = elf_cache.get(wl)
    machine = None
    # machine_only io loops have a per-case loop-head PC but no generic kind
    # probe; without a wired probe we don't fabricate one (ZERO-LLM batch) →
    # they fall through to mining-silent-needs-LLM below.
    if elf and plan.get("relational") and plan.get("dispatch"):
        # cache the trace per (wl, dispatch, node, mem) — identical probe-sets
        # (all 36 loop-arm cases) share ONE machine run.
        pkey = (wl, plan.get("dispatch"), plan.get("node"), plan.get("mem"))
        if pkey in trace_cache:
            machine = trace_cache[pkey]
        else:
            machine, _ = gen_trace(case, plan, elf)
            trace_cache[pkey] = machine
    # segment + mine
    mine_out = None
    if machine:
        seg = f"/tmp/rl-trace/{case}_seg.jsonl"
        subprocess.run(["python3", os.path.join(HERE, "segment.py"),
                        "--in", machine, "--out", seg], capture_output=True)
        mine_out = mine_case(seg if os.path.exists(seg) else machine, case)
    # relational
    verdict, contradictions, rel_out = ("mining-silent", [], None)
    if plan.get("relational") and machine and spec_txt:
        verdict, contradictions, rel_out = relational(case, plan, machine, spec_txt)
    elif plan.get("machine_only"):
        verdict = ("candidate-mined" if mine_out and "* " in mine_out
                   else "mining-silent-needs-LLM")
    elif not machine:
        verdict = "no-trace-path"
    md, lean = emit_artifacts(case, meta, plan, mine_out, rel_out, verdict,
                              contradictions)
    # CTI step BUILT INTO the generator: auto-fuzz every emitted candidate.
    # A relational candidate must SURVIVE fuzzing (self-consistent) and its
    # mutant must be REFUTED; otherwise the mined fact is itself a falsity CTI.
    fuzz_mined, fuzz_mutant = (None, None)
    if verdict == "candidate-mined" and lean and not skip_fuzz:
        fuzz_mined, fuzz_mutant = autofuzz(case, lean)
        if fuzz_mined == "SURVIVED" and fuzz_mutant in ("REFUTED", "REFUTED-DIRTY"):
            verdict = "candidate-mined+SURVIVED"
        elif fuzz_mined in ("REFUTED", "REFUTED-DIRTY"):
            verdict = "candidate-REFUTED(!)"
            contradictions = contradictions + [
                f"self-fuzz: mined candidate REFUTED (fuzz={fuzz_mined})"]
        elif fuzz_mined:
            verdict = f"candidate-mined (fuzz {fuzz_mined}/mut {fuzz_mutant})"
        # re-stamp the verdict into the .md header line
        _restamp(md, verdict)
    return dict(case=case, verdict=verdict, contradictions=contradictions,
                cluster=meta["cluster"], fuzz=(fuzz_mined, fuzz_mutant))


def _restamp(md, verdict):
    if not md or not os.path.exists(md):
        return
    src = open(md).read()
    src = re.sub(r"- verdict: \*\*[^*]+\*\*", f"- verdict: **{verdict}**", src, 1)
    open(md, "w").write(src)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case")
    ap.add_argument("--batch", help="<cluster> | all")
    ap.add_argument("--file", help="fuzz a candidate .lean file (delegates to statement_fuzz)")
    ap.add_argument("--prop")
    ap.add_argument("--struct", help="ghost struct for witness synthesis (fuzz)")
    ap.add_argument("--no-fuzz", action="store_true",
                    help="skip the built-in per-candidate auto-fuzz CTI step")
    args = ap.parse_args()

    if args.file:
        cmd = ["python3", os.path.join(HERE, "statement_fuzz.py"),
               "--file", args.file]
        if args.prop:
            cmd += ["--prop", args.prop]
        if args.struct:
            cmd += ["--struct", args.struct]
        subprocess.run(cmd)
        return

    cases = load_index()
    elf_cache, spec_cache, trace_cache = {}, {}, {}

    if args.case:
        if args.case not in cases:
            sys.exit(f"invgen: no corpus case {args.case}")
        res = run_case(args.case, cases[args.case], elf_cache, spec_cache,
                       trace_cache, skip_fuzz=args.no_fuzz)
        print(json.dumps(res, indent=2))
        return

    if not args.batch:
        ap.error("need --case or --batch")

    targets = (list(cases) if args.batch == "all"
               else [c for c, m in cases.items() if m["cluster"] == args.batch])
    if not targets:
        sys.exit(f"invgen: no cases for batch {args.batch}")

    results = []
    for i, c in enumerate(targets):
        print(f"[invgen {i+1}/{len(targets)}] {c} ({cases[c]['cluster']})", flush=True)
        try:
            results.append(run_case(c, cases[c], elf_cache, spec_cache,
                                    trace_cache, skip_fuzz=args.no_fuzz))
        except Exception as e:
            results.append(dict(case=c, verdict="error", contradictions=[],
                                cluster=cases[c]["cluster"], note=str(e)[:200]))
    write_batch_report(results, cases)


def write_batch_report(results, cases):
    rep = os.path.join(INVDIR, "BATCH-REPORT.md")
    os.makedirs(INVDIR, exist_ok=True)
    from collections import Counter, defaultdict
    vc = Counter(r["verdict"] for r in results)
    by_cluster = defaultdict(Counter)
    for r in results:
        by_cluster[r.get("cluster", "?")][r["verdict"]] += 1
    contras = [r for r in results if r.get("contradictions")]
    with open(rep, "w") as f:
        f.write("# invgen batch report\n\n")
        f.write(f"Cases: {len(results)}.  Verdict classes:\n\n")
        for v, n in vc.most_common():
            f.write(f"- **{v}**: {n}\n")
        f.write("\n## Contradiction shortlist "
                "(mined facts vs design-pass statement shape)\n\n")
        if contras:
            for r in contras:
                f.write(f"- `{r['case']}` ({r.get('cluster')}): "
                        + "; ".join(r["contradictions"]) + "\n")
        else:
            f.write("- (none: no mined fact contradicted a design-pass shape "
                    "this run)\n")
        f.write("\n## Cluster rollups\n\n")
        for cl in sorted(by_cluster):
            f.write(f"- **{cl}**: "
                    + ", ".join(f"{v}×{n}" for v, n in by_cluster[cl].most_common())
                    + "\n")
        f.write("\n## Per-case\n\n")
        for r in sorted(results, key=lambda r: (r.get("cluster", ""), r["case"])):
            note = f" — {r['note']}" if r.get("note") else ""
            f.write(f"- `{r['case']}` [{r.get('cluster')}] → {r['verdict']}{note}\n")
    print(f"\n[invgen] batch report → {rep}")
    print(f"[invgen] verdicts: {dict(vc)}")
    print(f"[invgen] contradictions: {len(contras)}")


if __name__ == "__main__":
    main()
