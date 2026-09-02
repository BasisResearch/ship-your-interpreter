#!/usr/bin/env python3
"""z3_residuals.py — ORCHESTRATOR ONLY (never parses Lean).

Runs Z3 on the per-field `.smt2` files written by the Lean `#dump_residuals`
command and collects a verdict per field.  The encoding is done entirely in Lean
(the elaborated-Expr walker); this script only shells Z3 over the files and joins
the verdicts with the coverage manifest.

  unsat ⇒ VALID (field holds in the encoded fragment)
  sat   ⇒ REFUTED (countermodel exists)
  unknown/timeout ⇒ UNKNOWN

Usage: python3 scripts/z3_residuals.py <dir> [--timeout SECS] [-jN]
"""
import os, sys, subprocess, concurrent.futures

def z3_one(path, timeout):
    try:
        r = subprocess.run(["z3", "-smt2", f"-T:{timeout}", path],
                           capture_output=True, text=True, timeout=timeout + 5)
        o = (r.stdout + r.stderr).strip()
    except subprocess.TimeoutExpired:
        return "UNKNOWN"
    if o.startswith("unsat"): return "VALID"
    if o.startswith("sat"):   return "REFUTED"
    return "UNKNOWN"

def main():
    d = sys.argv[1]
    timeout = 15
    jobs = 6
    for a in sys.argv[2:]:
        if a.startswith("--timeout"): timeout = int(a.split("=")[1] if "=" in a else sys.argv[sys.argv.index(a)+1])
        elif a.startswith("-j"): jobs = int(a[2:])
    # coverage manifest (produced by Lean; read as DATA)
    cov = {}
    mpath = os.path.join(d, "manifest.tsv")
    if os.path.exists(mpath):
        for i, line in enumerate(open(mpath)):
            if i == 0: continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2: cov[parts[0]] = parts[1]
    fields = sorted(f[:-5] for f in os.listdir(d) if f.endswith(".smt2"))
    def run(f):
        return (f, z3_one(os.path.join(d, f + ".smt2"), timeout))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        results = dict(ex.map(run, fields))
    out = os.path.join(d, "verdicts.tsv")
    with open(out, "w") as fh:
        fh.write("field\tz3_verdict\tcoverage\n")
        for f in fields:
            fh.write(f"{f}\t{results[f]}\t{cov.get(f,'?')}\n")
    from collections import Counter
    print("verdicts:", dict(Counter(results.values())))
    ref = [f for f in fields if results[f] == "REFUTED"]
    print(f"REFUTED ({len(ref)}):", " ".join(ref))
    print("wrote", out)

if __name__ == "__main__":
    main()
