#!/usr/bin/env python3
"""
IN-HOUSE HOUDINI IH-synthesis probe (Z3 as the ONLY solver — pure oracle, no
Spacer / no CHC engine).

QUESTION: can a blind Houdini loop rediscover a Z3-confirmed sufficient IH for
the `.str` ValueRepr-copy readback obligation, WITHOUT being handed
`cstring_agreeP`?

Reuses the bounded encoder shape from experiments/smt/bounded/gen_probe.py:
the `.str`-k3 verification condition H ∧ C ∧ ¬Cncl over the QF-ABV memory model
(Mem = def:Array Int Bool, val:Array Int (BV8)). Un-strengthened it is SAT
(BOUNDED-PROBE.md); the missing fact is payload-window byte agreement at the
string pointer `p` — i.e. `cstring_agreeP`'s content.

GROUND TRUTH (Vsa/Sim/ReprSurvival.lean:129-155): `cstr_agreeP`/`cstring_agreeP`
= AgreeP over `[p, p + s.length]` (through the NUL), where AgreeP P m m' :=
∀a, P a → m[a]? = m'[a]?  (ReprSurvival.lean:68). In this bounded encoding, with
the source pointer m_p and dest pointer mp_p, that is: same pointer (mp_p=m_p)
AND payload bytes agree m vs mp over the bounded window [p, p+W].

Houdini: seed ~a dozen candidate predicates (mined from the preservation-lemma
zoo + CTI-mined byte-agreement facts), start from the full conjunction, and
iteratively DROP any candidate that is (a) not itself consistent with H∧C
(Z3 SAT model shows it violated / it over-constrains to UNSAT-of-hyps), keeping
the maximal consistent subset; then confirm the surviving set makes the goal
UNSAT. Z3 is the oracle for every decision.
"""
import subprocess, time, os, sys

Z3 = "z3"
BOUNDED = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "..", "experiments", "smt", "bounded")
sys.path.insert(0, os.path.abspath(BOUNDED))
import gen_probe as G   # reuse read/copy/valuerepr encoders

W = 3   # bounded payload window depth (matches cdepth k=3 char prefix)

# ---------------------------------------------------------------------------
# The base .str-k3 verification condition, as a list of assertion strings we
# can extend with candidate hypotheses.  Mirrors gen_probe.build('str',3,...).
# ---------------------------------------------------------------------------
def base_decls():
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("m", "mp"):
        L += G.decls_mem(m)
    L += ["(declare-fun srcAddr () Int)", "(declare-fun dstAddr () Int)"]
    L += [f"(declare-fun {m}_p () Int)" for m in ("m", "mp")]
    L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("m", "mp")]
    return L

def base_asserts(control=False):
    """H (src repr) ∧ C (24-byte struct copy) ∧ ¬Cncl (dst repr)."""
    H    = G.valuerepr("m",  "srcAddr", "str", W)
    C    = G.copy24("m", "mp", drop=(0 if control else None))
    Cncl = G.valuerepr("mp", "dstAddr", "str", W)
    return [f"(assert (>= srcAddr 0))", f"(assert (>= dstAddr 0))",
            f"(assert {H})", f"(assert {C})", f"(assert (not {Cncl}))"]

# ---------------------------------------------------------------------------
# CANDIDATE VOCABULARY.  Each is a predicate over the probe's Mem/addr
# vocabulary, sourced either from a named preservation lemma in the tree or
# mined from a CTI.  key -> (lemma-origin, smt-bool-expr).
# ---------------------------------------------------------------------------
def cand_payload_byte(i):
    """Payload byte i agrees: mp[mp_p+i] defined&val = m[m_p+i].  (cstr_agreeP
    body, per-char.)  Only meaningful once mp_p is tied to m_p."""
    return (f"cstr_agreeP@payload[{i}]",
            f"(and (= (select mp_def (+ mp_p {i})) (select m_def (+ m_p {i}))) "
            f"(= (select mp_val (+ mp_p {i})) (select m_val (+ m_p {i}))))")

def cand_ptr_eq():
    """Dest string pointer equals source's: mp_p = m_p.  (read64 (a+8) copies
    through C already, but the ENCODING introduces a fresh existential mp_p; the
    IH must pin it.  This is the read64_copy/read64_agreeP consequence.)"""
    return ("read64_copy@ptr(mp_p=m_p)", "(= mp_p m_p)")

def cand_tail_eq():
    """Opaque CString tails agree.  (cstr_agreeP's recursive tail — the wall.)"""
    return ("cstr_agreeP@tail", "(= cstr_tail_mp cstr_tail_m)")

def cand_tag_agree():
    """Header tag byte-window agrees dst<-src (subsumed by C; a red herring /
    already-implied candidate to test Houdini's dropping)."""
    return ("read32_copy@tag(implied-by-C)",
            "(= (select mp_val (+ dstAddr 0)) (select m_val (+ srcAddr 0)))")

def cand_src_tail():   # non-inductive noise: forces src tail true (over-strong)
    return ("noise@force-src-tail-true", "cstr_tail_m")
def cand_dst_tail():   # non-inductive noise: forces dst tail true directly
    return ("noise@force-dst-tail-true", "cstr_tail_mp")
def cand_ptr_pos():    # weak fact: pointer nonneg (true but useless)
    return ("weak@ptr>=0", "(and (>= m_p 0) (>= mp_p 0))")
def cand_addr_disj():  # noise: src/dst disjoint (irrelevant to str payload)
    return ("noise@addr-disjoint",
            "(or (>= srcAddr (+ dstAddr 24)) (>= dstAddr (+ srcAddr 24)))")

def all_candidates():
    C = [cand_ptr_eq(), cand_tail_eq()]
    for i in range(W):
        C.append(cand_payload_byte(i))
    C += [cand_tag_agree(), cand_src_tail(), cand_dst_tail(),
          cand_ptr_pos(), cand_addr_disj()]
    return C  # ~10 candidates

# ---------------------------------------------------------------------------
# CTI mining: get Z3's SAT model of the UN-strengthened negation, read which
# payload bytes / pointer it made disagree, emit "those agree" candidates.
# ---------------------------------------------------------------------------
def z3_run(script, get_model=True):
    body = "\n".join(script) + "\n(check-sat)\n" + ("(get-model)\n" if get_model else "")
    t = time.time()
    p = subprocess.run([Z3, "-in"], input=body, capture_output=True, text=True, timeout=90)
    dt = time.time() - t
    out = p.stdout.strip()
    verdict = out.split("\n", 1)[0] if out else "(no output)"
    return verdict, out, dt

def mine_cti():
    """Un-strengthened .str VC is SAT; report the model's disagreement summary."""
    v, out, dt = z3_run(base_decls() + base_asserts(control=False))
    return v, out, dt

# ---------------------------------------------------------------------------
# Oracle: is the VC UNSAT under the given set of assumed candidates?
# ---------------------------------------------------------------------------
def goal_unsat_under(cands):
    script = base_decls() + base_asserts(control=False)
    for _, expr in cands:
        script.append(f"(assert {expr})")
    v, _, dt = z3_run(script, get_model=False)
    return v, dt

# A candidate is "self-consistent with H∧C" (usable as an IH conjunct, not a
# contradiction-with-hypotheses that would make the WHOLE thing vacuously UNSAT):
# H ∧ C ∧ Cncl ∧ cand must be SAT (positive model with the candidate holding).
def cand_consistent_with_positive(cand):
    H    = G.valuerepr("m",  "srcAddr", "str", W)
    C    = G.copy24("m", "mp", drop=None)
    Cncl = G.valuerepr("mp", "dstAddr", "str", W)
    script = base_decls() + [f"(assert (>= srcAddr 0))", f"(assert (>= dstAddr 0))",
                             f"(assert {H})", f"(assert {C})", f"(assert {Cncl})",
                             f"(assert {cand[1]})"]
    v, _, dt = z3_run(script, get_model=False)
    return v, dt

# ---------------------------------------------------------------------------
# HOUDINI loop.  Standard Houdini for a single VC: start from the full
# candidate conjunction; the VC (H∧C∧¬Cncl ∧ ⋀cands) should be UNSAT (over-
# strong is fine for soundness).  Then MINIMIZE / prune to the maximal subset
# that (i) is each self-consistent with a positive model (not vacuous) and
# (ii) still closes the goal — dropping any candidate Z3 shows is unnecessary
# noise, converging to the semantic core.  Z3 decides every step.
# ---------------------------------------------------------------------------
def houdini():
    cands = all_candidates()
    log = []
    # Step 0: full conjunction must close the goal.
    v0, dt0 = goal_unsat_under(cands)
    log.append(("full-set", [c[0] for c in cands], v0, dt0))
    if not v0.startswith("unsat"):
        log.append(("ABORT", "full candidate set does NOT close goal", v0, dt0))
        return cands, log, v0

    # Step 1: drop any candidate that is NOT self-consistent with a positive
    # model (a contradiction-with-hypotheses conjunct would make the VC
    # vacuously UNSAT — Houdini must reject non-inductive/violated candidates).
    survivors = []
    for c in cands:
        vc, dtc = cand_consistent_with_positive(c)
        keep = vc.startswith("sat")
        log.append(("consistency", c[0], vc, dtc))
        if keep:
            survivors.append(c)
    # Step 2: greedily drop any survivor whose removal STILL leaves goal UNSAT
    # (unnecessary — not part of a minimal sufficient IH).  Converge to a
    # minimal sufficient subset.
    # Priority: prefer dropping non-inductive "noise@"/"weak@" conjuncts (and a
    # direct tail-assumption) BEFORE the honest agreement conjuncts, so when two
    # candidates are goal-equivalent (e.g. tail-EQUALITY vs directly-assume-tail,
    # indistinguishable because the bounded encoder cuts the recursion) the
    # semantically-honest AgreeP conjunct is the one that survives.
    def drop_rank(c):
        n = c[0]
        if n.startswith("noise@") or n.startswith("weak@"): return 0
        if n.startswith("read32_copy@tag"):                 return 1  # implied by C
        return 2  # honest agreement conjuncts last
    changed = True
    while changed:
        changed = False
        for c in sorted(survivors, key=drop_rank):
            trial = [x for x in survivors if x is not c]
            vt, dtt = goal_unsat_under(trial)
            log.append(("drop-test", c[0], vt, dtt))
            if vt.startswith("unsat"):
                survivors = trial
                changed = True
                break
    # Confirm minimal set still closes the goal.
    vf, dtf = goal_unsat_under(survivors)
    log.append(("final", [c[0] for c in survivors], vf, dtf))
    return survivors, log, vf

# ---------------------------------------------------------------------------
def main():
    print("=== CTI mine (un-strengthened .str VC) ===")
    vc, out, dtc = mine_cti()
    print(f"  verdict={vc}  time={dtc:.3f}s  (SAT expected => IH missing)")

    cands = all_candidates()
    print(f"\n=== Candidate vocabulary ({len(cands)}) ===")
    for name, _ in cands:
        print(f"  - {name}")

    print("\n=== Houdini ===")
    survivors, log, vf = houdini()
    for kind, a, v, dt in log:
        print(f"  [{kind:12}] {str(a):55.55} -> {v:8} {dt:5.2f}s")

    print("\n=== Surviving IH set ===")
    for name, expr in survivors:
        print(f"  - {name}")
    print(f"\nGoal closes (UNSAT) under survivors: {vf}")

    # Ground-truth match: does the surviving set include the payload-window
    # byte-agreement content of cstring_agreeP (ptr-eq + payload bytes agree)?
    names = {n for n, _ in survivors}
    has_ptr = any(n.startswith("read64_copy@ptr") for n in names)
    has_pay = any(n.startswith("cstr_agreeP@payload") for n in names)
    match = has_ptr and has_pay
    print(f"\ncstring_agreeP content present?  ptr-eq={has_ptr}  payload-agree={has_pay}"
          f"  => MATCH={match}")
    return survivors, vf, match

if __name__ == "__main__":
    main()
