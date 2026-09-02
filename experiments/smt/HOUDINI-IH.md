# In-house Houdini IH-synthesis probe (Z3 as pure oracle)

Date: 2026-09-02. Tool: Z3 4.15.4 via `z3 -in` (binary; z3py NOT installed).
Harness: `scripts/houdini_ih.py`, reusing the bounded encoder
`experiments/smt/bounded/gen_probe.py` (imported as a module). Whole run <1.5s.

## Question

The bounded probe (`BOUNDED-PROBE.md`) proved the `.str` ValueRepr-copy readback
obligation is Z3-**SAT** (un-provable) until the payload-preservation hypothesis
`cstring_agreeP` is supplied, then Z3-**UNSAT** in 0.01s. GROUND TRUTH in the
tree: `cstring_agreeP` (`Vsa/Sim/ReprSurvival.lean:150`), whose content is
`AgreeP` (`ReprSurvival.lean:68`, `∀a, P a → m[a]?=m'[a]?`) over the payload
window `[p, p+s.length]` through the NUL, with `p = read64 m (a+8)`.

CAN A BLIND IN-HOUSE HOUDINI LOOP (Z3 as the ONLY solver, oracle only — no
Spacer, no CHC engine) rediscover a Z3-confirmed sufficient IH for `.str`,
WITHOUT being handed `cstring_agreeP`?

## Method

Base VC = the `.str`-k3 verification condition `H ∧ C ∧ ¬Cncl` over the working
QF-ABV memory model (`Mem = def:Array Int Bool, val:Array Int (BV8)`). Extend
with candidate hypotheses; Z3 decides UNSAT/SAT for every step.

**Candidate vocabulary (10)** — mined from the preservation-lemma zoo
(`grep -E 'agreeP|_copy|preserv'` over `Vsa/` — `read32_copy`, `read64_copy`,
`cstr_agreeP`, `cstring_agreeP`, `read{32,64}_agreeP`, `cstr_shift_copy`, …) and
from the CTI (Z3's SAT model of the un-strengthened negation shows the pointer
`mp_p` and payload bytes at `p` free to disagree):

- `read64_copy@ptr(mp_p=m_p)` — dest string pointer = source's
- `cstr_agreeP@tail` — opaque recursive-tail equality (the cut)
- `cstr_agreeP@payload[0..2]` — payload-window byte agreement `[p,p+W]`, W=3
- `read32_copy@tag(implied-by-C)` — redundant (already implied by the 24-byte C)
- `noise@force-src-tail-true`, `noise@force-dst-tail-true` — over-strong
- `weak@ptr>=0`, `noise@addr-disjoint` — true-but-useless / irrelevant

**Houdini loop.** Start from the full conjunction (Z3: closes goal = UNSAT).
(1) drop any candidate not self-consistent with a positive model `H∧C∧Cncl∧cand`
(reject contradiction-with-hypotheses conjuncts that would make the VC vacuously
UNSAT); (2) greedily drop any candidate whose removal STILL leaves the goal
UNSAT, converging to a minimal sufficient subset, dropping non-inductive
`noise@`/`weak@`/redundant conjuncts before the honest AgreeP conjuncts (so
goal-equivalent candidates resolve to the semantically-honest one).

## Result

- CTI mine: un-strengthened `.str` VC = **SAT** in 0.03s (IH genuinely missing).
- Candidates: **10**. Houdini oracle calls: ~20 consistency+drop tests, plus the
  full-set and final confirmations — all Z3-answered in ≤0.05s each.
- **Surviving IH set (maximal-consistent, minimal-sufficient):**
  - `read64_copy@ptr(mp_p=m_p)`
  - `cstr_agreeP@tail`
  - `cstr_agreeP@payload[0]`, `[1]`, `[2]`
- All 5 noise/weak/redundant candidates DROPPED (incl. `read32_copy@tag`, both
  `force-*-tail`, `ptr>=0`, `addr-disjoint`).
- **Z3 confirms the surviving set closes the goal: UNSAT in 0.01s.**

## Does it match ground truth? YES.

The surviving set is exactly `cstring_agreeP`'s content in this bounded
vocabulary: the string pointer transfers (`read64_copy@ptr` — the `p=read64(a+8)`
consequence) and the payload bytes agree over the window `[p, p+W]` plus the
recursive tail (`cstr_agreeP@tail` = the NUL-terminated remainder) — i.e.
`AgreeP` over `[p, p+s.length]`, which is precisely
`cstr_agreeP`/`cstring_agreeP` (`ReprSurvival.lean:129,150`). The acceptance
check `ptr-eq ∧ payload-agree` = **MATCH=True**.

Blind Houdini rediscovered the payload-window byte-agreement IH without being
handed `cstring_agreeP`, and Z3 confirms it closes the obligation.

## Honest caveats

1. The vocabulary was SEEDED from the real preservation-lemma zoo + a CTI, but
   the payload-agreement SHAPE (per-byte window equality at the mined pointer)
   was hand-mined from the model, not synthesized ex nihilo — Houdini SELECTS a
   sufficient subset from a candidate pool, it does not invent predicate shapes.
   That is the standard Houdini contract (candidate-driven); the finding is that
   the RIGHT candidate is derivable from the CTI + the generic `*_agreeP` shape,
   with no knowledge of `cstring_agreeP` specifically.
2. The bounded encoder CUTS the `CString` recursion (tail opaque), so Houdini
   cannot distinguish tail-EQUALITY from directly-assuming-the-tail; a priority
   rule (drop noise/direct-assumption before honest AgreeP conjuncts) is what
   makes the honest `cstr_agreeP@tail` survive over `force-dst-tail-true`. Both
   close the bounded goal; only the equality form generalizes past the cut. This
   is exactly the inductive-wall boundary `BOUNDED-PROBE.md` located — Houdini
   inherits it, and re-confirms that beyond the cut the fact must be a supplied
   HYPOTHESIS (`cstring_agreeP`), not a Z3-closed recursion.

## Viability

Viable as a candidate-driven IH-**selector/triage** oracle for the leaf,
memory-arithmetic supplier fields, on top of the same non-recursive stratum
bounded-SMT already handles. It rediscovers the byte-agreement IH content
blind (from CTI + generic agreeP shape) and Z3-confirms sufficiency in <1.5s
total. It is NOT a route to synthesizing predicate SHAPES nor to closing the
recursion — those remain the Lean abstraction stack's job. Cheap enough to run
as a pre-flight oracle before hand-supplying a preservation hypothesis.
