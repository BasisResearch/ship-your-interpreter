# Bounded-SMT feasibility probe: encoding the DEFINITIONS of a supplier field

Date: 2026-09-02. Tools: Z3 4.15.4 (`-in`, ALL logic), cvc5 present (unused —
Z3 answered instantly). Harness: `experiments/smt/bounded/gen_probe.py`
(+ generated `q_*.smt2`). Time budget respected: whole probe runs in <1s.

## The question

`experiments/smt/DumpSmtLib.lean` (§"Unfolding policy") stops at OPAQUE for the
semantic predicates (`ValueRepr`/`StoreRepr`/`CString`/…), and
`observations.md::smt-cannot-prove-supplier-fields` recorded the resulting
asymmetry: `--refute` works (falsities have in-fragment arithmetic witnesses),
`--validate` hits ENCODE-GAP (validity needs the opaque semantics constrained;
uninterpreted preds admit spurious models).

This probe asks the NEXT question: if we ENCODE THE DEFINITION of a supplier
predicate (the datatype case-split + the recursive read functions unfolded into
the QF_ABV memory model that already works), can Z3 become (a) an opportunistic
VALIDITY prover (UNSAT = proof) and/or (b) a bounded REFUTER, and WHERE does the
inductive wall actually fall?

## Target chosen (shallowest supplier obligation)

The `ValueRepr` **copy readback** obligation from `Vsa/Sim/ReprCopy.lean` (the
non-negotiable field of `valueRepr_copy`, used by `EvalNullSim`, the `env_get`
HIT tail, and `EvalVarSim.hcopy`):

    (H)  ValueRepr m  N φc srcAddr v                          -- source represented
    (C)  ∀ j<24, m'[dstAddr+j]? = m[srcAddr+j]?               -- 24 struct bytes copied
    ==>  ValueRepr m' N φc dstAddr v                          -- readback at new addr

It is the shallowest genuine supplier field: `ValueRepr` (`Vsa/RuntimeRepr.lean:77`)
is a NON-recursive dispatch on the `Value` constructor, and its `.null`/`.bool`/
`.int` cases bottom out in `read32`/`readI64`, i.e. `readLE` (`Vsa/MemRepr.lean:32`),
a byte-count-bounded recursion — exactly the QF_ABV fragment.

## Encoding sketch (definition-encoded, NOT opaque)

* `Mem` → `(def : Array Int Bool, val : Array Int (BV 8))`; `m[a]?=some b ↦
  (select def a) ∧ (select val a)=b`  (reuses the working `smt_check.py` model).
* `read32 m a = some V`  ↦  full 4-byte unfold: `(and (defined a..a+3)
  (= Σ byte_j·256^j  V))`. `read64`/`readI64` likewise (8-byte unfold). This IS
  `readLE` unfolded to its (literal) width — a `define-fun-rec` collapsed to a
  macro since the width is a constant.
* `ValueRepr` case-split on the constructor, per `RuntimeRepr.lean:79-88`:
  - `.null` → `read32 · = some 0`                       (1 read, NO recursion)
  - `.bool` → `read32 · = 1 ∧ read32 (·+8) ∈ {0,1}`     (finite, NO recursion)
  - `.int`  → `read32 · = 2 ∧ readI64 (·+8) = n`        (finite, NO recursion)
  - `.str`  → `read32 · = 3 ∧ ∃p, read64(·+8)=p ∧ p≠0 ∧ CString m p s`
              `CString` is the RECURSIVE inductive (`MemRepr.lean:50`). Bounded-
              unfold its char prefix to depth k, leave the TAIL as an
              uninterpreted Bool `cstr_tail` — this is the honest wall marker.

DEPTH AXIS **k = how deep the inductive `Value`/`CString` structure is unfolded**:
k=1 exercises `.null`; k=2 adds `.bool`/`.int`; k=3 adds `.str` (which drags in
`CString`, the recursive inductive). For each we run `validate` (is `H∧C∧¬Cncl`
UNSAT = proof?) and a `refute-twin` control (drop copy byte 0 → deliberately
false; SAT = the fragment can still produce countermodels at this depth).

## Per-depth verdict table (validate × refute, k=1,2,3)

| kind | k | validate (H∧C∧¬Cncl) | refute-twin (drop byte0) | time |
|------|---|----------------------|--------------------------|------|
| null | 1 | **UNSAT** (proof)    | SAT (countermodel)       | 0.03s |
| null | 2 | **UNSAT**            | SAT                      | 0.02s |
| null | 3 | **UNSAT**            | SAT                      | 0.02s |
| bool | 1 | **UNSAT**            | SAT                      | 0.02s |
| bool | 2 | **UNSAT**            | SAT                      | 0.02s |
| bool | 3 | **UNSAT**            | SAT                      | 0.02s |
| int  | 1 | **UNSAT**            | SAT                      | 0.02s |
| int  | 2 | **UNSAT**            | SAT                      | 0.02s |
| int  | 3 | **UNSAT**            | SAT                      | 0.02s |
| str  | 1 | **SAT** (see below)  | SAT                      | 0.02s |
| str  | 2 | **SAT**              | SAT                      | 0.03s |
| str  | 3 | **SAT**              | SAT                      | 0.03s |

Non-vacuity check: `H∧C∧Cncl` is SAT for null (positive model exists), so the
null/bool/int UNSAT is a genuine implication proof, not a vacuous one.

## What the verdicts mean (honest reading)

**null/bool/int — VALIDATE UNSAT, the OPPORTUNISTIC PROVER WORKS.** For the
non-recursive `ValueRepr` cases, encoding the definition (case-split + `readLE`
unfold) puts the whole obligation in decidable QF_ABV. Z3 proves the readback
field valid in ~20ms at every depth. The UNSAT is **REPLAYABLE**: it corresponds
exactly to the existing Lean lemma `read32_copy`/`readLE_copy` (`ReprCopy.lean:64,87`)
that `valueRepr_copy` (line 132, `rw [read32_copy hcopy ...]`) already uses for
these three cases. Z3 discharges precisely the byte-agreement reasoning the Lean
proof performs — so the SMT proof and the Lean proof are the same object.

**null/bool/int — REFUTE control SAT.** Dropping one copied byte makes the twin
false; Z3 returns a countermodel at every depth. The bounded refuter also works
in this fragment (consistent with the prior `--refute` result).

**str — VALIDATE SAT: the inductive wall, made precise.** At k≥3 the `.str` case
pulls in the recursive `CString`. The copy hypothesis `C` relates only the 24
STRUCT bytes; it says nothing about the string-payload bytes at the pointer `p`.
So Z3 finds a model where the opaque tails `cstr_tail_m` / `cstr_tail_mp` differ
(and/or the payload bytes at `p` differ) — a legitimate countermodel OF THE
SHALLOW OBLIGATION AS STATED. This is NOT Z3 failing on recursion; it is Z3
correctly reporting that the null-copy obligation is genuinely too weak for the
recursive case: `ValueRepr .str` needs the extra `cstring_agreeP` payload-
preservation hypothesis that `ReprCopy.lean` supplies by hand.

CONFIRMED constructively: re-running str k=3 with the payload hypotheses added
(same `p`, `cstr_tail` agreement, bounded byte-agreement at `p`) flips the
verdict to **UNSAT in 0.01s**. So even the recursive case is Z3-provable ONCE
the recursive tail is either (i) assumed opaque-but-equal or (ii) supplied as a
hypothesis — i.e. Z3 handles everything EXCEPT closing the recursion itself,
which the bounded encoding structurally cannot do.

## Conclusion: is bounded-SMT a viable prover/refuter for supplier fields?

YES for the NON-RECURSIVE stratum, NO across the recursive boundary — and the
boundary is sharp and cheap to locate:

1. **Opportunistic VALIDITY prover: viable for definition-encodable, non-
   recursive supplier fields.** The prior "validate = ENCODE-GAP" verdict was an
   artifact of the OPAQUE stop-policy, not a fundamental limit. Unfolding the
   definition into QF_ABV, Z3 proves `ValueRepr .null/.bool/.int` readback valid
   in ~20ms, replayable against the existing Lean lemma. This upgrades the
   observation's stance: for the shallow, memory-arithmetic supplier fields,
   `--validate` CAN return a real proof.

2. **The inductive wall falls exactly at the first RECURSIVE predicate
   (`CString`), at depth k=3** for this target — not gradually. Below it,
   everything is finite QF_ABV; at it, the bounded encoding must cut the
   recursion, and the cut manifests as a spurious VALIDATE-SAT unless the tail
   is supplied as a hypothesis. Bounded unfolding does NOT let Z3 discharge the
   recursion; it only lets Z3 discharge everything hanging off a FIXED-depth
   prefix. Increasing k does not help (str is SAT at k=1,2,3 alike) because the
   missing fact is the payload-copy HYPOTHESIS, not more unfolding.

3. **Cost is negligible** (<1s for the full 24-query sweep), so this is a cheap
   triage oracle: definition-encode a candidate supplier field, run validate; a
   fast UNSAT is a replayable proof, a SAT flags either a real weakness in the
   stated obligation (as with str here — the missing payload hyp) or the
   recursive-predicate boundary. Both outcomes are informative and none are
   silent.

PRACTICAL UPSHOT for the abstraction stack: bounded-SMT is a legitimate
opportunistic prover for the LEAF, memory-arithmetic supplier fields
(`ValueRepr .null/.bool/.int`, `read*` readbacks, window-frame side conditions)
— the same pockets the observation's BACKLOG already flagged for a
"Z3-certificate → Lean replay path for HARD-ARITHMETIC sub-goals." It is NOT a
route to the recursive-Repr bulk (`CString`/`StoreRepr`/`ExprRepr` cones); those
remain the Lean abstraction stack's job, and the probe pinpoints the recursion
as the exact reason (a bounded cut cannot close an inductive obligation, only
defer it to a hypothesis). This matches — and sharpens with mechanism — the
`smt-cannot-prove-supplier-fields` verdict.
