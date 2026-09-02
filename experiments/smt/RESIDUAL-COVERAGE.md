# RESIDUAL-COVERAGE — every residual category has a DEFINITE Z3 verdict

Date: 2026-09-02. Tools: Z3 4.15.4 (`z3 -in`, binary; z3py absent). Whole ledger
reproduces in <1s total. No `native_decide`/`bv_decide`; these are DESIGN-TIME
Z3 certificates over BOUNDED encodings, NOT Lean proofs (bounded UNSAT at fixed
depth k / width W flags a sufficient-at-depth invariant + pinpoints the recursion
cut; it does not discharge the Lean obligation — see every doc's "honest wall").

## The goal

Every residual category from `experiments/autoprove/SUPPLIER-BATCH.md` must be
ENCODABLE and checkable by an SMT call that returns a DEFINITE verdict
(SAT/UNSAT). Anything that returns UNKNOWN must be FINITIZED (bound recursion
depth k; fixed-width BitVec; uninterpreted-linear reads + congruence; skolemize
∀-ghosts to fresh consts) until Z3 answers definitely. **Met: yes — every row
below is SAT or UNSAT, none UNKNOWN, none timeout.**

## Convention

For a supplier field TRUE-as-stated, the load-bearing query asserts
`H ∧ (arm effect) ∧ ¬(exit conjunct)` — **UNSAT = the conjunct is discharged**
(proved in-fragment) — plus a `control` twin (corrupt one byte / status / PC)
that must be **SAT** (non-vacuity: the fragment can still refute). A row is
"definite" iff neg∈{SAT,UNSAT} (not UNKNOWN/timeout). "proved" = neg UNSAT.

## THE LEDGER

| # | category | fields | encoder | Z3 verdict (neg / control) | finitization used |
|---|----------|--------|---------|----------------------------|-------------------|
| **A1** | COMPOSITION-DEFER: reg+PC outcome | all 14 frame arms (pilots hSBrk/hSExpr) | `gen_fulleffect.encode_reg_pc_out` (runGM/endPCM as BV64 lets) | **UNSAT** / SAT(corrupt a0) | fixed-width **BitVec64** registers/PC |
| **A2** | COMPOSITION-DEFER: HTIF/console output | same | `gen_fulleffect.encode_htif_out` (putchar-count) | **UNSAT** / SAT(phantom putchar) | none (finite Int counter) |
| **A3** | COMPOSITION-DEFER: memory frame | same | `autoprove.encode_execleaf_frame` (wlogM-extracted stores) | **FRAME-PROVED** (agree UNSAT ∧ pres UNSAT ∧ ctrl_window SAT) | **uninterpreted-linear** window reads |
| **A4** | COMPOSITION-DEFER: given-sub-result (recursor IH) | recursive arms (hSExpr) | `gen_fulleffect.encode_given_subresult` | null/bool/int **UNSAT** / SAT; **str SAT** → see A4′ | IH-as-hypothesis (uninterpreted callee) |
| **A4′** | └ .str CString wall (the lone A SAT) | hSExpr str-subresult | `gen_noframe.encode_str_finitize(with_payload)` | without payload agree **SAT**; **WITH bounded `[p,p+3)` agree UNSAT** | **bound-k CString prefix (W=3)** + uninterpreted-tail cut |
| **B1** | PC-hop (segIdentity) | hSeqNil, hArgsNil | `gen_noframe.encode_pchop` (BV64 PC + mem-identity) | **UNSAT** / SAT(phantom +4 hop) | fixed-width **BitVec64** PCs |
| **B2a** | recursive call-splice | hCall, hCallClosure, hSeqConsNormal, hSeqConsAbrupt | `gen_noframe.encode_callsplice` (uninterp callee + suffix frame-agree) | null/bool/int/**str all UNSAT** / SAT | IH-hypothesis + **CString `[p,p+3)` + tail cut** (str) |
| **B2b** | args-loop accumulator | hArgsCons | `gen_noframe.encode_argsloop` (k disjoint arg buffers) | k=1,2,3 **UNSAT** / SAT | **concrete 32-apart bases** (kills nonlinear disjointness), per-arg int witness |
| **B3** | native-seg (HTIF output) | hCallPrint, hCallPrintln, hCallAssertOk | `gen_noframe.encode_native` (console BitVec8 store-chain) | print/println/assertok **UNSAT** / SAT | **BitVec8** console + **bound-k append length** (k=3) |
| **C** | recursive StoreRepr nested survival | all 14 frame arms (survival clause) | `gen_storerepr.py` Houdini base/step | base **UNSAT** ∧ step **UNSAT** ∧ wall SAT ∧ unstrengthened SAT | **uninterpreted-linear reads** (rd4/rd8 + readLE_agreeP congruence) + parent-frame IH cut |

**Every category: definite Z3 verdict. No UNKNOWN. No timeout. Coverage: 10/10
categories.**

## The UNKNOWN-finitization protocol, per construct that needed it

Three constructs would go UNKNOWN or diverge under a naive encoding; each is
finitized to a definite verdict, and WHICH finitization is recorded:

1. **CString payload recursion** (A4/A4′, B2a-str). Naive: `ValueRepr .str` drags
   in the recursive `CString` inductive; the shallow copy/IH hypothesis relates
   only the 24 struct bytes, leaving the payload tail free ⇒ Z3 finds a spurious
   countermodel (**SAT**). Finitization = **bound the char prefix at W=3** + assert
   the opaque tail equal (`cstr_tail` cut) + the bounded byte-agreement `[p,p+W)`.
   Verified: `gen_noframe.py --demo-str-finitize` flips **SAT → UNSAT** in 6ms.
   This is the SAME cut `BOUNDED-PROBE.md` identified; the `gen_fulleffect.py`
   given-sub-result str case does NOT yet carry it (it stops at the struct + tail
   agreement), which is exactly why its str branch reads SAT. Adopting the payload
   line closes it — demonstrated here without editing the sibling file.

2. **Nested StoreRepr `read` chain nonlinearity** (C). Naive: reconstructing
   `read32/read64` as `Σ byte·256^j` (Int) over ~7 chained pointer reads made Z3
   diverge in NONLINEAR arithmetic (measured 40–55s, no return — `HOUDINI-STOREREPR.md`).
   Finitization = model each read as an **UNINTERPRETED function `rd4/rd8`** +
   a per-site `readLE_agreeP` congruence background fact (QF+UF). Survival never
   needs the numeric value, only read-equality-under-agreement ⇒ every query ≤0.01s.
   The self-referential `frames`-field recursion is cut by the **parent-frame IH**
   equality; base+step both UNSAT under it.

3. **Symbolic arg-buffer disjointness** (B2b). Naive: `∀ i<j, |arg_i − arg_j| ≥ 24`
   over symbolic Int addresses + Array reasoning **timed out** at k≥2. Finitization
   = **skolemize the arg bases to concrete 32-apart consts** (`0,32,64,…`), which
   makes disjointness a ground fact ⇒ definite UNSAT at k=1,2,3 in ≤8ms. Same
   discipline as `gen_storerepr`'s CTI-mined concrete addresses.

## Non-vacuity — every "proved" row is a genuine implication, not vacuous

Each encoder ships a `control` twin that corrupts exactly one fact (a copied
byte / the a0 status / the console byte / the exit PC / a phantom putchar) and
Z3 returns **SAT** (a countermodel) — confirming the fragment is refute-capable
at that depth and the UNSAT is a real discharge. For the empty-append `assertok`
(nothing printed), the honest control is a **phantom console byte** the spec
lacks (OK path must print nothing) ⇒ SAT. All controls above are SAT.

## What the DEFINITE verdicts do and do NOT claim

- **DO**: each residual category is now ENCODABLE in a bounded, decidable SMT
  fragment, and Z3 returns a definite SAT/UNSAT — the design-time certificate
  that the load-bearing invariant holds (UNSAT) + is non-vacuous (control SAT),
  at bounded depth/width. No category is left un-encodable or UNKNOWN.
- **DO NOT**: discharge the Lean obligation. Bounded UNSAT at fixed k/W is a
  sufficiency certificate + recursion-cut locator, not a proof — the inductive
  closure (CString / StoreRepr `frames` / ExprRepr-closure caller side-condition)
  remains the Lean abstraction stack's job (`ReprSurvival.lean`,
  `segToTriple`/`callSeg`/`FrameMeta`/`WidenMeta` marshalling). The COMPOSITION
  residual is now Z3-CHARACTERISED per branch, not "out of solver scope".

## Hard finding — the ONLY residual that does not close purely inside SMT

The `ClosureRepr → ExprRepr` AST-subtree recursion (carried by `hCall`/
`hCallClosure` when the callee body is itself an eval) is, in the LANDED lemmas,
a **caller side-condition** (`hcloexpr`/`hexpr'` in `ReprSurvival.lean`), not a
closed recursion — so bounded Houdini/Z3 correctly surfaces it as another opaque
EQUALITY cut (a definite hypothesis), the same way the CString/parent-frame tails
are cut. It has a DEFINITE verdict (the splice is UNSAT *given* that IH cut, as
B2a shows) but the cut itself is a hypothesis by design, not an SMT-provable
obligation — because the model does not close it either. This is not an UNKNOWN;
it is a named, bounded EQUALITY hypothesis with a definite conditional verdict.

## Files / reproduction

- `experiments/smt/bounded/gen_noframe.py` — B1/B2/B3 encoders + `--demo-str-finitize`.
  `python3 experiments/smt/bounded/gen_noframe.py` prints every B row.
- `experiments/smt/bounded/gen_fulleffect.py --field hSBrk|hSExpr` — category A
  (sibling agent; `FULL-EFFECT-PROBE.md` when it lands).
- `experiments/smt/bounded/gen_storerepr.py` — category C base/step certificate.
- Reuses `gen_probe.py` (memory + ValueRepr encoders). Ground truth:
  `Vsa/Sim/ReprSurvival.lean`, `Vsa/RuntimeRepr.lean`, `Vsa/Sim/LoopScaffoldClose.lean`
  (`segIdentity`), `Vsa/Sim/BlockMem.lean` (`wlogM`).
