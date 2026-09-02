# Fleet batch B6-loopseq — landing log

Worker: fleet clone `/tmp/vsa-fleet-B6-loopseq` (HEAD 2865529, wave 46).
Fields (in order worked): hSeqNil, hSeqConsNormal, hSeqConsAbrupt,
hFlCondFalse, hFlBodyBreak, hFlBodyRet, hFlLoop.

Machine-checked obstruction anchor for the batch:
`Vsa/Sim/rows/B6LoopSeqObstruction.lean` (green, axiom-clean — see per-field
entries).  NOT a `Field_*.lean` — do not plug it; it certifies WHY the fields
skip.

---
## hSeqNil — SKIPPED (obstruction, machine-checked)

Hole: `SkelHSeqNil L = ∀ st d env, mExecSeq st d env [] st .normal (ExecSeq.nil …)`.
`mExecSeq` (TermSimAssembly.lean:178) quantifies entry PC `p` and exit PC `q`
INDEPENDENTLY.  The brief/TSV supplier note ("`ExecSimCommon.execSeqNil`
seg-identity — a `_row` wrap is trivial") is STALE: `execSeqNil` and
`LoopScaffoldClose.segIdentity` are zero-step identities at a SHARED PC, and
`B6LoopSeqObstruction.zeroStep_segSpan_forces_pc_eq` proves any zero-step
discharge covers ONLY `BitVec.ofNat 64 p = BitVec.ofNat 64 q`.
`B6LoopSeqObstruction.skelHSeqNil_offdiag_must_step` proves any discharge of
the hole must produce a ≥1-step run (`c' ≠ c`) from EVERY off-diagonal
`SegEntry` config — but `SegEntry` (InductionScaffold.lean:150) pins NO code
byte (no `code : …Loaded` field, unlike `EvalEntry.code`/`ExecEntry.code`),
so no machine step is derivable from the hypothesis set.  The committed
`rows/SeqForRows.lean` module doc already records this as the genuine `p → q`
span; its named carrier `Vsa.Sim.Rows.SeqNilResid` has NO provider anywhere
(grep-verified) and is unprovable as stated.
- missing supplier: a provider of `Vsa.Sim.Rows.SeqNilResid` — requires a
  `mExecSeq`/`SegEntry` amendment (pin `p = execSeqLoopPC`, `q = execSeqContPC`
  or add a code-image field) BEFORE any machine proof can exist.
- landed route once amended: `rows/SeqForRows.hSeqNil_row` consumes the resid.

## hSeqConsNormal — SKIPPED (same motive obstruction + engine-seam)

Same `mExecSeq` independent-`(p,q)` + code-free-`SegEntry` obstruction as
hSeqNil (the conclusion is the same motive at `s :: ss`).  The sub-IHs cannot
bridge it: the head IH is `ExecIH` (`ExecEntry → ExecExitD`) and `SegEntry`
cannot supply `ExecEntry.{pc@execStmtEntry, a0–a3, code, stmt, stackOK}`
(ExecEntry.lean:207-262 — grep-confirmed `code`/`stmt` fields); exit-side, the
landed engine `execSeqLoop`'s `ExecSeqExit` (ExecSimCommon.lean) lacks the
`memFrame`/`stackWin` fields `SegExit` demands.  Both adapter directions fail
— exactly the seam recorded in `rows/SeqForRows.lean`.
- missing supplier: a provider of `Vsa.Sim.Rows.SeqConsNormalResid`
  (landed route: `rows/SeqForRows.hSeqConsNormal_row`).

## hSeqConsAbrupt — SKIPPED (same)

Identical obstruction set (one-iteration abrupt exit, same motive, same
adapter failures).
- missing supplier: a provider of `Vsa.Sim.Rows.SeqConsAbruptResid`
  (landed route: `rows/SeqForRows.hSeqConsAbrupt_row`).

## hFlCondFalse — SKIPPED (obstruction, machine-checked)

`mForLoop` is the identity-PC span `SegEntry st p → SegExit st' p` (amended,
ledger `scaffold-motive-independent-pq`), but `ForLoop.condFalse`'s endpoint
`st'` comes from the cond `EvalE` and mutates the store in general — the DUAL
`scaffold-some-motive-unsatisfiable` shape that got `mExecInit`/`mForCond`/
`mExecStep` amended to `True` (mForLoop kept the span form).
`B6LoopSeqObstruction.zeroStep_forSpan_forces_rerepresentation` machine-checks
that a zero-step discharge forces the UNCHANGED entry memory `m0` to represent
BOTH `st.store` and the mutated `st'.store` (φ-extended over entry sizes) —
conflicting whenever `st'` rewrites an existing frame slot; a ≥1-step
discharge is barred by the code-free `SegEntry` (no step derivable).  The cond
sub-IH (`mEvalE = EvalIH`) cannot be entered from `SegEntry` (no
`EvalEntry.{code, expr, ABI}` fields available).
- missing supplier: a provider of `Vsa.Sim.Rows.ForResid` (landed route:
  `rows/SeqForRows.hFlCondFalse_row`); gated on a `mForLoop`/`SegEntry`
  amendment (honest exit PC ≠ entry PC + code-image linkage).

## hFlBodyBreak — SKIPPED (same ForResid obstruction)

Endpoint `st''` from the body `ExecS` (`.brk`) — store-mutating identity-PC
span; same analysis, same missing supplier `ForResid` (route:
`rows/SeqForRows.hFlBodyBreak_row`).  `mForCond` sub-IH is `True` (supplies
nothing); `mExecS` sub-IH not enterable from `SegEntry`.

## hFlBodyRet — SKIPPED (same)

Same as hFlBodyBreak with `.ret rv`.  Missing supplier `ForResid` (route:
`rows/SeqForRows.hFlBodyRet_row`).

## hFlLoop — SKIPPED (same + back-edge)

The back-edge case: even composing the recursive tail IH
(`mForLoop st''' … p`, usable as-is) still needs the one-iteration span
`SegEntry st p → SegEntry st''' p` — the same store-mutating identity-PC
machine content, unprovable without code linkage.  Missing supplier `ForResid`
(route: `rows/SeqForRows.hFlLoop_row`); the landed engine `execForLoopBody`
(ExecFor.lean) admits no adapter in either direction (entry: SegEntry lacks
the ExecEntry fields; exit: ExecExit lacks `memFrame`/`stackWin`).

---

## Batch verdict

0/7 green, 7/7 skipped on TWO shared named obstructions (both machine-checked
in `Vsa/Sim/rows/B6LoopSeqObstruction.lean`, green 3.6s wall, axioms exactly
{propext, Classical.choice, Quot.sound}, discipline OK):

1. `mExecSeq` independent `∀ (p q)` + code-free `SegEntry` (ExecSeq family);
2. `mForLoop` identity-PC with store-mutating endpoints + the
   `SeqForRows`-documented engine seam (`ExecSeqExit`/`ExecExit` lack
   `memFrame`/`stackWin`; `SegEntry` lacks `ExecEntry`/`EvalEntry`'s
   `code`/repr/ABI fields) (ForLoop family).

The fix is a MOTIVE/SegEntry amendment (coordinator-owned, shared-file):
pin `p`/`q` at the decoded PCs (`execSeqLoopPC`/`execSeqContPC`; honest
for-loop head/exit PCs) or thread a code-image field through `SegEntry` — then
the landed `rows/SeqForRows.lean` rows consume providers built from
`execSeqLoop`/`execForLoopBody` + a `memFrame`-carrying exit upgrade.
Observations ledger entries: `seq-motive-independent-pq-no-code` and
`forloop-motive-identity-pc-store-mutation` (2026-09-01).
