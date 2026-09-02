# prove-intcells — the 11 LA-int cell fields (clone /tmp/vsa-prove-intcells)

TARGET: hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe.
Skeleton holes in `Vsa/Sim/rows/AssemblySkeleton.lean` (SkelHIAdd…SkelHNe).

## Finding: all 11 holes are FALSE AS STATED (X2 class, machine-checked)

Each `SkelHI*` unfolds to `∀ g N A SL φf φc st st' st'' el er a b sp r sret
aExpr m0, BinIntCellResid <op> <Resid> … m0` (eq/ne: `… vl vr … ,
BinEqCellResid … m0`) with **no leading hypothesis**.  The ∃-body demands
`BinArmExtras … m0` whose field `slot6 : KindSlotPinned 6 (0x800034e8#64) m0`
is a static jump-table pin.  Instantiate at `m0 = ∅`: `KindSlotPinned 6 _ ∅`
requires four table bytes present in the empty memory — false.  Hence every
hole is refutable, not merely unprovable.  (hIDiv: discharge the non-overflow
guard `¬(a=-2^63∧b=-1)` with `a=0,b=1` first; identical `slot6` refutation.)

This is EXACTLY the design's X2 diagnosis (`experiments/design/loop-arm.md`
§LA-int: "refuted only by X2 — ∀-ghost, no entry").  Per Law 4 I return the
machine-checked obstruction, not a workaround.

## CURE (out of this pass's scope — a shared-file statement change)

Add `entry : EvalEntry g N A SL φf φc st … m0 (.binary op el er)` as a
HYPOTHESIS field to `BinIntCellResid`/`BinEqCellResid` in
`Vsa/Sim/rows/BinDispatchRow.lean` (the B2-carry amendment, design §(a),(d)).
Then `slot6`/`sproom`/`node_*` become preconditions the entry supplies instead
of free conclusions, and the LANDED value paths (AddResid…GeResid, binRow_*,
value_equal_spec_full) relight verbatim — no new value-path proof.  Coordinator
applies; the 11 int/eq cell rows then recompile (design T-LA-int-relight).

## Assumption gate (contract)

No NEW named premise was introduced mid-proof — the refutations are
self-contained falsity proofs (only proved lemmas: `kindSlot6_empty_false`).
Gate satisfied trivially.  Design-side evidence for the cure's direction:
the mined KindBridge / entry candidates in `experiments/invariants/hI*.md`
+ hEq/hNe all recorded **candidate-mined+SURVIVED** (statement_fuzz), i.e. the
entry-carry target is not-false; it is the coordinator's green target.

## Per-field table

| field | verdict | mechanism | mined-cand fuzz | elab |
|-------|---------|-----------|-----------------|------|
| hIAdd | REFUTED (false as stated) | slot6 @ m0=∅ | SURVIVED | ~0.9s (olean-built) |
| hISub | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hIMul | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hIDiv | REFUTED | guard a=0,b=1 then slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hIMod | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hILt  | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hILe  | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hIGt  | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hIGe  | REFUTED | slot6 @ m0=∅ | SURVIVED | ~1.0s |
| hEq   | REFUTED | slot6 @ m0=∅ (BinEqCellResid) | SURVIVED | ~1.0s |
| hNe   | REFUTED | slot6 @ m0=∅ (BinEqCellResid) | SURVIVED | ~1.0s |

All 11 theorems axiom-clean: {propext, Classical.choice, Quot.sound}.

## Files (all NEW under Vsa/Sim/rows/)

Field_hIAdd.lean (template: `witSt`, `kindSlot6_empty_false`, `field_hIAdd_refuted`)
Field_hISub/hIMul/hIDiv/hIMod/hILt/hILe/hIGt/hIGe/hEq/hNe.lean
  (each imports Field_hIAdd for the two shared helpers).
