# Wave 35 — ArmStages stagePre fan-out log

Task: fan out remaining ArmStages stage fields (divergence board 3/14 eval-child → as
far as possible). Own file: `Vsa/Sim/ArmStagesWave34.lean` capstone.

## Reading-pass verdict (the structural gap for binaryR/logicalR)

The `EvalChildStages.binaryR` field is typed
`EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) → LandedN 1 c (JalPreBundle r c' st')`.
Its inputs are the SPEC-level left eval `EvalE l st' lv` + the ARM-ENTRY config `c`.
The landed mid-arm re-cut `MidArmCombinator.binaryR_midStage1` starts from `cL` ALREADY
at `SubEvalReturn` (PC 0x800034fc, post-left-return). Bridging `c → cL` = running the
LEFT `jal eval_expr` and returning = `armTail_rec`, whose `hIH` premise is the
MACHINE-level `EvalIH st d env l st' vsub`. That IH is NOT a field parameter and is NOT
threaded by `armResidGap_of_stages`/`ApproxArmResidGapAssembly` (only `EvalE` + config
are passed). So binaryR/logicalR CANNOT close from the field inputs alone. Recorded in
observations.md (`2026-09-01 binaryR-field-lacks-machine-IH`).

## Batch 1 — the IH-carrying mid-arm field combinator (LANDED, axiom-clean)

`Vsa/Sim/MidArmFieldIH.lean` — verified green + axiom-clean (~1.4s), olean regen'd.

- `MidArmRightMarshal` (def : Prop) — the honest residual naming the DELTA between
  `SubEvalReturn`'s content and `binaryR_midStagePre`'s precondition: the RIGHT-operand
  facts that survive the left call (transported node ptr `read64 mem (aExpr+24)=aROp`,
  frame population `[sp-1120,sp)`, `ExprRepr aROp er` survival, Value_intLoaded/
  IntSlotPinned, BinExtras-shaped right geometry). SubEvalReturn does NOT carry these
  (it only knows the LEFT sub-result) — exactly the `hAgNode`/`hPopCL`/`hexprR2`
  transport `EvalBinSim.blockB_binary` derives inline from BinArmExtras + the left
  memFrame. Named ONCE so the fold discharges it per-arm (over its BinArmExtras), not
  per-operator.
- `midStage1_of_marshal` — feeds a SubEvalReturn-reached config (+ MidArmRightMarshal)
  into `binaryR_midStage1`, landing `JalPreBundle er`. The ONE plug point of the two
  halves; GoodState/tick/minstret/code come from SubEvalReturn (passed separately).
- `midArmField_of_IH` — THE FULL combinator: `armTail_rec` (left recursive call via the
  machine IH) ≫ `binaryR_midStage1` (mid-arm re-cut). From a config `c` at the LEFT jal
  (= JalPreBundle l content = armTail_rec precondition) + `EvalIH st d env l st' vsub` +
  `hMarshalAll` (MidArmRightMarshal on every SubEvalReturn config), lands
  `JalPreBundle r st'` — the exact binaryR/logicalR staging obligation. Composition:
  armTail_rec's Triple → Landed.of_triple → SubEvalReturn at cL → midStage1_of_marshal
  → JalPreBundle r; the two runs compose via Steps.toN + StepsN.trans_add (≥1 preserved).
  Op-independent (arm PCs 0x800034f8/0x800034fc/imm 0x1ffc6c are binary/logical-shared)
  → ONE combinator serves BOTH binaryR AND logicalR (logicalR's value_truthy tail is
  AFTER the right returns, not on this mid-arm span).

  All three axioms ⊆ {propext, Classical.choice, Quot.sound}.

### Gotcha caught
`obtain ⟨…⟩ := hSER` consumes the fvar; needed hSER twice (project shared facts +
feed hMarshalAll). Fix: `obtain ⟨…⟩ := id hSER` destructures the VALUE, leaving the
fvar in context.

## Why this is the honest deliverable (not the field wire)

`midArmField_of_IH` is the seam the FOLD instantiates once its strong-induction IH is
in scope. It does NOT close the binaryR field as-typed (the field lacks the IH). The
observation's proposal (b) — re-type binaryR/logicalR to carry the IH — makes the whole
`SubEvalReturn → JalPreBundle r` mid-arm a ONE-call composition, no re-derivation of the
7 sites or the node transport. This combinator IS that one call.

## Per-field board (unchanged field count; the seam is now BUILT)

### EvalChildStages (14)
3/14 FIELD-COMPOSED (unary, binaryL, logicalL — wave 34, via evalChildField_of_blockA_stage).
binaryR/logicalR: mid-arm SEAM now built (`midArmField_of_IH`), but the FIELD stays a
named residual — closable only when the fold provides the IH (structural, not wiring).
assignE/callF/argsHead + 6 exec-side stmt*/flCond: unbuilt per-arm arm-head cuts.

### NonEvalChildStages (11), SqEntryStages (3), flStep (1): unchanged from wave 34.

## Wiring lines (report-only; NOT applied — do not touch Vsa.lean/check_all.sh)
Add to Vsa.lean:
    import Vsa.Sim.MidArmFieldIH
Add to scripts/check_all.sh axiom-checked list:
    Vsa.Sim.midStage1_of_marshal
    Vsa.Sim.midArmField_of_IH
  (all ⊆ {propext, Classical.choice, Quot.sound})
