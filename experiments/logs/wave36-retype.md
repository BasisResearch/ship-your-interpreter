# Wave 36 — re-type binaryR/logicalR ArmStages fields to carry the left-child EvalIH

Task: statement surgery on `EvalChildStages.binaryR`/`logicalR` (ArmSegSplitEval) so the
landed mid-arm seam (`MidArmFieldIH.midArmField_of_IH`) can close both fields.
Precedent check (scaffold-motive amendment): verify consumers only touch the fields in
ways the amendment survives, BEFORE editing.

## 1. Consumer-surface analysis (done BEFORE any edit)

The two fields live in `structure EvalChildStages : Prop` —
`Vsa/Sim/ArmSegSplitEval.lean:516` (binaryR at :521, logicalR at :528). Full consumer
chain of the field CONTENT, from the structure down to the point where it is
eliminated:

1. **Constructors** (spell the field types verbatim as ∀-premise args, pass through
   positionally to the structure literal — these must be re-typed in lockstep):
   * `evalChildStages_mk` — `Vsa/Sim/ArmStagesPartial.lean:55` (args binaryR :60,
     logicalR :67; literal at :92).
   * `evalChildStages_binaryL_wired` — `Vsa/Sim/ArmStagesWave34.lean:72` (args :80/:84).
   * `evalChildStages_ublr_wired` — `Vsa/Sim/ArmStagesWave34.lean:122` (args :129/:133).
2. **Field projections** — the ONLY place `.binaryR`/`.logicalR` are projected is
   `armResidGap_evalChildFields` (`ArmSegSplitEval.lean:559`, uses at :594/:596 via
   `binaryR_split`/`logicalR_split` :323/:347). Its conjuncts 3/5 have the
   `ApproxArmResid` field types (`EvalE → EEntryC → LandedN 1 (EEntryC r)`).
3. **Conjunct routing** — `armResidGap_of_stages`
   (`Vsa/Sim/ApproxArmResidGapAssembly.lean:85`) routes conjunct e2/e4 BY NAME into
   `ApproxArmResidGap`'s `binaryR`/`logicalR` fields (:97/:99). It takes
   `S : ArmStages` (hence `S.eval : EvalChildStages`) OPAQUELY — no field type spelled.
4. **The fold** — `ApproxArmResidGap = ApproxArmResid` at concrete entries
   (`ApproxArmReseat`); `ApproxArmResid.binaryR`
   (`Vsa/Sim/ApproxDispatchSuppliers.lean:190`) is projected verbatim into
   `ApproxDispatch.binaryR` (`approxDispatch_of_armResid`, :338), which is ELIMINATED
   at `allLB`'s `binaryR`/`orR`/`andR` cases (`Vsa/Sim/ApproxSeamFold.lean:467-481`).
   In scope there: `hEv : EvalE st d env l st' lv`, `hE : EEntry c … (.binary op l r)`,
   and the strong-induction IH `ih : ∀ m < n, AllLB m` — whose conclusions are ONLY
   `Divg` step lower bounds for STILL-RUNNING derivations.
5. **Bundle-opaque capstones** (take `EvalChildStages`/`ArmStages` whole — signatures
   survive any internal re-typing): `armStages_mk`, `divFamily_of_armStageComponents`
   (ArmStagesPartial:118/:135), `divFamily_of_armStages`
   (ApproxArmResidGapAssembly:148), `divFamily_wave34` (ArmStagesWave34:185).
6. **No other consumers**: `StagePreSuppliers{,2}`, `SeqHeadStages`,
   `rows/UnaryLogicalArmBridge`, `rows/BlockA{Unary,Logical}ArmGen` mention
   `EvalChildStages` in doc comments only. `check_all.sh` references the theorem NAMES
   (armResidGap_evalChildFields :695, armResidGap_of_stages :705,
   divFamily_of_armStages :706, divFamily_of_armStageComponents :801,
   divFamily_wave34 :810, evalChildStages_ublr_wired :825) for axiom checks — no type
   spelled. Nothing anywhere applies `divFamily_*` yet (frontier capstones).

**Verdict (the analogous scaffold-motive property):** every consumer beyond the three
`_mk` builders and `armResidGap_evalChildFields` handles the bundle OPAQUELY or by
routing the SPLIT OUTPUT (whose type we keep identical). So the amendment is safe iff
the extra `EvalIH` hypothesis is DISCHARGED inside `armResidGap_evalChildFields` —
i.e. before the conjunct types that `armResidGap_of_stages` routes.

## 2. Where the EvalIH is (and is NOT) available — the step-2 check

* At the DEEPEST elimination site (`allLB`'s binaryR case, ApproxSeamFold:467) the
  machine-level `EvalIH st d env l st' lv` is NOT derivable: the fold's strong
  induction is on approx fuel and its IH yields only `Divg` (step lower bounds for
  still-running relations); `EEntry` is an abstract parameter; `EvalE` is pure spec.
  Threading a per-field IH premise up into `ApproxDispatch`/`allLB` would therefore
  dead-end (the fold cannot conjure a termination-simulation Triple).
* BUT the link `EvalE → EvalIH` IS a suppliable named fact — it is exactly the term
  family capstone: `TermSimAssembly.term_sim_of_cases`
  (`Vsa/Sim/TermSimAssembly.lean:217`) concludes `mEvalE st d env e st' v t` for every
  `t : EvalE st d env e st' v`, and `mEvalE … t := EvalIH st d env e st' v`
  (TermSimAssembly.lean:80-82). So the honest shape is proposal (b) of the
  observation: the fields gain the IH premise, and the BUNDLE gains one named link
  field `evalIH : ∀ st d env e st' v, EvalE st d env e st' v → EvalIH st d env e st' v`
  (doc: supplied by `term_sim_of_cases`, conditionally on the M4 residual bundle).
  `armResidGap_evalChildFields` discharges the per-field IH from `S.evalIH` + the
  conjunct's own `hEv`, keeping every downstream type BIT-FOR-BIT identical —
  `armResidGap_of_stages`, `ApproxArmResid`, `ApproxDispatch`, `allLB`,
  `divFamily_*` signatures all untouched.

This is NOT the Law-4 STOP case: the IH is genuinely available at the consumption
site once the bundle carries the (independently-suppliable, non-circular) term-family
link — the divergence argument for a `.binary`/`.logical` node whose LEFT completed
genuinely spends the machine steps of the left child's terminating run, and that
run's existence IS the term simulation. No circularity: `term_sim_of_cases` does not
depend on any divergence-family theorem (it is the `@EvalE.rec` assembly).

## 3. Planned edits

1. `Vsa/Sim/ArmSegSplitEval.lean` — `EvalChildStages.binaryR`/`logicalR` gain
   `EvalIH st d env l st' lv →` (before `EvalE`); new bundle field `evalIH` (the
   term-family link, doc'd); `binaryR_split`/`logicalR_split` gain `hIH` arg (their
   conclusions unchanged); `armResidGap_evalChildFields` proof discharges via
   `S.evalIH`. Statement of `armResidGap_evalChildFields` UNCHANGED.
2. `Vsa/Sim/MidArmFieldWire.lean` (NEW) — the ∃-ghost landing bundle
   `MidArmLeftJalBundle` (armTail_rec's left-jal pre at the PINNED arm PCs + the
   per-arm jal-site fact + `MidArmRightMarshal` on every `SubEvalReturn`), the
   destructurer `jalPreBundle_of_midArmBundle` (= ONE `midArmField_of_IH` call), the
   per-arm staging residuals `BinaryRStagePre`/`LogicalRStagePre` (arm entry →
   `MidArmLeftJalBundle`, strictly smaller than the fields), and the field closers
   `binaryR_field_of_stage`/`logicalR_field_of_stage`.
3. `Vsa/Sim/ArmStagesPartial.lean` — `evalChildStages_mk` re-typed args + `evalIH` arg.
4. `Vsa/Sim/ArmStagesWave34.lean` — both wired builders re-typed;
   `evalChildStages_ublr_wired` closes binaryR/logicalR via the closers (→ 5/14),
   its opaque binaryR/logicalR args replaced by the `*StagePre` staging residuals.
5. Re-verify serially (one lean process) the whole import cone of ArmSegSplitEval:
   ArmSegSplitEval → MidArmCombinator → MidArmFieldIH → StagePreSuppliers →
   StagePreSuppliers2 → EvalChildFieldCombinator → rows/UnaryLogicalArmBridge →
   rows/BlockAUnaryArmGen → rows/BlockALogicalArmGen → ApproxArmResidGapAssembly →
   ArmStagesPartial → MidArmFieldWire (new) → ArmStagesWave34.

## 4. RESULTS (all landed, green, axiom-clean)

Every verification via ONE serial `lake env lean` (+ `-o/-i` olean regen into
`.lake/build/lib/lean/`), in dependency order; all `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}; `scripts/check_discipline.py` OK.

### Edits
* `Vsa/Sim/ArmSegSplitEval.lean` (3.3s) — `EvalChildStages.binaryR`/`logicalR` gained
  `EvalIH st d env l st' lv →`; NEW bundle field `evalIH : ∀ …, EvalE → EvalIH` (doc:
  supplied by `TermSimAssembly.term_sim_of_cases`, mEvalE := EvalIH); `binaryR_split`/
  `logicalR_split` gained `hIH`; `armResidGap_evalChildFields` STATEMENT UNCHANGED
  (IH discharged internally via `S.evalIH … hEv`).
* `Vsa/Sim/MidArmFieldWire.lean` (NEW, 2.0s) — `MidArmLeftJalBundle` (∃-ghost
  left-jal landing bundle: armTail_rec pre at pinned PCs + `MidArmRightMarshal` on
  every `SubEvalReturn`, ONE ∃ for ghost coherence; R7 allow, precedent JalPreBundle);
  `jalPreBundle_of_midArmBundle` (ONE `midArmField_of_IH` call; hjaltgt/hlink/hretAl
  decided via the EvalBinSim:513 recipes; jal-site = landed
  `BinHeadSites.site_800034f8_ee` — NOT carried in the bundle);
  `BinaryRStagePre`/`LogicalRStagePre` (per-arm honest staging residuals, stop at the
  LEFT jal); `binaryR_field_of_stage`/`logicalR_field_of_stage` (field closers,
  `LandedN.bind`).
* `Vsa/Sim/ArmStagesPartial.lean` (0.7s) — `evalChildStages_mk` gained `evalIH` arg +
  re-typed binaryR/logicalR args. `divFamily_of_armStageComponents` signature-stable.
* `Vsa/Sim/ArmStagesWave34.lean` (0.7s) — both wired builders gained `evalIH` +
  re-typed args; `evalChildStages_ublr_wired` now CLOSES binaryR/logicalR via the
  field closers, modulo `hBinRStage`/`hLogRStage`. `divFamily_wave34` signature-stable.

### Regression (no consumer weakening)
`armResidGap_evalChildFields`, `armResidGap_of_stages`, `divFamily_of_armStages`,
`divFamily_of_armStageComponents`, `divFamily_wave34` — statements bit-for-bit
unchanged, all re-verified green + axiom-clean. `ApproxArmResid`/`ApproxDispatch`/
`allLB` (the fold) untouched. Re-verified import cone (serial): ArmSegSplitEval →
MidArmCombinator → MidArmFieldIH → MidArmFieldWire → StagePreSuppliers →
StagePreSuppliers2 → rows/UnaryLogicalArmBridge → rows/BlockAUnaryArmGen →
rows/BlockALogicalArmGen → EvalChildFieldCombinator → ApproxArmResidGapAssembly →
ArmStagesPartial → ArmStagesWave34.

### Fields board — EvalChildStages (14 + evalIH link)
5/14 MACHINE-COMPOSED: unary (UnaryArmGeomProvider), binaryL (BinArmGeomProvider),
logicalL (LogicalArmGeomProvider) — wave 34; binaryR (BinaryRStagePre), logicalR
(LogicalRStagePre) — wave 36, via `armTail_rec`(IH) ≫ `binaryR_midStage1`.
9/14 named ∀-premises: assignE/callF/argsHead/stmtExpr/stmtRet/stmtVarInit/
stmtIfCond/stmtWhileCond/flCond. New bundle-level named premise: `evalIH`
(supplier: term_sim_of_cases). NonEval (11) / SqEntry (3, seqHead wired) / flStep
unchanged.

### Wiring lines (NOT applied — coordinator)
Vsa.lean (after `import Vsa.Sim.MidArmFieldIH`):
    import Vsa.Sim.MidArmFieldWire
scripts/check_all.sh THEOREMS:
    Vsa.Sim.jalPreBundle_of_midArmBundle              # MidArmFieldWire (left-jal bundle + EvalIH -> JalPreBundle r; ONE midArmField_of_IH call)
    Vsa.Sim.binaryR_field_of_stage                    # MidArmFieldWire (re-typed binaryR field closed modulo BinaryRStagePre)
    Vsa.Sim.logicalR_field_of_stage                   # MidArmFieldWire (re-typed logicalR field closed modulo LogicalRStagePre)

### Observation appended
`2026-09-01 armtailrec-pre-tower-has-no-named-def` — the armTail_rec precondition
tower is now spelled 4x (armTail_rec / JalPreBundle / midArmField_of_IH.hpre /
MidArmLeftJalBundle); proposal: one `SubCallStagedPre` def in EvalRecCommon.
