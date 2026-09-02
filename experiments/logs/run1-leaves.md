# run1 — leaf fields (hInt/hNull/hBool/hStr)

## 2026-09-02 wave 47d (blocked; verdict machine-checked)

- Harvested the B1 re-attempt worker's artifacts into main:
  `experiments/fleet/obstructions/B1_leaves_reattempt.lean` (elaborates green +
  axiom-clean against main @ eb2a139) + the two observation entries
  (`leafwiden-entry-gap-persists`, `evalentry-missing-nbs-callee-geom`).
- Attempted the ordered re-seat (proposal (a): surface the sims' internal
  pres/surv through `EvalExitD`).  REFUTED as sufficient: the internal
  survival witness (`EvalIntSim2.lean:836-859`) has footprint
  `[SL.lo, sp) ∪ sret` — the motive-fixed `EvalExitD` demands
  `stackFoot SL = [SL.lo, SL.hi)`; the caller strip `[sp, SL.hi)` has no
  supplier (entry footprint stops at `sp`; `StoreRepr` leaves strings/AST
  region-unpinned, so no disjointness route).
- Landed the sharpened machine-checked verdict:
  `experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean` — green,
  axioms ⊆ {propext, Classical.choice, Quot.sound}.  Names the TWO suppliers
  (`EntryStackSurv` = the `EvalEntry.store_survives` footprint amendment
  `sp → SL.hi`; `LeafExitPin` = the block-interface re-land, transported by
  `blockD_v`'s existing `Q` parameter) and proves them JOINTLY SUFFICIENT:
  `skelH{Int,Null,Bool,Str}_of_pins` discharge the four holes given them
  (+ the independent null/bool/str callee geometry).
- Fan-out of the mandatory entry amendment measured: `store_survives :=` at 15
  construction sites in 13 files; 43 use sites; `ExecEntry.store_survives`
  cascade.  ITEM-ZERO-scale — deliberately NOT half-landed on main (sole
  writer) in a bounded task.
- No `Field_h*.lean` landed, no TSV rows flipped, no Vsa.lean wiring: nothing
  discharged.  Observation entry: `leaf-reseat-blocked-on-entry-footprint`.

## 2026-09-02 wave 47e (EntryStackSurv + LeafExitPin landing — this session)

- **EntryStackSurv LANDED**: `EvalEntry.store_survives` footprint amended
  `[SL.lo, sp)` → `[SL.lo, SL.hi)` (`InterpEntry.lean`) + the `ExecEntry`
  cascade (`ExecEntry.lean`); mono lemmas `EvalEntry.store_survives_sp` /
  `ExecEntry.store_survives_sp` / generic `storeSurvSp` recover the old form.
  Extension entries (`EvalNullEntry`/`EvalBoolEntry`/`EvalStrEntry`/
  `EvalVarEntry`), `ApproxArmReseat` twins, `LoopHeadDispatchGeom` widened to
  match.  Fan-out EXCEEDED the measured 15/43: the survival fact also rides
  ~a dozen inline ∧-tower conduits (blockA_k pre, ArmEntryK, armTail_v/rec/es,
  ArmSegSplit* bundles, ExecBlock, 2 ExecRecCommon premises) — all widened in
  place; child constructions got SIMPLER (sub-sret windows absorbed by
  `[SL.lo, SL.hi)`).  Observation:
  `entry-footprint-amendment-conduit-fanout`.
- **LeafExitPin LANDED**: `LeafMemPin` structure (EvalSimCommon; MemExtends +
  no-arena-drift agreement), threaded through `blockA_k` post
  (`∧ MemExtends m0 ment`), the leaf `blockC_*` posts, `armTail_v`, and carried
  across the epilogue by `blockD_v`'s existing `Q` — four PINNED sims
  `evalIntSimP`/`evalNullSimP`/`evalBoolSimP`/`evalStrSimP` (old sims = thin
  pin-forgetting weakenings).  `value_null_spec_full`/`value_str_spec_full`
  gained the presence clause (bool already had it; int's `int_post` already
  had it).  `MemExtends` block RELOCATED EvalRecCommon → EvalSimCommon (the
  leaf blockC files sit below EvalRecCommon).
- **Re-seat**: `EvalExitPinned`/`LeafWidenP` + `leafWidenP_of_entry` (the
  verdict's `leafWiden_of_pins`, landed) + `evalExitD_of_pinnedExit`
  (`EvalLeafD.lean`); `eval{Int,Null,Bool,Str}SimD` re-seated on the pinned
  sims; `TermRouting` leaf residuals restated at `LeafWidenP`.
- **Fields**: `rows/Field_hInt.lean` — `field_hInt` DISCHARGES `hInt`
  outright (`skelHInt_discharged`).  `rows/Field_h{Null,Bool,Str}.lean` —
  widener half discharged; residual = ONLY the callee geometry
  (`{Null,Bool,Str}LeafGeom`, = the verdict's `*Geom`), the INDEPENDENT
  pre-existing gap `evalentry-missing-nbs-callee-geom` (machine-checked in
  `B1_reseat_footprint_verdict.lean`); `field_h*_of_geom` are the reductions.
  So census expectation is 1 FOUND (hInt), 3 reduced-not-found — the task
  brief's "4 FOUND" overcounted by eliding the geometry premise the verdict
  itself names.
- **Latent-stale repairs surfaced by the full-cone regen** (pre-existing reds
  masked by fresh-looking oleans — the known stale-olean gotcha; all were
  broken by earlier ITEM-ZERO amendments, NOT by 47e):
  `rows/EvalVarBridge.lean` (`varLeafResid_of_rowResid` missing the `d`/`env`
  binders), `EntryDrive.lean` + `DriveToLoopHeadSpans.lean` (`DriveToLoopHead`
  and `SegEntryFields` gained the `Interp_runLoaded m0` image conjunct the
  amended `interpInitStoreRepr_of_drive` demands), `rows/CallCruxMarshal4.lean`
  (`ValueNullStage`/`FoldDefineExitReturn` gained `eval_code` +
  `buf_evalcode_disjoint` for the amended `BodyHandoff`), `rows/
  BinIntReadback.lean` + `TermBundles.lean` (the `BinIntCellResid` store-bodies
  conjunct), `rows/ArmDispatchCombinatorExec.lean` + `ArmDispatchInstancesExec`
  (the item-zero child-budget trio threaded through `execArmDispatch_of_slot`,
  derived per instance via `StackOK.child` + the `bodiesBound` kit).
- Full 300-file dependent cone regenerated dependency-ordered
  (`lake env lean -o`), final sweep: 0 failures, `Vsa.lean` root green.
- **Census (`field_census.py -j2`)**: `{'FOUND': 1, 'NOT_FOUND': 57}` — `hInt`
  is the FIRST field ever discharged (baseline 58/58 NOT_FOUND).
  `hNull`/`hBool`/`hStr` remain NOT_FOUND: their sole residual is the
  independent `evalentry-missing-nbs-callee-geom` geometry gap the verdict
  itself names as the `hG` premise of `skelH{Null,Bool,Str}_of_pins` — the
  task brief's "expect 4 FOUND" elided it.  Machine-checked obstruction:
  the `hG : {Null,Bool,Str}Geom` premise (verdict file) = the landed
  `{Null,Bool,Str}LeafGeom` (`rows/Field_h{Null,Bool,Str}.lean`); nothing on
  main pins the value_{null,bool,str} code bytes / jump-table slots 1-3 /
  str payload region under a bare `EvalEntry`.
- TSV: `hInt` flipped to `done`; null/bool/str notes updated (widener half
  discharged, geometry-only residual).  check_discipline OK (9 rules).
