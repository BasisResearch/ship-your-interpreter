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
