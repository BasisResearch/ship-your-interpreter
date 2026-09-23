# Lane F1: partial WP, `MachWP`, partial adequacy

Branch `lane-f1` (pushed to `hub`). Design: `VsaIris/INTERP_DESIGN.md` §1, §2 F1.

## Done (all in `lake build VsaIris`, axioms ⊆ {propext, Classical.choice, Quot.sound}, see `VsaIris/Audit.lean`)

- **`MachWP` interface — ready for F3/R/H lanes** (`VsaIris/MachWP.lean`):
  fields `W`, `lat` (step modality: `id` total, `▷` partial), `lat_intro`,
  `lagRun`, `halt`, `fupd`. Instances `twpW M` (`mTWP`) and `wpW M` (`mWP`).
  Derived for any `Wp`: `Wp.run`, `Wp.runL`, `Wp.local_step`, `Wp.local_stepL`.
- Lag kernel shared by both WPs (`VsaIris/Lag.lean`): `StepRule`, `LagFoot`,
  `lag_run`. The old total `run_aux` and `LocalRun.seg_aux` are deleted; both
  are now `LagFoot` instances (`RunFact.lagFoot`, `SegFrom.lagFoot`).
- Partial WP (`VsaIris/PartialWP.lean`): `mWP`, `wp_stepRule` (▷),
  `wpP_exec_halt`, `twp_wp`, `fupd_mTWP`, `fupd_mWP`.
- Mode-generic rules: `wp_retW`, `wp_jalW`, `fnSpecW`, `wp_callW`
  (`Call.lean`); `wp_localRunW`, `runKontW` (`LocalRun.lean`);
  `Inst.wp_segW` (`Vsa/Instance.lean`). Old names (`wp_run`, `wp_local_step`,
  `wp_ret`, `wp_jal`, `wp_call`, `fnSpec`, `wp_localRun`, `Inst.wp_seg`) are
  the `twpW` instances, unchanged statements.
- Löb support: `wp_run_later` (`(wpW M).runL`), `wp_call_later` (call into a
  `▷ fnSpecW (wpW M)` Löb hypothesis).
- Partial adequacy: `AdequacyHypP`, `mach_adequateP`, `mach_adequacyP`,
  `diverges_or_halts_of_adequate` (`Adequacy.lean`); at VSA:
  `Inst.vsa_adequacyP`, `Inst.vsa_adequacyP_nonzero` (exactly `stuck_sim`'s
  `Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0`), `Inst.stepsN_of_reachesN`.
- `Specs.lean` §A now points at the landed defs; §B keeps only F3's
  `fnSpecAbort`/`wp_callAbort`. `INTERP_DESIGN.md` §1/§2 record the interface
  change (`lagRun` + `lat` instead of a bare `run` field, and why).

## Holes

None added. `python3 scripts/check_iris_holes.py` passes.

## Notes for other lanes

- F2: add `putc` to `MachWP` and restate `halt` against the console. The
  lag helpers `fullInterp_lag`/`fullInterp_intro`/`lagInterp_intro` moved from
  `Step.lean` to `Lag.lean`.
- F3: `fnSpecW`/`wp_callW` are landed in `Call.lean` (signature as in
  `Specs.lean`); `fnSpecAbort`, `wp_callAbort`, `abort_rebase` remain yours.
  For recursive calls under Löb, `wp_call_later` shows the pattern
  (`wp_jalW` gives the continuation under `Wp.lat`).
- `Specs.lean` still fails to elaborate from line ~318 (`InterpGS ?m` stuck
  in §D), which is in R/§D territory.

## Next

Nothing outstanding in F1's package. Possible follow-up if a lane needs it:
a partial `wp_exec_step` twin.
