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

# Lane F2: the console resource

Package F2 of `VsaIris/INTERP_DESIGN.md` §9. Branch `lane-f2`, merged with `hub/lane-f1`
(`MachWP`, the partial WP, the shared lag kernel). As-built design: INTERP_DESIGN.md §2 F2.

## Done
All in `lake build VsaIris`; axioms ⊆ {propext, Classical.choice, Quot.sound} (`VsaIris/Audit.lean`).

- `MachineModel.out` (VSA: `Vsa.Machine.output`).
- Console cell `consoleOwn s` (`Ptsto.lean`): ghost map on `MachGS.conName`, key 0. Its authority
  `conInterp` is in `mstateInterp` and lags with the register and memory maps (`lagInterp`,
  `ConAgree`). `consoleOwn_excl`.
- Lag kernel (`Lag.lean`): `LagFoot.look`/`commit` carry all three authorities (`mauths`);
  `LagFoot.ofRM` builds a silent run's instance from register/memory lookup/commit plus its output
  frame.
- `Step.lean`: `OutStep`, `RunFactO … o` (console effect), `RunFact` = silent `RunFactO`,
  `RunFact.lagFoot` (silent), `RunFactO.lagFootPrint` (printing, owns the cell), `HaltFact`.
- `MachWP.lean`, for either WP: `MachWP.runOutL`/`runOut` (the `putc` rule) and
  `MachWP.haltConsole` (halt/console agreement), derived from `lagRun`/`halt`. Total names
  `wp_runOut`, `wp_halt_console`.
- Adequacy (total and partial) allocates the cell at the initial output; `AdequacyHyp`/
  `AdequacyHypP` take the initial output `o` and hand the client `consoleOwn o`.
- VSA (`Vsa/Instance.lean`, `Vsa/Tools.lean`): `vsaModel.out`, `VsaOk.htifIdle`
  (`htif_payload_writes = 0`), `seg_runFact` frames both, `jalExec_of_site` takes `StepConFrame`
  (`stepConFrame_of_jalObs`).
- VSA console (`Vsa/Console.lean`): `TohostSite` + decided `Cert`; `putc_runFact`, `wp_putcW`
  (print one character), `exit_haltFact`, `wp_exitW` (halt with the console's output),
  `vsa_adequacy_exit` (`Halts c out e ∧ φ`); newlib sites `putcSite` (`_write`, 0x8000005c) and
  `exitSite` (`_exit`, 0x80000190), both certified by `decide` + the decode table.

## In flight
Nothing.

## Holes
None added. `python3 scripts/check_iris_holes.py` passes.

## Notes for other lanes
- Every run fact frames the output: `SegFrom` (LocalRun), `RetExec`/`JalExec` (Call),
  `MachWP.local_step` have a `M.out σ' = M.out σ` conjunct. A new multi-step rule that prints
  nothing is `LagFoot.ofRM`; one that prints owns `consoleOwn` in its footprint.
- `VsaOk` has a fifth field `htifIdle`; `MachGS` has `conName`; `MachPreG` has `conG`; `MachGF`
  has slot 7; `lagInterp_intro` takes the console map `mo`.
- `world` (R) uses `VsaIris.consoleOwn st.out`; `InterpGS` no longer carries the console.
- A print path (H2 `value_print`, natives) ends in `_write`'s loop, whose store is `putcSite`:
  use `Inst.wp_putcW putcSite putcSite_cert`. The exit tail (A) ends in `_exit`'s store:
  `Inst.wp_exitW exitSite exitSite_cert`.

# Lane S1: cost existence, stack admissibility, Room/Cost bridge

Design: `VsaIris/INTERP_DESIGN.md` §5 (§5.1b), §9 (S1), §10.4, "STATEMENT CHANGE".

## Done
1. **StackAdmissible (Q1).** `InterpRunReadyFacts.stack_admissible`
   (`Vsa/Sim/LayoutInstance.lean`: `ProgramStackFits`, `programStackFits`
   checker, `ProgramStackFits.execBudget`). `Refinement.lean` is unchanged, and
   `interpRunLayout' = interpRunLayout`.
   - Control witness: `NativeNameAudit.Control.readyFacts`.
   - `c/tests/*.wl` witnesses: `Vsa/Sim/StackAdmissibleWitness.lean` (kernel
     `decide`).
2. **Cost existence/soundness.** `Vsa/While/CostExists.lean`:
   `EvalECost.exists` … `ExecSeqCost.exists`, `BigStep.cost`, and
   `EvalECost.sound` … `ExecSeqCost.sound` (`CostExists`/`CostSound`).
3. **Room ↔ Cost bridge.** `VsaIris/Vsa/CostRoom.lean`:
   - byte-credit `costRoom` for `isHeapRoom`;
   - per-site `Covers` lemmas (`physSize n ≤ 2c`);
   - `CostTop.spend`/`.split`;
   - `costRoomAt` + `mallocCostSpec`, with obligation `MallocCostRun` (H4);
   - boundary `costRoom_of_bigStep`;
   - control witness `Control.costReserve`.

## In flight
None.

## Holes
None added. The `alloc.mallocRoomRun` row in HOLES.md now names its
byte-credit form `MallocCostRun`, which H4 owns.

## Next (for other lanes)
- A0 sets `heapRes (.counted k) := isHeapRoom vsaLayout costRoom H k` and
  starts it from `costRoom_of_bigStep`.
- H4 proves `MallocCostRun`, and the realloc analogue at `costRoomAt`.
