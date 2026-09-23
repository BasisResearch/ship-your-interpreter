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
