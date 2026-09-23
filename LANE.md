# Lane F2: the console resource

Package F2 of `VsaIris/INTERP_DESIGN.md` §9.

## Done
- `MachineModel.out` (VSA: `Vsa.Machine.output`).
- Console ghost cell `consoleOwn s` (`Ptsto.lean`): a ghost map on `MachGS.conName`, key 0.
  Its authority `conInterp` is part of `mstateInterp` and lags with the register and memory
  maps (`lagInterp`, `ConAgree`).
- `RunFactO … o` (`Step.lean`): a run's console effect `OutStep` (`none` silent, `some o` prints `o`).
  `RunFact` is the silent case, so every segment fact must now frame the output.
  `wp_run` is unchanged for clients; `wp_runOut` is the printing (`putc`) rule; `wp_halt_console`
  and `HaltFact` give halt/console agreement.
- Adequacy allocates the console at the initial output. `AdequacyHyp` gains the initial output `o`
  and the client receives `consoleOwn o`.
- VSA: `vsaModel.out`, `VsaOk.htifIdle` (`htif_payload_writes = 0`). `seg_runFact` frames both.
  `jalExec_of_site` takes `StepConFrame` (`stepConFrame_of_jalObs`).

- `Vsa/Console.lean`: `TohostSite` + decided `Cert`; `putc_runFact`/`wp_putc` (print one
  character), `exit_haltFact`/`wp_exit` (halt with the console's output), `vsa_adequacy_exit`
  (`Halts c out e ∧ φ`), and the newlib sites `putcSite` (`_write`, 0x8000005c) and `exitSite`
  (`_exit`, 0x80000190).
- `Interp/Specs.lean`: `MachWP` has `putc`/`halt` fields; `InterpGS` no longer carries the console.
- INTERP_DESIGN.md §2 F2 and §3 record the as-built design and the two changes from the draft.

## In flight
- Waiting for F1's `MachWP` on `hub/lane-f1` to add the `putc`/`halt` fields there and prove them
  for the partial WP.

## Holes
None.

## Interface changes other lanes must know
- `SegFrom` (LocalRun) and `RetExec`/`JalExec` (Call) have a new `M.out σ' = M.out σ` conjunct.
- `VsaOk` has a fifth field `htifIdle`; `MachGS` has `conName`; `MachPreG` has `conG`; `MachGF` has slot 7.
- `lagInterp`/`lagInterp_intro` carry the console map `mo`.
