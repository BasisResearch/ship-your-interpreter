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

## In flight
- The VSA putchar and exit instances (`putc_runFact`, `exit_haltFact`) over
  `stepObs_tohost_putchar`/`stepOnce_tohost_G`.

## Holes
None.

## Interface changes other lanes must know
- `SegFrom` (LocalRun) and `RetExec`/`JalExec` (Call) have a new `M.out σ' = M.out σ` conjunct.
- `VsaOk` has a fifth field `htifIdle`; `MachGS` has `conName`; `MachPreG` has `conG`; `MachGF` has slot 7.
- `lagInterp`/`lagInterp_intro` carry the console map `mo`.
