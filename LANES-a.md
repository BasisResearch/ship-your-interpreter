# Lane A: the final assembly (`endToEnd_refinement` from `IrisHoles`)

Branch `lane-a` (from `hub/iris-main` `05874b5`; merged `hub/lane-e4` through
`e7a56ec`). Design: `VsaIris/INTERP_DESIGN.md` §4, §5, §9 package A.

## Status: done

`lake build Vsa VsaIris VsaIris.Audit` is green (2601 jobs).
`#print axioms Vsa.Sim.EndToEnd.endToEnd_refinement` reports
`[propext, Classical.choice, Quot.sound]`. `check_iris_holes.py`: 10 ledgered
holes (the scheduled `newlib.*`/`out.*` ones, unchanged). No `sorry`, `admit`,
`axiom`, `native_decide`, `bv_decide` or raised limits. The generated-case
drift gate (`gen_iris_cases.py --check`) is clean.

## The theorem (`VsaIris/Interp/EndToEnd.lean`)

```lean
theorem Vsa.Sim.EndToEnd.endToEnd_refinement (h : VsaIris.Interp.IrisHoles) :
    ∀ p c, Loaded interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)

structure VsaIris.Interp.IrisHoles : Prop where   -- Interp/Holes.lean
  newlib : Newlib.NewlibHoles   -- snprintf, fprintf, fwrite, exitHandlers
  out : Newlib.OutHoles         -- fputs, fputc, fwrite, fprintf, snprintfFn, snprintfInt
```

`Refinement.lean` is unchanged.

## How it is assembled

| piece | file |
|---|---|
| total recursion over the nine cost relations (fifty cases, `binOpSem` dispatch) | `Interp/TermSim.lean` (`interpSeqT_all`, `execDispT_all`) |
| partial specs by one Löb | `Interp/StuckSim.lean` (`specsP_all`) |
| `interp_run`'s whole run, both modes (prologue, `setjmp`, loop, normal/abrupt/abort exits, `main`, `exit`) | `Interp/TopRun.lean`, `TopRunP.lean`, `Vsa/MainOk.lean`, `TopEntryBoot.lean` |
| adequacy inputs (`topLive`, `VsaOk`, register map) | `Interp/TopBoundary.lean` |
| every callee spec and named premise, closed | `Interp/Supply.lean` (`supplies_of : IrisHoles → Supplies`), `SupplyBoot.lean` |
| string/memory routines proved on the Iris route | `ProofStrcmp`, `ProofMemcpy`, `ProofStrlen`, `ProofStrcpy(H)`, `ProofStrHeap` |
| composition with adequacy | `Interp/EndToEnd.lean` (`term_sim_of`, `stuck_sim_of`, `interpSim_iris`) |

## Statement changes (each recorded in `INTERP_DESIGN.md`)

- **Q7 (user decision): helper headroom.** `helperHeadroom = 2048` in
  `ProgramStackFits.need` (a `Loaded` narrowing) and in `stackBudget`.
- **`Loaded` boundary fields** (standing decision, control witness
  `physicalConfigS0`): every GPR present (`gprs`), `s0 = &_impure_ptr`
  (`s0_impure`).
- `newlib.exitHandlers` is exact (quiet) from `StdioOK`.
- `_impure_ptr` is read-only inside `stdioAt` (it was owned both exclusively
  and persistently).
- `closOwn` carries the closure's read geometry (`CloSupply` proved).
- Helper specs carry their code context (`codeX`, `binImg`) in their
  preconditions; `memcpy`/`strcpy` destinations lie above the HTIF words.
- `StackGeom.top`, and `evalCore`/`CoreOK` cover only the stack below
  `interp_run`'s frame; the top loop keeps the frame image on abort and the
  statement's `line` readable at abrupt exits; one top-abrupt rule.

## Removed

`Vsa/Sim/EndToEnd.lean` (`RemainingWork`, the old `endToEnd`),
`Vsa/Sim/DivFamilyAssembly.lean` (`DivWork`),
`Vsa/Sim/rows/ErrFamilyAssembly.lean` (`ErrWork`), and the feeders nothing
else imported: `Vsa/Sim/IndexedErrorPrototype.lean`,
`Vsa/Sim/rows/CallResidProviders.lean`, `Vsa/Sim/rows/NativeArmDispatch.lean`;
the `RemainingWork` refutation corollaries in `OutputAliasRefutation.lean` and
`AstAccessAudit/AccessRefutation.lean`; the design skeleton
`VsaIris/Interp/Specs.lean`. Kept because other modules or generators use
them: `TermResidualsBase` (extended by `TermResidualsCore`, which rows use),
`ExitPathSeg.lean` and the generated `rows/LayoutGround.lean`.

## Follow-ups (cleanup, not blocking)

- `SWP` hard-wires `gp` as its only read-only register; the memcpy (`MW`) and
  string (`SR`) runs are copies without it. Make `SWP` generic over its
  read-only list and retire the copies; add CLAUDE.md rows for these layers
  and register `gen_memcpy_steps.py`/`gen_str_steps.py` in the drift gate.
- `scripts/tests` failures in `test_check_all`/`test_boundary_regressions`
  exist before and after this lane (environment paths).

## Holes

None added. 10 ledgered (`newlib.snprintf`, `.fprintf`, `.fwrite`,
`.exitHandlers`; `out.fputs`, `.fputc`, `.fwrite`, `.fprintf`, `.snprintfFn`,
`.snprintfInt`); `newlib.exitHandlers` is now stated exact from `StdioOK`.
