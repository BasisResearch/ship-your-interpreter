# Lane E4: the call family (closure call, natives, call errors)

Branch `lane-e4` (from `wave4-base`, merged `hub/iris-main` with
`INTEGRATION.md`, and `hub/lane-e6` for the argument loop's statement).
Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row "call"). Rows:
`scripts/iris_arms/arms.d/e4-call.tsv`.

## Dependencies
- E6: the argument loop `evalArgsT_body`/`evalArgsP_body`
  (`VsaIris/Interp/SpecLoop.lean`), taken as hypotheses (E6's statement is
  used as is).

## Done
- `Interp/CallJalr.lean`: the indirect call `jalr a6` (the native dispatch):
  `JalrExec`, `wp_jalrW`/`wp_callRW`/`wp_callAbortR` (either WP), the VSA
  instance `jalrx_800039f4` (over VSA's observation `stepObs_jalr`),
  `ms_callHelperR`/`ms_callAbortR` (call from a run's state).

## In flight
- The shared call prefix (callee child, argc test, loop, kind dispatch) and
  the native arms.

## Holes
None added.
