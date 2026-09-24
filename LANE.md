# Lane E4: the call family (closure call, natives, call errors)

Branch `lane-e4` (from `wave4-base`; merged `hub/iris-main` with
`INTEGRATION.md`, `hub/lane-e6` for the argument loop's statement, and
`hub/lane-e2` for the eval error-arm layer). Design:
`VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row "call"). Rows:
`scripts/iris_arms/arms.d/e4-call.tsv`.

## Dependencies (used as is)
- E6: `evalArgsT_body`/`evalArgsP_body` (`SpecLoop.lean`), hypotheses of the
  prefix.
- E2: `errCtx`, `ErrEnv`, `ms_rtErrEval`, `valueKindNameSpec` (`SpecErr.lean`,
  `ErrArm.lean`).
- H2: the natives' specs; H5: `rtErr_spec`, `abortRes`.

## Done (axioms ⊆ {propext, Classical.choice, Quot.sound})
- `CallJalr.lean`: the indirect call `jalr a6` (the native dispatch):
  `JalrExec`, `wp_jalrW`/`wp_callRW`/`wp_callAbortR`, the VSA instance
  `jalrx_800039f4` (VSA's `stepObs_jalr`), `ms_callHelperR`/`ms_callAbortR`.
- `CallArm.lean`: `CallNode` (+ `callNode_of_repr`), runs 1-2.
- `CallSeg.lean`: the prefix's two runs as Wp-generic segment lemmas with
  named end states (`callSegA`/`CallA`, `callSegB`/`CallB`), `CallAt.of_seg`,
  the too-many-arguments run.
- `CallPrefix.lean`: `callPrefixT` (total: callee, count test, E6's loop, to
  the kind dispatch `0x80003254`, `CallAt`).
- `CallPrefixP.lean`: `callPrefixP` (partial: Löb callee, E6's loop, the
  too-many-arguments abort).
- `CallErr.lean`: the call errors' messages (`FmtArgsOK`).
- `CallNative.lean`, `CallNativeOut.lean`: `callNativeOut`, the printing
  natives' tail for either WP and regime (`jalr` into `native_print`/
  `native_println`, the argument array carved as `valsAt`, the console through
  the world).
- Dev case `caseT_CallPrint` (`CallCaseDev.lean`, to become generated).

## Statement changes (INTERP_DESIGN.md §10 "STATEMENT CHANGES (E4)")
- `world` owns `Newlib.binImg` (the natives, `stringify`, `runtime_error`
  need it; no recursive spec carried it).
- `nativeAssertSpec`'s abort carries its reason `⌜¬ AssertOk vs⌝` (total mode
  refutes the abort branch with the derivation's premise); H2's four abort
  paths supply it.
- `gen_interp_steps.py` emits `interp_code_<pc>` for `jalr` sites too.

## Findings / open obligations (named premises)
- `DispSupply N` (`CallNative.lean`): printing a closure needs its display
  geometry (`dispRes`), which `storeRepr`'s `closOwn` does not carry (H2's
  finding). Supplier: a geometry field on `closOwn` from the `EX_FN` arm.
- Native stack room: `print`/`println` need `nativePrint(ln)Need + 1088` below
  the arm's entry `sp`; `evalNeed (.call …) d` gives it only when
  `d < maxCallDepth` (at the deepest level a call node leaves ≥ 2176 bytes,
  `nativePrintlnNeed = 4224`). The cases take it as a premise (`hroom`); same
  family as Q7.

## In flight
- Partial native cases, `assert` (T and P, incl. assert-fail), not-callable,
  the closure call (T and P, arity/depth/escape errors), the generator family.

## Holes
None added.
