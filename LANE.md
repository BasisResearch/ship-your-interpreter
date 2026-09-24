# Lane E4: the call family (closure call, natives, call errors)

Branch `lane-e4` (from `wave4-base`). Merged: `hub/iris-main` (with
`INTEGRATION.md`), `hub/lane-e6` (argument loop), `hub/lane-e2` (eval error
arms), and `hub/lane-e5` (`ExecEnv`, `ExecBlock`; it carries E1). Design:
`VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row "call"), §10 "STATEMENT CHANGES
(E4)". Rows: `scripts/iris_arms/arms.d/e4-call.tsv`.

## Integration conflict: `errCtx` (E1 vs E2)
E1's `LeafErr.lean` and E2's `SpecErr.lean` both define
`VsaIris.Interp.errCtx`, with different jmp_buf side conditions (`ErrCtxOK`
vs `(jbWord inp jb 0).toNat % 4 = 0`). The two cannot be imported together.
This branch builds with E2's version, because the call errors go through
`ErrEnv`/`ms_rtErrEval`. It therefore leaves out of `VsaIris.lean` and
`Audit.lean` (commented, with the reason) E1's `LeafErr` and the
`Case.{Var,Assign}{T,P}` built on it. Integrator: pick one definition and
rename or merge the other.

## Dependencies (used as is)
- E6: `evalArgsT_body`/`evalArgsP_body` (`SpecLoop.lean`), hypotheses of the
  prefix.
- E2: `errCtx`, `ErrEnv`, `ms_rtErrEval`, `valueKindNameSpec`.
- H2: the natives' specs, `ms_callRegs`. H5: `rtErr_spec`, `abortRes`.
- E5: `ms_callEnvNewW`, `blockNode_of` (for the closure body).

## Done (axioms ⊆ {propext, Classical.choice, Quot.sound})

| Arm / layer | Generated (Case/) | Hand (lemmas) |
|---|---|---|
| layer: `jalr` call (`CallJalr`) | – | 358 |
| layer: call node, prefix runs (`CallArm`, `CallSeg`, `CallPrefix`, `CallPrefixP`) | – | 128 + 221 + 371 + 288 |
| error messages (`CallErr`) | – | 75 |
| print (T) | 72 (`CallPrintT`) | shared: `CallNative` 289, `CallNativeOut` 288 |
| println (T) | 72 (`CallPrintlnT`) | shared (as above) |
| assert-ok (T) | 66 (`CallAssertT`) | `CallNativeSeg` 369 |
| partial arm (P): natives, assert-fail, too-many, not-callable; closure is the named `CallCloP` | 160 (`CallArmP`) | `CallNotCallable` 165 |
| closure head (arity test, depth bump/test, `cl->env`; exits OK/arity/depth) | – | `CallClosure` 449, `CallCloHead` 406 |

Template lines (hand, but table-level): `callOut_T` 71, `callAssert_T` 65,
`callArm_P` 159, family `e4_call.py` 51. Generator additions (listed in
`gen_iris_cases.py`): step kinds `helperR` (indirect `jalr` helper) and
`loop` (a lemma hypothesis). `gen_interp_steps.py` also emits
`interp_code_<pc>` for `jalr` sites.

## Statement changes (INTERP_DESIGN.md §10)
- `worldE` owns `Newlib.binImg` (needed by the natives, `stringify`, and
  `runtime_error`). `binImg` moved to `Repr.lean`; the domains are in
  `Vsa/BinDom.lean`. E1's var/assign templates destructure it.
- `interpCtxE`: the jmp_buf target word is 4-aligned (needed by `longjmp`).
- `interpCoreE`: `d ≤ maxCallDepth` (the depth test's `sw`/overflow arm needs
  it).
- `nativeAssertSpec`'s abort carries `⌜¬ AssertOk vs⌝`. H2's four abort paths
  supply it.

## Named premises (findings, in PROOF_CLOSURE_PLAN.md)
- `DispSupply`/`CloSupply`: printing a closure needs display geometry that
  `closOwn` does not carry (H2's finding).
- Native stack room `hroom`: at `d = maxCallDepth`, a call node leaves
  ≥ 2176 bytes, but `nativePrintlnNeed = 4224` (Q7 family).
- `inp % 8 = 0` (interpreter struct alignment for the depth word).

## In flight
- Closure call after the head: env_new (counted; partial OOM via
  `wp_oomBlock`), the param `env_define` loop, `value_null(sp+144)`, the body
  (G's `closureSeq{T,P}_body`), and the exits (depth restore, return copy,
  escape error, arity `snprintf` error, depth error). Targets:
  `caseT_CallClosure` and a proof of `CallCloP`. Then the closure rows.

## Holes
None added.
