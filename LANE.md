# Lane E4: the call family (closure call, natives, call errors)

Branch `lane-e4` (from `wave4-base`). It is merged with `hub/iris-main`
(integration wave 4, with `INTEGRATION.md`) and with lanes E2, E5 and E6.
Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row "call") and §10 "STATEMENT
CHANGES (E4)". Rows: `scripts/iris_arms/arms.d/e4-call.tsv`. Audit:
`VsaIris/Interp/E4Audit.lean`, imported by `VsaIris/Audit.lean`. Every
theorem's axioms are ⊆ {propext, Classical.choice, Quot.sound}.

## Status: every arm in both modes; one named obligation

| arm / outcome | total | partial |
|---|---|---|
| `print`, `println` | `caseT_CallPrint`, `caseT_CallPrintln` | `caseP_CallArm` |
| `assert` returning | `caseT_CallAssert` | `caseP_CallArm` |
| closure call returning (normal end, `return`) | `caseT_CallClosure` | `caseP_CallArm` via `CallCloP` (`callCloP_of`) |
| too many arguments, not callable, assert failure | – (no derivation) | `caseP_CallArm` |
| call depth, `break`/`continue` escaping a body | – | `callCloP_of` (`cloErrDepth`, `cloExitEsc`) |
| out of memory (`env_new`, `env_define`) | – | `callCloP_of` (E5's `ms_callEnvNewP`/`ms_callEnvDefineP`, `wp_oomBlock`) |
| arity mismatch | – | the named obligation `CloArityP` (below) |

The recursor applies `caseP_CallArm` with `hclo := callCloP_of …`.

## Interface for A

- Total closure case: `caseT_CallClosure` takes the derivation's pieces
  (`CallCost.closure`), the children's motives (`evalSpecT_body`,
  `evalArgsT_body`), G's `closureSeqT_body` for the body, and the helper
  specs `valueNullSpec`, `envNewSpec`, `envDefineSpec`. It is stated at
  `vsaLayoutP`/`vsaRoomB`.
- Partial: `caseP_CallArm` needs `evalSpecsP ∗ errCtx ∗ execDispsP`
  (STATEMENT CHANGE, §10). Its closure branch is
  `callCloP_of hlive hE hvn hen hed hsup harity hinpA`.
- Named premises (all in `PROOF_CLOSURE_PLAN.md`, lane E4 entries):
  - `CloSupply N`: a closure's object, its `EX_FN` view and its environment
    binding, from the store. It subsumes `DispSupply`.
  - The native stack room `hroom` (Q7 family).
  - The interpreter struct's placement (`InpGeom`, `inp < 2^64`,
    `inp % 8 = 0`).
  - **`CloArityP`**: the arity error. Its obstruction is that `rtErr_spec`
    (H5) does not return the owned readable bytes (the message buffer in
    `eval_expr`'s frame). With them returned, the proof is a composition of
    existing runs (`CloE_runA`, `CloE_runA2`).

## Statement changes (INTERP_DESIGN.md §10 "STATEMENT CHANGES (E4)")

- `worldE` owns `Newlib.binImg`. Consumers were adjusted, including E1's
  `var`/`assign`/`fnLit` templates and E2's `catRest`.
- `interpCtxE`: the `jmp_buf`'s `ra` word is aligned.
- `interpCoreE`: `d ≤ maxCallDepth`.
- `nativeAssertSpec`'s abort carries `⌜¬ AssertOk vs⌝`.
- `caseP_CallArm` takes `execDispsP`, and `CallCloP` takes `execSpecsP`.

## Layers (hand; Wp-generic unless noted)

- Call arm: `CallJalr` (the native `jalr`), `CallArm`, `CallSeg`,
  `CallPrefix` (T) and `CallPrefixP` (P), `CallErr` (messages).
- Natives: `CallNative`, `CallNativeOut`, `CallNativeSeg`,
  `CallNotCallable`.
- Closure head: `CallClosure` (resources, `CloSupply`, the node, the
  depth word) and `CallCloHead`.
- After the head: `CallCloRuns` (12 runs), `CallCloBind` (the parameter
  loop, `env_define` abstract as `CloDefineStep`), `CallCloBody` (body
  entry), `CallCloExit` (normal and `return` exits).
- Mode-specific: `CallCloT` (`cloDefineStepT`, `cloCallT`, `callClosureT`)
  and `CallCloP` (`cloDefineStepP`, errors, `cloCallP`, `callClosureP`,
  `callCloP_of`).

## Line counts (generated vs hand)

| arm | generated | hand (templates) | hand (layers) |
|---|---|---|---|
| print / println (T) | 72 / 72 | `callOut_T` 71 | `CallNative` 289, `CallNativeOut` 288 |
| assert (T) | 66 | `callAssert_T` 65 | `CallNativeSeg` 369 |
| closure (T) | 75 | `callClo_T` 74 | `CallClosure` 431, `CallCloHead` 406, `CallCloRuns` 199, `CallCloBind` 602, `CallCloBody` 201, `CallCloExit` 360, `CallCloT` 388 |
| every outcome (P) | 163 | `callArm_P` 162 | `CallCloP` 673, `CallNotCallable` 165 |
| shared prefix | – | – | `CallJalr` 358, `CallArm` 124, `CallSeg` 221, `CallPrefix` 371, `CallPrefixP` 289, `CallErr` 75 |

Generated: 448 lines (5 files). Templates: 372 lines; family
`e4_call.py`: 60 lines. Layers: 5,235 lines.

Generator additions (additions only): step kinds `helperR` (an indirect
`jalr` helper) and `loop` (a loop lemma taken as a hypothesis). Families:
`callOut`, `callAssert`, `callClo`, `callArm`. `gen_interp_steps.py` also emits
`interp_code_<pc>` for `jalr` sites.

## Findings

- Keep `#ix_seg` runs free of arithmetic such as `24 * j` and of
  symbolic-length data views. `CloB_runL` took over 50 minutes (a kernel deep
  recursion) until each computed address was named as a `Nat` with bounds
  (E6's idiom).
- Two lanes' copies were deduplicated: `world_store` now lives once in
  `SpecEnv` (it was in E2's `BinEq` and in E4), and E6's `exprArray_length`
  is reused.

## Holes

None added (`check_iris_holes.py`: 10 ledgered).
