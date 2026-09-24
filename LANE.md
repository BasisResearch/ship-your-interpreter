# Lane H1: `env_*` helpers over `storeRepr`

Branch `lane-h1` (from `hub/iris-main`, merged `hub/lane-h4`). Design:
`VsaIris/INTERP_DESIGN.md` §9 H1. Status: **all four helpers proved**, `lake build Vsa
VsaIris` green, every H1 theorem's axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Done
- **Statements**: `VsaIris/Interp/SpecEnv.lean` — `envNewSpec`, `envDefineSpec`
  (`fnSpecAbort`, both regimes, the cost model's charges `envBytes`/`defineCost`,
  abort = `oomAt` parked before the OOM `fwrite`), `envGetSpec`, `envSetSpec`
  (`fnSpecW`); `heapStore` (= the heap/store part of `world`, `world_heapStore`);
  callee specs `strcmpSpec`/`strlenSpec`/`memcpySpec` as hypotheses.
- **`env_get`, `env_set`**: `envGet_spec`/`envSet_spec : textOwn envText ∗ gp ↦ᵣ□ gpV ∗
  strcmpSpec Wp ⊢ env{Get,Set}Spec Wp N`, every `MachWP` (`ProofEnvGet.lean`,
  `ProofEnvSet.lean`). The chain scan is proved once over a `ScanSite` (`EnvScan.lean`).
- **`env_new`**: `envNew_spec` over `heapStore`, both regimes (`ProofEnvNew.lean`),
  generalising the pilot; `mallocRho_spec` (`HeapCall.lean`), `wp_call_malloc`.
- **`env_define`**: `envDefine_spec : textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗
  strcmpSpec Wp ∗ strlenSpec Wp ∗ memcpySpec Wp ⊢ envDefineSpec Wp N`, every `MachWP`,
  both regimes, from `AllocHoles` and `ReallocNullHoles` (`ProofEnvDefine.lean`). Arms:
  `def_hit` (replace), `def_append` (strlen/malloc/memcpy, the name frozen persistent),
  `def_grow` (both arrays `realloc`ed from NULL or the live blocks), `def_ret`/`def_oom`
  (`EnvDefineArms.lean`, `EnvDefineGrow.lean`). The counted charge splits exactly:
  `defineCost = nameCopyCost + growthCost`, `growthCost = arrayReallocCost (nextCap n)`
  at a full frame, else 0 (`DefineCost.lean`: `capFor_succ`, `growthCost_eq`).
- **Reusable layer** (factored when the second/third use appeared):
  - `ScanLoop`/`ScanInv`: one frame's name loop, generic in the name/count registers
    and the invariant — `env_get`, `env_set` and `env_define` instantiate it
    (`scan_frame`; `defLoop`/`DefFrame`).
  - `frame_write_close`: `vals[j] := *v` then close the frame — `env_set` and
    `env_define`'s hit.
  - `wp_call_ks`: any `jal` from a span's register file (`CallKs.lean`); instances
    `wp_call_strlen`, `wp_call_memcpy`, `wp_call_allocKs` → `wp_call_realloc`,
    `wp_call_reallocNull`, `wp_call_reallocOpt` (`EnvDefineCalls.lean`).
  - `reallocRho_spec`/`reallocNullRho_spec` (one spec per regime pair),
    `heapRes_congr` (the heap depends on its live list only by membership)
    (`HeapRealloc.lean`).
  - env.c's step table from H4's generator (`gen_alloc_steps.py --target env`);
    `env_set`'s spans generated from `env_get`'s (`gen_env_set_spans.py`).
- **STATEMENT CHANGES** to R's predicates (INTERP_DESIGN.md "STATEMENT CHANGES (H1)"):
  `storeRepr` carries `StoreInvariant`; `strAt` carries `StrWin`; `FrameLayout` gains
  `win`/`e_align`/`cap_canon`; `FrameLayout.arrays` states the arrays' exact extents.

## In flight
- Nothing.

## Holes
- `reallocNull.chgRun`, `reallocNull.localRun` (`IrisHoles.reallocNull`,
  `SpecEnv.lean`): `realloc(NULL, n)`, used by `env_define`'s first growth. Owner H4.

## Interface requests to other lanes
- H3: `strcmpSpec`/`strlenSpec`/`memcpySpec` in `SpecEnv.lean` are the shapes H1
  consumes (strings persistent via `strAt`, whose `StrWin` covers the word
  over-read; no slack ownership).
- H4: `ReallocNullChgRun`/`ReallocNullLocalRun` (the `_malloc_r` path of `_realloc_r`);
  `envDefine_spec` takes `AllocHoles` (for the counted `reallocChgRun`, which
  `AllocSpecs` does not carry). `gen_alloc_steps.py` gained `--target` (default unchanged).
- E-lanes: `envGetSpec`'s `getSaved` includes `s6`; `FrameBridge.arrays` is now the
  exact extents (the ledger's entries are the exact requests).

## Line counts (hand lines vs VSA's cones)
- `env_define`: 3,375 (`EnvDefineSpans` 672, `EnvDefineArms` 794, `EnvDefineGrow` 685,
  `EnvDefineCalls` 445, `HeapRealloc` 287, `ProofEnvDefine` 271, `DefineCost` 149,
  `CallKs` 72) plus the shared scan/span layer, against VSA's `env_define` cone: 29,003.
- `env_get` + `env_set`: 2,580 (`EnvSpan` 329, `EnvScanCore` 178, `EnvScan` 1,027,
  `EnvGetSpans` 186, `EnvGetHit` 75, `ProofEnvGet` 165, `EnvSetHit` 74, `ProofEnvSet` 465;
  `EnvSetSpans` 186 generated) against 20,565.
- `env_new`: 653 (`EnvNewSpans` 91, `HeapCall` 89, `EnvCalls` 141, `ProofEnvNew` 332)
  against 3,235.
- Whole lane: 6,783 lines (incl. 186 generated) against 52,803 across the three cones.
