# Lane H1: `env_*` helpers over `storeRepr`

Branch `lane-h1` (from `hub/iris-main`, merged `hub/lane-h4`). Design:
`VsaIris/INTERP_DESIGN.md` §9 H1.

## Done
- **Statements**: `VsaIris/Interp/SpecEnv.lean` — `envNewSpec`, `envDefineSpec`
  (`fnSpecAbort`, both regimes, the cost model's charges `envBytes`/`defineCost`,
  abort = `oomAt` parked before the OOM `fwrite`), `envGetSpec`, `envSetSpec`
  (`fnSpecW`); `heapStore` (= the heap/store part of `world`, `world_heapStore`);
  callee specs `strcmpSpec`/`strlenSpec`/`memcpySpec` as hypotheses.
- **`env_get` and `env_set` proved**: `envGet_spec`/`envSet_spec : textOwn envText ∗
  gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ env{Get,Set}Spec Wp N` for every `MachWP`
  (`ProofEnvGet.lean`, `ProofEnvSet.lean`). Axioms: propext, Classical.choice, Quot.sound.
  The scan and parent chain are proved ONCE over a `ScanSite` (`EnvScan.lean`); each function
  is an instance plus its hit arm. `env_set`'s spans are generated from `env_get`'s
  (`scripts/gen_env_set_spans.py`, the same code 0xcc bytes later).
- **The exponentiating layer for env.c**: `scripts/gen_alloc_steps.py --target env`
  (H4's generator, now parameterized; default output byte-identical) emits
  `EnvCode.lean` (`envText`) and `EnvSteps/*` (235 `st_<pc>` lemmas over
  `EW = SWP envText eRegs`), so H4's `sx_run` drives env.c. Call-free spans are
  first-order lemmas (`EnvGetSpans.lean`: seven spans, mostly one `sx_run` each);
  `EnvSpan.lean` enters them at the Iris level (`wp_span`), splits the register file
  around calls (`regsOf_extract`), and assembles/disassembles ABI register files
  (`regsOf_entry`/`regsOf_exit`).
- STATEMENT CHANGES to R's predicates (INTERP_DESIGN.md "STATEMENT CHANGES (H1)"):
  `storeRepr` carries `StoreInvariant` (named pure part `StorePure`); `strAt` carries
  `StrWin` (bridges take `SharedWin P`); `FrameLayout` gains `win`/`e_align`/`cap_canon`.

## In flight
- `env_new` over `heapStore` (generalise the pilot, both regimes), then `env_define`.

## Holes
- `reallocNull.chgRun`, `reallocNull.localRun` (`IrisHoles.reallocNull`,
  `SpecEnv.lean`): `realloc(NULL, n)`, used by `env_define`'s first growth. Owner H4.

## Interface requests to other lanes
- H3: `strcmpSpec`/`strlenSpec`/`memcpySpec` in `SpecEnv.lean` are the shapes H1
  consumes (strings persistent via `strAt`, whose `StrWin` covers the word
  over-read; no slack ownership).
- H4: `ReallocNullChgRun`/`ReallocNullLocalRun` (7 step lemmas + your `_malloc_r`
  entry lemma). Also: `gen_alloc_steps.py` gained `--target` (default unchanged).
- E-lanes: `envGetSpec`'s `getSaved` includes `s6` (a span owns the whole file).

## Line counts (vs VSA's cones)
- env_get + env_set: 2,580 hand lines (`EnvSpan` 329, `EnvScanCore` 177, `EnvScan` ~990,
  `EnvGetSpans` 183, `EnvGetHit` 75, `ProofEnvGet` 160, `EnvSetHit` 74, `ProofEnvSet` 415;
  `EnvSetSpans` 186 generated) against VSA's `EnvGet*`+`EnvGetReflected/*`+`EnvSet*` cone:
  20,565 lines.
