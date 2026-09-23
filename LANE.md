# Lane H1: `env_*` helpers over `storeRepr`

Branch `lane-h1` (from `hub/iris-main`, merged `hub/lane-h4`). Design:
`VsaIris/INTERP_DESIGN.md` §9 H1.

## Done
- **Statements**: `VsaIris/Interp/SpecEnv.lean` — `envNewSpec`, `envDefineSpec`
  (`fnSpecAbort`, both regimes, the cost model's charges `envBytes`/`defineCost`,
  abort = `oomAt` parked before the OOM `fwrite`), `envGetSpec`, `envSetSpec`
  (`fnSpecW`); `heapStore` (= the heap/store part of `world`, `world_heapStore`);
  callee specs `strcmpSpec`/`strlenSpec`/`memcpySpec` as hypotheses.
- **`env_get` proved**: `envGet_spec : textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢
  envGetSpec Wp N` for every `MachWP` (`VsaIris/Interp/ProofEnvGet.lean`).
  Axioms: propext, Classical.choice, Quot.sound.
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
- `env_set`: factor the scan / parent-chain Iris lemmas over a site record
  (`env_get` and `env_set` are the same code 0xcc apart, differing in the hit arm),
  generate `env_set`'s spans from `env_get`'s.
- Then `env_new` over `heapStore` (generalise the pilot, both regimes), `env_define`.

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
- env_get: 1586 lines (`EnvSpan` 329 shared + `EnvGetSpans` 401 + `ProofEnvGet` 856)
  against VSA's `EnvGet*` cone (see final report).
