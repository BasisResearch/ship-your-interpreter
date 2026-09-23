# Lane H1: `env_*` helpers over `storeRepr`

Branch `lane-h1` (from `hub/iris-main`, merged `hub/lane-h4`). Design:
`VsaIris/INTERP_DESIGN.md` §9 H1.

## Done
- Merged `hub/lane-h4` (allocator specs over `MachWP`, counted regime, `AllocHoles`).
- STATEMENT CHANGES to R's predicates (recorded in INTERP_DESIGN.md "STATEMENT CHANGES (H1)"):
  - `storeRepr` carries `Vsa.Sim.StoreInvariant` (named pure part `StorePure`);
  - `strAt` carries `StrWin` (the `strlen`/`strcmp` word over-read window);
    bridges take `SharedWin P` once per view.

## In flight
- `VsaIris/Interp/SpecEnv.lean`: the statements (env_new / env_get / env_set / env_define,
  callee specs for `strcmp`/`strlen`/`memcpy` taken as hypotheses, MachCSL `Spec<F>` style).

## Holes
- none added yet.

## Interface requests to other lanes
- H3: `strcmp` spec shape — see `SpecEnv.lean` `strcmpSpec` (pre: two `strAt`, no slack ownership).
- H4: `realloc(NULL, n)` (the `beqz a1` tail-jump to `_malloc_r`, `0x80005480`) is used by
  `env_define`'s first growth; `AllocHoles` covers only the grow path of a live block.

## Next
1. Spec file; 2. env_new over `storeRepr` (generalise the pilot, both regimes);
3. env_get / env_set (one shared scan lemma); 4. env_define hit / append / grow.
