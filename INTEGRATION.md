# Integration: lanes BG, H4, H2 (with G, H1), G, H1 into `iris-main`

Status: `lake build Vsa VsaIris VsaIris.Audit` is green. `python3 scripts/check_iris_holes.py` reports
`ok: 12 ledgered holes`. All 135 `#print axioms` in `VsaIris/Audit.lean` report a subset of
{propext, Classical.choice, Quot.sound}.

## What merged

| lane | head | merge on `iris-main` | conflicts |
|---|---|---|---|
| BG | `522c210` | fast-forward | none |
| H4 | `8097b72` | `fe634d8` | `LANE.md` (archived) |
| H2 (includes G and H1 up to `36fd75f`) | `569177c` | `01a08fd` | `Audit.lean` (union of imports and `#print axioms`), `HOLES.md` and `Specs.lean` (H4's `alloc` field and rows dropped because they are proved; H1's `reallocNull` and H2's `out` kept) |
| G | `b8da1f7` | already contained in H2 | none |
| H1 | `7ae8d34` | `21116ba` | `LANE.md` (archived) |

Lane reports are archived as `LANES-a0.md`, `LANES-bg.md`, `LANES-h4.md` (both H4 reports), `LANES-h2.md`,
`LANES-g.md` and `LANES-h1.md`.

## What was fixed

Each fix changes a proof to match a new interface. A premise was added only where the new interface
required it.

- **H4's page-aligned shape now carries `Starts H`.** `World.lean` supplies `Starts` for the boundary list
  with `starts_inuseBlocks` over the chunk walk (`d30f984`). H1's `heapRes_congr`, `pShape_congr` and
  `vsaRoomB_congr` now take `H.Perm H'` instead of membership equivalence, because membership alone cannot
  carry `Nodup` (`EnvDefineGrow.obRest_perm`).
- **`IrisHoles.alloc` is gone.** H1 no longer takes the `AH : AllocHoles` premise. `reallocRho_spec`,
  `wp_call_realloc`, `wp_call_reallocOpt`, `def_grow` and `envDefine_spec` now use `reallocChgRun_proved`
  and `allocSpecs` (`a713485`).
- **H4 found the realloc run false for wrapped sizes** (`c4fa5f5`). `reallocRho_spec` and `wp_call_realloc`
  therefore take `nNew < 2^64`. `wp_call_reallocOpt` already had `nNew < 2^32`.
- **`VsaIris.Sym.swp_alu` was defined twice** (H4 `AllocSltu`, G `SymObs`). H4's list form is now named
  `swp_aluRR`, and `SymObs.swp_alu` is a corollary of it.
- **Tactic interaction.** H4 added word-load forwarding (`ldv_lw_miss`) to the shared `sx_mem`. In G and H2
  interpreter runs, a word load off a pointer the context does not separate from the stack then fails its
  discharge at every step, which caused timeouts in `ProofStringify` and `EnvDefineSpans.def_pro`. The fixes:
  - `ix_mem` keeps G's doubleword-only forwarding (`ITac.lean`).
  - `def_pro` separates the frame facts before `sx_run` and forwards per goal.
  - No heartbeat limit was raised.
- **H1's exact frame invariant at the boundary** (`0160ac1`):
  - The global frame's arrays are the chunk payloads cut to `8 cap`/`24 cap` bytes (`trimArrays`). The
    boundary live list `Boot.H` is trimmed the same way (`BlockHeapAt.shrink`, `Starts.map`).
  - `FrameChunks` carries disjointness and `cap_canon`.
  - Block windows come from the walk (`Boot.win_of_mem`).
  - H2's `storeRepr_allocFrame` gets `storeInvariant_initSt`.

### Statement change (user decision, 2026-09-24)

Two facts H1's invariant needs at the global frame do not follow from `Loaded`, so they became boundary
fields:
- `BootFrameChunks.cap_canon : F.cap = 8`.
- `BootHeapFacts.shared_geom : SharedGeom shared stackSL`.

Both are proved at the control snapshot (`Control.bootFrameChunks`, `Control.sharedGeom`), so vacuity is
kept. The change is recorded in `VsaIris/INTERP_DESIGN.md` ("STATEMENT CHANGE (integration)").

## Hole ledger

Before (`hub/iris-main` at `399253a`): 10 holes.
After: 12 holes.

| hole | before | after | justification |
|---|---|---|---|
| `alloc.mallocChgRun` | open | removed | `mallocChgRun_proved` (`VsaIris/Vsa/MallocRunAll.lean`, H4 `adda462`) |
| `alloc.mallocLocalRun` | open | removed | `mallocLocalRun_proved` (same file, `adda462`) |
| `alloc.freeChgRun` | open | removed | `freeChgRun_proved` (`FreeRunAll.lean`, `5d2f541`) |
| `alloc.freeLocalRun` | open | removed | `freeLocalRun_proved` (`FreeRunAll.lean`, `5d2f541`) |
| `alloc.reallocChgRun` | open | removed | `reallocChgRun_proved` (`ReallocRunAll.lean`, `e1dd783`) |
| `alloc.reallocLocalRun` | open | removed | `reallocLocalRun_proved` (`ReallocRunAll.lean`, `e1dd783`) |
| `reallocNull.chgRun` | — | added | `IrisHoles.reallocNull : ReallocNullHoles` (H1 `4ef92cf`): `realloc(NULL, n)` for `env_define`'s first growth; H4's runs cover only the grow path of a live block |
| `reallocNull.localRun` | — | added | same field |
| `newlib.snprintf`, `.fprintf`, `.fwrite`, `.exitHandlers` | open | open | unchanged (H5, Q4) |
| `out.fputs`, `.fputc`, `.fwrite`, `.fprintf`, `.snprintfFn`, `.snprintfInt` | — | added | `IrisHoles.out : Newlib.OutHoles` (H2 `d8e5889`): newlib stdout calls and `snprintf("<fn %s>")`, scheduled with the newlib holes (Q4) |

All six removed runs and `allocSpecs` are in `VsaIris/Audit.lean` with the three standard axioms. Every
added hole is an `IrisHoles` field with a `HOLES.md` row.

## Open

- `reallocNull.*` is now inexpensive to discharge. `realloc_entry` (`ReallocRunAll.lean`) covers the first
  four instructions, and the `_malloc_r` run it tail-calls is proved. The remaining work is the step lemmas for the NULL branch
  (`0x80005290` `beqz a1`, `0x80005480`, `0x80005484` `j _malloc_r`) plus the join to `mallocChgRun_proved`.
- `scripts/check_discipline.py` (stage a4) already failed on `399253a`, all on Vsa-side legacy files.
  Integration adds no finding. `LayoutInstance.lean`'s ∃ count rose from 20 to 22 through BG's `boot`
  field.
