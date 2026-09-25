# Integration: lanes BG, H4, H2 (with G, H1), G, H1 into `iris-main`

Status: `lake build Vsa VsaIris VsaIris.Audit` is green. `python3 scripts/check_iris_holes.py` reports
`ok: 10 ledgered holes` (12 at the integration push, then `reallocNull.*` was discharged; see Follow-ups). All `#print axioms` in `VsaIris/Audit.lean` report a subset of
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

- `scripts/check_discipline.py` (stage a4) already failed on `399253a`, all on Vsa-side legacy files.
  Integration adds no finding. `LayoutInstance.lean`'s ∃ count rose from 20 to 22 through BG's `boot`
  field.

## Follow-ups (after the integration push)

- **Q8 (user decision): the semantics cuts a named closure's rendering** (`d0d2609`).
  `Value.catDisplay` renders `.closure` with a name as `fnCatRender n` (`"<fn " ++ n ++ ">"`, first 63
  characters), the same as `Newlib.fnRender` (`fnRender_eq`, `rfl`). `strRender_eq : strRender st v =
  v.catDisplay st`, so `stringify` renders exactly the concatenation form. `Validation.lean` and `c/tests`
  needed no change. Recorded under Decisions in `INTERP_DESIGN.md` and in `PROOF_CLOSURE_PLAN.md`.
- **`reallocNull.chgRun` and `reallocNull.localRun` are discharged** (`VsaIris/Interp/ReallocNullRun.lean`).
  `reallocNull_entry` runs `realloc`'s five entry steps, the taken `beqz a1` (the pointer is NULL),
  `mv a1, a2` and `j _malloc_r`, then H4's `malloc_all`. `reallocNullChgRun_proved` and
  `reallocNullLocalRun_proved` reuse the malloc contexts (`mChgCtx`/`mLocCtx`). H4's `mOK_chg`/`mOK_loc`
  now accept entry registers at any entry PC and `a0`, because they only use the saved registers. The
  `IrisHoles.reallocNull` field and its two `HOLES.md` rows are deleted, and the `NH` premise is gone from
  `reallocNullRho_spec`, `wp_call_reallocNull`, `wp_call_reallocOpt`, `def_grow` and `envDefine_spec`.
  Ledger: 12 → 10 (`newlib.*` 4, `out.*` 6).

## Wave 4: the case families E6, E1, E2, E3, E5

Status: `lake build Vsa VsaIris VsaIris.Audit` is green. `check_iris_holes.py` reports
`ok: 10 ledgered holes`. The drift gate `python3 -B scripts/gen_iris_cases.py --check` is clean. All 240
`#print axioms` in `VsaIris/Audit.lean` report a subset of {propext, Classical.choice, Quot.sound}; this now
includes every `caseT_*`/`caseP_*`. E4 (call) is not merged.

### What merged

| lane | head | merge | conflicts |
|---|---|---|---|
| E6 (loops) | `e59de33` | `896a273` | none |
| E1 (leaves, var, assign, fn) | `8a2dc86` | `1e82e6a` | `Audit.lean` (union) |
| E2 (binary) | `eb166ca` | `3f59374` | `VsaIris.lean`, `Audit.lean`, plan (union) |
| E3 (unary, logical) | `fd37b10` | `a1bb3ec` | `Audit.lean` (union) |
| E5 (exec) | `3fa5911` | `493e6ec` | root/`Audit` (union); plan and design (union of separate sections); `gen_iris_cases.py` (by hand, below); `LANE.md` |

The lanes started from `hub/wave4-base`, which adds the per-family `scripts/iris_arms/arms.d/` tables.
Reports are archived as `LANES-e1.md`, `LANES-e2.md`, `LANES-e3.md`, `LANES-e5.md` and `LANES-e6.md`.
Git's rename detection had put an older E5 report onto `LANES-h2.md`; `LANES-h2.md` keeps H2's report.

### What was fixed

- **E1 and E2 both defined `VsaIris.Interp.errCtx`.** E1's version carries `ErrCtxOK` (the `jmp_buf` `ra`
  alignment, `InpGeom`, `inp < 2^64`); E2's carries only the alignment and keeps the rest in `ErrEnv`.
  E4 and E5 had worked around the clash by commenting E1's var/assign cases out of the root and the audit.
  Now E1's definition is `leafErrCtx` (in `LeafErr.lean` and the templates `var_P`, `assign_T`,
  `assign_P`, `fnLit_P`, regenerated), and `leafErrCtx_of_errCtx` derives it from E2's `errCtx` plus
  `ErrEnv`'s two fields. Var and Assign are back in the build and the audit.
- **`gen_iris_cases.py` merged by hand:** E5's exec start points (`STARTS`) and exec families, E3's
  `abort`-terminated rows, and E1's `fnLit` family.
- **E3's `unNegType_P` template:** E2 later added a memory-agreement premise to `ms_callKindName`'s
  continuation, so the template now introduces it (`%_hagK`).
- **`Audit.lean`** now also prints the cases that were only printed in lane audits (`AuditE2.lean`,
  `LoopAudit.lean`) or not at all (G's binInt rows, E3's logical rows, E5's exec arms).

### Arms proved

Total cases (T) are derivation-indexed, one per outcome. Partial cases (P) are per operator and cover the
error rows. A constructor marked P covers the operator's error and type-error rows.

| `eval_expr` arm | T | P |
|---|---|---|
| null / int / str / bool | `caseT_Leaf{Null,Int,Str,Bool}` | `caseP_Leaf{Null,Int,Str,Bool}` |
| var (hit; miss → error) | `caseT_Var` | `caseP_Var` |
| assign (ok; unbound → error) | `caseT_Assign` | `caseP_Assign` |
| fn literal | `caseT_FnLit` | `caseP_FnLit` |
| `+` | `caseT_BinaryAddInt`, `caseT_BinaryConcat` | `caseP_BinaryAdd` (and `caseP_BinaryAddInt`) |
| `-` `*` `/` `%` | `caseT_Binary{SubInt,MulInt,DivInt,ModInt}` | `caseP_Binary{Sub,Mul,Div,Mod}` (and `caseP_BinarySubInt`) |
| `==` `!=` | `caseT_Binary{Eq,Ne}` | `caseP_Binary{Eq,Ne}` |
| `<` `<=` `>` `>=` | `caseT_Binary{Lt,Le,Gt,Ge}{Int,Str}` | `caseP_Binary{Lt,Le,Gt,Ge}` |
| unary `-` | `caseT_UnaryNeg` | `caseP_UnaryNeg` (rows `caseP_UnaryNegInt`, `caseP_UnaryNegType`) |
| unary `!` | `caseT_UnaryNot` | `caseP_UnaryNot` |
| `&&` | `caseT_LogicalAnd{True,False}` | `caseP_LogicalAnd` (rows `…True`/`…False`) |
| `\|\|` | `caseT_LogicalOr{True,False}` | `caseP_LogicalOr` (rows `…True`/`…False`) |

| `exec_stmt` arm | T | P |
|---|---|---|
| expression | `caseT_ExecExpr` | `caseP_ExecExpr` |
| `var x = e` / `var x` | `caseT_ExecVarInit` / `caseT_ExecVarNull` | `caseP_ExecVarInit` / `caseP_ExecVarNull` |
| block | `caseT_ExecBlock` | `caseP_ExecBlock` |
| if (true / false / no else) | `caseT_ExecIf{True,False,None}` | `caseP_ExecIf` |
| while | `caseT_ExecWhile` (E6's `whileT_*`) | `caseP_ExecWhile` (`whileP_all`) |
| for | `caseT_ExecFor` (E6's `forLoopT_*`) | `caseP_ExecFor` (`forLoopP_all`) |
| `return e` / `return` | `caseT_ExecRet` / `caseT_ExecRetNull` | `caseP_ExecRet` / `caseP_ExecRetNull` |
| break / continue | `caseT_ExecBrk` / `caseT_ExecCont` | `caseP_ExecBrk` / `caseP_ExecCont` |

E6's shared loop lemmas (`whileT_*`, `whileP_all`, `forLoopT_*`, `forLoopP_all`, `execInit*`,
`evalArgsT_*`, `evalArgsP_all`) are proved in both modes.

### Arms still missing

Only the call family (E4: closure call, the natives print/println/assert, and the call errors). Against
the §8 inventory, no other arm is missing.

### Open named premises (hypotheses of the cases, not `IrisHoles`)

- `ErrRoom e d` (Q7) on `caseP_Var`/`caseP_Assign`. It holds for `d < maxCallDepth` (`errRoom_of_lt`).
- E2's callee specs:
  - `strcmpOrdSpec` and `strlenHeapSpec`/`strcpyHeapSpec` (H3);
  - `stringifySpecT`/`stringifySpecP` (H2's `stringify_spec` in the shapes the concat arm needs);
  - `CatDispSupply` (the same statement as E4's `DispSupply`).
- The error arms' `errCtx`/`ErrEnv` and E6's `valueTruthySpec` premise (H2's `valueTruthy_spec` supplies
  it) are supplied at the top (A).
- Duplicates E5 lists to fold later: `execSP_off`/`execSP_offF`, `ms_callEvalPx`/`ms_callEvalPF`, and
  `ms_truthyCall` (roughly `ms_callHelperVal` with `valueTruthySpec`).

## Lane INT2: the newlib lanes

### N1 + N4 (2026-09-25)

| lane | head | merge on `iris-main` | conflicts |
|---|---|---|---|
| N1 | `cf3c915` | fast-forward | none |
| N4 (contains N3 at `02baa6d`: `newlib.fwrite` proved) | `52b1e9d` | `b05d880` | `VsaIris.lean` (import union; N1 renamed `Stdout.FwriteOut` to `Stdout.StrOut`), `HOLES.md` (proved rows dropped, N3's narrowed `newlib.fprintf` row kept), `LANE.md` (archived as `LANES-n1.md`, `LANES-n4.md`) |

Hole ledger: before 10 (`newlib.{snprintf,fprintf,fwrite,exitHandlers}`, `out.{fputs,fputc,fwrite,fprintf,snprintfFn,snprintfInt}`);
after 5 (`newlib.snprintf`, `newlib.fprintf`, `out.fprintf`, `out.snprintfFn`, `out.snprintfInt`).
Checks: `lake build Vsa VsaIris VsaIris.Audit` green (2700 jobs), `check_iris_holes.py` ok (5),
`endToEnd_refinement` axioms `[propext, Classical.choice, Quot.sound]`.

### V (2026-09-25)

| lane | head | merge on `iris-main` | conflicts |
|---|---|---|---|
| V (REVIEW.md, P5 README, P6 dead-code removal: 88 modules) | `4b7604e` | `12e97be` | none (report archived as `LANES-v.md`) |

Hole ledger: before 5, after 5 (V proves no hole; its vacuity findings C1–C3/H1 go to B1–B3).
Checks: build green (2682 jobs), `check_iris_holes.py` ok (5), `check_final_axioms.sh` 10/10,
`endToEnd_refinement` axioms `[propext, Classical.choice, Quot.sound]`.

### N3 (2026-09-25)

| lane | head | merge on `iris-main` | conflicts |
|---|---|---|---|
| N3 (`newlib.fprintf` proved; contains N5 at `4423d4b`) | `ecc8d0a` | `761d764` | `HOLES.md` (both conflicting rows, `newlib.fprintf` and `out.fputs`, proved; dropped); report archived as `LANES-n3.md` |

Hole ledger: before 5, after 4 (`newlib.snprintf`, `out.fprintf`, `out.snprintfFn`, `out.snprintfInt`).
Phase 1 done: 6 of 10 holes proved. Checks: build green (2707 jobs), `check_iris_holes.py` ok (4),
`endToEnd_refinement` axioms `[propext, Classical.choice, Quot.sound]`.
