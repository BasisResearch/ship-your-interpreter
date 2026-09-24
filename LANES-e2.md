# Lane E2: the binary operators

Branch `lane-e2` (from `wave4-base`, `hub/iris-main` merged at its INTEGRATION), pushed to
`hub`. Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8 (family E2); statement changes in §10
"STATEMENT CHANGES (E2)". Rows: `scripts/iris_arms/arms.d/e2-binary.tsv`; families:
`scripts/iris_arms/families/e2_binary.py`; templates `scripts/iris_arms/templates/`. Every
case below is generated; `VsaIris/AuditE2.lean` prints their axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Done

Total cases (derivation-indexed, `evalSpecT_body`), one per row:

| operator | row | case | family |
|---|---|---|---|
| `+`, `-` | int/int | lane G's `caseT_BinaryAddInt`, `caseT_BinarySubInt` | `binInt` (G) |
| `+` | a string operand | `caseT_BinaryConcat` | `binConcat` |
| `*`, `/`, `%` | int/int (libgcc inline) | `caseT_Binary{Mul,Div,Mod}Int` | `binArith` |
| `<`, `<=`, `>`, `>=` | int/int | `caseT_Binary{Lt,Le,Gt,Ge}Int` | `binOne` |
| `<`, `<=`, `>`, `>=` | string/string | `caseT_Binary{Lt,Le,Gt,Ge}Str` | `binStr` |
| `==`, `!=` | any values | `caseT_Binary{Eq,Ne}` | `binEq` |

Partial cases (`evalSpecP_body`), ONE per operator, closed over every outcome of the
operands (no exported branch; family `binP`, and `binEq` for `==`/`!=`):
`caseP_BinaryAdd` (int row, the string row with `stringify`'s and `malloc`'s
out-of-memory aborts, both type errors), `caseP_BinarySub`, `caseP_BinaryMul`,
`caseP_BinaryDiv` and `caseP_BinaryMod` (with the zero divisor's `runtime_error`),
`caseP_Binary{Lt,Le,Gt,Ge}` (int, string and four type-error rows), `caseP_Binary{Eq,Ne}`.
Error rows end in `runtime_error` (`ms_rtErrEval`, H5's `rtErr_spec`) or the
out-of-memory block (`ms_evalOom`, `Oom.wp_oomBlock`).

Layer (hand, reusable by the other E lanes):

- **Error arms** (`SpecErr.lean`, `ErrArm.lean`): `errCtx inp`, `ErrEnv`, `CoreOK`,
  `coreOK_top`; `ms_rtErrEval`; `abortAt_of_evalCallee` (a callee's abort below an eval
  arm's `sp` is the arm's `abortAt Core s n`); `ms_callKindName` and `valueKindNameSpec`
  (`value_kind_name`, proved in `ProofValueKindName.lean`); message facts
  (`operand_fmt`, `plain_fmt`, `kindName_cstr`, `readable_rodata_fmt`).
- **Calls from a run**: `ms_callValueEqual` (`BinEq.lean`); `ms_callFree`/`freeRho_spec`
  (`CallFree.lean`, H4's `free` in either regime); `ms_callHelperA` (a helper that may
  abort), `ms_callMemcpyOwned`, `ms_callMallocN`/`ms_callFreeN` (register facts as a pure
  premise), `abortAt_of_stringify`, `ms_evalOom` (`ConcatCalls.lean`).
- **libgcc inline** (`ProofArith.lean`): `mul_iw`, `divdi3_iw`, `moddi3_iw` (continuation
  form over `IW`, by fuel induction); `__divdi3`/`__moddi3` clobber `ra`, so the arm follows
  them inside its own run (`iw_jal`).
- **Concatenation** (`ConcatArm.lean`): `concat_route`, `strOwn_cut`, `blockOwn_of_cut`,
  `ownImg_cat`/`cstrImg_cat`, `strAt_of_fresh`, `dispRes_of_valOf`, `CatSaved`, `catRest`,
  `world_of_catRest`, `binOpCost_concat`, `binOpSem_concat`, `addRows`.
- **Tactics** (`BinArm.lean`, `ITacTree.lean`): `ix_ro`, `ix_absurd` (`sx_side` rules),
  `e2_fwd` (cheap load forwarding over a run's memory), `#ix_tree` (a proof from a tree of
  pieces: the rows after one prefix).

Generator additions (additions only; G's arms regenerate identically, `--check` passes):

- `gen_interp_steps.py`: `value_kind_name`, libgcc `__muldi3`/`__divdi3`/`__moddi3`
  (+ `__hidden___udivdi3`, `__umoddi3`), the tables `CSWTCH.18`/`CSWTCH.25`, one lemma per
  loaded table word (`interpRO_acc{w}_{addr}`).
- `gen_iris_cases.py`: per-lane family modules `scripts/iris_arms/families/*.py`
  (`FAMILIES_EXT`, `FAMILIES_WHOLE_EXT`), so a lane never edits the shared file.
- E2's templates take optional context placeholders (`LHS`, `INTRO0`, `LHSX`, `INTROX`,
  `CTX*`): a family threads persistent resources (`binImg`, `textOwn allocText`) through the
  prefix's runs; empty for every arm that does not need them.

## In flight

Nothing. Next: dispatcher lemmas over all operators if package A wants them.

## Holes

None added. `python3 scripts/check_iris_holes.py`: `ok: 10 ledgered holes`. The cases take
callee specs as Lean hypotheses (other lanes prove them), recorded in
`experiments/smt/PROOF_CLOSURE_PLAN.md`:

- `strcmpOrdSpec` (H3): `strcmp`'s sign class; `strcmpSpecV` is too weak for `<`.
- `strlenHeapSpec`, `strcpyHeapSpec` (H3): on owned heap strings, `heapRes` lent for the
  word over-read.
- `stringifySpecT`, `stringifySpecP` (H2): `stringifySpec` in the counted regime without
  the abort branch, and with the slot returned on abort.
- `CatDispSupply` (E4's `DispSupply`), `memcpySpecOwned`, `valueStrSpec`,
  `valueIntSpec`, `valueBoolSpec`, `valueEqualSpec`, `valueKindNameSpec` (proved here).

## Findings (for the other E lanes)

- **An eval error arm needs `errCtx inp` and `ErrEnv`**, not in `evalPre` (binImg; the
  `jmp_buf`'s aligned `ra`). Q7 does not bite the binary arm: below its frame there are at
  least 2176 bytes (`evalNeed_binary_rtErr`).
- **A persistent resource does not survive `wp_swpF`** unless it is in the frame `F`:
  thread it through every run's frame (the `CTX*` placeholders).
- **`strlenPC` is a `def`**: pass `(entry := strlenPC)` to `ms_callHelper`, or `iframe`
  of the spec fails to unify.
- **`ihave H := spec $$ %args` on a `□ ∀ …` spec keeps an inner `□`**: state the callee
  spec per argument and quantify in the hypothesis (`⊢ ∀ q x, spec q x`).
- **Heartbeat hazards**: the `.rodata` membership `decide` (use `ix_ro`); `ix_fwd using`
  simps with every hypothesis (use `e2_fwd`); an `exact` inside an `sx_side` rule can
  succeed by error recovery; an address written as `(s + c).toNat` against a fact at
  `s.toNat - 1088 + k` reaches `maxRecDepth` in `exact` (keep one address form per fact,
  `CatSaved`).
- **Abort branches**: `ms_callHelperA` gives both continuations from one context (`∧`);
  `isplit; rotate_left` closes the abort first inside the same piece.

## Line counts (generated vs hand)

Generated (`python3 scripts/gen_iris_cases.py`; never edited):

| case file | lines |
|---|---|
| `Binary{Lt,Le,Gt,Ge}IntT` | 4 × 281 |
| `Binary{Lt,Le,Gt,Ge}StrT` | 4 × 340 |
| `Binary{Mul,Div,Mod}IntT` | 317, 320, 320 |
| `BinaryConcatT` | 893 |
| `Binary{Eq,Ne}T`, `Binary{Eq,Ne}P` | 2 × 370, 2 × 366 |
| `BinarySubP`, `BinaryMulP`, `BinaryDivP`, `BinaryModP` | 526, 549, 623, 623 |
| `Binary{Lt,Le,Gt,Ge}P` | 4 × 924 |
| `BinaryAddP` | 1229 |
| total | 13052 |

Hand: templates 3028 lines (`binConcat_T` 555, `binP_concat` 598, the rest 51–301 each),
family module 746, Lean layer 2358 (`ProofArith` 581, `BinArm` 314, `ErrArm` 268,
`ConcatCalls` 259, `ConcatArm` 252, `CallFree` 141, `SpecErr` 128, `BinEq` 128,
`SpecConcat` 121, `ITacTree` 102, `ProofValueKindName` 64).
