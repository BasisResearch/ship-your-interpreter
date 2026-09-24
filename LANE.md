# Lane E1: leaves, var, assign (eval_expr)

Branch `lane-e1` (from `wave4-base`). Design: `VsaIris/INTERP_DESIGN.md` §4,
§6, §8 (family "leaves" and "var/assign"), §9 E1; statement changes in §10
"STATEMENT CHANGES (E1)". Rows: `scripts/iris_arms/arms.d/e1-leaves.tsv`.

## Done
- **Family `leaf`** (`templates/leaf_{T,P}.lean`, `gen_iris_cases.py`
  `subst_leaf` + `LEAF_KINDS`): `int`, `str`, `bool`, `null`, both modes.
  Two `#ix_seg` runs (prologue + kind dispatch to the helper's `jal`; the
  shared epilogue `0x800033ec`) and the helper call (`ms_callHelper` against
  `valueIntSpec`/`valueStrSpec`/`valueBoolSpec`/`valueNullSpec`). The partial
  case has no error arm (returns with `EvalE.int`/…).
- **Hand layer** `VsaIris/Interp/LeafArm.lean`: `LeafNode` (the leaf analogue
  of G's `BinNode`), `leafNode_{null,int,bool,str,var,assign,fn}` from
  `ExprReprWithin`, `StrField`, `sharedWin_of_readOK`, `ldv_lw_zero_iff`.
- **Statement change**: `ReadOK.win` (INTERP_DESIGN.md §10 E1).

- **Family `var`** (`templates/var_{T,P}.lean`, `subst_call1`): row `Var`.
  Total: the lookup succeeds (`D`'s premise). Partial: after `env_get` the
  case splits on the lookup; found returns with `EvalE.var`, unbound runs to
  `runtime_error(in, line, "undefined variable '%s'", name, 0)` and aborts.
  One chain, no exported branches.
- **Hand layer** `LeafCalls.lean` (result slot in the run's owned bytes:
  `frS`, `ms_intro_sret`/`ms_exit_sret`; `env_get`'s out slot:
  `ms_carveSlot`/`ms_joinSlot`/`ms_unslot`; `ms_callEnv3`, the `env_get`/
  `env_set` register-form call from a run) and `LeafErr.lean` (`ev_rtErr`:
  `runtime_error` from an eval frame; `errCtx`, `ErrRoom`, `evalCore`; the
  two messages' formats).

## Interface for A (and the other E lanes)
- **Partial cases with error arms are stated at `Core := evalCore N L Room inp`**
  (the landing core over the whole stack segment; every site's
  `abortCore s n` widens to it, `evalCore_of`). Lane G's generic-`Core`
  cases instantiate at it.
- **`errCtx inp`** (persistent, `LeafErr.lean`): `binImg` and the `jmp_buf`
  read-only at an image with an aligned `ra` word, plus `in`'s placement
  (`ErrCtxOK`). The P cases with error arms take it beside the Löb
  hypothesis (`errCtx inp ∗ evalSpecsP … ⊢ …`). A supplies it once at
  `interp_run`'s `jal exec_stmt` (`TopLanding`).
- **`ErrRoom e d`**: `runtime_error`'s stack below the arm's frame; true for
  `d < maxCallDepth` (`errRoom_of_lt`). At `d = maxCallDepth` it is
  INTERP_DESIGN.md Q7 (open, needs the user).

## In flight
- `assign` (ok; partial: unbound → `runtime_error`, child abort), `fn`
  (partial: OOM → `oom80003e28`).

## Line counts (generated vs hand)
| arm | T generated | P generated | hand |
|---|---|---|---|
| leaf family (4 arms) | 4 × ~150 | 4 × ~150 | template 280 + LeafArm 220 + 60 python |
| var | ~240 | ~300 | templates 540 + LeafCalls 240 + LeafErr 250 |

## Holes
None added.
