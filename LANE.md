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

## In flight
- `var` (hit; partial: miss → `runtime_error`), `assign` (ok; partial:
  unbound → `runtime_error`, child abort), `fn` (partial: OOM →
  `oom80003e28`).

## Line counts (generated vs hand)
| arm | T generated | P generated | hand |
|---|---|---|---|
| leaf family (4 arms) | 4 × ~150 | 4 × ~150 | template 280 + LeafArm 220 + 60 python |

## Holes
None added.
