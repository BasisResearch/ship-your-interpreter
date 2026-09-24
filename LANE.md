# Lane E1: leaves, var, assign, fn (eval_expr)

Branch `lane-e1` (from `wave4-base`, `hub/iris-main` merged after
INTEGRATION.md). Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8, §9 E1;
statement changes and the interface for A in §10 "STATEMENT CHANGES (E1)".
Rows: `scripts/iris_arms/arms.d/e1-leaves.tsv` (7 rows).

## Done: every E1 arm, both modes

| row | total case | partial case | error arms (partial) |
|---|---|---|---|
| `LeafInt`/`LeafStr`/`LeafBool`/`LeafNull` | `caseT_Leaf*` | `caseP_Leaf*` | none |
| `Var` | `caseT_Var` (lookup found) | `caseP_Var` | unbound → `runtime_error` |
| `Assign` | `caseT_Assign` (name bound) | `caseP_Assign` | child abort (rebased), unbound → `runtime_error` |
| `FnLit` | `caseT_FnLit` (counted `malloc`) | `caseP_FnLit` | `malloc` NULL → `oom80003e28` → `exit(1)` |

- Each partial case is ONE `#ix_chain` with no exported hypotheses: the case
  split (lookup, `Store.set?`, `mallocRes`) closes one branch inside the
  splitting piece and continues the other.
- Children are hypotheses: `evalSpecT_body` of the child's derivation (total);
  the Löb hypothesis `evalSpecsP` (partial). Helper specs are hypotheses:
  `valueIntSpec`/`valueStrSpec`/`valueBoolSpec`/`valueNullSpec`,
  `envGetSpec`, `envSetSpec`; `fn` takes `AllocSpecs live` and
  `textOwn allocText` (`allocSpecs` is proved, H4).
- All in `lake build Vsa VsaIris VsaIris.Audit`; the 14 cases and the hand
  layer's call lemmas are in `Audit.lean`, axioms ⊆ {propext,
  Classical.choice, Quot.sound}. G's generated cases regenerate identically
  (`gen_iris_cases.py --check`).

## Generator additions (for the other E lanes)

- Families `leaf` (`LEAF_KINDS` table: per-kind node lemma, helper spec,
  pins), `var` and `fnLit` (`subst_call1`: run, one helper call, tail),
  `assign` (`subst_assign`: run, child, run, helper, tail). Row params:
  `kind`, `tail` (shared tail PC), `ej` (the `jal runtime_error`/OOM PC),
  `fmtok` (the message's `FmtArgsOK` lemma), `br` (a branch handled by hand),
  `oom` (the OOM block head); `errors` gives the divert targets (`E1TO`).
- Lessons that cost time:
  - A piece must not END inside a run: after `intro F'` the frame is a
    `let`, which `#ix_piece` cannot abstract ("mentions locals outside its
    statement"). Split pieces after `swp_closeM … iintro`.
  - A run's continuation sees only its frame `F` and the machine state:
    persistent hypotheses needed later (`errCtx`, the Löb hypothesis,
    `textOwn`, `□ valOf`) must be put in `F`.
  - `ix_run` cannot prune a branch on a register equal to a fact
    (`R 10 = 0` vs `h10 : R 10 = 1`): stop the run at the branch (`at pc`)
    and apply the step lemma `it_<pc>` by hand.
  - `rfl`/`rw` on goals with 64-bit literals can hit max recursion; close
    `R x = …` goals with `ix_reg` + `keep`-rewrites.
  - Heartbeats are per piece: forward loads through slot writes with the
    `slotWrite_ld*` lemmas, not `ix_fwd` (`LeafCalls.lean`).

## Hand layer (reusable)

- `LeafArm.lean`: `LeafNode` (leaf analogue of `BinNode`),
  `leafNode_{null,int,bool,str,var,assign,fn}`, `StrField`,
  `sharedWin_of_readOK`.
- `LeafCalls.lean`: the result slot in the run's bytes (`frS`,
  `ms_intro_sret`, `ms_join_sret`, `ms_exit_sret(Any)`), an out slot lent to
  a callee (`ms_carveSlot`/`ms_joinSlot`/`ms_unslot`), `ms_callEnv3`
  (`env_get`/`env_set` from a run), `ldv_ld_agree`, `slotWrite_ld*`,
  `imgW_low4`, `inExt_disj`.
- `LeafErr.lean`: `ev_rtErr` (`runtime_error` from an eval frame),
  `ev_oom` (an eval arm's OOM block), `errCtx`, `ErrRoom`, `evalCore`,
  `fmt1s_ok` + the two messages.

## Interface for A
- Partial cases with error arms are stated at `Core := evalCore N L Room inp`.
- They take `errCtx inp` (persistent) beside the Löb hypothesis.
- `ErrRoom e d` (`var`/`assign` partial) is Q7: true for `d < maxCallDepth`.
- `fn` is stated at `vsaLayoutP`/`vsaRoomB` (`malloc`'s heap).

## Line counts (generated vs hand)

| arm | T generated | P generated | hand (template T + P) |
|---|---|---|---|
| `LeafInt`/`Str`/`Bool`/`Null` | 159/163/159/159 | 140/144/140/140 | shared `leaf` 158 + 139 |
| `Var` | 239 | 280 | 238 + 279 |
| `Assign` | 341 | 370 | 340 + 369 |
| `FnLit` | 289 | 308 | 288 + 307 |
| shared hand layer | | | `LeafArm` 202, `LeafCalls` 283, `LeafErr` 288, generator +114, table 11 |

Generated total 3,091 lines; hand total 2,902 (templates 2,118, layer 773,
table 11). The `leaf` family pays off at 4 rows (1,264 generated lines from 297
template lines); `var`, `assign`, `fnLit` are one row each, so their
templates are the proofs.

## Holes
None added (`check_iris_holes.py`: 12 ledgered, unchanged). Open named
premise: `ErrRoom` (Q7), recorded in `experiments/smt/PROOF_CLOSURE_PLAN.md`.
