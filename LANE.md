# Lane E5: `exec_stmt`'s statement arms

Branch `lane-e5` (from `wave4-base`, merged `hub/iris-main` at INTEGRATION.md).
Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row "exec"); statement change in
§10 "STATEMENT CHANGES (E5)". Family: expr, varInit, varNull, block, if (3
outcomes), return (2), break, continue, and the while/for arms' non-loop parts.
Rows: `scripts/iris_arms/arms.d/e5-exec.tsv`.

## STATEMENT CHANGE: the exec motive is stated at the dispatch point

gcc compiled `if`'s `return exec_stmt(in, branch, env, ret)` as an in-frame
tail call (`0x8000422c ld s0,16(s0); j 0x80004014`, `0x800042cc ld s0,24(s0);
bnez s0,0x80004014`, after `li a6,8; auipc a4`). The branch never runs from
`exec_stmt`'s entry, so the entry spec `execSpecT_body` cannot discharge it.
Every exec arm is proved at the DISPATCH point `0x80004014`
(`VsaIris/Interp/SpecExecDisp.lean`):

- `execDispT_body … D` (total) — **the recursor motive of `ExecSCost` for A**;
- `execDispP_body Core …` (partial) and its Löb hypothesis `execDispsP`;
- `ExecDisp.lean`: `execSpecT_of_disp`, `execSpecP_of_disp`,
  `execSpecsP_of_disps` recover the entry specs (prologue run `ExecProl_run`,
  `wp_execProl`) for every `jal exec_stmt` caller (block/while/for bodies, closure
  bodies, `interp_run`). `execDispT_apply`/`execDispP_apply`/`execDispsP_at`
  instantiate the specs.

Dispatch-point state: `ms 0x80004014 R (InExt (s-176,176)) Mt`, `DispFacts`
(`DispRegs`: `sp = s-176`, `s0` stmt, `s1` in, `s2` ret slot, `s3` env,
`a6 = 8`, `a4 = 0x80019fb8`; `ExecSaved Mt s ret v8 v9 v18 v19`: the spills;
`ret` aligned; `StackGeom s (execNeed sm d)`; `SlotGeom aRet`; bodies bound).
The continuation `execDispK` gets `ExecRet` (sp, s0-s3 restored, s4-s11 kept,
status in `a0`) at the return address, the whole stack, `statusRet`.

**For E6 / A:** replace `execSpecT_body D` by `execDispT_body D` in the
`ExecSCost` motive (E6's `execSpecT_body D ∧ …while…`). The while arm enters its
loop at `0x8000403c`, the for arm at `0x8000423c`/`0x8000426c`, in the frame
at the dispatch-point state; E5 proves dispatch → loop head and the exits.

## Done (all axioms ⊆ {propext, Classical.choice, Quot.sound}, `E5Audit.lean`)

| arm | T | P | family / file |
|---|---|---|---|
| break, continue | `caseT_ExecBrk`/`Cont` | `caseP_…` | `execConst` |
| `expr e` | `caseT_ExecExpr` | `caseP_ExecExpr` | `execEval1 tail=epi` |
| `ret e` | `caseT_ExecRet` | `caseP_ExecRet` | `execEval1 tail=ret` |
| `ret;` | `caseT_ExecRetNull` | `caseP_ExecRetNull` | `execNullRet` |
| `if` true / false / none | `caseT_ExecIfTrue`/`False`/`None` | `caseP_ExecIf` (every outcome) | `execIf*` over `ExecIf.lean` |

Layers (hand): `SpecExecDisp.lean`, `ExecDisp.lean`, `ExecArm.lean` (node
facts `StmtNode`/`ExprFieldNode`/`IfNode`; shared exits `wp_execEpi` (a0 set,
`0x8000409c`) and `wp_execRetCopy` (`0x80004138`, copy into the `ret` slot),
both for either WP; `ms_callEvalPF` (partial child call from a frame of any
size); `ms_callHelperSlot`/`ms_callHelperVal` (a helper filling / reading a
frame slot); `ms_slotIn`/`ms_valOut`; the in-frame tail call `ifRedispatch`,
`execDispKP_redispatch`), `SymLater.lean` (`wp_swpF_later`: a symbolic run that
pays the Löb later — the `if` re-dispatch is a jump, not a `jal`),
`ExecIf.lean` (the `if` runs, `wp_ifTruthy`, `ifPrefixT/P`, routes).

Generator (additions only; G's rows regenerate identically):
`gen_iris_cases.py` accepts exec rows starting at the dispatch point
(`EXEC_DISP`); families `execConst`, `execEval1` (tail snippets
`execEval1_tail_{epi,ret}_{T,P}`), `execNullRet`, `execIfTrue/False/None/All`.
A family may emit only one mode (the three total `if` rows vs one partial row).

## Blocked / in flight
- **Partial cases that can run out of memory** (`var` via `env_define`,
  block and `for` via `env_new`): the partial specs abort with a FIXED `Core`
  (G), H5's out-of-memory core is site-indexed (`oomCore s n`); see
  `experiments/smt/PROOF_CLOSURE_PLAN.md` "The partial specs' abort core is
  not site-indexed". Proposed fix: abort with `abortRes s need`, rebase with
  `abortRes_widen`. Raised with the user (cove status). Total cases proceed.
- In flight: `var` (init/null) total, block total (G's `blockSeqT_body`),
  while/for total over E6's `SpecLoop`.

## Line counts (generated vs hand)
| arm | generated T | generated P | hand layer used |
|---|---|---|---|
| break / continue | 2 × 96 | 2 × 74 | ExecArm (shared) |
| expr / ret e | 136 / 117 | 124 / 111 | ExecArm exits |
| ret; | 131 | 106 | `ms_callHelperSlot` |
| if (T × 3, P × 1) | 42 / 42 / 37 | 59 | `ExecIf.lean` 715 |
| shared hand layer | | | `SpecExecDisp` 151, `ExecDisp` 278, `ExecArm` 923, `SymLater` 129 |

## Holes
None added.
