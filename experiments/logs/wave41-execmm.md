# Wave 41 lane execmm — the exec mail-merge (plan queue #2)

Supply the 5 exec-arm stage-pre fields: stmtRet, stmtVarInit, stmtIfCond,
stmtWhileCond, flCond — by riding `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix`
(`ArmSegSplitExecEval.lean`) + the landed split theorems `*_split'`.

Model: `Vsa/Sim/rows/StmtExprArmStagePre.lean` (stmtExpr, landed wave 40).
Model produces `LandedN 4 c (fun c' => ExecJalPreBundle e c' st d env)` via
`blockB_stmtExpr_stagePre` + a `StmtExprArmDispatch` residual + `stmtExpr_field_of_dispatch`
threading through `stmtExpr_split'`.

## Arm head survey (from disasm, CONFIRMED)

| arm         | armPC0     | head instrs                                        | branch |
|-------------|------------|----------------------------------------------------|--------|
| stmtExpr    | 0x80004170 | ld a2,8(s0); addi a0,sp,16; mv a3,s3; mv a1,s1; jal| no (LANDED wave40) |
| stmtRet     | 0x80004120 | ld a2,8(s0); beqz; mv a3,s3; mv a1,s1; addi a0,sp,16; jal | yes |
| stmtVarInit | 0x800040d8 | ld a2,16(s0); beqz; mv a1,s1; mv a3,s3; addi a0,sp,104; jal | yes |
| stmtIfCond  | 0x800041e8 | ld a2,8(s0); mv a3,s3; mv a1,s1; addi a0,sp,56; jal | no |
| stmtWhileCond| 0x8000403c| ld a2,8(s0); mv a3,s3; addi a0,sp,80; mv a1,s1; jal | no |
| flCond      | 0x8000426c | ld a2,16(s0); beqz; mv a3,s3; addi a0,sp,104; mv a1,s1; jal | yes |

Uniformity verdict: heads are NON-uniform (instr order differs; 3 have a mid-head
beqz null check). NOT the eval 3-step class. gen_stagepre.py targets the EVAL
`ld+addi+sd → jal` JalPreBundle 3-step class — a DIFFERENT shape (produces
JalPreBundle not ExecJalPreBundle, 3 steps not 4-6). See obs
`exec-eval-stagepre-frameshift-and-nonuniform` (2597) + `exec-stmt-stagepre-different-frame` (2541).

## Site battery status
- stmtRet 0x80004120: site_80004120..34 ALL LANDED (Exec_stmtSites, incl site_80004124_nottaken_es)
- stmtVarInit 0x800040d8: site_800040d8..ec ALL LANDED (incl site_800040dc_nottaken_es)
- stmtIfCond 0x800041e8: sites MISSING (need 800041e8,ec,f0,f4,f8)
- stmtWhileCond 0x8000403c: sites MISSING (need 8000403c,40,44,48,4c)
- flCond 0x8000426c: sites MISSING (need 8000426c,70(beqz),74,78,7c,80)
byte lemmas exec_stmt_at_* exist for whole text (generated).

## Progress
- LANDED stmtRet: `Vsa/Sim/rows/StmtRetArmStagePre.lean` green + axiom-clean.
  `blockB_stmtRet_stagePre` (LandedN 5, arm 0x80004120, 6-step head incl beqz nottaken),
  `StmtRetArmDispatch` + `stmtRet_field_of_dispatch`. beqz-nottaken via hExprNe from
  `0x80000000 ≤ aExprChild.toNat`. Reused landed site_80004120..34 from Exec_stmtSites2.
- LANDED stmtVarInit: `Vsa/Sim/rows/StmtVarInitArmStagePre.lean` green + axiom-clean.
  `blockB_stmtVarInit_stagePre` (LandedN 5, arm 0x800040d8, ld OFFSET 16, buf sp+104,
  mv order a1/a3), `StmtVarInitArmDispatch` + `stmtVarInit_field_of_dispatch`.
  Reused landed site_800040d8..ec from Exec_stmtSites3.
- NOTE on offset-16 ld: the stmt geometry premises use `aStmt+24` bounds (ld reads
  [aStmt+16, aStmt+24)), differs from stmtRet/stmtExpr (offset 8 → +16 bounds).
- LANDED sites: `Vsa/Sim/ExecCondArmSites.lean` (NEW FILE, green + axiom-clean).
  site_800041e8..f8 (if), site_8000403c/40/44/48/4c (while), site_8000426c/70(nottaken)/74/78/7c/80 (for).
  All modeled on existing `_es` sites; decode + byte lemmas pre-existed.
- LANDED stmtIfCond: `Vsa/Sim/rows/StmtIfCondArmStagePre.lean` green+clean.
  blockB_stmtIfCond_stagePre (LandedN 4, arm 0x800041e8, buf sp+56, no beqz),
  StmtIfCondArmDispatch + stmtIfCond_field_of_dispatch.
- LANDED stmtWhileCond: `Vsa/Sim/rows/StmtWhileCondArmStagePre.lean` green+clean.
  blockB_stmtWhileCond_stagePre (LandedN 4, arm 0x8000403c, buf sp+80, addi-before-mv,
  no beqz), StmtWhileCondArmDispatch + stmtWhileCond_field_of_dispatch.
- LANDED flCond: `Vsa/Sim/rows/FlCondArmStagePre.lean` green+clean.
  blockB_flCond_stagePre (LandedN 5, arm 0x8000426c, ld OFFSET 16, buf sp+104, beqz),
  FlCondArmDispatch (from FEntryC (some cc) step b) + flCond_field_of_dispatch.

## ALL 5 ARMS LANDED. gen_stagepre.py NOT extended (verdict above: non-uniform;
##   the true shared abstraction is the already-landed execEvalEntry_of_jalPrefix +
##   ExecJalPreBundle bridge, not a code-gen template).

## Wiring (return to coordinator; do NOT touch Vsa.lean / check_all.sh myself)
Imports for Vsa.lean:
  import Vsa.Sim.ExecCondArmSites
  import Vsa.Sim.rows.StmtRetArmStagePre
  import Vsa.Sim.rows.StmtVarInitArmStagePre
  import Vsa.Sim.rows.StmtIfCondArmStagePre
  import Vsa.Sim.rows.StmtWhileCondArmStagePre
  import Vsa.Sim.rows.FlCondArmStagePre
check_all THEOREMS entries (axiom-audit):
  Vsa.Sim.blockB_stmtRet_stagePre, Vsa.Sim.stmtRet_field_of_dispatch
  Vsa.Sim.blockB_stmtVarInit_stagePre, Vsa.Sim.stmtVarInit_field_of_dispatch
  Vsa.Sim.blockB_stmtIfCond_stagePre, Vsa.Sim.stmtIfCond_field_of_dispatch
  Vsa.Sim.blockB_stmtWhileCond_stagePre, Vsa.Sim.stmtWhileCond_field_of_dispatch
  Vsa.Sim.blockB_flCond_stagePre, Vsa.Sim.flCond_field_of_dispatch
  (optionally the ExecCondArmSites site_* lemmas)

## Exponentiation decision (per CLAUDE.md mandate)
- The 5 arms are the 3 beqz group (stmtRet/stmtVarInit/flCond) + 2 no-beqz
  (stmtIfCond/stmtWhileCond). stmtExpr (model) is a 3rd no-beqz. So there ARE ≥3
  uniform in each subgroup structurally, BUT: (a) instr ORDER differs per arm
  (mv/addi permutations), (b) ld-offset differs (8 vs 16), (c) beqz present in 3.
  gen_stagepre.py targets a DIFFERENT shape (eval 3-step ld+addi+sd→jal, produces
  JalPreBundle not ExecJalPreBundle). Extending it would require a per-instruction
  ordered-list schema + optional-beqz + the ExecJalPreBundle 6-tuple — a large new
  template class, and the sites for 3 arms don't exist yet either.
- DECISION: hand-write all 5 following the model (stmtExpr). Each blockB proof is
  ~230 lines but each landed FIRST TRY from the model with only the 5-tuple + instr
  order + beqz-peel changed. Cost is linear + one-shot, not exponential. The obs
  `exec-eval-stagepre-frameshift-and-nonuniform` already recorded ~5 distinct
  sub-shapes; a generator here is not justified (would be more code than the 5
  instances and the frame-shift core is already the shared `execEvalEntry_of_jalPrefix`
  + `ExecJalPreBundle` bridge — the TRUE shared abstraction, already landed).
