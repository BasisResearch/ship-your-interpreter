# Wave 40 — execFrameShift core + the exec-eval cuts

## Board on entry (from wave 38/39)
- eval-child: 7/14 machine-composed (unary, binaryL, binaryR, logicalL, logicalR,
  assignE, callF). 7 remaining: argsHead + the 6 exec-eval (stmtExpr/stmtRet/
  stmtVarInit/stmtIfCond/stmtWhileCond/flCond).
- non-eval (11 exec/args/for): named. SqEntry: seqHead wired. flStep: named.
- Wave 38 declared the 6 exec-eval fields BLOCKED on a "frame shift" (exec_stmt
  lowers sp by 176 not 1088) + non-uniform heads.

## CORE VERDICT: hypothesis-confirmed-EASY (ghost re-parametrization, no lemma)

Machine evidence (read this wave):
1. `evalEntry_of_jalPrefix` (ArmSegSplit.lean:143-251) DESTRUCTURES the five
   spill-window premises `hslotRa/hslotS0/hslotS1/hslotS2` (read64 mcall (sp-8/
   -16/-24/-32)) + `hspSLhi` from its `hpre` and NEVER USES them. The child
   `EvalEntry.spill_defined` is built from REGISTER facts (x8/x9/x18), not the
   memory slots. `landedN_eentryC_of_preBundle` wraps it → those JalPreBundle
   premises are DEAD for the divergence entry.
2. stmtExpr arm (0x80004170) disasm: `ld a2,8(s0); addi a0,sp,16; mv a3,s3;
   mv a1,s1; jal eval_expr`. It calls eval_expr with x2 = the exec frame's own
   lowered sp (execSp-176), NO further 1088 lowering.
3. So: instantiate `JalPreBundle.sp := (execSp-176)+1088`. Then `sp-1088 =
   execSp-176 = x2 at the jal`. The geometry facts are over the enlarged sp
   (esp+1088), and StoreRepr-survival over [SL.lo, esp+1088) is IMPLIED by
   ExecEntry's survival over the SMALLER [SL.lo, execEntrySp) (esp+1088 =
   execEntrySp+912 > execEntrySp). No ExecJalPreBundle twin, no per-frame spill
   reconciliation. The wave-38 obstruction assumed the spill-window was
   load-bearing; it isn't.

Observation appended: `jalprebundle-spill-window-vestigial-so-execframeshift-EASY`.

## Work log

## Outcome — execFrameShift core landed + stmtExpr closed end-to-end

### CORE VERDICT: twin-bundle (frame-shift itself is a ghost rebase; the real
### blocker was the jal-site loaded-predicate, resolved by ONE shared twin)
Three pieces, in ascending difficulty:
1. FRAME SHIFT (ghost rebase, trivial): instantiate `sp := (sp_exec-176)+1088` so
   `sp-1088 = x2` at the exec-arm jal. Confirmed by the machine (dead spill-window).
2. WIDE-WINDOW SURVIVAL (named premise): `StoreRepr` survival over `[SL.lo, esp+1088)`
   carried as a premise the M6 layout supplies (mirrors `EvalEntry.store_survives`).
3. JAL-SITE LOADED-PREDICATE (the REAL blocker, twin): `JalPreBundle.hjalSite` is
   typed `Eval_exprLoaded`, but the exec-arm jal @0x80004180 is in exec_stmt text
   (`Exec_stmtLoaded`; 0x80004180 ∉ any eval chunk). Resolved by the ONE shared twin
   `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix` (a clone of the eval bridge with
   the site loaded-predicate flipped), dropping the 5 dead spill-window premises
   (their addresses would be in the caller's frame with no memory fact).

### FILES (all green + axiom-clean {propext, Classical.choice, Quot.sound}, disc OK)
- NEW `Vsa/Sim/ArmSegSplitExecEval.lean` — the exec twin: `execEvalEntry_of_jalPrefix`,
  `ExecJalPreBundle`, `landedN_eentryC_of_execPreBundle`, `execEvalChildSplit_of_stage`,
  + the 6 field splits `stmtExpr_split'`/`stmtRet_split'`/`stmtVarInit_split'`/
  `stmtIfCond_split'`/`stmtWhileCond_split'`/`flCond_split'`.
- NEW `Vsa/Sim/rows/StmtExprArmStagePre.lean` — `blockB_stmtExpr_stagePre` (the 4-instr
  arm-head cut reusing the LANDED `site_80004170/74/78/7c_es`, no new site battery) +
  `StmtExprArmDispatch` + `stmtExpr_field_of_dispatch` (SEntryC (.expr e) → EEntryC e,
  modulo the dispatch residual).
- AMENDED `Vsa/Sim/ArmSegSplitEval.lean` — 6 exec-eval `EvalChildStages` fields re-typed
  from `→ JalPreBundle` to `→ EEntryC` (post-split; cannot reference ExecJalPreBundle
  from here — import cycle); `armResidGap_evalChildFields` uses them directly.
- AMENDED `Vsa/Sim/ArmStagesPartial.lean` — `evalChildStages_mk`'s 6 exec params re-typed.
- AMENDED `Vsa/Sim/ArmStagesWave34.lean` — 6 exec params re-typed in the 3 builders;
  NEW `evalChildStages_ublracSE_wired` (wires stmtExpr) + `divFamily_wave40` capstone.

### BOARD (eval-child)
- 8/14 machine-composed: unary, binaryL, binaryR, logicalL, logicalR, assignE, callF,
  **stmtExpr (NEW)**.
- 6 remaining: argsHead (blocked on crux arg-loop, unchanged) + the 5 other exec-eval
  (stmtRet/stmtVarInit/stmtIfCond/stmtWhileCond/flCond) — all now UNBLOCKED: they ride
  the SAME `ExecJalPreBundle` core + their split twins are landed; each needs only its
  arm-head cut supplier (a `blockB_<arm>_stagePre` clone; heads differ by instr order
  + an optional beqz null-branch for varInit/ret — a `gen_exec_stagepre.py` fans them).
- non-eval (11), SqEntry (seqHead wired; stmtBlock/callBody named), flStep: unchanged.

### divFamily premise shrink
`divFamily_wave40` = `divFamily_wave34` with the `eval` bundle now buildable via
`evalChildStages_ublracSE_wired` (stmtExpr no longer an opaque `∀`-premise — replaced
by the strictly-smaller `StmtExprArmDispatch` dispatch residual). 8/14 eval-child fields
have their whole `SEntryC/EEntryC → EEntryC child` path machine-composed.

### SIGNALS
- The 5 remaining exec-eval arms are a MAIL-MERGE off this wave's core: same twin,
  same split, same frame-shift/survival/geometry premise shape. `gen_exec_stagepre.py`
  over {armPC, head instr-order, optional beqz, child-node offset} would erase them.
- The dispatch residual `StmtExprArmDispatch` is dischargeable by `execBlockA` (LANDED)
  + the layout facts; a future `stmtExpr_dispatch_of_execBlockA` would remove even that.
