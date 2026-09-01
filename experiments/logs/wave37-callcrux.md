# Wave 37 — the CallClosure crux (EX_CALL closure arm at depth d+1)

Status log, incremental. Task: compose the closure-application route
(callee-eval ≫ depth guard ≫ arg loop ≫ env_new ≫ arg-define loop ≫ body
ExecSeq at d+1 ≫ ret copy) toward `CallClosureResid`
(`rows/CallClosureRow.lean` — the landed hCallClosure row's residual =
`CallClosureGeom` = `entryBase` + `entryFold` + `ret`, ∀-closed over ghosts).

## Session start (2026-09-01)

Landed raw material surveyed:
- `rows/CallClosureRow.lean` — the recursor row IS landed
  (`eval_callClosure_row` + slot-verify). Residual = `CallClosureResid` =
  ∀ ghosts, `CallClosureGeom` { entryBase, entryFold, ret }. The depth step
  (`mExecSeq … (d+1) … a_5` → `hBodyIH` at callBodyLoopPC/callBodyRetPC) is
  ALREADY composed there — definitional unfolding of `mExecSeq`, no new
  proof shape. So the flagged tail risk is narrower than feared: what
  remains is machine spans + contracts, not depth-indexed recursion.
- SIX Gen segs (committed): callArmCalleeEvalSeg/Bridge (0x800031b0→jal
  eval_expr@0x800031bc), callClosureArgLoopEntrySeg/Row (0x800031cc→blez
  @0x800031d8→0x800031dc), callClosureEnvNewCallSeg/Bridge (0x800032b4→jal
  env_new@0x800032bc, callee 0x800029fc link 0x800032c0),
  callClosureEnvDefineCallSeg/Bridge (0x8000330c→jal env_define@0x80003310,
  callee 0x80002a5c link 0x80003314), callClosureValueNullCallSeg/Bridge
  (0x80003324→jal value_null@0x80003328, callee 0x800027ec link 0x8000332c),
  callClosureRetCopySeg/Row (0x8000339c→j callJoinPC 0x800033ec).
- Splice layer: `SpliceChain`/`spliceFold`, `CallSpec` (EntryP/ExitP/Sat),
  `rzSeamFrame_of_run` (CallFrameMeta), pilot `StrdupTailSpliceFold`.
- Depth machinery: `execEntry_recast_depth` (SeqHeadStages),
  `callBody_split` (ArmSegSplitSqEntry §3).

## Next: arm map from disasm 0x80003254..0x800033ec

## Step 1 — the arm map (disasm 0x800031b0..0x800033ec + 0x80003954)

EX_CALL composite arm (context; OFF the CallClosureResid target, which starts
at callDispatchPC):
- 0x800031b0..0x800031bc  callee-eval staging ≫ jal eval_expr — GEN
  `callArmCalleeEvalBridge` (bridgeOfSeg; jal seam residual). Consumed by
  CallArmSpec (CallResidProviders residual 5), not by CallClosureGeom.
- 0x800031c0..0x800031c8  callee-eval return staging (ld a3,104?; lw a5,4(s0)
  argc reload) — NO seg (part of CallArmSpec).
- 0x800031cc..0x800031d8  arg-loop entry (sd s7,1016(sp); ld a3; li a6,0 ▷
  blez a5→0x80003254) — GEN `callClosureArgLoopEntryRow`.
- 0x800031dc..0x80003250  arg-loop body (per-arg jal eval_expr + 24-byte copy
  to sp+240+24k ▷ bne back-edge) — residual layer EXISTS:
  ArgsBodyOracle/ArgsPhiGlue/ArgsNilHop (CallResidProviders).

CallClosureGeom proper (callDispatchPC 0x80003254 → callJoinPC 0x800033ec):
- 0x80003254..0x80003284  fv-kind dispatch (ld a4,96(sp) fval kind; spill fval
  24B to sp+120..136; lw a1,4(s0) argc; mv s7,a1; beq kind,5→native;
  bne kind,4→error; fall-through = closure) — MISSING span; writes s7
  (callee-saved) ⇒ frame-tracking decode, NOT WrChainAvoidAbi/bridgeOfSeg.
- 0x80003288..0x800032b0  closure head (ld a4,0(a3) closure rec; sd s5,1032(sp);
  mv s5,a4; lw a4,24(a4) arity; bne argc→error; lw a4,8(s2) depth; ++, sw;
  sd s3,1048(sp); blt 1000,depth→error) — MISSING span; writes s5/s3 spills ⇒
  frame-tracking. a_2 gates arity-bne not taken; a_3 gates blt not taken.
- 0x800032b4..0x800032bc  env_new staging (ld a0,8(a3)=cd->env; sd a5,0(sp)) ≫
  jal env_new@0x800029fc link 0x800032c0 — GEN `callClosureEnvNewCallBridge`.
- env_new — REAL CONTRACT `env_new_spec` (EnvNewSpec), parentSpec := some
  cd.env, ret := 0x800032c0. a_4 = allocFrame (some cd.env).
- 0x800032c0..0x800032c8  env_new return (ld a5,0(sp) argc; mv s3,a0 frame ptr;
  blez a5→0x80003324 ZERO-PARAM BYPASS) — MISSING (writes s3).
- 0x800032cc..0x800032d8  fold init (sd s6,1024(sp); addi s0,sp,240;
  slli s6,a5,3; li a5,0) — MISSING (writes s6/s0).
- param fold, per k < n:  0x800032dc..0x80003308 staging (ld arg 24B from
  s0-cursor → sp+64..80 buffer; a4 := names+8k; a0:=s3; sd a5,0(sp); s0+=24)
  — MISSING (writes s0) ≫ 0x8000330c GEN `callClosureEnvDefineCallBridge` ≫
  env_define REAL contract (EnvDefCompose.envDefContract) ≫ 0x80003314..
  0x8000331c back-edge (ld a5,0(sp); a5+=8; bne s6,a5→head) — MISSING.
- 0x80003320  fold exit (ld s6,1024(sp) restore) — MISSING (tiny).
- 0x80003324..0x80003328  value_null staging ≫ jal value_null@0x800027ec — GEN
  `callClosureValueNullCallBridge`; value_null REAL (`value_null_spec` ValueSpec).
- 0x8000332c..0x8000333c  body entry (ld a6,32(s5)=cd->body; li s0,0;
  lw a5,16(a6)=count; bgtz→0x80003354 | j 0x80003954 EMPTY-BODY BYPASS) —
  MISSING (writes s0).
- 0x80003354..0x80003374  body per-stmt dispatch ≫ jal exec_stmt — the
  recursor's hBodyIH territory (mExecSeq at p=0x80003354, q=0x80003378).
- 0x80003378..0x80003398  status classification (beqz a0→loop cont;
  --call_depth; bgeu 1,a5→brk/cont error (OFF-premise per a_6); bne a0,3→
  0x80003960; fall-through=.ret) — MISSING (status→a0 ABI gap, cf.
  seqfor-motive-rows observation).
- 0x8000339c..0x800033c0  .ret result copy (24B sp+144→s1 sret; restore
  s3/s5/s7) ▷ j 0x800033ec — GEN `callClosureRetCopyRow`.
- 0x80003954..  .normal path (--call_depth + null-buffer copy → join) —
  MISSING span.

## Step 2 — STATEMENT FALSITY found in the landed CallClosureGeom (Law 4)

entryBase's post `SegEntry … boundSt (d+1) … callBodyLoopPC m0` is
unsatisfiable three ways: (1) SegEntry.mem pins post-route memory = entry m0
(route allocates + spills); (2) caller φf unextended but ∀-quantified in
CallClosureResid (fresh frame address can't equal φf(frame) for every φf);
(3) cd.body = [] route never visits callBodyLoopPC/callBodyRetPC (bgtz
@0x80003338 → j 0x80003954); zero-params route likewise bypasses the fold head
(blez @0x800032c8). Ledger entry appended to observations.md
(`callclosuregeom-entrybase-unsatisfiable`). AMENDING in place:
- new mid `BodyHandoff` = ∃ φf' mB, PhiExtends φf φf' st.store.frames.size ∧
  (stack/arena frame mB↔m0) ∧ SegEntry@callBodyLoopPC over φf'/mB;
- entryBase : cd.body ≠ [] → Triple (SegEntry@dispatch m0) BodyHandoff;
- ret : cd.body ≠ [] → ∀ φf' mB, PhiExtends → frame → Triple
  (SegExit@retPC over φf'/mB) (SegExit@join over φf/m0);
- emptyBypass : cd.body = [] → st' = boundSt → Triple (SegEntry@dispatch m0)
  (SegExit@join st' m0);
- callClosureSim gains hNilLink (from a_5 inversion in the row) + hBodyIH
  ∀-quantified over (φf', mB) — FREE from mExecSeq (quantifies φf/φc/p/q/m0).

## Step 3 — depth-step verdict (the flagged tail risk)

COMPOSED, no new proof shape. The landed row already threads the recursor's
`mExecSeq … (d+1) … a_5` motive to the body Triple by DEFINITIONAL unfolding,
instantiated at callBodyLoopPC/callBodyRetPC/(dLeft-1)/(aLeft-1) — and the
motive's universal (φf, φc, p, q, m0) quantifiers are exactly what the
amendment needs to instantiate at the ∃-bound (φf', mB). No
execEntry_recast_depth needed on this route (the motive is depth-indexed
already; recast is only for depth-phantom ExecEntry conclusions like
loopHeadDispatch_span's d=0). The depth guard d < maxCallDepth is a_3, gating
the blt @0x800032b0 in the (named) closure-head span.

## Step 4 — amendment LANDED (CallClosureRow.lean, green + axiom-clean ~1.4s)

- `BodyHandoff` def (R7-allow: reached-Config bundle, ∃-bound (φf', mB)).
- `entryBase`/`ret` guarded `cd.body ≠ []`; `ret` ∀ over the handoff pair with
  PhiExtends + stack/arena-frame hypotheses; NEW `emptyBypass` field.
- `callClosureSim` re-proved: cases on cd.body; nil → emptyBypass (st'
  rewritten via hNilLink); cons → callSeg with ∃-massaged Mid1/Mid2 (the
  handoff pair carried across the body IH by hand-rolled hop lambdas).
- `eval_callClosure_row`: hNilLink from a_5 inversion (fresh `hb ▸ a_5` copy —
  rewriting a_5 in place would disturb hBody whose TYPE mentions a_5; then
  `cases`+`rfl`); hBodyIH now the (φf', mB)-family, still free from mExecSeq.
- Slot-verify `eval_callClosure_row_fills_hCallClosure` UNCHANGED and green —
  the verbatim hCallClosure premise is untouched by the amendment.
- Axioms all ⊆ {propext, Classical.choice, Quot.sound}. Olean regenerated in
  place (lake env lean -o). Zero non-doc consumers of the old field shapes
  (grepped: only doc comments + the stale un-imported EvalCallClosure.lean).

## Step 5 — next: the splice file (entry route as spliceFold + loop invariants)

## Step 4b — second + third statement fixes in the same Geom

- `entryFold` DELETED: ∀-quantified arbitrary `pcf : Nat → Nat` (independent-PC
  disease, unsatisfiable) AND dead plumbing (never consumed by callClosureSim).
  Ledger `callclosuregeom-entryfold-pcf-unsatisfiable`. closureParamsFold kept
  (carrier-agnostic storeChainList witness).
- Ghost-tie fix: the route clobbers s0/s3/s5/s6/s7 before callBodyLoopPC, so
  BodyHandoff's SegEntry could not tie to the ARM's g — now ∃-binds the body's
  own ghost g' (mExecSeq is universal in g); ret ∀-quantifies (g', φf', mB).
- All green + axiom-clean after each step; olean regenerated.
- RESIDUAL-STRENGTH RISK noted (not fixed, motive-family scope): `ret`'s
  discharger must restore the caller's s3/s5/s7 from the 1016..1048(sp) spill
  slots, but the body IH's SegExit.memFrame only frames memory OUTSIDE SL — the
  spill slots are INSIDE SL, so their survival across the body is not derivable
  from the motive as stated. Same class as the seqfor-motive-rows "motives lack
  sp/ABI" gap; needs a stack-window-discipline clause in the motive family
  (exec-side lane), NOT a per-row hack.

## Step 6 — the splice layer LANDED (rows/CallClosureSplice.lean, green 1.5s, axiom-clean)

NEW FILE `Vsa/Sim/rows/CallClosureSplice.lean`:
- §1 the two loop invariants as named-field structures:
  `CallArgLoopInv` (arg loop @evalArgsLoopPC: a6=index, a5=argc, s0=call node,
  s2=interp, a3=env, ValueRepr slots at sp+240+24i, stack/arena memFrame) and
  `CallParamFoldInv` (fold @0x800032dc: s0=cursor sp+240+24k, a5=8k, s6=8n,
  s3=frame ptr, s5=closure ptr, StoreRepr of foldStore k under φf') +
  `callParamFoldCarrier` (the storeChainList index family).
- §2 `callParamFoldSeam_of` — per-param seam = staging ≫ env_define contract
  (envDefContract boundary pair) ≫ back-edge.
- §3 `callClosureEntrySplice` — THE COMPOSITION: ONE spliceFold
  (.step hDispatchStage (env_new_spec …) (.tail …)) with env_new REAL at
  parentSpec := some cd.env, ret := 0x800032c0 (the Gen bridge's concrete
  link); tail cases the zero-param blez bypass vs the storeChainList fold at
  the ∃-bound φf' (bound by hEnvNewToFold, fresh frame ↦ env_new_post's p);
  conclusion = the amended entryBase Triple (SegEntry@dispatch → BodyHandoff).
  Named premises = hDispatchStage (frame-tracking dispatch+head span),
  hEnvNewToFold, hFoldSeam family, hFoldToHandoff (value_null ≫ body entry),
  hNoParams.
- §4 `CallRetShape` + `callClosureRet_of_status` — the a_6 status split for the
  ret field (.normal via 0x80003954 / .ret via retCopy row), residual-strength
  gap cross-referenced.
- §5 `callClosureGeom_of` — the 3-field assembly into the residual slot.
- §6 red-zone mechanics: `callClosureEnvNewSpill_logInRZ` (sd a5,0(sp)),
  `callClosureArgSpill_logInRZ` (sd s7,1016(sp)),
  `callClosureValueNull_log_nil` (log = [] by rfl), and
  `callClosureEnvNewSeamFrame` = rzSeamFrame_of_run FIRING on the env_new
  staging seam (AInv + Env_newLoaded survival one-shot).

Verify: `lake env lean` green 1.5s; axioms of every theorem ⊆
{propext, Classical.choice, Quot.sound}; `scripts/check_discipline.py` OK.

## Wiring lines (coordinator; NOT applied)

Vsa.lean (after `import Vsa.Sim.rows.CallClosureRow`):
  import Vsa.Sim.rows.CallClosureSplice
check_all axiom list additions:
  Vsa.Sim.callClosureEntrySplice        # rows/CallClosureSplice (entry route: ONE spliceFold, env_new_spec threaded real, storeChainList fold at the ∃-bound φf')
  Vsa.Sim.callClosureRet_of_status      # rows/CallClosureSplice (a_6 status split for the amended ret field)
  Vsa.Sim.callClosureGeom_of            # rows/CallClosureSplice (3-field Geom assembly)
  Vsa.Sim.callClosureEnvNewSeamFrame    # rows/CallClosureSplice (rzSeamFrame firing on the env_new staging seam)
(CallClosureRow entries unchanged — eval_callClosure_row / _fills_ already listed.)

## Named residuals remaining (each doc'd at its premise)

1. hDispatchStage — 0x80003254..0x800032bc incl. the frame-tracking spills
   (s7/s5/s3) + env_new_pre side conditions (Env_newLoaded, M.AInv,
   φf cd.env = par.toNat from StoreRepr, non-exhaustion selector). The Gen
   callClosureEnvNewCallBridge covers its jal tail.
2. hEnvNewToFold — 0x800032c0..0x800032d8 + φf'-binding (fresh frame at
   env_new_post's p; StoreRepr extension = the storeRepr-allocFrame
   marshalling).
3. hFoldSeam — per-param staging (0x800032dc..0x80003308, writes s0) ≫
   envDefContract instance ≫ back-edge (0x80003314..0x8000331c); Gen
   callClosureEnvDefineCallBridge covers the jal tail.
4. hFoldToHandoff / hNoParams — 0x80003320..0x8000333c via value_null_spec +
   Gen callClosureValueNullCallBridge; binds the body ghost g'.
5. CallRetShape's two routes — classification span (status→a0 ABI gap) +
   Gen callClosureRetCopyRow / the 0x80003954 .normal span; BLOCKED at full
   strength on the motive-family stack-window clause (ledger
   body-ih-no-caller-frame-slots).
6. emptyBypass — shared entry splice to the bgtz check + the .normal arm.
