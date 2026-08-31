# Observations ledger — missing general facts, workarounds, abstraction candidates

Append-only channel from working agents to the coordinator. APPEND AN ENTRY THE
MOMENT YOU NOTICE, not in your final report — entries on disk survive agent
stalls; final reports don't. The coordinator harvests entries into the task
board; harvested entries get a `> harvested: <task#/decision>` line, and stay
here as the record.

Entry format (append at the END of this file):

```
## <date> <short-slug> (<task or agent context>)
- missing: <the general fact/lemma/abstraction that does not exist>
- workaround: <what you did instead, or NONE if you stopped>
- cost: <what the workaround cost — lines, decides, per-site work — and who
  else will pay it again>
- proposal: <the abstraction that would eliminate the class, named concretely>
```

Rules: one entry per observation; never edit others' entries; a workaround
noted here is NOT thereby sanctioned — if the discipline gate or brief forbids
it, still stop and report instead.

---

## 2026-08-31 keys-decides-per-seg (bridgeOfSeg, task #28)
- missing: keys (evalBlocks bs L).regs ⊆ keysG L ++ wrChain bs (fold subset lemma)
- workaround: caller-supplied hKeysOut/hRaOut per concrete seg, by decide
- cost: 2 extra decides per bridge row, forever, until the lemma lands
- proposal: one structural-induction subset lemma; hypotheses become derivable
> harvested: task #31

## 2026-08-31 site-batteries-beside-tabled-region (env_define bridges, task #6)
- missing: nothing — the decode table already covered the region 106/106
- workaround: four hand prefix-run site batteries were written beside it
- cost: ~58 lines + ~10 site lemmas per prefix, four times
- proposal: discipline gate (landed: check_all stage a4) + EnvDefSeg model
> harvested: tasks #27/#28, gate committed f2670f5

## 2026-08-31 stmt-amendment-three-holes (StmtDispatchClose trichotomy close)
- missing: the three spec-completeness holes needed landed-def amendments to
  discharge; C-faithfulness verdicts: (1) top-level abrupt (interp.c:333-361)
  = runtime error for ALL of ret/brk/cont (each `return 1;` → exit 70), so
  `status ≠ .normal → BigStepErr` is exact; (2) closure with unresolved addr
  = spec artifact, faithful fix is a `CallErr.badClosure` leaf; (3) for-init
  abrupt (interp.c:308) = C SWALLOWS the status (return value discarded, loop
  proceeds), so the C-faithful fix is a SEMANTICS change to `ExecInit`, NOT an
  error — `ForInitAbruptErrs` (which demanded `ExecErr`) is therefore FALSE as
  stated and is removed, not discharged.
- workaround: NONE (authorized statement amendment). Amendments: `ExecSeqErr.abruptHead`
  (new leaf, top-level+general abrupt sequence head → error), `CallErr.badClosure`
  (new leaf), and GENERALIZE `ExecInit.some` (+ `ExecInitCost.some`) to accept any
  terminating status (swallow).
- cost: generalizing `ExecInit.some` changes the recursor minor-premise TYPE
  (gains a `status` binder) at every hand-written `.rec` scaffold: `Cost.lean`
  (`c_isome`), `TermCaseBundle`/`TermSimAssembly`/`TermSimClose` (`hInitSome`),
  and `Derive.lean` (drop the `.normal` guard). Adding `ExecSeqErr.abruptHead`
  + `CallErr.badClosure` extends every `cases`/pattern over those error
  inductives (StmtDispatchClose progress split + any Sim error-routing that
  cases on `ExecSeqErr`/`CallErr` — audited: Sim consumers use them as opaque
  hypotheses / positive witnesses, not by `cases`, so they only GAIN a
  constructor they never destruct).
- proposal: none new — this is a one-time statement fix (precedent: the
  Trichotomy falsity finding in StmtDispatch.lean). Machine side of the new
  top-level-abrupt error route = a NAMED residual premise in the routing shape
  (modeled on the other 42 exit-70 premises), no new machine proof built.

## 2026-08-31 branch-terminated-seg-no-bridge (EnvDefBridges4, items 1/2/3)
- missing: NONE — no `bridgeOfSegBr` variant was needed after all.
- workaround: none; `segToTriple` (over `segEval_sound`) ALREADY carries a
  branch/jump-terminated seg: `BlockTerm`'s `TKind` (`br`/`j`) is in-model and
  `evalBlocksPC` computes the terminator target as the end PC. So the append-head
  (`beqz;bnez`), append-store (`j`), and update-store (fall-through) bridges are
  plain `segToTriple` rows landing the computed machine post — NO `bridgeOfSeg`.
  `bridgeOfSeg` is only for the `jal`-SEAM (call) case, where the terminator is a
  call that links x1 and is deliberately out of `TKind`.
- cost: none — this is the cheap path (each row ~35 lines, 1 kernel decide).
- proposal: document in the abstraction table that `segToTriple` = the tool for
  ANY straight-line-or-branch/jump-terminated span; `bridgeOfSeg` only for
  call-seam (`jal`) spans. Avoids a future agent factoring a needless
  `bridgeOfSegBr`.

## 2026-08-31 memcpy-word-route-not-framed-not-reflected (EnvDefBridges4, item 4)
- missing: an ABI-frame-carrying variant of the memcpy WORD route
  (`dispatch_to_word ≫ word_loop_spec ≫ epilogue_{notail,tail}_spec`), so
  `envDefAppendContract`'s `hrouteCbyte` (byte-route restriction) could be dropped.
- workaround: NONE — stopped. Item 4 as specified (use
  `FrameMeta.abiFrame_of_wrChain`/`memFrame_of_chain` over the epilogue's
  *reflected chain*) is not applicable: (a) the memcpy word-path epilogue
  (`MemcpySpec4.epilogue_notail_spec`/`epilogue_tail_spec`, `word_loop_spec`) is
  NOT in reflected/`#derive_case` form — it is entirely legacy `site_*`/`NotWrittenW`
  ghost style; (b) its conclusion carries NO `bblocks_sound_bt`-shaped register-frame
  clause at all (the ABI frame is threaded through the `∃ g'` ghost and RESET at the
  `NotWrittenW → NotWrittenB` crossover), so there is no frame clause for
  `abiFrame_of_wrChain` to collapse; (c) the tail variant contains a byte-tail LOOP.
  Making the word route framed therefore requires FIRST seg-ifying the whole word
  path + its tail loop into reflected form AND restating the memcpy word specs to
  expose an ABI-frame clause — a memcpy-file statement change, out of scope for a
  ~35-line env_define bridge, and the current word specs ARE the ghost-reset
  approach the "no ghost re-run" rule bans re-doing by hand.
- cost: `hrouteCbyte` stays a parameter of `envDefAppendContract`. For the actual
  env_define call (`memcpy(copy, name, len+1)`, dst = fresh malloc block) it is the
  HONEST routing side-condition (byte route taken iff src/dst mutually misaligned or
  len+1 < 8), not a gratuitous restriction — so the cost is only the residual word-copy
  case, not correctness.
- proposal: reflect the memcpy word path (`#derive_case` the epilogue straight-line
  blocks + `loopFromBody` the tail loop), restate `epilogue_*_spec`/`word_loop_spec`
  to expose the `bblocks_sound_framed` register+footprint frame, then
  `memcpy_spec_framed_word` falls out of `abiFrame_of_wrChain`/`memFrame_of_chain`
  exactly like the byte route's `memcpy_spec_framed_byte`. Sized as a memcpy-file
  task, not an env_define bridge.
> harvested: task #15 rescoped to the reflect-first proposal

## 2026-08-31 hole1-not-execseqerr-rule (StmtDispatchClose, correction)
- missing: Hole 1's docstring suggested "add an ExecSeqErr abrupt-head rule",
  but that is UNFAITHFUL: C's ST_BLOCK (interp.c:286) PROPAGATES an abrupt head
  (`return st`), it does NOT error — only interp_run (the top-level driver,
  interp.c:333) errors on abrupt. `ExecSeqErr` is the SAME relation for blocks
  and the top-level program, so a general abrupt-head ExecSeqErr rule would
  wrongly turn every `{ break; }` in a loop body into a runtime error.
- workaround: NONE — took the docstring's OTHER sanctioned option (line 79: "or
  a BigStepErr re-route"): amend `BigStepErr p` to the disjunction
  `ExecSeqErr initSt 0 0 p ∨ (∃ st' status, status ≠ .normal ∧ ExecSeq initSt 0
  0 p st' status)`. This is top-level-only, leaving ExecSeqErr's nested meaning
  intact. `TopLevelAbruptErrs` then closes by `Or.inr`.
- cost: the M5 machine error simulation (errorSimFull/stuck_of_bigStepErrFull/
  ErrFamily) takes `(h : BigStepErr p)`; it now cases on the disjunction and
  gains ONE new NAMED residual premise `hTopAbrupt` (the abrupt-top-level →
  exit-70 machine route), shaped exactly like the other 42 site residuals — no
  new machine proof built, per brief.
- proposal: none — one-time top-level statement fix.

## 2026-08-31 strarmresid-is-wholenode-evalih (StrArmChain, str-cmp arm)
- missing: `StrArmMachineResid op bres` (StrCmpBlockC) is DEFINED as the whole-node
  `EvalIH st d env (.binary op el er) st'' (.bool (bres sl sr))` — the ENTIRE arm
  (prologue `blockA_binaryArm` ≫ both operand recursions `blockB_binary` ≫ str seam
  ≫ sign tail ≫ `value_bool` box ≫ `blockD_v_rec`), the ~700-line `blockC_ge`-scale
  object. There is NO int-arm `blockC` for the str operands to clone: `blockC_ge`
  proves the INT path (both operands `.int`, kinds=2), whose prologue reads/spills
  int payloads; the str arm (kinds=3) has a DIFFERENT prologue+operand recursion and
  no landed `blockA_binaryArm`/`blockB_binary` for it. So `StrArmMachineResid` cannot
  be honestly discharged end-to-end without first building the str-operand prologue
  (out of scope; overlaps the concat-blocked `stringify` prologue in BinStrCells §b).
- workaround: NONE for the whole-node. What IS buildable+kernel-checked: the str-arm
  MACHINE TRANSPORT from the kind-check branch (0x80003628) through strcmp
  (`strcmp_full_spec`) + rejoin + sign tail (`sTail*Row`) + `value_bool` box — the
  exact analogue of `EvalEqNeFront.blockC_eqne_front` (which composes the eq/ne front
  seam over an `EqFrontData` bundle but ALSO leaves the outer `EvalIH` a residual).
  Delivered as `StrArmChain.lean`: span-1 seg (`strKindCheck`), span-2 bridge
  (`strcmpSeamBridge` via `bridgeOfSeg`+`jalStep_of_obs`), span-3 sign-tail rejoin
  facts, all composed into a front Triple over a `StrArmFrontData` bundle.
- cost: the whole-node `StrArmMachineResid` stays a NAMED residual exactly as it was;
  the four `strCmpCell_*_of` providers still consume it. This agent lands the machine
  spans + the front-transport combinator, shrinking the residual's UNBUILT surface to
  the str-operand prologue (`blockA_binaryArm`/`blockB_binary` at kind=3), not the
  strcmp seam / sign tail / box, which are now proved and composable.
- proposal: `StrArmFrontData` (post-prologue caller bundle: parked at 0x80003b0c with
  both operand `.str` reprs staged, strcmp region witnesses, box obligations) +
  `strArmFront` (the composed Triple) — the str sibling of `EqFrontData`/
  `blockC_eqne_front`. Then `StrArmMachineResid` = str-prologue ≫ `strArmFront`, with
  only the prologue left, mirroring how `evalEqNeSim` = eq-prologue ≫ blockC_eqne_front.

## 2026-08-31 badclosure-recursor-adds-43rd-site (M5 error-family re-thread)
- missing: the `stmt-amendment-three-holes` cost note claimed Sim error-family
  consumers "use `ExecSeqErr`/`CallErr` as opaque hypotheses, not by `cases`, so
  they only GAIN a constructor they never destruct" — WRONG for the recursor
  sites. `errorSim_of_sites` (ErrorSimFull.lean) is a literal `@ExecSeqErr.rec`
  application with all six motives constant `ErrHalts c`; adding the
  `CallErr.badClosure` leaf (inserted between `notCallable` and `arity`) SHIFTS
  the recursor's minor premises, so the rec application now demands a `badClosure`
  minor premise. Without it `hArity` lands in the `badClosure` slot → type
  mismatch at the `.rec` call. So the M5 error family gains a NEW named residual
  `hBadClosure` (the 43rd error site), NOT just the `hTopAbrupt` route.
- workaround: NONE needed beyond naming — `hBadClosure : ∀ (st) (d) (a) (vs),
  st.store.closures[a]? = none → ErrHalts c` is a plain named typed premise (the
  constant-motive minor premise for `badClosure`), same shape as the other 42
  site residuals, no machine proof. Threaded through `errorSim_of_sites` →
  `errorSimFull` → `stuck_of_bigStepErrFull` → {`stuckSimClosed`,
  `errFamily_of_sites`}, inserted right after `hNotCallable` to match the
  constructor order. Plus `hTopAbrupt : TopAbrupt p → ErrHalts c` (the top-level
  abrupt → exit-70 route) on the same theorems. Net M5 residual delta: 42 → 44
  named error routes (was: 42 + badClosure + topAbrupt).
- cost: every mirror of the recursor application (5 theorems across ErrorSim/
  ErrorSimFull/StuckSimClose/InterpSimBundle) gains 2 premises. Purely additive
  named premises; no proof obligation discharged here (the dangling-closure and
  top-level-abrupt machine routes are the honest exit-70 residuals, unreachable
  from a well-formed `initSt` but demanded by the arbitrary-config recursor).
- proposal: none — one-time consequence of the authorized `badClosure` leaf. The
  `stmt-amendment-three-holes` audit should have counted the explicit `.rec`
  sites; future inductive-leaf amendments must grep for `@<Rel>.rec` applications,
  not just `cases`/`rcases`.

## 2026-08-31 loadbearing-seg-register-readback (StrArmChain span-3 rejoin)
- missing: a `gholds_lookup`-companion that reads a register value off a
  load-bearing `#derive_case` seg outcome. `gholds_lookup L hregs (by rfl)`
  closes register projections for load-free segs (all sign-tail / cmpFixup /
  arithmetic rows), because `evalBlocks seg …` reduces to the reg pin under
  `rfl`. The MOMENT the seg body contains an `ld`/`lw`/`lbu`, `rfl` on
  `lookupG n (evalBlocks seg (init L lds)).regs = some v` gets STUCK: `runGM`
  threads `stepLdsM .ld lds = lds.tail` and `wvalM .ld (lds.headD [])` with
  symbolic `lds`, so the reg-map spine carries an un-reducible `bytesVal .ld …`
  cell (the dead loaded reg) that whnf refuses to skip. With
  `maxRecDepth` high this manifests as a NATIVE STACK OVERFLOW (SIGABRT), not a
  `rfl`-failed error — a nasty diagnosis trap.
- workaround: `rw [evalBlocks_regs]` then a hand `simp only [runGM, stepGM,
  wvalM, srcVal, lookupG, eraseG, <six `show (mkLine pc w).field = _ from rfl`
  field pins>, Nat.reduceEqDiff, if_true, if_false, Option.getD_some]` then
  finish the `+ sext 0#12` by `BitVec.add_zero`. ~10 lines per register read.
- cost: ~10 lines + 6 field-`rfl`s PER load-bearing register projection; every
  future rejoin/spill-reload seg row (any arm that reloads a spilled arg before
  using it) pays it again. The `mkLine.field` pins are per-word, so a wider
  load block multiplies them.
- proposal: `gholds_lookup_ld` (or extend `segToTriple`'s `hpost` marshalling):
  a lemma `lookupG n (runGM body L lds) = some v` given `n ∈ keysG L`, `n` not
  written by any `ld` in `body`, and the concrete `runGM`-over-ALU reduction —
  i.e. peel the loads structurally (à la `srcVal_runGM_ne` in SegFrameFactsAuto,
  which already peels a register unaffected by the body) and expose the ALU
  outcome. `srcVal_runGM_ne` is the closest existing brick; it peels but does
  not deliver the post-mv value. A `runGM`-load-peel readback would collapse the
  10-line hand simp to one application.

## 2026-08-31 chainfacts-branchguard-arith-overflow (StrArmChain span-1 kind-check)
- missing: `chain_facts … all_goals rfl` (the model idiom in `cmpFixupTail_facts`,
  `sTailLt_facts`) does NOT close a branch guard whose value is a NON-TRIVIAL
  reflected arithmetic. `cmpFixupTail`'s guards are `x12 ≠ 21/22/23` (pinned-int
  vs literal — cheap `rfl`). The str kind-check's guards are `x15 = x10 - 3 = 0`
  and `x16 - 3 = 0`: `rfl` must reduce the `addi`'s `sign_extend (0xffd = -3)` +
  64-bit subtraction through `runGM` with symbolic `lds`, which recurses to
  unbounded depth → NATIVE STACK OVERFLOW (SIGABRT) at `maxRecDepth 1000000`, NOT
  a bounded error. Predecessor's `all_goals rfl` was never actually built (the
  file only ever failed earlier on missing oleans), so this shipped latent.
- workaround: replace `all_goals rfl` with `all_goals (simp only [runGM, stepGM,
  wvalM, srcVal, guardB, <per-word `mkLine.field = _ from rfl` pins>,
  Nat.reduceEqDiff, if_true, if_false, Option.getD_some] <;> decide)` — the simp
  collapses each guard to a concrete `BitVec` compare, `decide` finishes. Lets
  `maxRecDepth` stay at the 8000 standard (no bump).
- cost: ~14 lines (8 field pins) once per kind-check-style facts row; any arm
  whose branch guard is a subtract/compare-against-computed (not a pinned literal)
  pays it. Diagnosis cost is the real tax: the SIGABRT gives no line number —
  found only by lowering `maxRecDepth` to force a located error + `trace_state`.
- proposal: teach `chain_facts`'s guard-closing tail to try the symbolic-reduce
  path (`simp only [runGM,stepGM,wvalM,srcVal,guardB,…] <;> decide`) as a fallback
  after `rfl`, driven by the seg's own per-word decode facts (it already has the
  `mkLine` field values from the `#derive_case` table). Would make both cheap and
  arith-heavy guards close with the same one-liner and never overflow.

## 2026-08-31 strArmFront-landed (StrArmChain str-cmp arm front transport)
- missing: N/A (deliverable note, not an obstruction) — `Vsa/Sim/rows/StrArmChain.lean`
  LANDS the str-cmp arm machine transport as the `blockC_eqne_front` analogue:
  span-1 kind-check (`strKindCheckRow`, `#derive_case`+`segToTriple`, branch-terminated),
  span-3 rejoin (`strRejoinRow`, `ld;mv;j`→0x800036a4), and the `strArmFront` combinator
  (`strcmp_full_spec` ≫ rejoin ≫ `SignTailLeg` ≫ `value_bool` box, pure `Steps.trans`).
  `strArmMachineResid_{of,lt,le,gt,ge}` factor `StrArmMachineResid` (StrCmpBlockC) as
  `StrArmPrologue ≫ strArmFront`, leaving ONLY the kind-3 str-operand prologue
  (blockA_binaryArm/blockB_binary — the same one that blocks BinStrCells §b concat).
- workaround: span-2 marshalling (`mv;mv;sd;jal strcmp`) is STAGED INTO the
  `StrArmFrontData` bundle (operands pre-placed in x10/x11, a2 spilled into mA, the jal
  seam collapsed into `strcmp_full_pre` with link=0x80003b1c=rejoin-entry) rather than
  built as a standalone `bridgeOfSeg`+`jalStep_of_obs`, mirroring how `EqFrontData` parks
  at the jal PC. The post-strcmp→rejoin register reconcile is the bundle's `hReconcile`
  named residual (a frame projection off `strcmp_post`, x2/x9 callee-saved) — the single
  honest connective gap, analogous to `EqFrontData.hsnapEval`/`hMemExtRet`.
- cost: the `hReconcile`/`hTokAtRejoin`/`hBox`/`hSignTail` bundle legs are named `Triple`
  premises the eventual live wiring must discharge (each a short frame/box reconcile).
- proposal: none needed here — matches the established front-residual pattern. When the
  kind-3 str-operand prologue (blockA/blockB) lands, `strArmMachineResid_of` closes the
  four `strCmpCell_*_of` cells (StrCmpBlockC) directly.

## 2026-08-31 anon-projection-towers (user-observed, session-wide pattern)
- missing: posts/entries stated as anonymous ∃/∧ towers force consumers into
  positional projection chains (hPostS.2.2.2.2.2.2.2.2.2) — fragile under
  reorder, elaboration-heavy, and agents burn turns counting conjuncts.
- workaround: agents navigated towers by hand across multiple fronts.
- cost: every consumer of every tower, repeatedly; mis-counts surface as
  opaque type errors.
- proposal: named-field `structure ... : Prop where` for all NEW posts/entries
  (FoundSt/GeomFacts/FrameCalc are the models); ONE named destructuring lemma
  beside each LANDED tower that must stay; enforce mechanically.
> harvested: gate rules R6/R7 + CLAUDE.md law 6 + table rows (153 legacy
> violators grandfathered at rule introduction)

## 2026-08-31 segreadback-mechanized (SegReadback.lean, T1.5)
- missing: N/A (deliverable note) — the two hand idioms from the two prior
  entries (`loadbearing-seg-register-readback`, `chainfacts-branchguard-arith-
  overflow`) are now MECHANIZED in `Vsa/Sim/SegReadback.lean`, axiom-clean, ~1.3s:
  (1) `seg_guard_close [pin,…]` — a standalone tactic = the exact working
  `simp only [runGM,stepGM,wvalM,srcVal,guardB,lookupG,eraseG,<caller pins>,
  Nat.reduceEqDiff,if_true,if_false,Option.getD_some] <;> decide`; call it in an
  `all_goals` after `chain_facts`, ADDITIVE (does not touch ChainFactsTac). Demo
  `gcDemo_facts` = strKindCheck's two arith guards, verified (probe: `chain_facts`
  alone genuinely leaves the 2 `guardB … = false` goals) at maxRecDepth 4000.
  (2) `gholds_lookup_ld` + `lookupG_runGM_snoc` — the load-bearing companion of
  `gholds_lookup`. `lookupG_runGM_snoc pre a L lds hstore n hrd` reads the value
  the seg's LAST writer `a` (`a.rd=n`, non-store) deposits as `wvalM a (runGM pre …)`,
  the leading loads peeled by the existing `srcVal_runGM_ne` (Fix 1a) — no fold
  reduction, no deep rfl. `gholds_lookup_ld L bs lds hregs hread` then lands
  `gprGet σ n = some v`. Demos `rbDemo_x11`/`rbDemo_gprGet` = strRejoin's
  `[ld x12,0(x2); mv x11,x10]` readback of x11, 6 lines vs the 10-line hand simp.
- workaround: none — bricks, not workarounds.
- cost: ZERO to callers now; each row calls one lemma/tactic. SegReadback imports
  SegFrameFactsAuto + ChainFactsTac + rows/StrCmpSignTail.
- proposal (follow-up, NOT done here): reseat the 3 live hand sites onto these —
  `StrArmChain.strKindCheck_facts` (→ seg_guard_close), `strRejoin_x11`/`_x9`
  (→ lookupG_runGM_snoc), owned by a sibling this session so NOT edited. Plus the
  SWEEP found 3 more hand-unfold sites of this class:
  `EntryHaltsSpans.lean:178` (`hlk`: lookupG 10 through a 2-block restoreChain —
  the mv copies a LOADED s5=a0v, so lookupG_runGM_snoc reaches the writer but the
  value is load-carried not source-peelable; needs a load-value variant),
  `EntryHaltsSpans.lean:162` + `ExitPathSpans.lean:219` (both `srcVal 1 (runGM …)`
  = restored-ra PC readbacks feeding `chainEndPC`, a srcVal-not-lookupG shape that
  `srcval_peel` already covers — reseat onto `srcval_peel`). Total remaining
  hand-unfold sites of this class after this file: 6 (3 in StrArmChain +
  2 EntryHaltsSpans + 1 ExitPathSpans), all reseatable, none blocking.

## 2026-08-31 widen-meta-unification (T1.2 parametric exit-widener)
- missing (now built): ONE parametric exit-widener replacing the 5-widener zoo
  (`LeafWiden`/`ExecLeafWiden`/`ExecRecWiden`/`EvalRecWiden` + the
  `evalExit_rebase`/`blockD_v_phic` epilogue). Built `Vsa/Sim/WidenMeta.lean`:
  named-field `structure Widen (ExitP : Config → Prop) N A φf φc nf nc st' m0
  (foot : Nat → Prop)` with fields `pres` (MemExtends) + `surv` (∃ φf' φc',
  PhiExtends ∧ PhiExtends ∧ survival-at-foot). Relation-agnostic (ExitP fully
  applied). `foot` = FrameMeta-style footprint predicate (`stackFoot SL`,
  `retslotFoot SL aRet`). Two family bridges `evalExitD_of_widen`/
  `execExitD_of_widen` + `Widen.footMono` (foot ⊇ stackFoot ⇒ discharges the
  [SL.lo,SL.hi)-fixed *ExitD). Elab ~1s, axiom-clean.
- LANDED: 4 of the 5 wideners re-landed as THIN ALIASES — `LeafWiden`
  (EvalLeafD), `ExecLeafWiden` (ExecCaseGeom), `ExecRecWiden` (ExecRecRows),
  `EvalRecWiden` (CallRows) are now `abbrev`s = `Widen … (stackFoot SL)`; their
  `*_of_*` bridges are one-line corollaries of the family bridges. Consumers
  (TermRouting/EvalVarRow/EvalVarBridge/ExecRouting/CallResidProviders/
  CallArmEpilogue) UNCHANGED and green (they carry the widener opaquely).
- GOTCHA: a `structure … : Prop` cannot carry the φ witnesses as DATA fields
  (`φfExt : Addr → Nat`) — large-elim restriction means those projections aren't
  generated. Bind the φ pair inside the `surv` field's `∃` instead (also matches
  the *ExitD existential shape exactly, so bridges are trivial `⟨…⟩`).
- PAYOFF: the 5th widener (`evalExit_rebase`/`blockD_v_phic`) is NOT an
  ExitD-producer — it is the pure `PhiExtends.mono/.trans` φ-rebasing PRIMITIVE
  the survival witnesses use, orthogonal to the widening reassembly; left as-is
  (statement unchanged, green). The step-6b `hSVarNull`/`hSRetNull` "blocked by
  identity-φ ExecLeafWiden" note was already stale (both use ExecRecWiden). I
  built the missing `execVarNullSimD` + `exec_varNull_row` (ExecRecRows) — the
  genuine non-identity-φ statement leaf (`Store.define` grows the frame count),
  discharged by the parametric widener's `∃ φf' φc'`; the surfaced open residual
  is only the `value_null`+`env_define` body glue (unchanged from
  `execVarDeclNullSim`), NOT the widener. Wiring: `import Vsa.Sim.WidenMeta` into
  EvalLeafD/CallRows/ExecCaseGeom; `import Vsa.Sim.ExecVarNull` into ExecRecRows.

## 2026-08-31 termbundles-loop-measures-and-envdefine (T1.4 TermBundles assembly target)
- missing: (1) a SHAPE-generic loop back-edge termination measure the four loop
  premises (`hSWhileLoop`/`hFlLoop`/`hArgsCons`/`hSeqCons*`) share — `loopFromBody`
  consumes one per shape but there is no landed generic carrier; (2) a landed
  COMPOSED `env_define` post-predicate to type `TermCallees.envDefine` against
  (`envDefContract` is a `Triple P Q`-combinator theorem, not a named contract
  struct like `MallocContract`/`ReallocOps`).
- workaround: (1) typed the four `*Measure` fields as opaque named `Prop` slots
  in `TermGuards` (law-2 named typed premise + doc), SHAPE fixed by field name,
  witness deferred to the per-shape `loopFromBody` argument; (2) typed
  `TermCallees.envDefine` as the general `∀ {P Q}, Triple P Q → Triple P Q`
  combinator shape (matches `envDefContract`'s form; instantiated at M6 by the
  composed append≫grow≫dispatch join from EnvDefCompose).
- cost: the `Prop` loop-measure slots carry no structure, so the capstone can only
  discharge them per loop shape (4 witnesses), not once; the `envDefine` combinator
  typing means the eventual wiring must thread `envDefContract`'s P/Q through the
  three consuming premises (`hAssign`/`hSVarInit`/`hCallClosure`) rather than
  projecting one field.
- proposal: (1) a `LoopMeasure`/`loopFromBody`-facing carrier record (one field per
  loop SHAPE with the well-founded relation) so `TermGuards` holds structured
  measures; (2) promote the composed `env_define` behaviour to a named
  `EnvDefineContract` struct (like `MallocContract`) in EnvDefCompose so
  `TermCallees.envDefine` is a projectable field, matching the malloc/realloc form.

## 2026-08-31 imagegeom-sufficient-for-termshared (T1.4 TermBundles)
- missing: nothing — `ImageGeom` (TermImageGeom.lean) already carries exactly the
  two `decide`-provable G facts (`stack_ram`, `stack_win`) that `TermShared.geom`
  needs; the sp-dependent facts (`stackBounds`) are correctly site-parameters via
  `ImageGeom.stackBounds`, NOT struct fields (matches the record's own doc: "Static
  facts common to the current EvalE rows ... site-dependent facts remain explicit").
- workaround: NONE — reused `ImageGeom N A SL` verbatim as the `geom` field; no
  additive extension required.
- cost: none.
- proposal: keep `ImageGeom` as-is; if a future row needs a NEW whole-program
  (non-sp) constant, add it additively to `ImageGeom` (one field) — do NOT widen
  `TermShared` directly.

## 2026-08-31 armpostgeomv-two-hidden-axes (T1.1 fan-out)
- missing: the survey's "byte-identical modulo opTok/slot/value-form" understated
  two axes: (1) the value-image region is a literal PAIR (viLo/viHi) appearing in
  two fields, not a single predicate swap; (2) tableStk's offset is per-op
  (4 add/sub/cmp, 12 mul, 20 div/mod).
- workaround: none — both became parameters of ArmPostGeomV (the right fix).
- cost: none paid; a naive bool-copy would have been WRONG silently.
- proposal: none new; lesson = when a survey claims "identical modulo X", the
  fan-out agent should diff two instances mechanically before templating.
> harvested: ArmPostGeomV landed (7/8 ops; EqResid correctly resisted — its
> collapse point is EqNeBoxPre, documented in-file)

## 2026-08-31 if-branch-dispatch-ih (ExecDispatchRows, dispatch/loop rows task)
- missing: `ExecIH → ExecDispatchIH` bridge for the `if` re-dispatch branch. The
  recursor hands the then/else branch sub-derivation as `mExecS = ExecIH`
  (full-entry, through the prologue at 0x80003fe0); `execIfTrueSim`/`execIfFalseSim`
  consume it as `ExecDispatchIH` (post-prologue re-entry at 0x80004014, shared frame).
- workaround: carried `ExecDispatchIH` as a NAMED field `hBranch` of
  `IfTrueGeom`/`IfFalseGeom`; the recursor's `ExecIH` is threaded but unused by the sim.
- cost: the branch-from-dispatch simulation is duplicated per if-arm as a residual;
  it cannot be supplied from the recursor IH.
- proposal: a `dispatchIH_of_execIH` lemma is FALSE in general (re-dispatch skips the
  prologue). The honest fix is either (a) `execPrologue`-strip: a metatheorem that the
  branch's `ExecDispatchIH` follows from its `ExecIH` composed with the fact that the
  re-dispatch state IS a valid `ExecEntry`-minus-prologue — i.e. prove
  `ExecDispatchReady → ∃ pre-prologue ExecEntry` is UNREACHABLE and instead land the
  branch sim natively at `ExecDispatchReady`; or (b) a second motive `mExecS_dispatch`
  in the recursor giving branches the `ExecDispatchIH` shape directly.

## 2026-08-31 scaffold-motive-independent-pq (ExecDispatchRows, hInitNone/hFcNone/hEsNone)
- missing: the `mExecInit`/`mForCond`/`mExecStep` recursor motives quantify the
  entry PC `p` and exit PC `q` INDEPENDENTLY (`TermSimAssembly.lean:114-152`), so the
  honest identity rows `LoopScaffoldClose.segIdentity{,_of_eq}` (which need `p = q`)
  cannot discharge `hInitNone`/`hFcNone`/`hEsNone`. Machine-checked: `segIdentity`
  yields `SegExit … st p`, the motive demands `SegExit … st q`, `q ≠ p`.
- workaround: NONE — stopped; these rows are blocked at the current motive shape.
- cost: hInitNone/hFcNone/hEsNone (3 scaffold no-op premises) + hInitSome (needs a real
  ExecIH→Seg control bridge) remain open; hFl*/hEs*/hFc-some are the actual machine
  segments (not identity), also blocked on the Seg-motive control-flow.
- proposal: amend the four Seg-skeleton motives to relation-specific PCs with `p = q`
  for the no-op relations (the `LoopScaffoldClose.lean` module doc already flags this
  as the required motive repair), OR give them a single shared PC parameter. Once
  `p = q`, `execInitNone_samePC`/`forCondNone_samePC`/`execStepNone_samePC` close them
  immediately (already landed, awaiting the motive fix).

## 2026-08-31 store-init-locus-off-interp_run-path (EntrySeams, StoreInitSeam)
- missing: no fact ties `Loaded interpRunLayout p c` (machine at `interp_run` entry
  `0x800043ec`, `a0`/`a1` = AST base/len) to `StoreRepr … initSt.store` at the loop
  head. The store (single global frame + 3 natives) is built by `interp_init`
  (`0x80004308`: `env_new` @ `0x80004324` + `env_define`×3 @ `0x80004364/9c/d4`), which
  `main` calls at `0x800045b4` — a call that has ALREADY RETURNED before the
  `interp_run`-entry `Loaded` config. So the store-init representation is genuinely
  OFF the `interp_run` prologue path: decoding `[0x800043ec, 0x8000448c)` (spills, jal
  setjmp, loop-bound setup) never touches the store. `interpRunLayout.atInterpRun`
  pins only PC + a0/a1, not the store.
- workaround: NONE for the store fact itself — named it precisely as the ONE residual
  `InterpInitStoreRepr` (PC spans decoded in its doc) and reduced `StoreInitSeam` to
  it via `storeInitSeam_of_initRepr`. The epilogue side WAS tightened: 4 of 5
  `EpilogueFrame` control conjuncts (GoodState/tick/PC/output) are direct `SegExit`
  projections (`epilogueControl_of_segExit`), reseating the seam on the smaller
  `EpilogueSpill` (spill ChainFacts + s5=0 + Interp_runLoaded + ExitTailChain0).
- cost: whoever closes `InterpInitStoreRepr` must either (a) strengthen
  `interpRunLayout.atInterpRun`/`Loaded` to carry the store-init representation as a
  precondition (statement change — the store IS established before interp_run, so this
  is faithful), or (b) run a main-prologue machine span that invokes `interp_init`'s
  env_new/env_define specs (all landed: EnvNewSpec.env_new_spec, EnvDefSpec*). Option
  (a) is cheap and honest; the AST→store correspondence is `interp_init`'s postcondition.
- proposal: an `InterpInitSpec` (interp_init's total-correctness spec: `env_new` +
  3× `env_define` over `ProgramRepr` → `StoreRepr initSt.store` in the interp struct),
  composed via `callSeg` at main's `jal interp_init` @ `0x800045b4`; then strengthen
  `atInterpRun` to assert the store is represented at the `a0` interp base, so `Loaded`
  discharges `InterpInitStoreRepr` directly.

## 2026-08-31 framerepr-update-no-append-analogue (env_define marshal, bridgeStore/hUpdate)
- missing: no landed forward `FrameRepr`-UPDATE reconstruction (the update-path
  analogue of `EnvDefBridges3.frameRepr_append`). `frameRepr_append` reconstructs the
  name-ABSENT/append frame `⟨parent, vars ++ [(x,v)]⟩` from readback facts; the
  name-PRESENT/UPDATE case (`env_define_update_post`'s `if f.vars.any … then map …`
  branch — slot `hit`'s value replaced by `v`, all others survive) has NO such lemma.
- workaround: `frameRepr_of_updateStore` (EnvDefMarshal) takes the update `FrameRepr`
  as a named premise `hFrameUpdate` (dispatch-supplied), same as `bridgeStore`'s
  `hFrameAppend` — but for append the dispatch has `frameRepr_append` to discharge it,
  for update it has NOTHING landed, so `hFrameUpdate` is an unbacked named residual.
- cost: whoever closes `hUpdate` for real must first build `frameRepr_update` (the
  map-branch reconstruction: OLD slots ≠ hit survive their name/value readback, slot
  hit reads back the new `v`, count/cap/pointers unchanged) — ~1 lemma mirroring
  `frameRepr_append`'s structure but over `List.map`/`getElem_map` instead of `++`.
- proposal: `frameRepr_update (m N φf φc e f nameStr v hit …) : FrameRepr m N φf φc e
  ⟨f.parent, f.vars.map (fun p => if p.1==nameStr then (nameStr,v) else p)⟩`, beside
  `frameRepr_append` in EnvDefBridges3, consuming the same header/slot readback shape.
  Note the `if any then map else append` join in `env_define_update_post` means the
  UPDATE arm needs the map branch; `hit < length ∧ vars[hit].1 = nameStr` gives `any`.

## 2026-08-31 env-define-store-seg-post-shape (EnvDefMarshal, marshalling boundary)
- missing: the seg rows (`appendStoreRow`/`appendHeadRow`/`updateStoreRow`,
  EnvDefBridges4) land `c.σ.mem = writeLog m0 (evalBlocks seg init).log`, but the
  readback facts `frameRepr_append` needs (`read32/read64/CString/ValueRepr` over that
  computed memory) have NO landed reduction from the write-log — they are re-supplied
  as caller data. So the seg row's computed memory and the representation predicates
  are only tied at the call site, by hand, per-field.
- workaround: took the whole `FrameRepr`/`EnvDefFrame` over `c.σ.mem` as named premises
  (`hFrameAppend`/`hCarry`), marshalled to the epilogue-entry carrier by `rfl`-level
  destructuring. NONE of the write-log→readback reduction is done here.
- cost: the dispatch/caller pays a per-field readback (`getElem_writeMap8_disjoint`
  towers, like `namesToValsPrefix_run`'s env->vals-survives-env->names-store) to turn
  the 5-store `writeLog` into the `read32/read64` header + slot facts, for EACH of the
  append/update/head store blocks.
- proposal: a `writeLogReadback` calculus over `evalBlocks seg init` (project
  `read32/read64` at a target address off the canonical seg log by
  disjointness/last-writer, à la `FrameCalc.pin8`/`pin4`/`slot` but delivering
  `read32 (writeLog …) a = some w` directly), so the store-block posts feed
  `frameRepr_append` mechanically instead of by hand-threaded byte pins.

## 2026-08-31 triple-profunctor-calculus (TripleCat task)
- missing: a first-class name for the `Triple` consequence rule as a profunctor
  action (`dimap`), for entailment (`Ent`) as its acting preorder, and for an
  adapter PAIR as one iso (`PredIso`). Every `_wired`/`_ofBundle` conseq adapter
  and every `X_of_Y`+`Y_of_X` pair was hand-rolling `Triple.conseq …` /
  `⟨…⟩ + ⟨…⟩` with the identity-side entailment (`fun _ h => h`) written out.
- workaround: NONE — built `Vsa/Sim/TripleCat.lean` (Ent/refl/trans, Triple.dimap
  /lmap/rmap, PredIso/symm/trans/transportPre/transportPost) + demos in
  `Vsa/Sim/TripleCatDemos.lean` re-expressing `callSegConseq`,
  `bridgeNamesToVals_wired`, and the `LtResid↔ArmPostGeomV` pair. Both files
  green + axiom-clean, elab <1.5s (dominated by heavy olean loads, not the new
  decls). Discipline: OK.
- cost: the compression is real but MODEST for the residual-iso pairs — the two
  33-field `⟨…⟩` projections are irreducible (they physically shuffle fields);
  PredIso only saves the caller a `conseq` at the USE site, not the pair's body.
  The clean win is on conseq-shaped `_wired` adapters: `Triple.lmap hEntry core`
  drops the `(fun _ h => h)` postcondition-identity noise and names the
  profunctor direction. KEY FINDING: because `Triple` is a `Prop`, ALL the
  interchange/associativity/functoriality laws hold DEFINITIONALLY by proof
  irrelevance (`Subsingleton.elim`) — there is nothing to prove and nothing for
  simp to rewrite between equal proofs; the value is purely the directional
  CONSTRUCTORS (`dimap`, `transportPre`), not equational normalization.
- proposal: gate rule — new consequence adapters (`*_wired`, `*_ofBundle`, any
  `Triple.conseq` application whose postcondition side is `fun _ h => h` or whose
  pre side is `fun _ h => h`) SHOULD be written as `Triple.dimap`/`lmap`/`rmap`;
  new predicate adapter PAIRS SHOULD be a single `PredIso` with the two
  directions in its fields + `transportPre`/`transportPost` at use sites. A
  COUNT>N discipline rule catching bare `Triple.conseq _ (fun _ h => h)` /
  `(fun _ h => h) _` outside TripleCat.lean would enforce it once the calculus is
  wired into Vsa.lean.

---

## 2026-08-31 interp-init-println-route (InterpInit, InterpInitStoreRepr close)
- missing: a framed WORD-route memcpy spec (the task's "#15") + a layout fact
  deciding `(src ^^^ dst) % 8` for `interp_init`'s statics-vs-malloc-block copies.
  `env_define`'s memcpy copies `len+1` bytes; `env_define_append_spec`'s byte-route
  premise `hrouteCbyte = (src^^^dst)%8≠0 ∨ nMemcpy<8` covers print(6) and assert(7)
  by `nMemcpy<8`, but println is `len+1 = 8` so `nMemcpy<8` is FALSE — the println
  cell is gated ONLY on mutual misalignment `(src^^^dst)%8≠0`, a concrete layout
  fact not derivable at the composition level (src = static "println"@0x80019540,
  dst = fresh malloc'd 8-byte block).
- workaround: NONE — named it as the precise per-define premise (`hRoutePrintln`
  in the InterpInit doc; the println `hDefPrintln` seam carries it). Did not
  fabricate a route. print/assert cells are byte-route unconditional.
- cost: until a word-route framed memcpy spec lands OR the M6 layout pins the
  static/heap alignment, EVERY 8-byte-name native binding (here just "println",
  but any future len-7 native) carries this named misalignment obligation.
- proposal: `memcpy_spec_framed_word` (word-route analogue of
  `memcpy_spec_framed_byte`, MemcpySpecFramed) + an `ImageStatics` alignment lemma
  giving `(N.staticName ^^^ mallocBlock) % 8` from the linker layout; then the
  println cell discharges without the named premise.

## 2026-08-31 interp-init-store-carrier (InterpInit, env_new ≫ define×3 compose)
- missing: a reusable STORE-ACCUMULATOR seam for a sequence of store-mutating
  callee splices (env_new then N×env_define) — a `Config→Prop` carrying
  `StoreRepr <store-so-far>` + control pins, advanced one `Store.define` per splice.
  `SegEntry` is store-parametric but bundles budget/frame/mem fields the pure
  store-threading composition doesn't need; there was no lean carrier for "the
  store built so far at PC k".
- workaround: NONE (built the named structure) — landed `InitSeg` (5-field
  named structure, GoodState/tick/PC/StoreRepr/OutRepr) + `interpInitStore_compose`
  (pure `Triple.seq` chain of env_new + 3 define seams). The 3-fold `Store.define`
  = `initSt.store` holds by `rfl` (`initStore_eq_initSt`, axiom-free); each
  intermediate append verified by `rfl` (append path, name absent).
- cost: `InitSeg` is bespoke to interp_init's store shape; a second store-building
  caller (e.g. a runtime that binds more globals, or nested-scope init) would want
  the same carrier generalized over the store-advance function.
- proposal: `StoreSeg N A SL φf φc store pc` + a `storeChain` combinator
  (`Triple` fold over a list of `(Store.define-step, seam)` pairs) so any
  env_new/env_define call sequence composes by naming the per-step contracts only.

## 2026-08-31 scaffold-motive-independent-pq-RESOLVED (TermSimAssembly, scaffold motive amendment)
- missing: the four loop-scaffold motives (mExecInit/mForCond/mExecStep/mForLoop)
  quantified entry PC `p` and exit PC `q` INDEPENDENTLY, so the `.none` premises
  (hInitNone/hFcNone/hEsNone) were unfillable — segIdentity yields exit=entry but
  the motive demanded arbitrary `q`.
- workaround: NONE (statement-change, authorized). AMENDED the four motive defs to
  a single identity-PC parameter `p` (entry PC = exit PC = `p`). The 50-premise
  lists in TermSimAssembly/TermSimClose/TermCaseBundle are UNCHANGED (they only ever
  reference the fully-applied motive `mExecInit st d env none st (proof)`; no p/q is
  visible in any premise), so only the four defs changed. ExecDispatchRows'
  exec_forStart_row consumes the mExecInit/mForLoop IHs as ignored (`_`) opaque
  values — stable. Downstream all green + axiom-clean.
- cost: zero re-threading of consumers (the p/q was fully hidden inside the motive
  bodies); the `.some` companions now state an honest identity-PC span at `p` (their
  named residuals hInitSome_resid/hFcSome_resid/hEsSome_resid in rows/ScaffoldRows.lean).
- proposal: LANDED — rows/ScaffoldRows.lean (hInitNone_row/hFcNone_row/hEsNone_row
  via LoopScaffoldClose.segIdentity, slot-verified against TermCases fields). The
  `.some` bridges (straight-line init/cond/step machine seg collapsing to loop PC `p`)
  remain the only open scaffold obligation — a #derive_case seg / callSeg per arm.

---

## 2026-08-31 storeseg-storechain (StoreSeg/exec_varInit/eval_assign, task: env_define capstone fan-out)
- missing: (1) a store-generic carrier + chain combinator generalizing InterpInit's
  bespoke `InitSeg`/`interpInitStore_compose`; (2) an `env_set` top-level Triple / an
  `evalAssignSim` machine derivation; (3) an `env_define`→`SubExecReturn` varInit-arm
  call-linkage bridge.
- workaround: (1) LANDED `Vsa/Sim/StoreSeg.lean` — `StoreSeg` (store/PC/out-parametric
  named-field carrier) + `storeChain1/3/List` (fold of `Triple.seq` over env-call
  seams); re-expressed `interpInitStore_compose` through it non-invasively
  (`interpInitStore_compose_viaStoreSeg`, InitSeg↔StoreSeg via `Ent` dimap, R8-clean).
  (2)/(3) NAMED oracles, NOT built: `eval_assign_row` (rows/EvalAssignRow.lean) threads
  the whole assign arm as `AssignArmSpec` (the EvalVarRow "row now, arm spec later"
  precedent); `exec_varInit_row` (rows/ExecVarInitRow.lean) threads the env_define
  callee inside `ExecVarInitGeom.hGlue`.
- cost: the two arm-spec oracles must each be discharged once by a callSeg-style splice
  (assign: arg-setup ≫ jal eval_expr ≫ jal env_set = Store.set? ≫ HIT-return @0x80003448;
  varInit: same shape ≫ jal env_define ≫ li a0,0 @0x80004118). env_set's in-place update
  IS the `hUpdate_wired` shape (EnvDefMarshal), env_define's append IS
  `env_define_append_spec` — both landed spec-side; only the arm call-linkage is left.
- proposal: a shared `envCallArmBridge` (callSeg over the env_set/env_define contract
  into the recursive-arm SubExecReturn/EvalExitD carrier) would discharge BOTH oracles
  and Call.closure's params-fold from one template; StoreSeg's `storeChainList` is the
  spec-side skeleton it targets.

## 2026-08-31 callclosure-row (eval_callClosure_row, hCallClosure crux, task: last recursor premise)
- missing: (1) the stale `Vsa/Sim/EvalCallClosure.lean` no longer type-checks — the
  store-size ghost refactor (git 9d853eb "nf/nc threaded through the full M4 stack")
  added `nf nc` size args to `SegExit`/`CallExitP`, so `callClosureSim`'s
  `CallExitP g N A SL φf φc st' m0` (8 args, missing `nf nc`) is now an
  application-type-mismatch. That file is NOT imported into Vsa.lean/check_all, so the
  breakage was invisible. (2) no landed `env_new_spec`→SegEntry or `env_define`-fold→
  SegEntry seam for the closure arm (the machine spans between the fval-kind dispatch,
  `jal env_new`, the per-param `env_define`s, and `callBodyLoopPC`).
- workaround: built `Vsa/Sim/rows/CallClosureRow.lean` fresh, size-correct: a
  `CallClosureGeom` named-field structure with the two straight-line seams
  (`entryBase` dispatch→callBodyLoopPC in the FULL bound store, `ret`
  callBodyRetPC→callJoinPC WITH the boundSt.sizes→st.store.sizes ghost bridge) +
  the `storeChainList`-shaped `entryFold` params-fold field. `callClosureSim`
  re-landed via `DeriveCallSeg.callSeg` (prefix ≫ body-IH ≫ return); the body IH is
  the recursor's `a_5`/`mExecSeq` motive at callBodyLoopPC/callBodyRetPC (dLeft-1/
  aLeft-1), passed through unconditionally. `closureParamsFold` witnesses the fold
  IS `StoreSeg.storeChainList` over `foldStore … k` (`foldStore_full` = take-length).
  Slot-verified against the VERBATIM hCallClosure premise
  (`eval_callClosure_row_fills_hCallClosure`). Green+axiom-clean ~1.5s.
- cost: the stale `EvalCallClosure.lean` should be DELETED or reseated (its
  `callClosureSim`/`ClosureEntrySpec`/`ClosureRetSpec` are superseded by the
  size-correct ones in the row). The two `CallClosureGeom` seams remain NAMED
  oracles: `entryBase` = closure-arm decode ≫ `env_new_spec` (EnvNewSpec) ≫ the
  per-param `env_define` fold (envDefContract); `ret` = return-block reflection
  (value_null / 24-byte memcpy) + the size-ghost revert. Each is a callSeg-style
  splice — the SAME `envCallArmBridge` template the assign/varInit oracles want.
- proposal: the ledger's `envCallArmBridge` (callSeg over env_new/env_define into the
  recursive SegEntry carrier) discharges `entryBase`+`entryFold` here AND the
  assign/varInit oracles from one template; `storeChainList`+`foldStore` are the
  spec-side skeleton it targets (now instantiated). Separately: reseat or delete the
  stale EvalCallClosure.lean so the M4 stack has ONE size-correct closure crux.

## 2026-08-31 term-assembly-capstone (TermAssembly.lean, the assembly capstone)
- missing: 10 recursor premises have NO landed `_row` theorem — the for-loop
  scaffold `.some`/body/loop cases (`hInitSome`/`hFcSome`/`hEsSome`/`hFlCondFalse`
  /`hFlBodyBreak`/`hFlBodyRet`/`hFlLoop`) and the `ExecSeq` cases
  (`hSeqNil`/`hSeqConsNormal`/`hSeqConsAbrupt`). ScaffoldRows has `_resid` DEFs
  (statement-only) for the three `.some` cases; the other 7 have neither a row nor
  a residual def. `hSeqNil` is essentially LANDED (`ExecSimCommon.execSeqNil`,
  seg-identity) — only a `_row` wrapper is missing. These are the honest tail of
  the "49/50 rows landed" claim: 40 `_row` theorems exist + hCallClosure crux =
  41; the remaining 9 (10 minus hSeqNil) are genuine whole-premise gaps carried as
  named `TermResiduals` fields typed VERBATIM as the `TermCases` field.
- workaround: carried all 10 as whole-premise `TermResiduals` fields (law-2 named
  typed premises, doc comment names supplier). No assertion; the fill uses them
  directly (definitional match for the ScaffoldRows `_resid` defs).
- cost: NONE beyond the field count; the capstone is agnostic to whether a field
  is a row-residual or a whole premise. Each becomes a discharge task.
- proposal: `hSeqNil_row` (trivial `execSeqNil` wrap) + `execSeqLoop`-based
  `hSeqConsNormal_row`/`hSeqConsAbrupt_row` + `execForLoopSim`-based for-loop rows;
  once these land, swap the 10 fields for row applications (mechanical, like the
  other 40). Tracked as the `TermResiduals` for-loop/seq field cluster.

## 2026-08-31 divstep-corr-machine-gated (TermAssembly.lean hdivFam design)
- missing: no spec-only concrete `Corr` for `DivFamily` — confirmed by
  `DivFamily.lean`'s verdict AND now machine-checked here: `divStep_vacuous`
  proves `DivStep (fun _ … => False)` (both arms vacuous), so the ONLY genuine gap
  is the entry `Corr c initSt 0 0 p`, which is machine-side (`Loaded L p c`). The
  progress arm is the M4 exec_stmt Triples' "≥1 step, still corresponds" skeleton.
- workaround: kept the `DivCorrFamily` reduction (`R.hDivCorr`) as the single named
  divergence residual; added `divStep_vacuous` to record the obligation is
  well-formed and localize the gap to entry-not-progress.
- cost: NONE — the reduction was already the honest design in DivFamily.lean.
- proposal: a `divCorr` = ExecEntry/SegEntry correspondence with `DivStep` proved
  from the shared M4 case Triples; this is the same machine layer that discharges
  `hterm`, so it lands WITH the term-arm rows, not separately.
