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

## 2026-08-31 seqfor-motive-rows (rows/SeqForRows.lean, task: TermResiduals seq+for cluster)
- missing: a landed adapter from the loop ENGINES' machine contracts to the
  recursor MOTIVE contracts. `execSeqLoop` speaks `ExecSeqEntry → ExecSeqExit`
  (sp/r/minstret, NO depth/arena budget); `execForLoopBody` speaks
  `ExecEntry → ExecExit` at the child scope. The `mExecSeq`/`mForLoop` motives
  demand `SegEntry → SegExit` (depth_budget/arena_budget, NO sp/r). None of these
  entry/exit structures is DEFEQ (field sets differ), so the motive Triple is NOT
  a free `rfl`/`.1`-map of the engine output — a real ABI+budget reconciliation
  span is missing. ALSO: `mExecSeq … []` is NOT the trivial `execSeqNil` wrap the
  prior ledger claimed — the motive's entry PC `p` and exit PC `q` are INDEPENDENT
  (block/interp_run need p=execSeqLoopPC≠q=execSeqContPC), so hSeqNil is a genuine
  p→q empty-seq hop, not an identity segment (only `mForLoop` was amended to
  identity-PC; `mExecSeq` legitimately keeps independent p,q).
- workaround: landed `Vsa/Sim/rows/SeqForRows.lean` — 7 `_row` theorems
  (hSeqNil_row/hSeqConsAbrupt_row/hSeqConsNormal_row + hFl{CondFalse,BodyBreak,
  BodyRet,Loop}_row) each routing to a NAMED residual (SeqNilResid/
  SeqConsAbruptResid/SeqConsNormalResid + ONE shared ForResid, WhileGeom
  precedent). The cons/loop residuals take the recursor sub-IHs (head ExecIH,
  tail mExecSeq Triple; mForCond/mExecS/mExecStep/mForLoop) as EXPLICIT inputs so
  the residual carries ONLY the machine span, not the sub-derivation
  correspondences. Green + axiom-clean {propext, Classical.choice, Quot.sound},
  elab ~2s. Two slot-check `example`s type-verify all 7 against the VERBATIM
  TermCaseBundle.TermCases field types; a wiring check confirms `{ B with hSeqNil
  := hSeqNil_row R.hSeqNil ; … }` record-update type-checks.
- cost: the residual still carries the whole motive Triple (the ABI+budget
  adapter + the ExecForStep/ExecSeqStep body oracle live inside it). Discharging
  each *Resid needs (1) a SegEntry↔ExecSeqEntry / SegEntry↔ExecEntry adapter and
  (2) the body oracle, which is blocked on exprRepr_agreeP (loop-fanout.md) —
  shared with the already-landed block/while engines, NOT new per-row work. The
  row layer is the mechanical fill point; the semantic gap is unchanged in size.
- proposal: a `segOfExecSeq` / `segOfExecEntry` reconciliation lemma (drop
  sp/r, synthesize depth_budget/arena_budget from the SegEntry's own fields) would
  let the *Resid bodies delegate to execSeqLoop/execForLoopBody once the body
  oracle lands — collapsing all 7 residuals to the shared oracle + ONE adapter.

## 2026-08-31 genseg-arm-compiler (arm-compiler task)
- missing: a single generator that turns an *arm description* (span + pins +
  terminator) into the whole seg-layer row (`#derive_case` seg + `L` + `Post` +
  `segToTriple` row). The seg/row idiom was hand-transcribed per span across
  `EnvDefSeg`/`EnvDefBridges4`/`StrArmChain`/`StrCmpSignTail` — each author
  re-decodes the branch terminator record (`⟨pc,word,4 LE bytes,.br op taken?,
  rs1,rs2,imm13,imm21,imm12⟩`) and re-writes the identical `segToTriple`
  ceremony by hand.
- workaround: BUILT the compiler — `scripts/genseg/lib.py` (shared plumbing:
  disasm parse, terminator decode, decode-index tabledness check, Lean
  emit/TSV/TOML) + `scripts/genseg.py` (the arm compiler). Regenerated 3 LANDED
  hand segs (mallocArg/appendHead/appendStore) — output is byte-identical to the
  hand version modulo names + line-wrapping; all green + axiom-clean.
- cost: NONE going forward — a new straight-line/br/j span is now ~15 TSV/TOML
  lines → ~60 generated lines, vs ~120+ hand `site_*` lines the legacy idiom
  would pay. Everyone building an M4/M5 machine-span oracle pays the hand cost
  otherwise.
- proposal: `scripts/genseg.py` (LANDED). Follow-ups: (1) the `jal` (Shape-D)
  path emits a NAMED `hjalSeam : JalStep …` residual + a `bridgeOfSeg` skeleton
  — the callee `site_*` obs glue stays region-specific, so the jal row is not
  yet fully closed by the compiler (honest: the body run + ABI frame ARE free,
  only the one call-seam obs is left). (2) retarget the 5 existing generators
  onto `genseg/lib.py`'s `Emitter`/`load_tsv`/`le_bytes` (safe, mechanical) —
  deferred to avoid touching landed generators mid-campaign.

## 2026-08-31 envcallbridge-defineprint-untabled (EnvCallBridge demo (a), genseg define("print") arm)
- missing: the interp_init define("print") arg-setup span (0x80004328..0x80004360)
  has SIX body words NOT on the block-reflection decode table: sw@0x80004328
  (02912423), addi@0x80004338 (20458593), sb@0x80004344 (0e040023), auipc@0x80004348
  (fffff797), addi@0x8000434c (b8c78793), mv@0x80004350 (00010613). So `genseg` on
  this TOML (scripts/arms/interpInitDefinePrint.toml, written + committed) HALTS at
  the decode-index gate ("NOT ALL WORDS TABLED"), before even the jal seam. The jal
  word ef8fe0ef is also untabled (the expected region-specific call-seam residual).
- workaround: threaded the demo's `hPre` (arg-setup prefix ≫ jal env_define) as a
  NAMED genseg-shaped `Triple` premise (exactly how InterpInit threads `hDefPrint`),
  and instantiated `envDefineArmBridge` over it — the template demo is complete and
  green; only the machine derivation of that ONE seg row is blocked on decode-table
  coverage. NOT fabricated.
- cost: every InterpInit define seam + any arg-setup seg over this 0x80004xxx region
  pays the same untabled-words wall until the six words (+ the jal) are added to
  scripts/decode_index.tsv and the corresponding DecodeTable batches. That is a
  decode-batch rebuild (per memory: DecodeTable = ~80% of build CPU), out of scope
  for the template task and gated by the elab budget.
- proposal: a targeted decode-index extension for the interp_init init region
  (six store/addi/auipc/mv words), OR route these arg-setup segs through a
  lighter store-only reflection path; until then the InterpInit define seams stay
  named genseg-row residuals the template consumes (which is the honest split).

## 2026-08-31 m5-error-hsites-coalesce (gen_m5_error_routing fix + ErrShared/hsite classes)
- missing: an arm-context → `JalErrPre` projection that could DISCHARGE the 42
  `errFamily_of_sites` `hsite` residuals. `JalErrPre g inp m0 <pc> <bytes> c`
  pins `c` to the error `jal`'s PC with `x10=inp`, `mem=m0` (runtime_error/longjmp
  images), ghost `g` preserved, tick<2, and the 4 decode bytes present. NO landed
  arm row establishes a config parked at any error `jal`: the 50 arm rows post the
  SUCCESS path; the error branch (spill `sd s3..s7` ≫ `auipc/addi` msg-ptr ≫ `mv
  a0,s2` ≫ `jal runtime_error`) is a different span the rows never run. So the
  hsites are irreducibly the M4 caller-linkage residual — not provable unconditionally
  (JalErrPre is false for a `c` not at that jal).
- workaround: COALESCED not closed. The 42 hsite types depend ONLY on the PC (+S),
  not the premise body → they collapse to 19 distinct classes (= the 19 `errSite_<pc>`
  Triples). Landed `Vsa/Sim/rows/ErrorRoutingClasses.lean` (generated): `ErrSiteLinks S`
  = 19 `hlink_<pc>` fields; `errFamilyClosed_ofClasses` feeds each of the 42 route
  slots the shared per-PC field (pure identity projection) + the 2 passthroughs.
  Axiom-clean. Reduces the error-side supplier's work 42 → 19 NAMED links. 0 of 43
  closed (none dischargeable from existing rows), 19 classes named (was 42).
- cost: the 19 `hlink_<pc>` are still open — each needs a `#derive_case` prefix seg
  over its error-branch spill run (ending `JalErrPre`) composed with the arm's
  error-branch entry context. The arm rows would first have to expose an error-branch
  entry post (a config at the spill-prefix head with `g`/`inp`/`m0` staged); today they
  don't. Whoever supplies `hErrFam` pays 19 seg derivations + 19 arm-entry glues.
- proposal: add an error-branch-entry post to each arm row (or a shared `ArmErrEntry`
  geom like ArmPostGeom for the success path), then a `hlink_of_armErrEntry` family:
  one `#derive_case` spill-prefix seg per PC (19), marshalled to `JalErrPre` exactly
  as `jalStep_to_runtimeError` consumes it. That closes the 19 classes mechanically.

## 2026-08-31 envcallbridge-template-LANDED (EnvCallBridge.lean + Demos, task: the ONE env-call arm template)
- missing: the ~8 env-call arm seams (4 InterpInit defines, AssignArmSpec's env_set,
  hSVarInit's hGlue, CallClosureGeom's entryFold) each hand-composed "prefix ≫ callee
  contract ≫ FrameRepr-post → StoreSeg marshalling" — no single template.
- workaround: NONE (built the template). LANDED `Vsa/Sim/EnvCallBridge.lean`:
  `envCallArmBridge` (= hPre ≫ hCallee ≫ rmap hMarshal, pure Triple.seq/rmap) +
  `StoreDefineAdvance` (the marshalling core, a named-field structure lifting
  EnvDefMarshal's per-frame FrameRepr readback to the whole-store StoreRepr advance;
  `Store.define a` mutates only frame `a` + leaves closures, so the advance = mutated
  frame's FrameRepr + others survive + injectivity/arena preserved) + its
  `toStoreRepr` assembler + `storeSeg_advance_define` (the marshalling Ent) + three
  flavor wrappers (`envDefineArmBridge`/`envNewArmBridge`... actually envDefine +
  envSet; env_new is the empty-frame define special case). All green+axiom-clean ~1.4s.
  Demos `Vsa/Sim/EnvCallBridgeDemos.lean`: discharged TWO InterpInit seams
  (interpInitStore_compose's hDefPrint + hDefAssert) through envDefineArmBridge,
  reindexed StoreSeg→InitSeg by the landed storeSeg_ent_initSeg Ent (R8 rmap), each
  ~30 lines, differing ONLY in (store,x,v,pc) data. Shared readback factored ONCE as
  `NativeDefinePins`. Green+axiom-clean ~1.2s.
- cost: remaining per-seam residual through the template = the THREE named premises
  (hPre = genseg arg-setup+jal row [blocked on decode-table coverage for the 0x80004xxx
  init region, see envcallbridge-defineprint-untabled]; hCallee = the landed contract
  [env_define_append_spec done; env_set/env_new contracts likewise landed]; hPins =
  the StoreDefineAdvance readback [caller's frameRepr_append data]). Once genseg's
  region words are tabled, hPre falls out of the compiler; the other two are already
  spec-side. Estimate: each of the remaining ~6 seams is ~30 lines of instantiation +
  its own hPins data, sharing NativeDefinePins for the native defines.
- proposal: LANDED — envCallArmBridge IS the ledger's requested template; wire into
  Vsa.lean after `import Vsa.Sim.StoreSeg` (line 471): `import Vsa.Sim.EnvCallBridge`
  then `import Vsa.Sim.EnvCallBridgeDemos`. Fan-out: instantiate for the env_set assign
  seam + the closure params-fold (storeChainList carrier) next.

## 2026-08-31 errlink-forall-shape-obstruction (close hlink_<pc> error-routing classes)
- missing: the 19 `ErrSiteLinks.hlink_<pc>` fields have type `∀ c : Config,
  JalErrPre S.g S.inp S.m0 <pc> <bytes> c` — a UNIVERSAL over all configs, which
  is machine-checked FALSE (`Vsa/Sim/rows/ErrLinkObstruction.lean :
  jalErrPre_forall_false`, axiom-clean ~1s: a config with `tick := 2` violates
  JalErrPre's `tick < 2` conjunct). The genseg/arm machinery (bridgeOfSeg,
  #derive_case+segToTriple) produces `Triple SitePre (JalErrPre …)` = the
  implication `∀ c, SitePre c → …`, a DIFFERENT shape that cannot inhabit a bare
  `∀ c, JalErrPre … c`. So NO seg/arm/TOML can close these fields as stated.
- root cause: `route_h*` (ErrorRouting.lean, GENERATED by gen_m5_error_routing.py)
  DISCARDS every spec-level error-derivation premise (`fun c _ _ … =>`) and feeds
  `errRow` an UNCONDITIONAL `hsite : ∀ c, JalErrPre … c` applied at arbitrary `c`.
  The correct residual is `SitePre`-conditioned: "the spec error derivation +
  the M4 arm sim for this arm ⟹ this reachable `c` is parked at the jal", i.e.
  a `Triple`/reachability, NOT an unconditional universal. The generator
  over-weakened the premise into an unprovable shape.
- workaround: NONE. Landed the machine-checked obstruction instead of a seg that
  cannot type-check into the field. The error-branch span IS genseg-shaped
  (e.g. negType/ret 0x800034e4: `mv a0,s2 ≫ li a4,0 ≫ auipc/addi msg-ptr ≫
  sd s3..s7 ≫ [fallthrough @jal]`; erow_demo already #derive_cases the sd s3..s7
  sub-span) and would end with a FALLTHROUGH terminator AT the jal PC
  (JalErrPre = state at the jal, seg ends before executing it) — but the target
  type is wrong, so building it is futile until the generator changes.
- cost: all 19 classes (42 premises) blocked identically; any future agent asked
  to "close hlink_<pc>" pays the same dead end. No landed arm-sim post exposes
  an error-branch-entry pin (checked EvalNegSim*/EvalBinSim*): none pin PC to the
  error edge 0x800034c0; the success-path blockA_k/ArmEntryK dispatch state is the
  natural SitePre but is not carried to the guard-failure edge by any row.
- proposal: change `gen_m5_error_routing.py` (and ErrorRoutingClasses' emit_classes)
  so each `hlink_<pc>` is `Triple <BranchEntryPre_<arm>> (JalErrPre …)` (supplied
  by a genseg error-branch arm) AND `route_h*` derives `SitePre c` from the
  retained spec premises + the arm sim (stop discarding them). Then errRow's
  `hsite : SitePre c` is met by real reachability, not a false universal. This is
  a routing-generator statement change (out of the seg-building lane); until it
  lands, the classes are genuinely unclosable.

## 2026-08-31 genseg-jal-stub-typebug (AssignArmSpec/CallClosure seams, task genseg-first)
- missing: genseg's `emit_jal_row` (`scripts/genseg.py`) emits a `<name>Run`
  theorem whose `JalStep` application has the WRONG argument order/types:
  `JalStep (evalBlocksPC …) callee_pc (span_end+4) (writeLog …)` but the real
  sig is `JalStep (calleeEntry link : BitVec 64) (σp : MState) (ip up : Nat)`.
  It passes the seg-post PC as `calleeEntry`, `callee_pc` as `link`, and a
  `BitVec 64` (`span_end+4`) where an `MState` is expected — type error. The
  body is also just `trivial : True`, so it proves nothing load-bearing.
- workaround: rewrote `emit_jal_row` to emit a REAL `bridgeOfSeg`-based row
  (`<name>Bridge`) modelled on `EnvDefSeg.capComputeSeg_run`: the seg run + ABI
  frame are FREE via `bridgeOfSeg`, and the region-specific jal seam is a single
  NAMED residual `hjalSeam : ∀ σ' i' u', … → JalStep calleeEntry link σ' i' u'`
  (the callee `site_*` obs the caller threads). The row's conclusion is the
  landed `∃ σ2 i2, Steps … ∧ … ∧ PC = calleeEntry ∧ x1 = link ∧ …` — the actual
  bridge post, not `True`.
- cost: the buggy stub had shipped for `interpInitDefinePrint.toml` (sibling's,
  never generated to a compiling file) and would have bitten every jal span
  (AssignArmSpec entry/stage, CallClosure entryBase/ret). One emitter fix clears
  the whole class.
- proposal: DONE in-lane (emitter rewrite). Remaining genuine residual per jal
  span = the `hjalSeam` `JalStep` (needs the callee `site_<pc>_*` lemma), which
  is correctly a NAMED premise, not fabricated.

## 2026-08-31 callclosure-entrybase-abi (CallClosureGeom.entryBase, task 2)
- missing: a bridge combinator for a jal-terminated span that WRITES ABI
  callee-saved registers (the entryBase base seam 0x80003254..0x800032bc does
  `mv s7,a1` / `mv s5,a4` / `sd s5,1032(sp)` / `sd s3,1048(sp)` — deliberate
  callee-saved spills). `bridgeOfSeg` requires `WrChainAvoidAbi bs` (so the ABI
  frame is FREE across the bridge); this span legitimately fails it, and also the
  ChainOK decide fails on the 5-block guard chain.
- workaround: NONE for the base seam via bridgeOfSeg. Landed the genseg TOML
  (scripts/arms/callClosureEntryBase.toml) as the decoded record but did not ship
  a compiling row — the tool is wrong-shape for an ABI-mutating span.
- cost: entryBase cannot be a bridgeOfSeg row; every closure/fn-arm prologue that
  spills callee-saved regs before its first jal hits this (the fn-arm alloc, the
  call-arm dispatch too). The CallClosureGeom.entryBase field stays a NAMED
  residual, discharged by a frame-TRACKING bridge, not the frame-free one.
- proposal: a `bridgeOfSegFramed` variant that, instead of asserting the ABI
  frame survives, THREADS the seg's write-log ABI-register updates into the post
  (the seg already computes `.regs`; expose the callee-saved deltas as part of
  the post rather than requiring WrChainAvoidAbi). Alternatively split entryBase
  at the last callee-saved write so the jal-adjacent tail IS frame-free.

## 2026-08-31 errlink-forall-shape-fix (corrected error-routing residual shape LANDED)
- resolves: errlink-forall-shape-obstruction (above). The refuted universal
  `∀ c, JalErrPre S … <pc> <bytes> c` is REPLACED by the `SitePre`-conditioned
  reachability the errRow proof actually requires.
- root requirement (from errRow's proof): `errRow … (SitePre := P) (T : Triple P
  (RuntimeErrorAt …)) c (hsite : P c)`. `errFamily_of_sites` binds `c` at the TOP
  LEVEL (`intro p c _ herr`) and passes `(hVarUndef c) …`, so each premise must
  yield `ErrHalts c` for the ENTRY config `c` from spec-derivation data only — no
  machine facts. Hence the honest `SitePre := ReachJal S … <pc> … := ∃ c', Steps c
  c' ∧ JalErrPre … c'` ("`c` RUNS to the jal"), with `T := Triple.seq
  (reachJal_triple …) (errSite_<pc> …)`.
- landed: `Vsa/Sim/ErrorReach.lean` (ReachJal + reachJal_triple, green, axiom-clean).
  Generator `scripts/gen_m5_error_routing.py` route emission KEEPS the spec binders
  (`fun c a1 … ak =>`), takes `hsite : ∀ c <binders>, <hyps> → ReachJal … c`, and
  routes through new `errRow_reach` combinator (emitted after ErrShared). Regenerated
  `rows/ErrorRouting.lean` (2.1s) + `rows/ErrorRoutingClasses.lean` axiom-clean;
  generator idempotent (diff-clean 2nd run). `ErrSiteLinks` now bundles the 42
  CONDITIONED links (one per routed premise) — the 42→19 PC coalescing was an
  ARTIFACT of the false universal (types depended only on PC because it dropped spec
  context) and does not survive honest conditioning; names `ErrSiteLinks`/
  `errFamilyClosed_ofClasses` kept, types corrected.
- consumers re-threaded: `TermAssembly.errFamily_ofShared` 43 hsite premises →
  conditioned shape (green 30s, axiom-clean; `interpSim_of_residuals` still clean).
  `TermResiduals.hErrFam` is a plain `ErrFamily L` field — UNCHANGED (only its doc).
  `InterpSimBundle.errFamily_of_sites`/`ErrorSimFull`/`StuckSimClose` untouched (the
  semantic premises were always fine). `ErrLinkObstruction.jalErrPre_forall_false`
  kept as HISTORICAL witness of the removed universal (still green, axiom-clean).
- inhabitability demo: `Vsa/Sim/rows/ErrorReachInhab.lean` (green, axiom-clean):
  `reachJal_of_armBranch` inhabits `ReachJal … c` from ANY error-branch `Triple
  ArmBranchPre (JalErrPre …)` + `ArmBranchPre c`; `negType_hsite_of_armBranch` builds
  the full hNegType route residual from such an arm branch and closes it through
  `route_hNegType`. Parametric in the arm seg (no landed arm-sim pins the error edge
  0x800034c0→0x800034e4 yet) — so the remaining genuine work is exactly: land those
  per-arm error-branch segs `Triple ArmBranchPre (JalErrPre … <pc> …)` + arm-linkage
  `spec-hyps → ArmBranchPre c`. That is now a WELL-TYPED target (was impossible).
- WIRING (agent cannot edit Vsa.lean/check_all.sh): add `import Vsa.Sim.ErrorReach`
  before Vsa.lean:359 and `import Vsa.Sim.rows.ErrorReachInhab` after Vsa.lean:361;
  regenerate top-level Vsa.olean. check_all THEOREMS: the existing errFamilyClosed/
  errFamilyClosed_ofClasses/jalErrPre_forall_false lines stay (types changed, names
  same); add `Vsa.Sim.errRow_reach`, `Vsa.Sim.reachJal_triple`,
  `Vsa.Sim.negType_hsite_of_armBranch` if desired; update the 621 comment (19-class
  coalescing → 42 conditioned links).

## 2026-08-31 strcmp-order-bridge-false (StrCmpOrderBridge close, StrCmpBlockC)
- missing: an HONEST order bridge between the C strcmp sign and Lean `String.<`.
  The LANDED `StrCmpOrderBridge op bres := ∀ (w:BitVec 64) (sl sr:String),
  (sTailWord op w != 0) = bres sl sr` is FALSE as demanded (`TermBundles.strCmp`
  requires it `∀ op bres`, and even per-op it quantifies `w` FREE of `sl sr`).
  Machine-checked falsity (`/tmp/falsity.lean`): for `op=.lt`, `bres=fun _ _=>true`,
  `w=0`: `sTailWordLt 0 = srli 0 0x3f = 0`, so LHS=false≠true. The bug: `w` (the
  strcmp return) is unconstrained; nothing ties it to `sl sr`.
- workaround: restated the bridge honestly in `Vsa/While/StringOrder.lean` as the
  order agreement tied through `strcmpSign w = strcmpSpecSign csa csb`
  (`sl=ofList csa`, `sr=ofList csb`, CStr ⇒ ASCII bytes<128 ⇒ byteVal=codepoint),
  proved it (List.Lex ↔ byte-lex, no UTF-8 multibyte since CStr is single-byte),
  and reseated the `StrCmpBlockC` def + `strCmpCell_*_of` legs onto it. The four
  `binOpSem` closures (.lt/.le/.gt/.ge) are the only instances needed; the
  `∀ bres` form in TermBundles.strCmp must narrow to those four (falsifiable
  otherwise).
- cost: statement change (like the Trichotomy spec bug precedent). Downstream
  `StrArmChain.hOrder` and `TermBundles.strCmp` slots must adopt the tied form.
- proposal: `StringOrder.lean` order-agreement lemmas
  `strcmpSpecSign_neg_iff_lt` / `_pos_iff_gt` / `_zero_iff_eq` as the reusable
  spec-layer bridge; the machine bridge instantiates them at
  `strcmpSign w = strcmpSpecSign`.

## 2026-08-31 bridgeOfSegFramed (avoid-set-generic frame core, both ABI-mutating fronts)
- resolves: callclosure-entrybase-abi (above) + supplies the error-branch spill
  seg for errlink-forall-shape-fix's `hlink`. LANDED `Vsa/Sim/BridgeSegFramed.lean`
  (green 9.8s, axiom-clean, discipline OK).
- design verdict (the two consumers DIFFER — this was the key finding):
  * (b) error-branch spill prefixes need NO framed variant AT ALL. The `sd s3..s7`
    are STORES: `wrChain = []`, so the raw seg frame preserves every register free;
    s3..s7 (=x19..x23) are exempt in NotWrittenJmp anyway. The ONLY real obligation
    is MEMORY: `Runtime_errorLoaded`/`LongjmpLoaded` must survive the stack stores
    (code ⊥ stack) — the footprint frame, avoid-set-independent. Neither spill
    tracking NOR an avoid-set swap; a plain `segEval_sound` + the raw frame clause
    (wrChain-guard vacuous) discharges the whole `JalErrPre` register+ghost side.
  * (a) closure entryBase (`mv s7,a1`@0x80003278 / `mv s5,a4`@0x80003290) genuinely
    needs delta EXPOSURE, not an avoid-set swap: s5,s7 are BOTH written AND
    callee-saved, so no predicate collapse recovers their frame. The seg ALREADY
    computes the reseated values in `out.regs` (`GHolds σ' out.regs`) — that IS the
    "spill tracking"; expose it, and assert the ABI frame only for the UNwritten
    callee-saveds via a restricted predicate.
- generic core (the exponentiating fix): FrameMeta's KERNEL (`abiPreserved_ne`) was
  never AbiPreserved-specific — it proves `(X==R)=false` from R,X on opposite sides
  of the SAME predicate. Factored the hardcoding out into ONE `P`-generic layer:
  `regAvoids_ne`/`WrChainAvoids P`/`noise_avoids`/`wrChain_avoids`/
  `frame_of_wrChain_avoids (P : Register → Bool)`. `AbiPreserved` re-expressed as a
  THIN instance (`wrChainAvoids_abi_eq : WrChainAvoids AbiPreserved = WrChainAvoidAbi`
  by rfl; `frame_of_wrChain_avoids_abi` recovers `abiFrame_of_wrChain`). Landed
  `bridgeOfSeg` path untouched.
- `bridgeOfSegFramed`: `bridgeOfSeg` with `WrChainAvoidAbi` REPLACED by
  (`hnoiseP` + `WrChainAvoids P` + `hPabi : P ⊆ AbiPreserved`), exposing
  `GHolds σ2 out.regs` (the reseat deltas) + the P-restricted callee-saved frame.
  The jal side reuses `JalStep`'s own AbiPreserved frame via `hPabi`.
- demos (both green, axiom ⊆ {propext, Classical.choice, Quot.sound}):
  * (a) `entryBaseReseat_framed` — the REAL `mv s7,a1` reseat (0x80003278, word
    0x00058b93) bridged at `P := AbiExceptS7`; post carries `s7 = a1v` (off
    out.regs) + ABI frame for all callee-saveds EXCEPT s7. env_new `JalStep` stays a
    NAMED per-callee residual. (Full 5-block entryBase adds a guard-branch ChainOK
    concern, orthogonal to the frame issue — that's a separate genseg branch-chain.)
  * (b) `spillNeg_toJalErr` + `negType_link_closed` — a REAL `#derive_case` on the
    hNegType spill prefix (0x800034d0..0x800034e0, five `sd`) → `Triple ArmBranchPre
    (JalErrPre S … 0x800034e4 …)` via `segEval_sound`, fed through
    `negType_hsite_of_armBranch`. ONE complete hNegType error link CLOSES to
    `ErrHalts c` modulo ONLY the arm-linkage `hlink` (the genuine M4 residual
    ErrorReachInhab already names) and `SpillNegArmPre`'s named `Runtime_errorLoaded
    S.m0` (code ⊥ stack, the honest geometric datum). No bridgeOfSegFramed used for
    (b) — precisely because (b) never needed frame tracking.
- fan-out: the P-generic core is the reusable frame collapse for ANY prologue that
  spills callee-saveds before its first jal (fn-arm alloc, call-arm dispatch);
  instantiate `P` at AbiPreserved-minus-written-set, read deltas off out.regs. The
  42 error spill prefixes are all the (b) shape — plain seg, no framed variant.
- wiring: add `import Vsa.Sim.BridgeSegFramed` to Vsa.lean; add
  `Vsa/Sim/BridgeSegFramed.lean` to scripts/check_all.sh (owner: do not edit those
  here per task constraint).

## 2026-08-31 strcmp-order-bridge-CLOSED (StrCmpOrderClose landed)
- missing: N/A — the order bridge is now PROVED.  `Vsa/While/StringOrder.lean`
  (`strcmpSpecSign_neg_iff_lex` / `_pos_iff_lex`, byte-lex ↔ List.Lex under the
  ASCII `AllNonzero` invariant, no UTF-8 multibyte since CStr is single-byte) +
  `Vsa/Sim/rows/StrCmpOrderClose.lean` (four fixup lemmas `{lt,gt,le,ge}_fix`
  reducing `sTailWord op w` to a signed test on `w`; `strCmpOrderBridge_{lt,le,gt,ge}`
  discharge the now-honest `StrCmpBlockC.StrCmpOrderBridge` for the four binOpSem
  closures).  All axiom-clean {propext, Classical.choice, Quot.sound}.
  `StrCmpBlockC.StrCmpOrderBridge` REDEFINED to the honest tied form (was false);
  `strCmpCell_*_of` (unused `_hOrder`) + `StrArmChain` still compile axiom-clean.
- REMAINING SEAM (statement change, out of this task's scope): `TermBundles.strCmp`
  demands `∀ op bres, StrCmpOrderBridge op bres` — with the honest def this is STILL
  FALSE for arbitrary `bres` (same falsity class: `bres = fun _ _ => true`, op=.lt,
  w=0, csa=csb=[] gives strcmpSign 0 = 0 = strcmpSpecSign [] [] but LHS false ≠ true).
  The field MUST narrow to the four binOpSem closures (supplied by
  `strCmpOrderBridge_{lt,le,gt,ge}`).  Likewise `StrArmChain.strArmFront` line ~371
  DISCARDS (`⟨_csa,_csb,x,-⟩`) the strcmp-post sign fact `strcmpSign x =
  strcmpSpecSign csa csb`; to CONSUME the honest bridge it must retain that fact and
  pass it (+ the operand-string `AllNonzero` from the CStr witnesses) into
  `hData.hOrder`.  That is a `StrArmFrontData.hOrder`/`strArmFront` restatement
  (BridgeSeg territory, sibling-owned) — flagged, not done here.
- proposal: narrow `TermGuards.strCmp` to the four cells; reshape
  `StrArmFrontData.hOrder` to the tied signature and thread the retained sign fact.

## 2026-08-31 errlink-familyB-x10-computed (error-site fan-out, task cont.)
- missing: a spill-prefix bridge whose entry does NOT pre-hold `x10 = inp`.
  The 8 Family-A error sites (jal preceded ONLY by `sd sN,off(sp)` stores,
  `wrChain=[]`) fan mechanically off the negType model: `ErrSpillCore.spillSeg_toJalErr`
  + the `gen_err_spill_rows.py` emitter close all 16 Family-A premises modulo the
  named `ErrArmLinks.link_*` residual.  The 11 Family-B sites (`0x80002e90`,
  `0x80002ebc`, `0x80003b9c`, `0x80003c10`, `0x80003c7c`, `0x80003cc4`, `0x80003d5c`,
  `0x80003da0`, `0x80003de8`, `0x80003e98`, `0x80003f58`) have a register-SETUP
  prefix ending `mv a0,s2; li a4,0; auipc a2; addi a2,a2,off` (msg-ptr + `a0:=s2`).
  So `wrChain ≠ []` AND — decisively — `x10 (=a0)` is SET by the seg (`mv a0,s2`),
  not preserved; `JalErrPre` demands `x10 = inp` as a POST, so the entry predicate
  cannot carry it as a preserved fact. Several also sit AFTER a `jal value_kind_name`
  call, so the true error-branch entry is a call-return, not a straight-line block.
- workaround: NONE for Family B — templated only the 8 pure-store sites; Family B
  emitted as named residual comments (report). `spillSeg_toJalErr`'s `wrChain=[]`
  hypothesis structurally rejects them (correct: it must, they write registers).
- cost: 11 PCs / 27 premises still need per-site bridges. Each needs the seg's
  computed `a0`-post read off `GHolds σ' out.regs` (the s2 value = inp), plus the
  arg-register writes (a2/a3/a4) shown ABI-irrelevant to `NotWrittenJmp` — a
  DIFFERENT marshalling than the pure-store carry.
- proposal: a `spillSetupSeg_toJalErr` variant whose `SpillSetupArmPre` drops the
  entry `x10=inp` and instead demands `lookupG 10 out.regs = some inp` (the seg
  computes it), reusing the `NotWrittenJmp`-noise frame for the g-frame only
  (a0/a2/a3/a4 are all noise-disjoint from the protected jmp set). The value_kind_name
  call-return sites additionally need a `callSeg` prefix. Family B is the honest
  next wave; Family A is closed by shape here.

## 2026-08-31 strarm-order-retie (str-order consumer seams, this task)
- missing: nothing new — `cstr_allNonzero` (CStr → AllNonzero) was the one glue
  lemma the proved bridges needed; landed in `Vsa/While/StringOrder.lean` (uses
  `char_ofNat_toNat`, axiom-clean). The over-general `StrArmFrontData.hOrder`
  (`∀ x, (sTailWord op x != 0) = bres`, `bres : Bool`) discarded the strcmp-post
  sign fact and was the same falsity shape the tied `StrCmpOrderBridge` already fixed.
- workaround: NONE — retied honestly. `StrArmFrontData` now carries `bres :
  String → String → Bool` + `hOrder : StrCmpOrderBridge op bres` (the proved
  bridge); `strArmFront` retains `⟨csa,csb,x,…,hsign⟩` from strcmp_post (no longer
  `⟨_,_,x,-⟩`), feeds `cstr_allNonzero` + `hsign` to `hOrder`, and rewrites the
  box's `.bool (sTailWord op x != 0)` to `.bool (bres sa sb)`. `TermGuards.strCmp`
  retyped from `∀ op bres` to the FOUR `strCmp{Lt,Le,Gt,Ge}` fields at the exact
  binOpSem closures (supplied by `strCmpOrderBridge_{lt,le,gt,ge}`).
- cost: none ongoing — the retype is additive; no consumer re-thread (TermAssembly
  references `TermGuards.strCmp` only in doc comments; TermResiduals' str fields are
  the `EvalIH` cells, not the bridge). check verified: StringOrder, StrArmChain,
  StrCmpBlockC, BinStrCells, TermBundles, TermAssembly all green + axiom-clean.
- proposal: none needed for these two seams. Item 3 (`StrArmPrologue`) remainder
  below.

## 2026-08-31 strarm-kind3-blockb (StrArmPrologue front residual, this task)
- missing: `blockB_binary` AT KIND 3 (the str-operand operand-recursion prologue).
  `blockA_binaryArm` is LANDED (entry → 0x800034e8, conditional on `BinArmExtras`)
  and `strKindCheckRow` is LANDED (kind-check span 0x80003628→0x80003b0c), but the
  two-operand recursion that lands `TwoSubReturn` with `.str` operands has no kind-3
  instance — only the int-arm blockB paths exist (same gap that blocks the concat
  cell, BinStrCells §b). So `StrArmPrologue` cannot be discharged end-to-end.
- workaround: named decomposition, NOT a full build. Landed: `StrSeamSpan2` (the
  SPAN-2 `mv a1,a7; mv a0,s3; sd a2,0(sp); jal strcmp` residual, `bridgeOfSeg`
  shape) + `strKindToStrcmp_seam` = `Triple.seq (strKindCheckRow mA) hSpan2` — a
  GENUINE composition making the landed kind-check row load-bearing (reaches the
  strcmp entry `strcmp_full_pre` from 0x80003628, residual = only the span-2 seam).
  Plus `StrArmToStrcmp`/`strArmPrologue_of_parts` naming the reach+marshal residual
  bracketing the LANDED `strArmFront` middle. All green + axiom-clean.
- cost: the genuine remainder is (i) kind-3 `blockB_binary` (~operand-recursion
  prologue, blockC_ge-scale), (ii) ONE `bridgeOfSeg` for `StrSeamSpan2` (store+jal,
  strcmp link 0x80003b1c), (iii) the box→EvalIH epilogue marshalling. The eq/ne arm
  will pay the same kind-3 blockB cost.
- proposal: a kind-generic `blockB_binary` (operand recursions parameterised by the
  operand-value kinds) so the str arm and the eq/ne/int arms share ONE operand
  prologue — the single abstraction that unblocks both `StrArmPrologue` and the
  concat cell.

## 2026-08-31 blockB-already-kind-generic (CORRECTS strarm-kind3-blockb, this task)
- missing: NOTHING new for the operand recursion — the prior entry's premise
  ("`blockB_binary` AT KIND 3 is missing") is WRONG.  Machine-checked reading of the
  LANDED statement (`Vsa/Sim/EvalBinSim.lean:242`): `blockB_binary`'s value params are
  `vl vr : Value` (no `.int`); its entry `ArmEntryK … (.binary op el er)` is kind-blind
  (`EvalSimCommon.lean`); the two operands are consumed via `EvalIH`/`SubEvalReturn`
  whose post is `ValueRepr … vsub` for ARBITRARY `vsub` (`EvalRecCommon.lean:205`); and
  its post `TwoSubReturn` (`EvalBinSim.lean:118`) stages the sub-values as GENERIC
  `ValueRepr … (sp-944) vr` / `… (sp-968) vl` (lines 149–150).  The ONLY int-flavoured
  thing is the `hVlSurv` PREMISE (left value survives the right sub-call) — a parameter,
  vacuous for int, non-vacuous for str; NOT baked-in int-ness.  So the (a)-vs-(b)
  verdict of this task is (b): the landed statement already lands a kind-blind
  `TwoSubReturn`; the str side needs a READBACK, not a new blockB.
- workaround: NONE — landed the correct cheap thing.  `Vsa/Sim/rows/BinStrReadback.lean`:
  `StrOperandsStaged` (named-field bundle: two operand kind tags = 3 + two CString
  pointers) + `strOperandsStaged_of_twoSubReturn` (the readback — a definitional
  projection: `ValueRepr … (.str s) = read32 = 3 ∧ ∃ p, read64 (a+8) = p ∧ p≠0 ∧
  CString`, consumed through ONE named `obtain` on the `TwoSubReturn` tower per R7).
  Plus `StrArmStageSpan` (the box→register op-dispatch staging span, NAMED residual) +
  `strReadbackToKindCheck` (readback ≫ staging ≫ LANDED `strKindCheckRow` ≫ named
  `StrSeamSpan2` → reaches `strcmp_full_pre`).  All green + axiom-clean (~clean {propext,
  Classical.choice, Quot.sound}).
- cost: the genuine remainder shrinks to: (i) `StrArmStageSpan` — the op-dispatch
  str-arm box→register staging span `0x8000351c → 0x80003628` (`#derive_case` seg once
  the `jr` route to the str-compare arm is pinned), (ii) `blockB_binary`'s `hVlSurv`
  supplied non-vacuously for `.str` (a layout survival residual, like `store_survives`),
  (iii) the ALREADY-named `StrSeamSpan2` + box→EvalIH epilogue.  NO kind-3 blockB rebuild
  — that class does not exist.  The eq/ne arm reuses the SAME generic blockB + a kind-2
  readback (int payload) instead of kind-3.
- proposal: the operand recursion is DONE (kind-generic already).  The reusable
  abstraction to still factor is a per-kind READBACK family (`StrOperandsStaged` at
  kind 3 here; a kind-2 int-payload readback + kind-1 bool for eq/ne) projecting
  `TwoSubReturn`'s two generic `ValueRepr` boxes into the register-staging obligations —
  one tiny lemma per kind, all definitional unfolds of `ValueRepr`.

## 2026-08-31 famB-middle-writer-readback (errlink Family-B x10-computed)
- missing: `SegReadback` had `lookupG_runGM_snoc` (readback of a register whose
  writer is the body's LAST instruction) but NO readback for a MIDDLE writer —
  Family-B setup runs write `x10` via `mv a0,sN` and then keep writing `a2/a3`
  (`auipc/addi` message ptr) AFTER it, so `x10`'s writer is not last and
  `lookupG_runGM_snoc` does not apply.
- workaround: added `lookupG_stepGM_ne`/`lookupG_runGM_ne` (lookupG preserved by a
  step/run not writing n, the `srcVal_runGM_ne` analogue for lookupG) + a
  `lookupG_runGM_mid pre a post` peel that reduces the middle-writer case to
  `lookupG_stepGM_writer` after peeling `post` — all in `rows/ErrSetupCore.lean`,
  axiom-clean, structural (never reduces the fold).
- cost: ~35 lines once; the per-site x10 readback is then a fixed 8-line
  `rw`-chain the emitter generates (`lookupG_runGM_mid` ≫ `srcVal_runGM_ne` ≫
  `sext 0` cleanup). Every future register-setup arm (the `mv a0,sN`-computed
  dispatch-arg shape) reuses it.
- proposal: promote `lookupG_stepGM_ne`/`lookupG_runGM_ne`/`lookupG_runGM_mid` up
  into `Vsa/Sim/SegReadback.lean` beside `lookupG_runGM_snoc` (the natural home)
  so non-error rows (rejoin/kind-check with trailing writes) can call them too.

## 2026-08-31 armspec-oracle-family (armSpec_of_seams, ArmSpecBridge.lean)
- missing: the three composite-arm oracles (FnArmSpec/CallArmSpec are machine
  `Triple EvalEntry→EvalExit`; AssignArmSpec is `EvalIH→EvalIH`) have the SAME
  entry≫seams≫epilogue spine but at different type indices, so no single
  combinator captures all three; ALSO the generic `InterpEntry.EvalEntry` bakes
  in int-callee fields (`value_int_code`/`int_slot`/`vicode_stack_disjoint`/
  `table_stack_disjoint`), so `blockA_k` cannot run at the fn/call/assign armPC
  off a bare `EvalEntry` — the var arm already worked around this with a bespoke
  `EvalVarEntry`. There is no generic "arm-entry widening" from `EvalEntry` to an
  arbitrary arm's `ArmEntryK` (callee-loaded/slot generalized over the arm).
- workaround: a FAMILY of three combinators (fnArmSpec_of_geom /
  assignArmSpec_of_machine / callArmSpec_of_geom), each closed modulo a per-arm
  NAMED structure (FnArmGeom / AssignArmMachine / CallArmGeom) whose `hArm` field
  IS the entry→PreEpilogueV (or EvalEntry→EvalExitD) run — i.e. the entry-widen +
  seam-marshal is deferred INTO the geom field rather than composed from the
  landed gens. The combinator proper is pure Triple.seq + blockD_v_phic (fn/call)
  / pure EvalIH-rewrap (assign). Axiom-clean, ~1.6s user CPU.
- cost: the `hArm` field still hides the real machine work (blockA_k at the arm
  slot + marshalling the fnArmMallocCall/ClosureBuild `Steps`-chains and the
  CallClosure crux into PreEpilogueV's ValueRepr/StoreRepr). Each arm pays that
  marshalling separately when its geom is discharged; the seams are landed but
  their write-log→PreEpilogueV lift is not.
- proposal: (1) a generic `armEntry_widen : EvalEntry → (∃ ment v8 v9 v18,
  ArmEntryK … armPC calleeLoaded e …)` parameterized by (armPC, calleeLoaded,
  slot-pin), factoring blockA_k's precondition off a callee-generic entry (the
  EvalVarEntry pattern generalized) — would let the fn/call `hArm` fields START
  from ArmEntryK not EvalEntry; (2) a `preEpilogueV_of_writeLog` marshaller
  (segToTriple's FnArmClosureBuildPost write-log memory → PreEpilogueV's
  ValueRepr sret + StoreRepr survival), the box/store lift every leaf arm's
  block-C already does by hand — factor it once.

## 2026-08-31 bin-int-readback-reverse-isos (kind-2 operand readback + ArmPostGeomV cell consumer)
- missing: `ArmPostGeom.lean` landed FORWARD `armPostGeomV_of_{add,sub}Resid` (via
  `armPostGeom_of_addResid` ≫ `armPostGeomV_of_armPostGeom`) and BOTH directions for
  lt/le/gt/ge/mul/div/mod, but NO reverse `{add,sub}Resid_of_armPostGeomV`. To reduce a
  `.add`/`.sub` int cell's `AddResid`/`SubResid` production to an `ArmPostGeomV` instance
  (the point of the geometry-collapse), a reverse iso is required — the two int/`tblOff=4`
  cells were the only ones without it.
- workaround: NONE (built the two reverse isos in the new file `rows/BinIntReadback.lean`
  as clean `⟨…⟩` projections, mirroring `ltResid_of_armPostGeomV`; axiom-clean). No hand
  navigation — each is a 32-field structural iso.
- cost: ~10 lines each, one-time; anyone doing the add/sub geometry collapse would have
  re-derived them. The 9 `binIntCellResid_<op>_ofStaged` corollaries then all follow the
  SAME 4-line `refine ⟨…⟩; intro; obtain; exact` shape (mul/div/mod thread their libgcc
  `…Loaded`/`<op>Stk` extras through the reverse iso).
- proposal: relocate `addResid_of_armPostGeomV` + `subResid_of_armPostGeomV` into
  `rows/ArmPostGeom.lean` beside the other reverse isos so the int/tblOff=4 pair is
  symmetric with the bool/int-seam ops; then the 9-cell fan-out is a single `gen_*_row.py`
  emitter row (op → opTok/slotDef/valLoaded/viLo/viHi/tblOff/reverseIso/extras).

## 2026-08-31 divcorr-loophead-reflect (entry+divergence endgame, hDivCorr item)
- missing: a FAITHFUL loop-head divergence correspondence — `SegEntry` at
  `interpLoopHeadPC` pins the spec STATE `st` (store+out) but carries NO reflection
  of WHICH statements remain (`ss`) nor the active scope `Addr` (`env`), so a naive
  `divCorr` built on `SegEntry` alone collapses distinct spec nodes and drops
  `env`/`ss` (Lean flags them unused).
- workaround: LANDED `Vsa/Sim/DivCorrClose.lean` — `divCorr` carries an ABSTRACT
  per-node reflection `Reflect : Config → Addr → List Stmt → Prop` (a section
  variable) as an explicit conjunct, so distinct `(env, ss)` are distinct nodes and
  the loop-body progress residual supplies+consumes it. `DivCorrFamily` reseated on
  TWO named residuals: `DivEntryDrive` (= the SAME `Loaded → SegEntry@loopHead` drive
  as the term-arm entry / `InterpInitStoreRepr`) and `DivLoopProgress` (the
  still-running per-statement forward sim). All reachability plumbing (StepsN prepend
  via `trans_add`, entry k=0 reindex) PROVED, axiom-clean.
- cost: ~130 lines; the `Reflect` predicate is un-instantiated (whoever supplies the
  loop-body machine seams must define the concrete induction-register reflection:
  `s0`=Stmt* cursor, loop bound `s2`, scope pointer). Every future consumer of the
  loop-head correspondence (both divergence AND the term-arm loop) pays this once.
- proposal: promote a concrete `LoopHeadReflect` to a landed def beside `SegEntry`
  (reflecting the top-level statement-loop induction registers against `(env, ss)`),
  and re-export it so BOTH the term-arm `mExecSeq` loop drive and this divergence
  `divCorr` share ONE reflection — the loop head is the single convergence point the
  brief flags ("the drive is the shared crux").

## 2026-08-31 epiloguespill-genuinely-open (entry endgame, EpilogueSpill item)
- missing: NO discharge of `EntrySeams.EpilogueSpill` from `SegExit` — its fields
  (`x21=0` s5-latch, `Interp_runLoaded`, `ExitTailChain0` = a machine-span Triple,
  and the restore-block `ChainFacts`) are BYTE-LEVEL facts + a downstream tail-span
  Triple that `SegExit`'s abstract M4 representation genuinely does NOT expose (that
  is exactly why `EntrySeams` named it the residual). The `s5=0` latch needs the
  PROLOGUE fact `g s5 = 0` (not in `SegExit`); `ExitTailChain0.chain` is the
  interp_run-return/main/crt0/exit span Triple (genuine machine content).
- workaround: NONE (stopped — did not fabricate). Verified against
  `EntrySeams.lean:105-131` + `TermEntry.lean:452-458`: EpilogueSpill is the honest
  irreducible epilogue seam, not derivable from `SegExit` + `restoreRetChain_run`.
- cost: item-3 as briefed ("discharge EpilogueSpill from SegExit facts") is
  infeasible without the prologue s5-latch + the exit tail-span decode; both are
  off-`SegExit` machine content.
- proposal: EpilogueSpill's ONLY genuine sub-gaps are (a) the prologue `s5:=0` latch
  (a fact of the ENTRY drive — factor it out of the shared drive as `latchS5_of_drive`
  once the drive lands) and (b) `ExitTailChain0` (already isolated + consumed by
  `cleanExitTail`). Re-state EpilogueSpill to REFERENCE those two rather than re-bundle
  the bytes, so it shrinks to exactly the restore `ChainFacts` (the one honest spill).

## 2026-08-31 elabCommand-theorem-async-invisible (DeriveMeta #derive_destructurer, meta task)
- missing: a reliable way for a custom `command_elab` to emit a `theorem` whose
  constant is IMMEDIATELY visible to the rest of the same command / the rest of the
  file. `elabCommand <|← `(command| theorem …)` from inside a `CommandElab`
  elaborates the theorem WITHOUT error (logInfo of the generated syntax is perfect,
  no elab error surfaces) yet `(← getEnv).contains name = false` afterward and every
  later reference reads "unknown constant". A `structure` emitted the same way IS
  visible — the divergence is theorem async/snapshot proof elaboration. `set_option
  Elab.async false in <theorem>` in the generated syntax did NOT fix it; `withOptions`
  is unavailable in `CommandElabM` (no `MonadWithOptions`).
- workaround: build the theorem's proof term + type as `Expr` in `liftTermElabM`
  (elaborate `fun params => (bodyStx : Src → Tgt)`, `instantiateMVars`, `inferType`)
  and `addDecl (.thmDecl { name, levelParams := [], type, value })` directly. This
  commits synchronously; the constant is visible immediately and downstream. Works
  for the destructurer isos (green + axiom-clean on the real ArmEntryK/TwoSubReturn
  towers). The `structure` can still go through `elabCommand` (structures are sync).
- cost: any future command that GENERATES theorems (not just structures) — row
  emitters, iso generators, `#derive_row`-style commands — must use the `addDecl`
  route or they silently produce unusable "unknown constant" theorems. Cost me ~5
  build cycles to localize (the swallowed-error behavior is the trap).
- proposal: a tiny shared helper `Vsa.Sim.DeriveMeta.addThmFromSyntax (name)
  (binders) (type) (body) : TermElabM Unit` wrapping the elabTerm→instantiateMVars→
  addDecl dance, reused by every theorem-emitting command.
- REFINED (measured after the fix): the trap is NOT "any theorem via elabCommand".
  `#derive_row` emits a SINGLE `theorem … := segRow_of_hpost … (by decide) hpost`
  via `elabCommand` and it commits fine (`demoRowGen` axiom-clean, visible to
  `#print axioms` and consumers). The destructurer failed because it emits a
  `structure` AND then two theorems in the SAME command elaborator: the structure's
  async snapshot is what left the following theorems' env-extension invisible. So:
  a lone `elabCommand`-emitted theorem is fine; a theorem emitted AFTER a structure
  in the same command needs the `addDecl` route (or emit the structure in a
  separate command first). Keeps the helper proposal but narrows when it is needed.

## 2026-08-31 stringify-display-level-contract (StrConcatCellResid / stringify decode)
- missing: a framed callee contract for `stringify`@0x80002fc0 that composes via
  callSeg (the landed value_str/strlen/malloc/memcpy specs are low-level machine
  Triples over bespoke pre/post records, NOT callSeg-composable high-level
  contracts; no `free` contract exists at all — the arena is no-free, so the two
  `jal free` in the concat arm are frame no-ops with no spec to consume).
- workaround: NONE for the machine Triple. Instead I DECODED stringify per-kind
  and factored StrConcatCellResid at the `Value.display` level: proved the
  load-bearing reductions GREEN (`stringifyDisplay_str/int/bool/null`), named the
  callee post as `StringifyContract`/`StringifyResult` and the shared strdup tail
  as `StringifyStrdupTailResid`, and reduced `StrConcatCellResid` to a
  `stringify`-free `StrConcatHeapResid` (`strConcatCellResid_of_heapResid`) — so
  the "blocked on a stringify spec" gate is closed at the display level; the only
  residual left is the byte-exact malloc/memcpy/strcpy/value_str concat-into-a-
  fresh-ValueRepr .str.
- cost: the concat heap Triple (malloc+memcpy+strcpy+value_str byte-exact into a
  fresh heap ValueRepr .str, plus showing free×2 don't disturb the public heap) is
  still bespoke (~several hundred lines); every future value-formatting concat pays
  it. The int/bool/null stringify branches each still need the strdup-tail Triple.
- proposal: a `CalleeContract`/`callSeg`-shaped wrapper over the landed
  strlen/malloc/memcpy machine specs (a StrdupContract), reused by BOTH the
  stringify tail and the concat cell; plus a `freeFrame` no-op lemma (free = frame
  identity on the public heap under the no-free arena) so free×2 discharges by
  frame metatheory instead of a bespoke argument.

## 2026-08-31 genseg-jal-sp-reseat (DriveToLoopHead assembly, task #33)
- missing: genseg.py's `terminator = "jal"` path emits a `bridgeOfSeg` row with
  `WrChainAvoidAbi bs` hardcoded, but does not detect when the span reseats a
  callee-saved register (here `addi sp,sp,-176` writes x2 = sp). The generated
  `driveSpillBridge`'s `WrChainAvoidAbi driveSpillSeg` decide is FALSE.
- workaround: hand-reseat the generated jal row on `bridgeOfSegFramed` with
  `P := AbiExceptSp` (AbiPreserved && !(R == x2)), reading the new sp off the
  exposed `GHolds σ2 out.regs` post bundle (exactly the BridgeSegFramed demo (a)
  idiom for the closure `mv s7`/`mv s5` reseats). The prologue frame-setup
  `addi sp,sp,-C` is a UNIVERSAL idiom (every C function prologue), so every
  prologue-drive jal row pays this.
- cost: one hand-edited row per prologue-terminated-in-jal span (~30 lines vs the
  generated ~10), plus the sp-delta readback; recurs for interp_init's prologue,
  every callee prologue that calls before the frame is torn down.
- proposal: genseg detect `wrChain bs ∩ AbiPreserved ≠ ∅` and emit the
  `bridgeOfSegFramed` shape with `P := AbiPreserved && !(R ∈ wrChain∩Abi)`
  automatically, exposing the reseated callee-saveds' deltas off out.regs.

## 2026-08-31 driveToLoopHead-store-offpath (DriveToLoopHead assembly, task #33)
- missing: NOTHING new — this is a CONFIRMATION of the codebase's own analysis
  (EntrySeams.lean:149-160). `DriveToLoopHead L` demands a loop-head `SegEntry`
  whose `store` field is `StoreRepr initSt.store`, but `Loaded L p c` (via
  `atInterpRun`) pins ONLY PC + a0/a1 — never the store. The store is built by
  `interp_init`, which `main` calls @0x800045b4 BEFORE `interp_run` (@0x800045e8),
  so it has already returned by the time the machine is `Loaded`. The `interp_run`
  prologue spans [0x800043ec, 0x8000448c) NEVER touch the store (spill/setjmp/loop
  bound only). CONCLUSION: the SegEntry's `store`/`out` representation fields can
  NEVER be closed by the prologue machine drive; they are irreducibly NAMED
  premises consuming the interp_init build (InterpInit.interpInitStore_compose).
- second finding: `DriveToLoopHead L` is stated over an ABSTRACT `L`, so
  `L.atInterpRun` is opaque — the drive has NO machine facts at all until
  instantiated at the CONCRETE `interpRunLayout` (whose atInterpRun unfolds). So
  the assembly target is `DriveToLoopHead interpRunLayout` /
  `InterpInitStoreRepr interpRunLayout`, not the abstract carrier.
- workaround: NONE needed — assembled the REAL machine Steps chain (3 proved seg
  rows spliced through the named setjmp seam) and left the store/out
  representation + setjmp-buffer geometry as named-field structure premises, which
  is the correct decomposition (the convergence point EntrySeams describes).
- proposal: the store premise should be discharged by wiring
  InterpInit.interpInitStore_compose's output (StoreRepr storeAfterAssert =
  StoreRepr initSt.store) into hFields — but that needs a main-frame fact
  (interp_init ran and its store survives to interp_run's loop head across the
  intervening main code), which is a genuine separate machine obligation.

## 2026-08-31 strconcat-no-free-contract (task #64 gap 3, StrConcatHeap)
- missing: a `free` contract. The str-concat arm (`0x80003abc`/`0x80003ac4`)
  calls `free` twice on the two `stringify` scratch buffers, but the arena
  allocator (`Vsa/Alloc.lean` `MallocContract`) models NO free — the arena
  never reclaims. So there is no theorem "`free(p)` leaves the public heap /
  every live extent `AInv`-unchanged".
- workaround: named the two frees as a public-heap frame NO-OP obligation
  folded into `StrConcatCBlockResid` (the concat-C-block residual). Not built —
  it is one of the sub-facts of that named typed residual.
- cost: every arena-frees-nothing call site (concat here; any future
  interpreter path that calls `free` on a scratch buffer) must re-argue that
  `free` is a public-heap no-op from scratch inside its block residual.
- proposal: add `MallocContract.freeNoOp : ∀ g exts p n sp r m0, Triple (free-pre
  p) (free-post : mem-agrees-outside-privFoot ∧ AInv unchanged ∧ ABI frame)` —
  a frame-only contract mirroring `memcpy_framed_ainv_stable`'s outside-footprint
  clause but with EMPTY write footprint (free touches only allocator-private
  metadata). One `decide`-free structure field; then every free call is a
  `callSeg` with a trivial frame-preserving suffix, same as the other callees.
- RESOLVED (2026-08-31, task #68): landed as `MallocContract.freeSpec`
  (`Vsa/Alloc.lean`), entry `freeEntry = 0x8000479c`. NOT a pure no-op (the
  proposal's `freeNoOp` was too weak): the extent is POPPED (`AInv c.σ' exts`
  from pre `AInv c.σ ((q,n)::exts)`) because dlmalloc REUSES freed blocks — a
  frame-only free would keep `(q,n)` live and make malloc's `ExtDisjoint`
  freshness clause uninhabitable after enough cycles. And the freed chunk's
  bytes `[q, q+n)` are FORFEIT (free writes free-list link pointers into the
  payload) so the untouched region excludes `privFoot ∪ [q,q+n) ∪ stack
  window`. Pre mirrors `spec`'s ABI entry. World re-elaborates; EnvDefCompose +
  Alloc axiom-clean. Consume it as a `callSeg` callee, same as `spec`.

## 2026-08-31 setjmp-post-no-sp-frame (task #66, SetjmpSplice)
- missing: `setjmp_post` (Vsa/Sim/JmpSpec.lean) does NOT preserve the stack
  pointer `x2`. Its frame conclusion is `∀ R, NotWrittenJmp R → σ' R = g R`, and
  `NotWrittenJmp` EXCLUDES x2 (it is the SHARED union predicate covering both
  setjmp and longjmp; longjmp writes x2, setjmp does not). So even though setjmp
  physically writes only x10 + the 14 buffer stores (never x2), the post cannot
  state `sp` survives the call. The `SetjmpSplice` seam in DriveToLoopHeadSpans
  needs `sp = spNew` at the setjmp return (loop-setup A/B reload 16(sp)/24(sp)
  off it), and `setjmp_spec` alone cannot supply it.
- workaround: NONE in the theorem — named the sp-preservation as an explicit
  typed residual `spRet` field on `SetjmpGeom` (the setjmp caller must supply
  "x2 unchanged across the setjmp call", which is TRUE — setjmp does not write
  x2 — but not derivable from the current post). `hSplice_of_setjmpSpec` reuses
  `setjmp_spec` verbatim for the ret + a0=0 and consumes `spRet` for x2.
- cost: every setjmp-call splice that must preserve sp (this drive; any interp
  path that setjmps and then reloads off sp) re-argues sp survival by hand or
  carries it as a premise. The buffer-geometry residual already blocks full
  discharge, but this makes even the sp thread a named input.
- proposal: add a setjmp-SPECIFIC frame `setjmp_post.frameSetjmp : ∀ R,
  NotWrittenSetjmp R → σ' R = c.σ R` where `NotWrittenSetjmp` excludes only
  x10/PC/noise (NOT x2/callee-saveds) — setjmp genuinely preserves every GPR but
  x10. The proof already threads `h_x2_*`/`h_x1_*`/`h_x8..x27_*` through all 14
  store sites (they are all in scope at the ret), so it is a strengthening of the
  existing frame clause, no new site work. Then sp (and every callee-saved) is
  free from the post.

## 2026-08-31 landing-bundle-must-be-prop-existential (DriveToLoopHeadSpans §1/§5, resume task)
- missing: a canonical shape for a "seam landing" bundle that (a) carries the
  reached Config as DATA, (b) is BUILT from a `Triple`/callee-spec result (an
  `Exists`), and (c) is CONSUMED inside Prop-goal proofs. A `structure … where`
  (Type-valued) fails (c-side) because building it from the `Triple`'s `Exists`
  is large elimination (Exists→Type, forbidden: "recursor Exists.casesOn can only
  eliminate into Prop"); a `structure … : Prop where` fails at DECLARATION —
  projection generation errors "field must be a proof, but it has type Config"
  (the WidenMeta gotcha, but here it kills the whole structure, not just usage);
  and a Type-valued structure mixing a `g : (R:Register)→Option (RegisterType R)`
  field beside 12 `BitVec 64` value fields ALSO wedges universe inference
  (`?u+1 =?= max(…)` / CoeT typeclass timeout).
- workaround: write the bundle as a Prop-valued `def … : Prop := ∃ (data…), (props…)`
  and consume via `obtain` (Prop-into-Prop elim, legal). Applied to SpillLanded,
  SegLanded, SetjmpSplice, SetjmpGeom. Also split the two big Prop obligations
  inside the geometry (SpRetSurvives, BnezFallthrough) into their own named defs.
- cost: no positional-tower navigation (each obtain is a flat named pattern at the
  binder site), but the pattern is re-derived per bundle; every future "landing"
  seam (bridge/row/callee-splice → reached-config carrier) will re-invent it.
- proposal: a `Landed` combinator/abbrev family — `def Landed (c : Config)
  (P : Config → Prop) : Prop := ∃ c', Steps c c' ∧ P c'` — so SegLanded/SpillLanded
  are `Landed c (fun c' => …)` and the destructurer is shared. The `Triple`
  result IS `Landed` at the pre-config; marshalling becomes `id`.

## 2026-08-31 step-count-layer-landed (Task #70, resume)
- RESOLVED (uncommitted): `Vsa/Sim/StepCount.lean` (3.5s, all thms axiom-clean
  ⊆ {propext,Classical.choice,Quot.sound}). Delivers the step-counting
  exponentiating layer.
- KEY REUSE: the whole `TripleN` algebra ALREADY exists in `Vsa/Triple.lean`
  (`TripleN.mono` = the weaken lemma, `TripleN.seq` = counted `Triple.seq` with
  counts adding, plus `of_triple`/`of_step`/`conseq`/`toTriple`). Task parts 2
  needed NO new composition lemmas — point future agents there.
- CRUX FACT: `Config.steps` is threaded by `stepOnce` (Elf.lean:47) as `used + 1`
  on BOTH `.inr` continue leaves, so every `Step` advances `steps` by exactly 1
  (`Step.steps_succ`, proved by `unfold stepOnce; repeat' (simp bind/EStateM
  layer | split | inject-payload | .inl→False)`). ⇒ `Steps a b` with
  `b.steps = a.steps + k` is `StepsN k` (`Steps.toN_of_stepsEq`). `segEval_sound`
  already pins the reached `steps` to `u + evalBlocksFuel bs`, so
  `segToTripleN bs L lds pc0 m0 Q hwf hpost : TripleN (evalBlocksFuel bs)
  (SegPre …) Q` — SAME hwf/hpost as `segToTriple`, upgraded count. THIS is the
  free lower bound for every existing/future `#derive_case` seg row.
- `Landed`/`LandedN` combinators landed (the resolution of the prior
  landing-bundle entry): `Landed c P := ∃ c', Steps c c' ∧ P c'` +
  mk/refl/weaken/bind/of_triple, and counted `LandedN n` +
  mk/toLanded/weakenCount/weaken/bind(adds counts)/of_tripleN. SpillLanded/
  SegLanded in DriveToLoopHeadSpans are literal `Landed` instances — reseat is
  future work, combinator is ready.
- RECIPE for a future agent to count a row `myRow : Triple (SegPre bs …) Q`:
  don't touch myRow; call `segToTripleN bs L lds pc0 m0 Q hwf hpost` with the
  same args → `TripleN (evalBlocksFuel bs) …`; then `TripleN.mono` down to
  `TripleN 1` (iterFromCountedRun) or `TripleN (n+1)` (approxFromCountedRun) via
  a `decide` on the fuel (`segToTripleN_one`/`_succ` package that arithmetic).

## 2026-08-31 interior-call-span-combinator (Task #69 loop-head dispatch span)
- missing: a combinator for a span shape `seg ≫ CALL ≫ seg ≫ jal` (an INTERIOR
  call in the middle of a straight-line span, then more marshalling, then a
  terminal jal). `bridgeOfSeg` handles `seg ≫ jal` (one trailing call);
  `callSeg` handles `prefix ≫ callee ≫ suffix` at the Config→Prop `Triple`
  level. Neither composes a `#derive_case` seg run ACROSS an interior call at
  the raw `Steps` level and continues into a second seg + trailing jal.
- workaround: the interp_run loop-head→exec_stmt span
  (0x8000448c br → value_null CALL @0x8000445c → arg-setup seg → jal exec_stmt
  @0x80004474) was split into `loopHeadDispatchRow` (br seg) + a NAMED
  `ValueNullSplice` premise (the interior value_null call, phrased like
  `DriveToLoopHeadSpans.SetjmpSplice`) + `loopHeadArgSetupBridge` (bridgeOfSeg
  for the second seg + trailing jal), then `Steps.trans`-composed by hand in
  `loopHeadDispatch_span`. The value_null splice is a genuine off-path CALL so
  naming it is legitimate — but the HAND `Steps.trans` composition + the manual
  richer-landing helper (`loopHeadDispatchLanded`, needed because the generated
  `*Row` post drops the tick/minstret the next splice consumes) is the
  mechanical part.
- cost: ~40 lines of hand composition + one bespoke `loopHeadDispatchLanded`
  helper per interior-call span. The `hterm` back-edge assembly and any other
  interp-loop-body span with an interior helper call (there are several:
  value_print, env_get in the eval arms) will pay it again.
- proposal: `callSpanSeg` — a combinator taking (segA, calleeSplicePremise,
  segB, jalSeam) and returning the composed `Steps` landing, folding the
  `Steps.trans` + the tick/minstret threading. Alternatively, extend the genseg
  arm compiler with a `mid_call` terminator-list so a single arm description
  emits the whole `seg ≫ CALL ≫ seg ≫ jal` row with the interior call named.

---

## 2026-08-31 dirty-tree-olean-cascade (iterSeam assembly, task iterSeam)
- missing: a supported way to complete the olean closure for `lake env lean
  <file>` when the working tree has modified sim sources (EnvDefCompose/
  TermRouting/StrlenSpec were `M` in git status). Wave-25 files
  (ExecDispatchRows/ExecWhile2/TermSimClose/EvalIntSim2-4/ExecBrkCont/
  EvalVarSim/ExecExprRet/ExecRet/ExecVarNull/WidenMeta/EvalRecCommon/
  EvalSimCommon/SnprintfSpec20) had NO committed olean, so the target's import
  closure was incomplete and `lake env lean` errors "object file … does not
  exist" ONE missing module at a time (it stops at the first missing import).
- workaround: computed the target's import closure in python, topo-sorted, and
  built each genuinely-missing olean with `lake env lean -o <olean> <src>`
  SERIALLY (parallel `-o` builds of sibling modules appeared to delete/
  invalidate each other's freshly-written oleans — SnprintfSpec20 vanished twice
  after concurrent builds; likely a non-atomic olean write or shared temp).
  ~14 oleans, several multi-minute (EvalIntSim2/SnprintfSpec20 heavy). NEVER used
  `lake build` (forbidden).
- cost: ~40 min of wall time chasing the cascade one module at a time; every
  future agent whose target sits above the wave-25 sim layer pays this again
  until those oleans are committed or a warm .lake is seeded.
- proposal: (a) commit the wave-25 oleans (or seed a warm .lake per the
  remote-build-pro memory), so downstream targets load without a rebuild; OR
  (b) a `scripts/warm_closure.sh <module>` that topo-builds exactly the missing
  oleans in a target's closure SERIALLY with `lake env lean -o` (never parallel,
  never `lake build`) — the mtime heuristic is wrong (content-hash, not mtime;
  build only the MISSING, not the "stale").

## 2026-08-31 nullbridgeseam-splice-entry-contradictory RESOLVED (task #72, amendment `nullBridgeSeam_oldEntry_false` + `execRetNullGlue_closed`)
- resolution: AMENDED `NullBridgeSeam.splice`'s entry from the contradictory
  `∃ mid, … PC=0x800042f0 … ∧ ExecArmEntryK … execArmRet …` (which pinned PC to BOTH
  0x800042f0 and execArmRet=0x80004120 = False) to the plain post-beqz predicate
  `RetNullPostBeqz g … out0 m0 ment` at 0x800042f0 (moved `RetNullPostBeqz` above the
  struct so the field can reference it). Also fixed `retNoneExpr` to be `ment`-indexed
  (`∀ ment, (frame m0) → read64 ment (aStmt+8) = some 0`) so the prefix's `ld` reads
  the current memory, not `m0`. `retNullGluePrefix` now lands EXACTLY in
  `RetNullPostBeqz`, so `execRetNullGlue_closed` composes `retNullGluePrefix ≫
  S.splice` via `Steps.trans` (`ExecArmEntryK@0x80004120 → SubExecReturnR@0x80004138`)
  — the machine half of `ExecRetNullGeom.hGlue`, MODULO the still-named `value_null`
  callee content inside `S.splice`. Regression guard `nullBridgeSeam_oldEntry_false`
  (theorem: the OLD entry ⇒ False). All 4 theorems axiom-clean, ~ under file elab
  budget. Consumers of NullBridgeSeam/RetNullPostBeqz/retNullGluePrefix: NONE outside
  ExecRetNullGlue.lean (grep-verified). Vsa.lean green.
- missing: a usable NullBridgeSeam.splice whose ENTRY predicate is inhabitable.
  As landed (Vsa/Sim/rows/ExecRetNullGlue.lean lines ~220-232) the `splice`
  field's entry conjoins `c.σ.regs.get? PC = some 0x800042f0` with
  `ExecArmEntryK … execArmRet …`, and `ExecArmEntryK` (Vsa/Sim/ExecBrkCont.lean:162)
  PINS `PC = some armPC = execArmRet = 0x80004120`. Both cannot hold: the entry
  is `False`, so `splice` is vacuously provable but can never fire from the real
  post-beqz config (PC=0x800042f0, no longer ExecArmEntryK). `execRetNullGlue_closed`
  (ExecArmEntryK@0x80004120 → SubExecReturnR@0x80004138) therefore CANNOT be
  assembled from this seam: after site_80004120_es ≫ site_80004124_taken_es the
  config is at 0x800042f0 and does not satisfy the splice's entry.
- workaround: NONE (stopped; landed only the honest partial glue segment
  0x80004120→0x800042f0 as ExecRetNullGlue.retNullGluePrefix, taking NullBridgeSeam
  for the retNoneExpr pin — see file). The final splice→SubExecReturnR remains open
  and BLOCKED on the seam statement.
- cost: the value_null-bridge glue (#13) cannot close until the seam is amended;
  any agent picking up hSRetNull.hGlue pays a statement fix first.
- proposal: amend NullBridgeSeam.splice's entry to a PLAIN post-beqz predicate at
  0x800042f0 (GoodState + tick + PC=0x800042f0 + x2=sp-176 + x18=aRet + x8=aStmt +
  minstret + Exec_stmtLoaded + the stack memframe + the StoreRepr/spill survival
  carried explicitly), i.e. the fields ExecArmEntryK gives MINUS the PC pin,
  restated at 0x800042f0 — NOT ExecArmEntryK verbatim. Then the prefix segment
  below composes into it by Triple.seq. (Same shape as EvalVarBridge's post-call
  predicates, which do not reuse the arm-entry predicate at a moved PC.)

## 2026-08-31 scaffold-some-motive-unsatisfiable RESOLVED (task #72, motives→True + `hInit/Fc/EsSome_row`)
- resolution: took the proposal's first option — set `mExecInit`/`mForCond`/
  `mExecStep` (TermSimAssembly.lean) to `True` (dead recursor plumbing;
  `execForStartSim` ignores these sub-derivations, real work in `hArm` + `ExecForStep`
  oracle). This makes BOTH `.none` and `.some` constructors `trivial`. LANDED the six
  rows `hInitNone_row`/`hInitSome_row`/`hFcNone_row`/`hFcSome_row`/`hEsNone_row`/
  `hEsSome_row` (all `trivial`) in rows/ScaffoldRows.lean; DELETED the unsatisfiable
  `hInitSome_resid`/`hFcSome_resid`/`hEsSome_resid` defs. Removed the corresponding
  GAP fields `hInitSome`/`hFcSome`/`hEsSome` from `TermResiduals` (TermAssembly.lean)
  and changed `termCases_of_residuals` to supply them unconditionally
  (`hInitSome := hInitSome_row` etc, mirroring the `.none` treatment). ZERO consumer
  re-threading confirmed: SeqForRows ForLoop rows consume `mForCond`/`mExecStep`
  sub-IHs as ignored `_`; `exec_forStart_row` consumes `mExecInit`/`mForLoop` as `_`;
  `mForLoop` UNCHANGED (still identity-PC, used by `ForResid`/`segIdentity`). All
  downstream green + axiom-clean (TermSimAssembly, ScaffoldRows, TermCaseBundle,
  TermSimClose, ExecForStart, SeqForRows, ExecDispatchRows, TermAssembly, Vsa.lean).
- missing: an inhabitable statement for the `.some` loop-scaffold rows
  (hInitSome_resid/hFcSome_resid/hEsSome_resid, Vsa/Sim/rows/ScaffoldRows.lean).
  The amended scaffold motives (mExecInit/mForCond/mExecStep, TermSimAssembly.lean)
  demand, for the `.some` constructor, `∀ p, Triple (SegEntry … st … p) (SegExit …
  st' … p)` with entry PC = exit PC = a SINGLE universally-quantified `p` and
  `st' ≠ st` (the sub-stmt/expr mutates the store). No machine seg runs a
  store-mutating call from an ARBITRARY abstract PC back to the SAME PC; the
  `.none` amendment fixed the identity case but gives `.some` the mirror-image
  obstruction the old independent-(p,q) motive had for `.none`. Crucially
  execForStartSim (Vsa/Sim/ExecForStart.lean:101) takes the ExecInit/ForCond/
  ExecStep sub-derivations as IGNORED `_` — the REAL init/cond/step machine work
  flows through hArm + the ExecForStep `hstep` oracle, NOT the scaffold motives.
  So the `.some` scaffold Triples are DEAD recursor-plumbing that cannot be
  honestly inhabited.
- workaround: NONE (stopped; the three rows remain `def *_resid` statements,
  threaded as `R.hInitSome`/etc. in TermAssembly.lean — an unfillable premise the
  top-level residual carries).
- cost: the `for`-family TermCases can never be assembled UNCONDITIONALLY while
  these three premises are unsatisfiable-as-stated; #50 blocked on a motive fix.
- proposal: change the `.some` scaffold motives to `True` (they are consumed as
  `_` — the honest work is already in ExecForStep), OR give them a two-PC shape
  `(entryPC pRet)` with `pRet` the sub-call's fixed return address and a real
  `bridgeOfSeg`/callSeg span; the current single-`p` shape is provably vacuous for
  `.some`. Matches precedent: the (p,q)→p amendment fixed `.none` but created this
  dual gap.

## 2026-08-31 approxdispatch-entries-cannot-be-weakest-pc-only (task #73)
- missing: a concrete instantiation of the six ApproxSeamFold entry predicates
  (EEntry/AEntry/CEntry/SEntry/FEntry/SqEntry) under which ALL 37 ApproxDispatch
  fields are provable FROM EXISTING segs via segToTripleN. The brief's "weakest =
  PC + GoodState + GHolds + tick/minstret" is NOT sufficient: each field maps
  entry-of-COMPOUND to entry-of-CHILD, and a PC-only entry cannot compute the
  child's machine entry PC (it depends on the child NODE ADDRESS, carried by
  neither the spec term nor a PC pin). This is exactly why DivergeSim.Corr keeps
  correspondence abstract. Moreover the real M4 arm segs (blockA_binaryArm,
  ExecDispatchRows sims) start from the RICH EvalEntry/ExecEntry and produce rich
  posts; forgetting the post is easy (LandedN drops it) but the ENTRY they need
  is SegPre-at-arm-PC (needs GHolds pins + ChainFacts decode), not a weak entry.
- workaround: instantiate SqEntry = SegEntry@interpLoopHeadPC ∧ Reflect (the
  loop-head shape) so hSqEntry is DEFINITIONAL; discharge the two Approx-sequence
  fields (seqHead via loopHeadDispatch_span, seqStep via the iterSeam body span)
  as the genuinely-supplied class; leave the other five entries as an abstract
  Corr-family and the 35 non-sequence fields as a NAMED residual structure
  (ApproxArmResid) with one field per SEG CLASS, each stating precisely the
  step-lower-bound the class's M4 arm seg would supply once weakened.
- cost: the 35 arm fields are not closed here; each needs its M4 arm seg
  (blockA_binaryArm / blockB_binary / ExecDispatchRows / ScaffoldRows) re-exposed
  as a LandedN-1 step-lower-bound FROM a weak SegPre-at-arm-PC entry TO a weak
  SegPre-at-child-PC entry — a per-class re-seat (~6-8 classes), not per-field.
- proposal: a `weakEntry`/`SegPreEntry` predicate = SegPre at the relation's arm
  entry PC, PLUS a Corr-carried child-node-address map, so each class's field is
  `segToTripleN` over the arm dispatch seg (forgetting post) landing at the
  child's SegPreEntry. The child-PC computation is the ONE piece Corr must carry;
  once that lemma exists the 35 fields fan out mechanically per class.

## 2026-08-31 approxarmresid-fields-need-arm-seg-split-at-jal (task #74)
- missing: for each ApproxArmResid field (binaryL/unaryE/argsHead/stmtExpr/callBody
  /flCond/…), a lemma cutting the M4 arm seg at its recursive `jal`/dispatch-to-
  child point: `arm-head-entry → LandedN ≥1 → child-rich-entry` (EvalEntry/ExecEntry
  at the child sub-node, or SegEntry at the new frame's loop head). The divergence
  fold recurses INTO the child (which never returns), so it needs the PREFIX landing
  AT the child entry — the exact opposite of what the normal-termination arm segs
  produce.
- workaround: instantiate the five interior entries (EEntryC/AEntryC/CEntryC/SEntryC
  /FEntryC in Vsa/Sim/ApproxArmReseat.lean) as ∃-ghost bundles over the rich
  EvalEntry/ExecEntry (child address carried by aExpr/aStmt) or SegEntry@interior-PC
  (args/callee/for), bundle the 36 fields as ApproxArmResidGap = ApproxArmResid at
  those entries (NO smaller remainder — none of the 36 discharges from an existing
  seg), and give the capstone divFamily_of_armResidGap. Each field is now a
  precisely-typed, upstream-dischargeable split-lemma statement. Verified: axiom-
  clean, ⊆{propext,Classical.choice,Quot.sound}.
- cost: the 36 split lemmas are not built here — each is arm-seg surgery (re-cut
  blockA_binaryArm/blockB_unary/ExecDispatchRows at the recursive jal). blockB_unary
  literally CONSUMES `hIH : EvalIH …` and lands at SubEvalReturn (post-return), so
  the child EvalEntry is a buried sub-config of its Steps chain, not a lemma. Whoever
  closes the divergence arm pays this per class (~6-8 classes: eval-kind-dispatch,
  binary-arm, unary-arm, call/args, exec-dispatch, for/scaffold).
- proposal: split each arm seg into (prefix: arm-head → recursive-jal-target =
  child entry) ⊗ (suffix: child-return → arm exit), the prefix supplying the
  ApproxArmResid field via segToTripleN, the suffix + child IH re-composing the
  existing normal-path arm Triple. The `jal`-target-is-child-entry marshalling is
  the ONE shared fact (analogous to jalStep_of_obs for the CALL seam).

## 2026-08-31 armentry-widen+preepilogue-writelog (Task #48 remainder, ArmSpecBridge *Geom discharge)
- missing: the two proposals from the 2026-08-31 armspec-oracle-family entry were
  documented but unbuilt: (1) a generic arm-entry widening from `EvalEntry` to the
  arm dispatch target, and (2) a value-region marshaller off an arm's reflected
  write-log into `PreEpilogueV`.
- workaround: NONE — both LANDED as parametric lemmas (green, axiom-clean):
  * `armEntry_widen` (`Vsa/Sim/ArmEntryWiden.lean`, ~2.8s): `EvalEntry g … e …` +
    the arm-specific callee-generic dispatch facts (`hkind`/`hslot`/`hcallee`/
    `hcalleeSurv`/`hexprSurv`/`harmAl`/`htableStk`) → `∃ out0 ment v8 v9 v18,
    ArmEntryK … armPC calleeLoaded e`. Pure `blockA_k`-application: the
    case-independent tower is reconstructed from `EvalEntry`'s named fields (the
    exact projection `evalVarSim` did inline). CONFIRMS the int-coupling finding:
    the callee-loaded/slot facts CANNOT come from `EvalEntry` (which bakes in
    int-only `value_int_code`/`int_slot`), so they are explicit args. `out0` is
    EXISTENTIAL in the post (not `c.σ.sailOutput`) because `ArmEntryK` pins
    `sailOutput = out0` and the dispatch preserves it — pinning to the entry's
    sailOutput makes the exit-config post mismatch.
  * `preEpilogueV_of_writeLog` (`Vsa/Sim/PreEpilogueWriteLog.lean`, ~0.6s):
    value-region readback `valueRepr_closure_of_reads` (kind4+payload=φc a+nz →
    `ValueRepr … (.closure a)`) folded into a `PreEpilogueV … (.closure a)`
    assembler that takes the register/store/geometry `hrest` bundle separately.
- MACHINE-CHECKED OBSTRUCTIONS (why no *Geom bundle fully closes today):
  * `FnArmGeom.hArm` needs the `allocClosure` callee contract (`EvalFn.lean:26`:
    "no allocClosure machine contract exists yet") to link the malloc'd payload to
    `φc' a`/`φc' a ≠ 0` and give `hpc : PhiExtends`. NOT fabricated.
  * `AssignArmMachine` needs `evalAssignSim` (the `EvalEntry (.assign) → EvalExitD`
    sim; `jal eval_expr` ⋈ IH ≫ value-stage ≫ `jal env_set`) — unbuilt; the
    AssignArmEntry/Stage/Return gens are landed seg rows but not composed.
  * `CallArmGeom.hArm` needs the full CallClosure crux assembly (`Call`-consuming
    sim); the CallClosure*Gen seg rows are landed but not composed.
  * `PreEpilogueV` demands MANY facts NOT in the arm write-log (registers x9/x2/
    minstret/ABI-frame, StoreRepr@φc', GoodState, ~20 geometry facts);
    `FnArmClosureBuildPost` carries only `GoodState ∧ mem=writeLog ∧ PC`. So the
    write-log determines ONLY the value region — proposal 2 correctly factors
    exactly that; the rest is threaded from the seam context.
  * `ArmPostGeomV` (rows/ArmPostGeom) is the binary post-`TwoSubReturn` residual
    over the operator jump-table region, a DIFFERENT memory region than the fn-arm
    sret buffer — NOT a source for the closure `ValueRepr` (its `vloaded` pins
    Value_int/boolLoaded code, not sret contents). So the "ArmPostGeomV
    consumption" framing does not literally apply; the honest analogue is the
    value-region readback built here.
- cost: `fnArmGeom_hArm_of_seam` (`Vsa/Sim/FnArmGeomReduce.lean`, ~0.9s,
  axiom-clean) brackets the whole `EX_FN` run with the two new lemmas (front =
  armEntry_widen, back = preEpilogueV_of_writeLog), reducing `FnArmGeom.hArm` to
  the strictly-smaller NAMED middle residual `FnArmSeamRun` (ArmEntryK → the two
  sret reads + hrest bundle) whose opens are exactly the malloc/build write-log
  marshalling + the missing allocClosure contract. Every future closure arm reuses
  the front/back for free; only `FnArmSeamRun` is per-arm.
- proposal: land the `allocClosure` callee contract (closure-arena analog of
  env_new_spec) — it is the ONE fact blocking `FnArmSeamRun` and thus
  `fnArmGeom_closed`. The call/assign bundles want `evalAssignSim` and the
  CallClosure crux assembly respectively (separate, larger machine spans).

## 2026-08-31 allocClosure-contract-decode (FnArmSeamRun / fnArmGeom_closed)
- missing: an `allocClosure` machine callee contract (the closures-arena analog of
  `env_new_spec`): from a fresh `malloc(16)` block `p` (MallocContract.spec) + the
  two closure-build stores (closure[0]=fn_expr, closure[8]=φf env), assemble
  `StoreRepr mpre N A φf φc' (st.store with closures.push cd)` at an EXTENDED
  `φc'` with `φc' (st.store.closures.size) = p ≠ 0`, i.e. `PhiExtends φc φc' n`.
  There is NO StoreRepr-grow / push-closure lemma anywhere (grep: only PhiExtends
  refl/mono used; no `storeRepr_grow`/`closures.push` StoreRepr constructor).
- decoded EX_FN arm path (validated vs disasm 0x800031ac dispatch → arm):
  * eval_expr prologue @0x80003168 lowers sp by 1088, spills ra/s0/s1/s2, sets
    s0=a2(Expr node=aExpr), s2=a1(interp*=aEnv), s1=a0(sret). jump-table @0x80019f58,
    dispatch `jr a5` @0x800031ac. `ArmEntryK` = exactly this dispatch-target config.
  * fn slot targets 0x800033c4 DIRECTLY (nothing branches to 0x800033c4; 0x800033c0
    is `j 0x800033ec`, NOT fallthrough). So there is a per-fn-arm HEAD (dispatch→
    0x800033c4) that must set a3 := (env frame ptr) — NOT yet decoded/landed and NOT
    in ArmEntryK's pins (which pin x8=aExpr,x9=sret,x18=aEnv but NOT a3). This is the
    concurrent arm-head-prefix agent's territory OR a genuine gap. The two malloc/
    build seg rows (fnArmMallocCallBridge @0x800033c4→jal malloc, fnArmClosureBuildRow
    @0x800033d8→0x800033ec) ARE landed+green.
  * fnArmClosureBuild stores: sd s0,0(a0)=closure[0]:=aExpr(fn_expr ✓ ClosureRepr
    offset 0), sd a3,8(a0)=closure[8]:=a3(must be φf env ✓ ClosureRepr offset 8),
    sd a0,8(s1)=sret[8]:=p(closure addr), sw a5,0(s1)=sret[0]:=4(VAL_CLOSURE kind).
- workaround: land `AllocClosureContract` as a named-field structure (env_new_spec
  analog) + `fnArmSeamRun_of_allocClosure` consuming it; genuine opens (arm-head a3
  decode, malloc splice ABI threading, StoreRepr-grow) become doc-commented fields.
- cost: the StoreRepr-grow lemma is a real reusable fact needed by EVERY future
  allocating arm (allocFrame/env_new already inline it by hand in env_new_spec's tail).
- proposal: `StoreRepr.pushClosure` — StoreRepr m φf φc s → (fresh p, ClosureRepr at p,
  arena/align/inj-extension) → StoreRepr m φf φc' (s.closures.push cd). One lemma,
  reused by allocClosure here and any closure producer.

## 2026-08-31 armsegsplit-marshalling-fact-built + unary-class-done (task #75)
- missing: the shared jal→child-entry marshalling fact feeding ApproxArmResidGap's
  Eval-child fields, and the per-class arm-seg splits.
- workaround: NONE for the marshalling fact — LANDED as `evalEntry_of_jalPrefix`
  (`Vsa/Sim/ArmSegSplit.lean`, green ~2.8s, axiom-clean). It is EXACTLY
  `EvalRecCommon.armTail_rec` truncated BEFORE its `hIH` call (lines 311–401,
  verbatim): from the arm state at the recursive `jal eval_expr` PC with the sub-call
  args staged (a0=subsret,a1=aIn,a2=aOperand, sp lowered to sp-1088) + the full
  lowered-frame geometry bundle, ONE jal step ⇒ `LandedN 1 c (fun c' => EvalEntry …
  esub … (sp-1088) …)`. FINDING (field-by-field audit of EvalEntry's ~40 fields):
  the jal step SUPPLIES for free good/tick/pc(=evalExprEntry via hjaltgt)/a0/a1/a2/
  ra(=retPC)/spReg/minstret/mem/out/frame(sub-ghosts=post-jal regfile ⇒ rfl)/
  spill_defined; the sub-call GEOMETRY at the lowered frame (stackOK@sp-1088 needing
  SL.lo+3264≤sp, operand ExprRepr/align/RAM/disjointness@sp-1088, sub-buffer geom,
  StoreRepr+survival, code/table/arena disjointness re-checked vs sp-1088) MUST be
  premises — these are precisely blockB_unary's "recursive-case extras" beyond
  ArmEntryK (the ArmEntryK widening residual), NOT projectable from EvalEntry(parent).
- cost: unary class LANDED (`Vsa/Sim/ArmSegSplitEval.lean`, green ~5s, axiom-clean):
  `landedN_eentryC_of_jalPrefix` (wraps the marshalling fact into the ∃-ghost
  `EEntryC` divergence-fold entry — the ONE reusable bridge for ALL Eval-child
  classes), `JalPreBundle e` (the pre-bundle as a config predicate, ghosts ∃'d),
  `landedN_eentryC_of_preBundle` (pre-bundle ⇒ EEntryC, pure bridge application),
  and `unaryE_split` = ApproxArmResid.unaryE's EXACT type, proved by `LandedN.bind`
  of the staging residual `UnaryStagePre` onto the marshalling bridge (counts add
  1+1, weakenCount→1). `unaryE_split` covers BOTH neg AND not (blockB_unary is
  op-agnostic). The ONLY residual per Eval-child class is now `UnaryStagePre`-shaped:
  `EEntryC(compound) → LandedN 1 (JalPreBundle child)`, strictly SMALLER than the raw
  field (stops at the jal pre-bundle; the verified marshalling finishes). That
  residual = blockB_unary's body (dispatch blockA_k + operand ld + sub-buffer addi)
  RE-CUT to land at JalPreBundle instead of consuming hIH — an upstream arm-seg
  surgery, still unbuilt.
- proposal: land the per-class *StagePre lemmas by re-cutting each arm seg at its
  recursive jal (the "stop at JalPreBundle" cut). The dispatch prefix (blockA_k) is
  SHARED across all EX_* arms, so factor `dispatchToArm : EEntryC(compound)@evalEntry
  → LandedN k (armPC-with-kind-read)` ONCE, then each arm adds only its short head
  (operand load / operand staging) to reach JalPreBundle. binaryL/logicalL reuse the
  unary shape with a 2-operand head; binaryR/logicalR/argsTail need the MID-arm
  re-staging span (second jal, after left/head returned) = a second JalPreBundle cut.

## 2026-08-31 allocClosure-contract RESOLUTION (FnArmSeamRun)
- landed: Vsa/Sim/AllocClosure.lean = `storeRepr_pushClosure` (THE missing
  StoreRepr-grow / closures.push lemma, axiom-clean {propext,Classical.choice,
  Quot.sound}) + `AllocClosureContract` (env_new_spec analog structure, fixed
  φc'/p/mpre params so its Triple post composes). Vsa/Sim/rows/FnArmSeamReduce.lean
  = `fnArmSeamRun_of_allocClosure` (contract.spec ≫ storeRepr_pushClosure ⇒
  FnArmSeamRun at grown store, axiom-clean). Composition probe: the produced
  FnArmSeamRun feeds fnArmGeom_hArm_of_seam ⇒ FnArmGeom.hArm end-to-end (green).
- residual for fnArmGeom_closed = ONLY constructing an AllocClosureContract, i.e.
  its .spec Triple: ArmEntryK-dispatch → fresh-block+ClosureRepr+sret-bundle. That
  is the genuine machine work (EX_FN arm-head `a3 := φf env` decode from armPC to
  0x800033c4 [NOT in ArmEntryK's pins — likely the concurrent arm-head agent's
  seg]; malloc splice via MallocContract.spec over fnArmMallocCallBridge; the
  fnArmClosureBuild write-log → mpre/ClosureRepr/sret reads marshalling). The two
  seg rows (fnArmMallocCallBridge/fnArmClosureBuildRow) are landed+green already.
- the proposed StoreRepr.pushClosure abstraction is DONE and reusable.

## 2026-08-31 armsegsplit-eval-child-fan-out-complete (task #75 cont'd)
- missing: (follow-up to armsegsplit-marshalling-fact-built) fan-out of the
  marshalling bridge across ALL eval-child-landing fields of ApproxArmResidGap.
- workaround: NONE — LANDED. The unary result generalised into ONE combinator
  `evalChildSplit_of_stage` (`Vsa/Sim/ArmSegSplitEval.lean`, green ~6s, axiom-clean)
  = `LandedN.bind` of a staging residual (to `JalPreBundle child`) onto the verified
  marshalling bridge (`landedN_eentryC_of_preBundle` ∘ `evalEntry_of_jalPrefix`),
  counts 1+1→weakenCount→1. 15 eval-child fields landed as `<field>_split` corollaries
  (unaryE/binaryL/binaryR/logicalL/logicalR/assignE/callF/argsHead/stmtExpr/stmtRet/
  stmtVarInit/stmtIfCond/stmtWhileCond/flCond + flStep w/ extra ForCond/ExecS hyps),
  each EXACTLY the corresponding ApproxArmResid field type. Capstone: `EvalChildStages`
  (bundle of the 14 hyp-free staging residuals) + `armResidGap_evalChildFields`
  (discharges all 14 fields as a field-typed conjunction the final ApproxArmResidGap
  assembly consumes). CONFIRMED both binary AND for-loop arms use the SAME `armTail_rec`
  seam for their recursive jals (EvalBinSim.blockB_binary:513 left / :911 right;
  binaryR/logicalR/flStep = the MID-arm re-staging = a SECOND JalPreBundle cut at the
  second jal after the left/head returned).
- cost: the 14+1 staging spans are the ONLY remaining upstream work for eval-child
  fields — each = the arm-head+dispatch chain re-cut to LAND at JalPreBundle instead
  of consuming the eval IH. Strictly SMALLER than the raw field (the verified
  marshalling finishes). blockA_k dispatch prefix is SHARED across all EX_* arms.
- proposal: factor `dispatchToArm` (EEntryC(compound)@evalEntry → armPC, shared) ONCE
  so each staging span adds only its short operand-load head. The ~21 NON-eval-child
  fields (AEntryC arg-tail, CEntryC callee body, SEntryC/SqEntryC/FEntryC statement/for
  control) need their OWN marshalling facts (exec_stmt-entry via `ExecRecCommon`'s
  armTail analogue / SegEntry-anchored) — the exec-stmt-entry twin of
  `evalEntry_of_jalPrefix` is the next shared fact to extract.

## 2026-08-31 stringify-code-pins-missing (task #71 strdup-tail jal seams)
- missing: `Vsa/Sim/Code/Stringify.lean` byte-pin lemmas (`stringify_at_80003048`
  = strlen jal, `_at_80003058` = malloc jal, `_at_8000306c` = memcpy jal, and the
  `StringifyLoaded`/`Env`-style loaded predicate over the stringify function's
  bytes). Every OTHER function with jal-seam bridges (env_define, env_new) has a
  Code file supplying `<fn>_at_<pc>` byte pins; stringify has NONE.
- impact: the strdup-tail seg CORES (strdupStrlenArgSeg/…MallocArg/…MemcpyArg)
  are landed + green, but they park at the jal seam over caller-supplied `lds`.
  Composing the trailing `jal` via `jalStep_of_obs`/`bridgeOfSeg` needs the
  callee-jal DECODE, which needs the stringify code bytes present in `σ'.mem`
  (`writeLog m0 out.log`) — i.e. a `StringifyLoaded m0` code-pin battery. Without
  it the frame-carrying bridges (bridgeStrlenPre/MallocPre/MemcpyPre for the
  strdup tail) CANNOT close their jal seam; they remain typed residuals citing
  the seg core + the missing Code pins.
- workaround: NONE for the jal seams. Landed only the self-contained epilogue seg
  (jr-terminated, no external jal) + named the three jal-seam frame residuals.
- proposal: generate `Vsa/Sim/Code/Stringify.lean` from the disasm byte pins
  (same generator as `Code/Env_define.lean`), then the three bridges are the
  exact `bridgeStrlenPre_closed`/`bridgeOfSeg` idiom over those pins.

## 2026-08-31 strcpycontract-frame-unsound (task #71 Part 2)
- missing: nothing — `strcpy_full_spec` (StrcpySpecW3.lean:1217) IS the complete
  entry-to-ret strcpy spec (both paths, CString-phrased). `StrcpyContract.lean`'s
  doc ("no composed strcpy_full_spec exists") is STALE.
- bug: `StrcpyContract`'s post frame `∀ R, StrcpyNotWritten R → get? R = g R` with
  `StrcpyNotWritten := NotWrittenB` (avoid {x11,x14,x15}) is UNSOUND. The aligned
  word path clobbers x12/x13/x16 (a2/a3/a6, disasm 0x80006e00..e78, no restore
  before ret). Machine-checked: `NotWrittenB x16` holds but `¬NotWrittenCpw x16`,
  so the contract falsely claims `get? x16 = g x16` for aligned inputs → the
  contract is FALSE on the word path and cannot be inhabited.
- workaround: landed `StrcpyContractCpw` (Vsa/Sim/rows/StrcpyContractInhab.lean) —
  the corrected contract with the honest frame split (pre pins g on NotWrittenCpy,
  post restores only NotWrittenCpw), fully proved from strcpy_full_spec + a caller
  geometry supplier `StrcpyGeom` (StrcpyLoaded + CpyRegions + CpwRegions +
  SrcWordMapped). Also landed `cstr_shift_copy`/`cstring_shift_copy` (transport a
  CStr/CString along a byte-equal copy — the dual of cstring_bytes, reusable).
- proposal: re-point `StrcpyContract.lean`'s `StrcpyNotWritten` alias from
  `NotWrittenB` to `NotWrittenCpw` and add the pre `NotWrittenCpy` frame (one-line
  fix; the file was read-only for this task). Then StrConcatHeap's strcpy splice
  consumes StrcpyContractCpw directly.

## 2026-08-31 approxarmresid-field-count-29-not-36 (Task #76)
- missing: NONE (documentation drift, not a missing fact). The Task #76 brief and
  the `ApproxArmReseat`/`ApproxDispatchSuppliers` file headers say
  `ApproxArmResid`/`ApproxArmResidGap` has "36 fields"; the structure actually has
  29 fields (counted: 9 EApprox + 2 ArgsApprox + 1 CApprox + 14 SApprox/FlApprox +
  seqHead). The "36" appears to double-count or predate a merge.
- workaround: covered the real field set — 15 eval-child (ArmSegSplitEval) + 11
  non-eval-child (ArmSegSplitNonEval: stmtIfThen/stmtIfElse/stmtWhileBody/
  stmtWhileLoop/stmtForInit/flBody/callArgs/argsTail/callC/stmtForLoop/flLoop) = 26
  of 29. The 3 remaining (callBody/stmtBlock/seqHead) land at `SqEntryC`
  (`SegEntry + Reflect`), needing the extra `Reflect` witness a bare jal→SegEntry
  twin cannot supply — correctly the IterSeamAssembly/SqEntryC boundary.
- cost: none beyond the miscount confusion; future agents should treat "36" as "29
  actual fields, 26 twin-dischargeable + 3 SqEntryC-boundary".
- proposal: correct the "36" literal to "29" in ApproxArmReseat.lean /
  ApproxDispatchSuppliers.lean headers when those files are next edited (read-only
  this task).

## 2026-08-31 sqentryc-boundary-3-fields-closed + halfB-recut-cost (Task #78)
- missing (Half A): NONE — the 3 SqEntryC-boundary fields (callBody/stmtBlock/
  seqHead) are now closed the same way as the 26 twin fields. Key finding: the
  target `SqEntryC Reflect c' st d env ss = ∃ ghosts, SegEntry@loopHead c' ∧
  Reflect c' env ss`. The `SegEntry` half is machine content; the `Reflect` half is
  the OPAQUE section variable (DivCorrClose) — machine-underivable. Honest shape:
  the `*StagePre` residual LANDS at a config carrying BOTH (SqLoopHeadPreBundle for
  callBody/stmtBlock; loopHeadDispatch_span's ExecEntry for seqHead — the reverse
  direction), the Reflect component TRANSPORTED by the caller from its own Reflect
  at the compound node. Bridge = definitional repack (mirror of sqEntryC_of_seg).
  Landed `Vsa/Sim/ArmSegSplitSqEntry.lean` (5 thms, axiom-clean, 22s) +
  `Vsa/Sim/ApproxArmResidGapAssembly.lean` (armResidGap_of_stages assembles the
  FULL 29-field ApproxArmResidGap from 4 staging bundles: EvalChildStages(14) +
  flStep(1) + NonEvalChildStages(11) + SqEntryStages(3); divFamily_of_armStages →
  DivFamily L, both axiom-clean 1.3s).
- missing (Half B, binary-RIGHT + the other re-stagings): a cheap way to re-cut the
  MID-arm span. binaryR's span (0x800034fc..0x80003518, 7 sites → RIGHT jal) is NOT
  a truncation of a straight-line head like blockB_unary/leftStagePre: it starts
  from `cL` = the post-LEFT-return SubEvalReturn bundle and needs the memory
  transport ment↔mcall1↔cL.mem (hAgNode/hMemExtM0) + hPopCL frame-population +
  node-24 readback before the 7 sites even begin. A clean re-cut is ~250 lines of
  bespoke machine threading PER mid-arm (binaryR/logicalR/callC-mid/argsTail-mid),
  each entangled with its own SubEvalReturn post — the EvalBinSim.blockB_binary body
  lines 512-911.
- workaround (Half B): NOT built (budget: each re-cut risks the elaboration wall the
  discipline forbids bumping). Delivered Half A + the full capstone instead (higher
  leverage: it is the LAST divergence content reduced to ONE supplier interface).
  The two landed models (blockB_unary_stagePre, blockB_binary_leftStagePre) already
  cover unary + binary-LEFT; the rest are the honest named ArmStages fields.
- cost: the mid-arm/exec-side stagings (~13 spans) each pay ~150-250 lines when
  built; whoever builds them reuses evalChildSplit_of_stage/execChildSplit_of_stage
  (the marshalling is done — only the head span remains).
- proposal: a `subEvalReturn → JalPreBundle` mid-arm combinator that abstracts the
  "transport node pointer across a returned sub-call + run the operand-load sites"
  shape, so binaryR/logicalR share ONE re-cut like binaryL shares one marshalling
  bridge. Until then each mid-arm is its own StagePreSuppliers2 entry.

## 2026-08-31 strdup-tail-memcpy-seam-needs-framed (Task #77 Part 2)
- missing: NONE (abstraction existed). The strdup-tail memcpy arg-staging seg
  `strdupMemcpyArgSeg` (`ld a2,8(sp) ; mv s0,a0 ▷ beqz(false) ; mv a1,s1`) reseats
  the CALLEE-SAVED `x8`/s0 (holds the malloc result across the memcpy call), so
  `WrChainAvoidAbi strdupMemcpyArgSeg` is FALSE and plain `BridgeSeg.bridgeOfSeg`
  cannot land its jal seam.
- workaround: used `BridgeSegFramed.bridgeOfSegFramed` at `P := AbiExceptS0`
  (`AbiPreserved R && !(R==x8)`) — the EXACT `mvS7Seg` idiom already in that file;
  s0's reseated value is exposed via the `GHolds σ2 out.regs` post. Green + axiom-clean.
- cost: one extra `def AbiExceptS0` + two `decide`s (hnoiseP/hAvoidP) + one hPabi
  one-liner. The strlen/malloc seams use plain `bridgeOfSeg` (WrChainAvoidAbi holds).
- proposal: none — the two-combinator split (bridgeOfSeg / bridgeOfSegFramed) is the
  right factoring. A future generator (`scripts/genseg.py`) emitting the jal-seam
  bridge should pick bridgeOfSegFramed automatically when `wrChain ∩ calleeSaved ≠ ∅`.

## 2026-08-31 strdup-tail-bridges-closed + concat-cblock-scope (Task #77)
- DONE (Parts 1+2): `Vsa/Sim/Code/Stringify.lean` (generated, 105 sites/7 chunks,
  grandfathered) + `Vsa/Sim/rows/StrdupTailJalSeams.lean` (5 thms green+axiom-clean):
  the wave-31 obstruction (three strdup-tail jal seams needed a byte-pin battery) is
  CLOSED. `strdupTail_{strlen,malloc,memcpy}_run` = bridgeOfSeg(Framed) + jalStep_of_obs
  over the Stringify pins; `strdupTailBridgeStrlenPre_closed` = the frame-carrying
  strlen bridge (contract's `bridgeStrlenPre` shape).
- residual (Part 2): the malloc + memcpy `*Pre_closed` wrappers (contract's
  `bridgeMallocPre`/`bridgeMemcpyPre` shapes) + `bridgeEpilogue` — the seams are the
  machine cores; the wrappers are the ~50-line-each field marshalling into the
  malloc-entry/PreDispatch predicates (malloc: x8 ghost reseat g', x1%4=0; memcpy:
  PreDispatch + OOM non-null branch, reads s0 off the exposed GHolds since memcpy seam
  is AbiExceptS0). Then `stringifyStrdupTailContract` instantiates modulo entry supplier.
- residual (Part 3): `StrConcatCBlockResid` (StrConcatHeap.lean) unbuilt — the
  10-callee heap splice 0x80003a20→0x80003ae0 (2×stringify HYP ≫ strlen ≫ strlen ≫
  malloc ≫ [beqz] ≫ memcpy ≫ strcpy ≫ free ≫ free ≫ value_str) + EvalIH lift. All 7
  callee contracts EXIST (MallocContract.{spec,freeSpec} @ Alloc.lean:80/139,
  strlen framed via EnvDefCompose, memcpy framed splice, StrcpyContractCpw @
  StrcpyContractInhab, value_str_spec_full @ EvalStrSim:200) + 3 staging segs landed
  (ConcatCBlockStaging). This is a several-hundred-line callSeg/Triple.seq assembly —
  needs its own session; land in stages (heap-splice core, then EvalIH lift).
- WIRING (report-only, not applied per task): add `import Vsa.Sim.rows.StrdupTailJalSeams`
  to Vsa.lean; check_all axiom entries strdupTail_{strlen,malloc,memcpy}_run +
  strdupTailBridgeStrlenPre_closed. Stringify.lean added to discipline_grandfather.txt.

## 2026-08-31 midarm-combinator-landed (Task #79 priority 1)
- missing: a `SubEvalReturn → JalPreBundle` mid-arm re-cut (the 2026-08-31
  halfB-recut-cost proposal). binaryR/logicalR (and callC-mid/argsTail-mid) each
  paid ~250 lines of bespoke machine threading (EvalBinSim.blockB_binary:540-929).
- workaround: NOT a workaround — BUILT the combinator. `Vsa/Sim/MidArmCombinator.lean`
  `binaryR_midStagePre` (green, axiom-clean {propext,Classical.choice,Quot.sound},
  ~6s). VERDICT: **factorable**. The hand threading's ONLY entanglement with the
  left span (ment↔mcall1↔cL.mem node transport + hPopCL frame-pop) is consumed
  purely as facts ABOUT cL.σ.mem (`read64 cL.σ.mem (aExpr+24)=aROp`, presence on
  [sp-1120,sp)), which SubEvalReturn's memframe+MemExtends clause already
  establishes at the caller — so honest carried premises, not re-derived internals.
  The 7 sites (0x800034fc→0x80003518) + mcall2 marshalling are op-INDEPENDENT (arm
  PC is op-generic; op matters only at the value-combine tail after the right
  returns), so ONE combinator serves every binary/logical operator.
- KEY GOTCHAS: (1) the right-operand node `ExprRepr` survival needs `rop_stkfull`
  (aROp+16≤SL.lo ∨ sp≤aROp — node either below the whole stack or above sp), NOT
  `rop_stk` (which allows sp-1088≤aROp, overlapping the sd a6,0(sp) write at
  [sp-1088,sp-1080)); use it with getElem_writeMap8_disjoint against the SINGLE
  write, not hAgMcall2 over all of [SL.lo,sp). (2) site_800034fc_ee needs the RIGHT
  NODE geometry at aExpr+24 (node_lo 0x80000000≤aExpr, node_align aExpr%8=0,
  node_win tohost+32≤aExpr, node_hi aExpr+32≤2^64) — carry all four, not just
  node_hi. A failing omega inside a nested `(by …)` shows up as `sorryAx` in
  `#print axioms` (not an error), with the omega dump printed — grep the error line.
- cost: none; landed. binaryR/logicalR now instantiate this cheaply (the 7-site
  span is shared). Remaining per-op work at the caller = unpack SubEvalReturn +
  supply the node/geometry facts (all present in the arm's BinExtras/SubEvalReturn).
- proposal: DONE (binaryR_midStagePre). Same shape re-usable for callC-mid /
  argsTail-mid once their entries are pinned (both are the "returned sub-call →
  reload next node ptr → jal" idiom).

## 2026-08-31 logical-left-head-cut + midarm-recut-verdict (Task #79 priority 2)
- LANDED (priority 2, logicalL): `Vsa/Sim/StagePreSuppliers2.lean`
  `blockB_logical_stagePre` (green, axiom-clean, ~10.7s) — the logical-arm-head
  → JalPreBundle cut, mirror of StagePreSuppliers.blockB_unary_stagePre but for the
  two-operand logical arm @0x8000355c (3-site head: ld a2,16(a2) ≫ addi a0,sp,120 ≫
  sd a3,0(sp) env-spill → σ3 @0x80003568 = LEFT jal). Op-generic (`&&`/`||` share
  the head). Now unary + binary-LEFT + logical-LEFT all have their ArmEntryK→JalPreBundle
  head cut; each is a drop-in EvalChildStages.{unary,binaryL,logicalL} supplier
  MODULO the shared blockA_k dispatch (EEntryC→ArmEntryK, standing upstream).
- NOT a cheap clone (machine-checked): logicalR (the logical mid-arm) is NOT an
  instantiation of binaryR_midStagePre. binaryR's mid-arm is 7 straight-line ALU/store
  sites (0x800034fc→0x80003518). logicalR's span (EvalLogical3, from SubEvalReturn
  @0x8000356c) includes a `jal value_truthy` CALL (0x80003594) for the short-circuit
  test + a 24-byte copy — a structurally different, larger span. It needs its own
  re-cut (a value_truthy-seam mid-arm combinator), not this one.
- assignE / callF / argsHead / the exec-side stagings (stmtExpr/stmtRet/...): each is
  its OWN arm-head straight cut (different arm PC, different spill pattern), same
  SHAPE as blockB_unary_stagePre/blockB_logical_stagePre. Not built this task
  (budget); the template is now demonstrated twice (unary model + logical clone).

## 2026-08-31 strdup-memcpy-a2-reload (Task #80 Half A)
- missing: a `lds`-carrying variant of `strdupTail_memcpy_run` (or a `writeLog`/`ld`
  readback lemma) that reconstructs the reloaded `x12 = ofNat nMemcpy` from the
  `sd a2,8(sp)` spill the malloc-staging wrote into `mMalloc`. `strdupTail_memcpy_run`
  runs the seg with `lds = []`, so the `ld a2,8(sp)` reads the empty loads list, NOT
  `mMalloc[spM+8]` — the `PreDispatch.a2` field cannot be discharged from it.
- workaround: named the whole memcpy bridge as the typed residual
  `StrdupTailMemcpyBridge` (Vsa/Sim/rows/StrdupTailContractClose.lean §2); the
  contract instantiation `stringifyStrdupTailContract_closed` takes it as a hypothesis.
- cost: the memcpy bridge stays a hypothesis; also blocks the analogous
  `bridgeMemcpyPre` of any spill-then-reload arg-staging seam (env_define's memcpy
  bridge would pay the same if re-seated on the seg layer).
- ALSO missing (same bridge): a NULL-branch exclusion. The malloc-post disjunction's
  NULL branch (`x10=0`) takes the seg's `beqz a0 → 80003140` (OOM error path), so the
  unconditional `PreDispatch @ memcpy-entry` target is only provable with the arena
  no-OOM guarantee (`nMalloc ≤ maxReq ⇒ malloc ≠ NULL`, a MallocContract property).
- proposal: `segToTripleLds` — a `segToTriple` variant threading a caller `lds` whose
  head is the spilled-value image (`writeLog`-consistent), so reload-after-spill segs
  read back the spilled datum; plus a `MallocContract.nonNull_of_bounded` field
  exposing the arena's no-OOM guarantee to prune the NULL disjunct.

## 2026-08-31 concat-cblock-evalih-lift (Task #80 Half B)
- missing: the whole-node `EvalIH` lift for the `.binary .add` str-concat arm — the
  `blockA_binaryArm ≫ blockB_binary(two sub-EvalIH) ≫ concatHeapCore ≫ blockD_v_rec`
  pipeline (BinArmBridge pattern) does NOT yet exist for the STR/concat arm, and
  `concatHeapCore` itself (the ~7-callee post-stringify splice: strlen×2 ≫ staging ≫
  malloc ≫ beqz ≫ memcpy ≫ strcpy ≫ free×2 ≫ value_str) is unbuilt.
- workaround: landed the reusable byte fact `cstring_append`/`concatReadback`
  (Vsa/Sim/rows/CStringAppend.lean, green+axiom-clean) — the concat CString readback
  (memcpy's NUL-free left run ++ strcpy's NUL-terminated right tail); left
  `concatHeapCore` + the EvalIH lift as `StrConcatCBlockResid` (the existing named
  residual in rows/StrConcatHeap.lean).
- cost: `StrConcatCBlockResid` stays the one bespoke heap Triple; the concatHeapCore
  splice + STR-arm BinArmBridge remain to build. concatReadback removes the CString
  reasoning from that build (it was the one non-mechanical step in the splice's post).
- proposal: a `binArmStrResid_of_cblock` combinator (STR-arm analogue of the
  add/sub blockC rows) that lifts a concatHeapCore Triple to `StrConcatCBlockResid`
  via blockA_binaryArm/blockD_v_rec, once concatHeapCore is a Triple.

## 2026-08-31 seqhead-loopheaddispatch-depth-phantom (Task #81 item 5)
- missing: a `SeqHeadStagePre`-producer wrapping `loopHeadDispatch_span`. The span
  concludes `ExecEntry g N A SL φf φc st 0 env s ...` (depth HARDCODED to 0), while
  `ArmSegSplitSqEntry.SeqHeadStagePre` needs `ExecEntry ... st d env s` for arbitrary
  `d`. VERDICT (machine-checkable): `ExecEntry`'s field bodies (InductionScaffold /
  ExecEntry.lean:207-280) reference `d` ONLY through `st`/`env`/`s` — NO machine-state
  field mentions `d`; the depth is a PHANTOM parameter on the machine side. So the
  span at `0` re-types to any `d` for free (the `ExecEntry` term is definitionally
  independent of `d`). The real gap is that `SegEntry` (SqEntryC's payload) does NOT
  project the `x2=sp` / `x8=s0` register pins that `loopHeadDispatch_span` demands as
  `hspH`/`hs0H`; those + the span's `hGeom`/`hValueNullSplice`/`hArgSetup` splices are
  the honest carried residual.
- workaround: landed `seqHeadStagePre_of_span` (SeqHeadStages.lean) — packages the
  loop-head sp/s0 pins + the span premises into a `SeqHeadStagePre`, collapsing the
  seqHead field to `loopHeadDispatch_span`'s already-built inputs. NOT closing the
  span premises themselves (geom/value_null/arg-setup — the standing DriveToLoopHead
  residual).
- cost: seqHead now = loopHeadDispatch_span inputs (no NEW machine content); the span's
  4 premise families remain (shared with driveToLoopHead, already the endgame residual).
- proposal: extend SegEntry with the `sp`/`s0` loop-head register pins (or a
  `SegEntry.loopHeadRegs` projection) so SqEntryC directly feeds loopHeadDispatch_span.

## 2026-08-31 strdup-memcpy-s0-reseat-frameghost (Task #82 Part 1)
- missing: `stringifyStrdupTailContract`'s `bridgeMemcpyPre` target (and the
  `bridgeEpilogue` source + the `envDefMemcpyFramedSplice`/`envDefMemcpyFramed`
  threading) uses ONE frame ghost `gm` for BOTH the malloc-staging entry (`rM`,
  pre-`mv s0,a0`) and the memcpy entry (post-`mv s0,a0`). But the memcpy-staging span
  RESEATS s0/x8 to the malloc result (`mv s0,a0` @0x80003060 — deliberate: s0 carries
  `new` across memcpy for the epilogue's `mv a0,s0`). `EnvDefFrame.hAbi` pins
  `∀ R AbiPreserved → get? R = gm R` and `AbiPreserved x8 = true`, so the pre pins
  `s0 = gm x8` (old) and the target pins `s0 = gm x8` (= new). No single gm satisfies
  both ⇒ `StrdupTailMemcpyBridge` (the exact Triple the contract demands) is
  UNCLOSABLE as stated. Machine-checked: `strdupMemcpy_frame_obstruction`
  (StrdupTailContractClose.lean §2b) isolates `sOld = dst` from the two same-gm frame
  pins over the reseated s0.
- workaround: NONE for the bridge (statement is READ-ONLY; Law 4 → reported not
  worked-around). The TWO documented gaps ARE discharged as standalone witnesses:
  `strdupMemcpy_prune_null` (gap 2, via new `M.nonNull_of_bounded`) and
  `strdupMemcpyArg_a2_reload` (gap 1, via the now-lds-generic `strdupTail_memcpy_run`
  at singleton `[sizeBytes]` + a `bytesVal MKind.ld sizeBytes = ofNat nMemcpy`
  readback) — both green + axiom-clean.
- ALSO: the §2 doc UNDER-COUNTED the bridge's suppliers — beyond the a2-reload +
  no-OOM it also needs `MemcpyLoaded`/`Regions`/`MemInv`/`0<nMemcpy`/`dst=ofNat p`
  (the memcpy CALL's own precondition over the fresh block + copy-source `mMalloc`).
  Those are genuine additional residuals, orthogonal to the frame-ghost bug.
- cost: `stringifyStrdupTailContract_closed` still takes `hMemcpyBridge` as a
  hypothesis; the whole strdup tail (and thus every non-str `stringify` branch's
  fresh-copy) stays gated on the unclosable bridge until the contract is amended.
  Any spill-then-callee-with-callee-saved-reseat splice pays the same (env_define's
  own memcpy bridge is safe ONLY because it does not reseat a callee-saved before the
  call).
- proposal: AMEND `stringifyStrdupTailContract` to thread `gm[x8 := dst]` (the
  reseated ghost) in the memcpy target / epilogue source / the framed-memcpy splice,
  OR state the memcpy target's `EnvDefFrame` over `AbiExceptS0` (the frame the run
  actually preserves) + a separate `s0 = dst` pin. Then `strdupTailMemcpyBridge_of`
  (drafted here, blocked on this) closes from the two witnesses + the memcpy-content
  bundle.

## 2026-09-01 concat-blockC-stringify-dispatch-missing (Task #82b step 2)
- missing: a `blockC_concat`-analogue combinator lifting the concat C-block to
  `StrConcatCBlockResid`. `blockA_binaryArm` (BinArmBridge) lands
  `EvalEntry (.binary op) → blockB_binary`'s entry, and `blockB_binary` produces
  `TwoSubReturn @0x8000351c` for the ARITH/comparison path (operator token read at
  0x8000351c → int add/sub/cmp tail). But the STR/concat arm does NOT reuse
  blockB_binary's two `eval_expr` sub-calls the same way: the concat C-block
  (0x80003a20) is reached through the operator-dispatch → STRINGIFY-arm span, and
  its two sub-calls are `stringify` (0x80002fc0), NOT the two operand `eval_expr`
  calls blockB_binary threads. So the `blockA_binaryArm ≫ blockB_binary ≫
  concatHeapCore ≫ blockD_v_rec` pipeline named in the plan is NOT type-correct as
  stated — the middle needs a bespoke `blockC_concat` span (operator-token dispatch
  → the two-stringify entry → concatHeapCore's P) that has never been built. That
  span is ~200+ lines of straight-line + jal-split machine content (the forbidden
  site-battery shape).
- workaround: NONE for step 2 (stopped per Law 3b). Step 1 IS landed: `ConcatSeams.lean`
  (green + axiom-clean) discharges the 3 MallocContract callee slots (malloc=M.spec,
  free1/free2=M.freeSpec), the no-OOM prune (M.nonNull_of_bounded → concatOOM_prune),
  and the value_str readback seam (concatReadback → concatValueStrSeam_readback), and
  packages the rest as `concatCBlockTriple_of` (concatHeapCore with those slots
  pre-plugged; the 4 call-threaded callees + 7 marshalling seams remain arguments).
- cost: `StrConcatCBlockResid` stays the one bespoke residual until the
  `blockC_concat` span + the two-stringify jal-split sub-EvalIH marshalling is built;
  the concat C-block Triple (`concatCBlockTriple_of`) is ready to be its C-block core
  the moment that entry/exit marshalling exists.
- proposal: a `blockC_concat` combinator (the STR-arm analogue of blockC_add) landing
  `operator-dispatch-at-str-token → concatHeapCore.P`, plus a `binArmStrResid_of_cblock`
  that composes `blockA_binaryArm ≫ blockC_concat ≫ concatCBlockTriple_of ≫ blockD_v_rec`
  — mirroring evalAddSim's blockB≫blockC≫blockD but with the stringify sub-calls
  (jal-split layer / evalEntry_of_jalPrefix) in place of the eval_expr operand calls.

## 2026-09-01 evalchild-field-combinator (Task #81 item 1)
- signal (Law 3): THREE eval-child arm-head cuts had landed as ~200-line hand
  batteries (`blockB_unary_stagePre` 2 steps, `blockB_binary_leftStagePre` 4 steps,
  `blockB_logical_stagePre` 3 steps), all stated over the `ArmEntryK`-∃ ENTRY bundle
  (their `hpre`), NOT the `EvalChildStages`-field entry `EEntryC`. The gap to each
  field is the SAME two-factor composition: `EEntryC node ─unpack→ EvalEntry
  ─blockA(Triple)→ (stagePre entry bundle) ─stagePre(LandedN k)→ JalPreBundle child`.
  Building that seam per-field is the forbidden 3rd+ clone.
- FACTORED: `evalChildField_of_blockA_stage` (Vsa/Sim/EvalChildFieldCombinator.lean,
  green + axiom-clean) — the ONE parametric composer: `Triple P Mid` (dispatch bridge)
  + `∀c Mid c → LandedN k (JalPreBundle child)` (arm-head cut, 1≤k) ⇒ `LandedN 1
  (JalPreBundle child)`. Prefix `Steps` lifted via `Steps.toN`, counts added via
  `StepsN.trans_add`, total ≥ k ≥ 1. Kills the hand composition out of all ~14
  eval-child fields; each field is now one `evalChildField_of_blockA_stage` call.
- INSTANTIATED: `binaryL_field_of_extras` — FIRST fully-machine-composed eval-child
  field. `blockA_binaryArm`'s POST is bit-for-bit `blockB_binary_leftStagePre`'s
  `hpre`, so the two landed halves thread with ZERO impedance. Closes
  `EvalChildStages.binaryL` MODULO one honest named premise `BinArmGeomProvider`
  (= `blockA_binaryArm`'s `BinArmExtras`, over the rich entry's own ghosts + the two
  run-time operand-node addresses aLOp/aROp under ∃).
- STILL bespoke (the ACTUAL residual, not the seam): `unaryE`/`logicalL` cannot use
  the combinator yet because there is NO packaged `blockA_unaryArm`/`blockA_logicalArm`
  bridge (`EvalEntry (.unary/.logical) → the stagePre entry bundle`). Only the binary
  arm has its `blockA_binaryArm` (rows/BinArmBridge.lean) built; unary/logical apply
  `blockA_k` INLINE inside each evalXSim, and their stagePre `hpre` needs operand
  geometry (`ExprRepr esub`, `hpay`, sub-buffer disjointness) NOT in `blockA_k`'s
  post. So `unaryE`/`logicalL` fields wait on a `blockA_unaryArm`/`blockA_logicalArm`
  (each ~ the `BinArmBridge.lean` build: `blockA_k` ≫ the operand-pointer read-back +
  the `*Extras` packaging). Once built, both are one-line combinator instantiations.
- proposal: build `blockA_unaryArm` / `blockA_logicalArm` as `BinArmBridge.lean`
  clones (they ARE clones of each other — a fourth signal: parametrize the arm bridge
  over {armPC, calleeLoaded, operand-count, the `*Extras` struct}). Then all of
  unaryE/binaryL/logicalL/assignE/callF/stmtExpr/... close via one combinator call
  each.

## 2026-09-01 blockc-concat-landed (Wave-34 blockC_concat)
- missing: (1) a `bridgeOfSeg` variant whose ABI-frame post tracks a SMALL SET of
  intentionally-clobbered callee-saved regs.  The concat arm's SECOND stringify-arg
  staging span `0x80003a44 → 0x80003a68` runs `mv s2,a0 ; mv s3,a0` (writes x18/x19 =
  s2/s3, both `AbiPreserved`) to record the L-stringify result pointer — so
  `WrChainAvoidAbi concatStringifyRArgSeg` is FALSE and the genseg-emitted
  `bridgeOfSeg` row's `decide` fails (a `sorryAx` sneaks in).  The R staging genuinely
  clobbers callee-saved regs by design; `bridgeOfSeg`'s frame no-op cannot model it.
  (2) `ConcatDispatchResid` = the operator-dispatch + str-kind-branch span
  `TwoSubReturn@0x8000356c → concat arm 0x80003a20`: the STR-kind twin of
  `evalAddChain_run` (which hardcodes int×int, kind loads = 2, lands x10=2/x16=2, both
  `beqz@0x8000388c/0x80003894` NOT taken → int-add fallthrough).  The str case needs
  the SAME block-reflected dispatch chain with a kind load = 3, landing at 0x80003888
  and taking the `beqz` to 0x80003a20.  Genuine new block-reflection content, not built.
- workaround: LANDED `Vsa/Sim/rows/BlockCConcat.lean` (green + axiom-clean, discipline
  OK) as PURE composition algebra over named `Config→Prop`-boundary Triples, matching
  the `concatHeapCore` design: `concatStringifySpan` (2 stringify callees + 3 staging
  seams), `blockC_concat` (= dispatch ≫ two-stringify span), `binArmStrResid_of_cblock`
  (= blockA ≫ blockB ≫ blockC_concat ≫ concatCBlockTriple_of ≫ blockD_v_rec as a
  `Triple.seq` tower), and `ConcatDispatchResid`/`blockC_concat_of_dispatchResid`.  The
  two StringifyContracts thread from blockC_concat's stringify slots into the C-block's
  EvalIH obligation.  LANDED `Vsa/Sim/rows/ConcatStringifyLArg.lean` (green + axiom-clean)
  = the FIRST stringify-arg staging seg (0x80003a20, `concatStringifyLArgBridge` via
  genseg's `bridgeOfSeg`; L span writes only caller-saved x10/x13/x14/x15 + memory, so
  ABI-frame holds).  The R staging seg is NOT landed (ABI-clobber above).
- cost: `binArmStrResid_of_cblock` closes the WHOLE-node lift modulo exactly THREE honest
  named residuals: (a) `ConcatDispatchResid` (the dispatch+branch block-reflection twin),
  (b) the R staging seg's non-ABI bridge (segR slot), (c) the two `StringifyContract`
  discharges (str LANDED, int-tail assembled).  All composition is done.
- proposal: (1) a `bridgeOfSegClobber` combinator = `bridgeOfSeg` whose post reads the
  reflected write-log for the named clobbered regs (s2/s3 here) and only frames the
  UNwritten ABI regs — one `decide` over `wrChain \ {clobbered}`.  Then the R staging
  seg lands like the L one.  (2) parametrize `evalAddChain_run` over the operand kind tag
  {2=int, 3=str} + the landing PC / taken-branch, yielding `ConcatDispatchResid` as the
  kind=3 instance — the dispatch span is op-generic, only the kind literal + branch fate
  differ.

## 2026-09-01 arm-dispatch-bridge-parametrized (wave34 task #81 item 1-2)
- missing: the arm-dispatch bridges `blockA_unaryArm`/`blockA_logicalArm` (the unary/
  logical companions of `blockA_binaryArm`) did not exist — only the binary arm had a
  packaged `EvalEntry → ArmEntryK`-∃ bridge, so `evalChildField_of_blockA_stage` could
  not fire for unary/logical even though their `blockB_*_stagePre` cuts were landed.
- workaround: NONE (built the real thing). LANDED `Vsa/Sim/rows/UnaryLogicalArmBridge.lean`
  = `blockA_unaryArm` (tag 8, 0x800035e0, UnaryArmCallee) + `blockA_logicalArm` (tag 7,
  0x8000355c, LogicalArmCallee), each = the block-A prefix of `evalNegSim`/`evalAndSim`
  cut at the stagePre `hpre` instead of consuming the eval IH. Both axiom-clean first-run.
  Then closed `unaryE`/`logicalL` EvalChildStages fields via `evalChildField_of_blockA_stage`
  (EvalChildFieldCombinator §3/§4), each modulo its arm-geometry provider.
- cost: 3-of-14 eval-child recursive-eval fields now machine-composed (was 1). No new
  machine steps — pure bridge+seam composition of two landed halves each.
- PARAMETRIZATION VERDICT (the "4th-clone signal"): the shared body (blockA_k run +
  ArmEntryK-copy destructure + gpre call-point ghost + node-ExprRepr operand transport +
  out0 realign) IS identical verbatim across all 3 arms. The three bridges differ ONLY in
  {tag, armPC, calleeLoaded + its writeMap8-survival lemma, #operands transported, output
  post shape}. Because the output post genuinely differs (each downstream stagePre demands
  a different conjunct list), a single fully-parametric theorem would need the POST itself
  as a parameter -> a trivial wrapper. The real factored seam is the FIELD-LEVEL composer
  `evalChildField_of_blockA_stage` (already landed last wave) — the ONE point all three
  plug into. VERDICT: 3 concrete arm bridges is the right shape; a `blockA_arm_core`
  helper factoring the shared prologue+destructure would save ~40 lines/bridge but the
  post-packaging refine is irreducibly per-arm. NOT pursued (diminishing return; 3 bridges
  is the closed set for recursive-eval single-child arms — binaryR/logicalR are MID-arm,
  a DIFFERENT SubEvalReturn-entry bridge, not a blockA_k instance).
- BLOCKER (honest, not falsity): assignE/callF/argsHead/logicalR + all 6 exec-side
  stmt*/flCond fields have NO landed `blockB_*_stagePre` arm-head cut — each needs a fresh
  #derive_case seg at its arm PC/spill offsets (+ for exec, an ExecEntry→exec-ArmEntryK
  dispatch bridge, unbuilt). That is per-arm machine work, out of scope for the
  bridge-parametrization+ready-field-fanout this wave. The 3 fields closed here are exactly
  those whose stagePre was ALREADY landed.

## 2026-09-01 fnarm-closurebuild-seg-duplication (wave 34, coordinator)
- duplicate: an agent hand-wrote `#derive_case fnArmClosureBuildSeg` for the EX_FN
  closure-build span although the GENERATED `rows/FnArmClosureBuildGen.lean` already
  defines the identical seg + a `segToTriple` row (surfaced only as an import clash
  at Vsa.lean wiring time — `environment already contains 'fnArmClosureBuildSeg'`).
- cost: none after the fact (the duplicate file was re-seated on the Gen seg, keeping
  only its NEW write-log reflection layer: log_eq/mem_eq/reads); but the collision
  was silent until top-level wiring.
- proposal: (a) `abs_inventory.sh` should list the `rows/*Gen.lean` generated files
  under a dedicated GENERATED heading so agents grep them before any `#derive_case`;
  (b) a discipline rule catching a second `#derive_case <name>` for a PC span whose
  first instruction address already appears in another seg's chain literal.

## 2026-09-01 binaryR-field-lacks-machine-IH (wave 35, ArmStages fan-out)
- missing: the `EvalChildStages.binaryR`/`logicalR` field, as typed, takes only the
  SPEC-level `EvalE st d env l st' lv` (+ `EEntryC c ... (.binary op l r)` at the ARM
  ENTRY config `c`) and must produce `LandedN 1 c (JalPreBundle r c' st')`. The landed
  mid-arm combinator `MidArmCombinator.binaryR_midStage1` starts from `cL` at
  `SubEvalReturn` (PC 0x800034fc, POST-left-return) — NOT from the arm entry `c`. Bridging
  `c → cL` requires running the LEFT `jal eval_expr` and applying `armTail_rec`, which
  demands the MACHINE-level `EvalIH st d env l st' vsub` (EvalRecCommon). That IH is NOT a
  field parameter and is NOT threaded into the binaryR field by
  `armResidGap_of_stages`/`ApproxArmResidGapAssembly` (it only passes `EvalE`+config).
- workaround: NONE. binaryR/logicalR stay as named residual fields this wave. The mid-arm
  cut is landed but cannot be wired at the field level because its entry precondition
  (a config at SubEvalReturn) is unreachable from the field's inputs.
- cost: 2 of the 14 eval-child fields (binaryR, logicalR) blocked on a layer above the
  field — the recursive-descent (left-eval-run-and-return) that lives in the fold's
  strong-induction, not in the per-field staging. Same block will hit callArgs/argsTail
  mid-arms and any other post-sub-call-return staging.
- proposal: either (a) re-type the binaryR/logicalR fields to receive a reached-config
  `cL` at SubEvalReturn (a `SubEvalReturnReached` premise) so the mid-arm cut wires
  directly — moving the left-descent obligation up to the fold where the IH lives; or
  (b) a `midArmField_of_IH` combinator: `EvalIH l → armTail_rec ≫ binaryR_midStage1`,
  taking the IH as an explicit premise, that the fold instantiates with its
  strong-induction IH. (b) is the honest shape: the field's `EvalE` premise is the SPEC
  witness, but the MACHINE staging genuinely needs the IH — so the field type is
  under-powered and must gain an IH premise to be closable. NAMED, not worked around.

## 2026-09-01 midarm-field-ih-seam-BUILT (wave 35, follow-up to binaryR-field-lacks-machine-IH)
- resolved-partial: built the honest seam proposal (b) named above:
  `Vsa/Sim/MidArmFieldIH.lean` (green + axiom-clean, olean regen'd):
  * `MidArmRightMarshal` (def : Prop) = the DELTA `SubEvalReturn` does not carry (the
    right-operand facts surviving the left call — node ptr transport, frame pop,
    ExprRepr survival, Value_intLoaded/IntSlotPinned, BinExtras-shaped right geometry).
  * `midStage1_of_marshal` = SubEvalReturn-reached config + MidArmRightMarshal →
    `binaryR_midStage1` → `JalPreBundle er`.
  * `midArmField_of_IH` = the FULL seam `armTail_rec` (left call, via `EvalIH`) ≫
    `binaryR_midStage1`, landing `JalPreBundle r st'`. Op-independent (arm PCs
    0x800034f8/0x800034fc/imm 0x1ffc6c shared) → ONE seam for BOTH binaryR AND logicalR.
- STILL BLOCKED (structural, not falsity): the `binaryR`/`logicalR` FIELDS cannot be
  wired because they are typed with `EvalE` (spec) not `EvalIH` (machine). The seam is
  READY; the fold must re-type the two fields to carry the IH before they close. That
  re-typing is a fold-level change (owner: whoever owns ApproxArmResidGapAssembly /
  ArmStages), out of scope for the stagePre-fan-out lane.
- cost after seam: closing binaryR/logicalR is now a ONE-call `midArmField_of_IH` per
  field (no re-derivation of the 7 mid-arm sites or the ~80-line node transport) — the
  moment the field gains its IH premise.

## 2026-09-01 allocClosureContract-inhabited-malloc-splice-named (wave 34)
- resolved-partial: BUILT `allocClosureContract_of` (`Vsa/Sim/rows/AllocClosureInhab.lean`,
  green + axiom-clean {propext, Classical.choice, Quot.sound}, discipline-clean).
  Inhabits `AllocClosureContract` (`Vsa/Sim/AllocClosure.lean`) end-to-end EXCEPT the
  malloc splice, which is packaged as ONE named-field reached-config structure
  `AllocBuildEntry` + the premise `hEntry : Triple Pre AllocBuildEntry` (Pre = the
  ArmEntryK-∃ the seam consumer fixes). PROVED with no further hypotheses: the pure
  `fnArmClosureBuildSeg` run (`fnArmClosureBuildSeg_seg`), the four record reads
  (`fnArmClosureBuild_reads`) → `ClosureRepr` + `VAL_CLOSURE` sret reads, the
  register/geometry/frame bundle transfer (build writes only x15; `hframe'` register-frame
  + `hMpreFrame`/`hSpillReads` for the memory-frame), and `storeRepr_pushClosure` (via the
  seam consumer). Composition `allocClosureContract_of → fnArmSeamRun_of_allocClosure →
  fnArmGeom_hArm_of_seam` typechecks (probe green).
- missing (the honest gap, now a single named premise): the malloc-splice machine run
  `Pre → AllocBuildEntry`. It must establish (AllocBuildEntry's fields): the build-entry
  config at 0x800033d8 with a0=p/s0=aExpr/a3=φf env/s1=sret pinned; the malloc result
  (p≠0, p%8=0, A.contains p 16, freshness, φc' size = p, PhiExtends); the OLD store at φc'
  and ExprRepr/code-loaded/spill-reads/memframe survival to the post-build map; and the
  build-seg's ChainFacts/KeysOK. That is exactly the `fnArmMallocCallBridge ≫
  MallocContract.spec ≫ nonNull_of_bounded prune ≫ ld a3,0(sp) reload ≫ beqz-not-taken`
  chain (the reload seg 0x800033d0 was NOT separately built — folded into hEntry).
- proposal: build `hEntry` from `fnArmMallocCallBridge` (already GENERATED) spliced with
  `MallocContract.spec` via `callSeg`/`bridgeOfSeg`, the OOM prune, and the reload — the
  env_new_spec malloc-splice template but landing `AllocBuildEntry` instead of env_new_post.
  This is the SINGLE remaining machine residual for fnArmGeom_closed → evalFnSim on EX_FN.

## 2026-09-01 genseg-false-wrchainavoid-silent-sorryax (wave35 residual 2)
- missing: `scripts/genseg.py` `emit_jal_row` (line 388) emits
  `(by show WrChainAvoidAbi {seg}; decide)` UNCONDITIONALLY for EVERY jal-terminated
  span. When the span writes a callee-saved register (e.g. `mv s2,a0`/`mv s3,a0` =
  `addi x18/x19,...` in the concat R-arg span 0x80003a44), `WrChainAvoidAbi seg`
  reduces to `False`, `decide` cannot produce a proof, elaboration errors, and Lean's
  error-recovery inserts `sorryAx` into the partial term — so the file LOOKS green at
  a glance (the row still elaborates) but `#print axioms` shows sorryAx. This is the
  "genseg emitted a false decide → sorryAx" the wave-34 note flagged; the mechanism is
  now pinned: it is line 388's unconditional emission + Lean error-recovery, NOT a
  decode error.
- workaround: NONE for genseg (bypassed it). Built the R-arg bridge by hand with
  `BridgeSegFramed.bridgeOfSegFramed` at a new `AbiExceptS2S3` avoid-set predicate
  (`AbiPreserved && !x18 && !x19`), exactly the `entryBaseReseat_framed`/`AbiExceptS7`
  idiom — NOT the proposed new `bridgeOfSegClobber`. `Vsa/Sim/rows/ConcatStringifyRArg.lean`
  `concatStringifyRArgBridge`, axiom-clean.
- cost: one hand file per callee-saved-clobbering jal span (the L-arg span, which
  writes only caller-saved regs, WAS genseg-able; the R-arg was not). Any future
  reseat-then-call span hits this.
- proposal: genseg `emit_jal_row` should (a) compute `wrChain(seg)` and, if any written
  reg is `AbiPreserved`, emit the `bridgeOfSegFramed`-at-restricted-predicate path
  (avoid-set = `AbiPreserved && !clobbered_i`) with the exposed `GHolds σ2 out.regs`
  bundle, instead of `bridgeOfSeg`; OR (b) at minimum STATIC-CHECK `WrChainAvoidAbi`
  before emitting line 388 and hard-ERROR (refuse to emit) rather than emit an
  unprovable `decide` that silently sorryAx's. Either kills the whole "green file with
  sorryAx" failure class. (Broader: any genseg-emitted `decide` on a proposition that
  could be `False` should be guarded — a `decide` that can't succeed must not be emitted.)

## 2026-09-01 evalAddChain-kind-generic-parametrization (wave35 residual 1) SUCCESS
- finding: the "exponentiating move" the wave-34 note proposed WORKED verbatim.
  `evalAddChain_run`'s ~190-line dispatch-chain proof (0x8000351c → 0x80003888) NEVER
  inspects the operand kind VALUE — it threads it only via `hc ▸`/`hk ▸` (value-agnostic
  `block_reg` rewrites). Parametrizing the two kind-load hyps (`hc`/`hk`) and the `x10 =
  x16 = 2` conclusion over a free `κ : BitVec 64` yielded `evalConcatDispatchChain_run`
  (`Vsa/Sim/rows/ConcatDispatchChain.lean`) axiom-clean ON FIRST RUN with ZERO proof
  edits (only the 6 literal `2#64` → `κ` substitutions in the statement). The int route
  is the `κ=2` instance, the str route the `κ=3` instance. Then the str-kind head block
  `concatStrHead` (`addi x15,x10,-3 ; beqz x15,0x80003a20`, x10=3 ⇒ x15=0 ⇒ TAKEN) chains
  onto it to reach the concat arm entry 0x80003a20 (`evalConcatDispatch_run`). Taken end-PC
  via the direct `tgtPC0 = pc + sext imm13` reduction (`show (0x8000388c#64) + sign_extend
  (0x0194#13) = 0x80003a20#64; decide`) — NOT `chainEndPC_eq_bt` (that lemma is for
  `chainEndPC`/multi-block NoJr, not single-block `endPCB`; the wave-34 hint mislabelled it).
- cost: none beyond the one κ-clone (a genseg-adjacent mechanical transform). `blenB` of a
  1-body+terminator block = 2 not 1 (fuel bookkeeping gotcha caught by `decide`).
- proposal: a `#derive_dispatch_chain`-style generator that emits the block-reflected
  operator-dispatch chain parametrized over {kind tag, landing PC, branch fate} would let
  every future kind-arm reuse ONE chain. Not built this wave (the κ-clone is the closed set
  for the add-family dispatch); named as the abstraction if a 4th kind-arm appears.

## 2026-09-01 blockA-arm-bridge-emitter-scope (wave36-armgen)
- missing: a uniform DOWNSTREAM target for the blockA_*Arm dispatch bridge across
  ALL eval arms. unary/logical/binary feed a `blockB_*_stagePre` cut (post = ∃ ment
  ArmEntryK + N geometry conjuncts); but assign/call/args have NO stagePre — their
  arm-head is a genseg jal-seg (`assignArmEntryBridge`) whose precondition is a
  SegPre/ChainFacts bundle, not an ArmEntryK-post. And there is NO `AssignArmCallee`/
  `CallArmCallee`/`ArgsArmCallee` calleeLoaded Mem→Prop predicate, nor a
  `KindSlotPinned 5` assign-slot pin, established anywhere.
- workaround: the emitter parametrizes the blockA_*Arm bridge over {tag, armPC,
  calleeLoaded, calleeSurv proof-term, #operands, post-conjunct list, extra-reach
  (x13)}; it can regenerate unary+logical+binary verbatim. It CANNOT emit
  assign/call/args blockA bridges without those three missing per-arm inputs
  (calleeLoaded predicate + its writeMap8 survival lemma + KindSlotPinned tag).
- cost: assign/call/args dispatch bridges remain unbuilt until someone defines
  `AssignArmCallee`/`CallArmCallee`/`ArgsArmCallee` + the `*_writeMap8` survival
  lemma + establishes the dispatch tag. The emitter is READY to consume them.
- proposal: the emitter is the abstraction; the residual is 3 per-arm calleeLoaded
  predicates + survival lemmas (small, model: UnaryArmCallee + loaded_int_writeMap8).

## 2026-09-01 eval-missing-arms-are-stagePre-not-blockA (wave36-armgen)
- missing: the eval-side residual owed for assignE/callF/argsHead is a `LandedN 1 c
  (JalPreBundle e …)` STAGING CUT (the `hstage` premise of assignE_split/callF_split/
  argsHead_split in ArmSegSplitEval.lean:361-493), which is the blockB_*_stagePre
  FAMILY (a bespoke machine-step chain: per-arm site_* lemmas, addi sub-buffer
  offsets, jal-target BitVec computation — see blockB_unary_stagePre in
  StagePreSuppliers.lean), NOT the blockA_*Arm dispatch-bridge family the emitter
  generates. The blockA bridge is the OTHER factor (EvalEntry → ArmEntryK-post);
  unary/logical/binary already have BOTH factors, so they are closed.
- workaround: NONE for the stagePre cut — it does not parametrize as literals. The
  AssignArmEntryGen/CallArm*Gen/CallClosure*Gen segs (genseg.py output) DO provide
  the straight-line machine spans, so a stagePre cut for these arms = compose the
  existing Gen seg's Steps chain + the jal-pre-bundle packaging (a `bridgeOfSeg` +
  JalPreBundle assembly, ~40 lines each), but the JalPreBundle field list and the
  jal-target arithmetic are per-arm.
- cost: assignE/callF/argsHead stagePre cuts remain hand-built (~40 lines each,
  reusing the existing Gen segs). The blockA emitter does NOT reduce them.
- proposal: a SECOND emitter (gen_stagepre.py) consuming {arm seg name, jal-target,
  JalPreBundle field projections} — but the per-arm JalPreBundle conjunct list is
  the same non-uniformity that blocks the blockA post; likely 1 hand template +
  regeneration rather than a clean compiler. Deferred; flagged for coordinator.

## 2026-09-01 armtailrec-pre-tower-has-no-named-def (wave 36, binaryR/logicalR re-type)
- missing: a single NAMED def for `armTail_rec`'s precondition (the "config at a
  `jal eval_expr` with the sub-call staged" tower: ~45 conjuncts of regs/mem/store/
  geometry). It is currently spelled THREE times: inline in `armTail_rec`
  (EvalRecCommon), as the body of `JalPreBundle` (ArmSegSplitEval, ∃-wrapping the
  callPC/retPC/jalImm pins away), and as `midArmField_of_IH`'s `hpre`
  (MidArmFieldIH, pins instantiated at 0x800034f8/0x800034fc/0x1ffc6c).
- workaround: wave-36 adds a FOURTH copy — `MidArmLeftJalBundle` (MidArmFieldWire),
  the ∃-ghost landing bundle for the binaryR/logicalR staging residual, which must
  carry the pinned-PC pre + the jal-site fact + `MidArmRightMarshal` under ONE ∃ so
  the ghosts cohere (JalPreBundle cannot be reused: its ∃ forgets the PC pins, and
  the marshal must be stated over the SAME ghost tuple as the pre).
- cost: ~45 conjuncts re-spelled once more; any future change to the sub-call
  staging contract must now be threaded through 4 sites; the same will hit the
  callArgs/argsTail mid-arm staging bundles when they are built.
- proposal: factor `def SubCallStagedPre (gpre N A SL φf φc st l callPC sp rr sret
  subsret aIn aOperand v8 v9 v18 out0 mcall) (c : Config) : Prop := <the tower>` in
  EvalRecCommon; restate `armTail_rec`'s pre, `JalPreBundle`'s body,
  `midArmField_of_IH.hpre`, and `MidArmLeftJalBundle` as applications of it (each a
  1-line rewrap; all landed consumers keep their statements via the definitional
  unfold). One def, four call sites.

## 2026-09-01 loaded-batteries-lack-footprint-stability-lemmas (wave36-callspec)
- missing: per-code-object stability lemmas `MemPredStableOn XLoaded F` (for
  StringifyLoaded/StrlenLoaded/MemcpyLoaded/…): "the pin battery survives any
  memory change confined to a footprint disjoint from the code region". The
  interface now exists (`Vsa/Sim/CallFrameMeta.lean:MemPredStableOn` +
  `loaded_writeLog_of_rz`, the hjalmem-killer), but no instance is proved for
  any concrete *Loaded battery.
- workaround: NONE needed for this wave (the pilot re-seat keeps the hand
  route's hjalmem-shaped premises); the metatheorem's code-survival leg stays
  conditional on the once-per-object instance.
- cost: until instances land, every splice still threads a bespoke
  `hjalmem : XLoaded (writeLog m0 seg.log)` premise (currently one per staging
  seam, ~19+ sites across the tail/concat/env_define families).
- proposal: one generator-style lemma per *Loaded def: unfold the battery to
  its pin list, each pin address in the code range [lo,hi), then
  `MemPredStableOn XLoaded F` for any F with `∀ a, F a → a < lo ∨ hi ≤ a`
  (Layout-level disjointness, stated once). Could be emitted by the same
  script that emits the *Loaded defs.

## 2026-09-01 record-projection-fields-opaque-to-tactics (wave36-callspec)
- missing: a `@[simp]`-lemma battery (or unfold attribute discipline) for
  `CallSpec` instance projections (`strlenCallSpec.foot g a`,
  `memcpyByteCallSpec.mem0 g`, …): omega/rw cannot see through structure-
  instance field projections even though they are defeq to their literals.
- workaround: defeq re-statement at each use (`have ha' : ¬(dst.toNat ≤ a ∧ …)
  := ha`, `show c'.σ.mem[a]? = g.m0[a]? …`) inside the Sat proofs.
- cost: 1-2 bridge lines per Sat proof field; every future CallSpec instance
  pays it again.
- proposal: emit `@[simp] theorem <spec>_foot_eq : <spec>.foot g a ↔ …` (and
  mem0/entry/ret) beside each instance, or a tiny `callspec_defeq` macro; keeps
  Sat proofs pure field-assembly.

## 2026-09-01 callclosuregeom-entrybase-unsatisfiable (wave37 call crux, CallClosureRow.lean)
- missing: a SATISFIABLE mid-predicate for the closure-arm entry seam. The landed
  `CallClosureGeom.entryBase` post was `SegEntry g N A SL φf φc (closureBoundSt …)
  (d+1) … callBodyLoopPC m0` — THREE independent unsatisfiabilities for a machine
  discharger: (1) `SegEntry.mem` pins the body-loop-head memory EQUAL to the
  dispatch-entry `m0`, but the route necessarily writes (callee-saved spills at
  1032/1048(sp), `env_new`'s fresh 32-byte Env + malloc metadata, the per-param
  `env_define` heap growth); (2) the post reuses the CALLER's `φf` unextended, but
  `CallClosureResid` ∀-quantifies `φf`, so the discharger would have to place the
  fresh machine Env at `φf(frame)` for EVERY `φf` — the fresh-frame address must
  come from an ∃-bound `PhiExtends` extension (exactly what `SegExit.store` and
  the mCall exit already do); (3) for `cd.body = []` the machine (bgtz a5
  @0x80003338 not taken → j 0x80003954) NEVER visits `callBodyLoopPC`/`callBodyRetPC`
  — the prefix≫IH≫suffix decomposition through those PCs has no machine run on the
  empty-body route (same through-PC disease as the amended scaffold `.some` motives).
  Same class for the zero-params route: `blez a5 @0x800032c8` bypasses the
  param-fold loop head, so any fold carrier pinning PC=0x800032dc is off-route
  at n=0.
- workaround: NONE bypassed — amending `CallClosureGeom` in place (wave37):
  `BodyHandoff` mid (`∃ φf' mB, PhiExtends … ∧ stack/arena frame to m0 ∧
  SegEntry@callBodyLoopPC over mB,φf'`), `ret` ∀-quantified over `(φf', mB)`,
  both guarded `cd.body ≠ []`, new `emptyBypass` field for the `[]` route;
  `callClosureSim`/row re-proved (body IH instantiated at `φf'`,`mB` — free,
  `mExecSeq` quantifies both). Zero outside consumers of `CallClosureResid`
  (grepped), so the amendment is contained to CallClosureRow.lean + wave37 files.
- cost: one wave of re-proof in CallClosureRow.lean; the falsity would otherwise
  surface only at discharge time (undischargeable residual = dead row).
- proposal: the recurring lesson is a LAW-shape: any Geom field that re-uses an
  ENTRY-pinned predicate (`SegEntry`-with-m0 / caller-φ) as an intermediate POST
  of an allocating route is wrong on arrival; mid-posts must ∃-bind (mem, φ) with
  a frame clause. Candidate gate rule: flag `Triple (SegEntry … m0) (SegEntry …
  m0)`-shaped fields whose route crosses a callee contract.

## 2026-09-01 assign-call-logical-stagepre-uniform (wave37 stagePre cuts)
- missing: no generator for the `ld+addi+sd → JalPreBundle` arm-head stagePre cut.
  `blockB_unary_stagePre` (2-step), `blockB_binary_leftStagePre` (4-step),
  `blockB_logical_stagePre` / `blockB_assign_stagePre` / `blockB_call_stagePre`
  (all 3-step `ld a2,off(a2) ; addi a0,sp,buf ; sd a3,0(sp) ; jal eval_expr`) are
  hand clones differing ONLY in the 5-tuple (arm PC, operand-load offset, sret
  buffer offset, jal target imm, callee bundle). The four per-PC `site_*_ee` site
  lemmas per arm are ALSO clones differing only in (PC, offset, encoding bytes).
- workaround: cloned `blockB_logical_stagePre` + `LogicalSites.site_*_lg` to the
  assign arm (`rows/AssignArmStagePre.lean`) and call arm (`rows/CallArmStagePre.lean`),
  both green + axiom-clean.
- cost: ~380 lines per arm (4 site lemmas ~200 + the 3-step chain ~180), verbatim
  modulo the 5-tuple. The remaining EEntryC-valued fields (stmtExpr/stmtRet/
  stmtVarInit/stmtIfCond/stmtWhileCond/flCond) are the SAME shape at exec/for arm
  PCs — 6 more clones owed. This REVIVES the gen_stagepre.py proposal the #14 agent
  deferred: the non-uniformity it feared (per-arm JalPreBundle conjunct list) is
  NOT real for the 3-step class — the conjunct list is IDENTICAL, only the 5-tuple
  and the site-lemma encodings vary.
- proposal: `scripts/gen_stagepre.py` over a `.toml` row
  {name, armPC, opLoadOff, bufOff, jalPC, jalImm, jalBytes, calleeBundle, node_pat,
   child_field} emitting the 4 site lemmas + the `blockB_<name>_stagePre` body +
   the `<Node>ArmDispatch` residual + `<field>_field_of_dispatch` composer. The
   3-step `ld+addi+sd` template is the invariant 95%; the site encodings come from
   `eval_expr_at_<PC>` (already generated) + the decode_<enc> lemmas (already exist).

## 2026-09-01 exec-stmt-stagepre-different-frame (wave37 exec-side assessment)
- missing: the exec-side stmt* stagePre cuts (stmtExpr/stmtRet/stmtVarInit/
  stmtIfCond/stmtWhileCond/flCond) are NOT the eval-side 3-step `ld+addi+sd → jal`
  shape. The exec stmtExpr arm (0x80004170) head is
  `ld a2,8(s0) ; addi a0,sp,16 ; mv a3,s3 ; mv a1,s1 ; jal eval_expr@0x80003164` —
  5 instrs, s0-based operand load, two `mv` moves, EXEC-frame buffer at sp+16 (the
  exec_stmt prologue does NOT lower sp by 1088). `JalPreBundle` pins the EVAL frame.
- workaround: NONE (deferred, out of the wave-allowed eval 3-step class).
- cost: each of the 6 exec/for stmt* cuts is a distinct 5-instr `_es`-site battery in
  the exec frame + an `ExecEntry`→`JalPreBundle` marshalling (via
  `execEntry_of_jalPrefix`, ArmSegSplitExec), not a clone of the eval 3-step template.
- proposal: a SECOND stagePre template for the exec class (5-instr `ld s0 ; addi ;
  mv ; mv ; jal`) parametrized on (armPC, opLoadOff, bufOff, jalPC, jalImm), feeding
  the exec-frame JalPreBundle marshalling. Separate from the eval gen_stagepre.py.

## 2026-09-01 callclosuregeom-entryfold-pcf-unsatisfiable (wave37 call crux, CallClosureRow.lean)
- missing: same independent-PC disease, second instance in the same structure:
  `CallClosureGeom.entryFold` ∀-quantified an ARBITRARY `pcf : Nat → Nat` and
  demanded a per-param `StoreSeg (pcf k) → StoreSeg (pcf (k+1))` Triple — for a
  garbage `pcf` the pre is satisfiable (StoreSeg pins only PC/StoreRepr/OutRepr)
  but no machine run advances the fold store, so the ∀-pcf field is
  unsatisfiable. It was also DEAD plumbing: `callClosureSim` never consumed it
  (the fold is absorbed into `entryBase`), exactly the amended scaffold-`.some`
  precedent (unsatisfiable AND dead ⇒ delete).
- workaround: NONE — field DELETED (wave37); the fold's named home is now the
  machine-honest `CallParamFoldInv` carrier + `storeChainList` composition in
  `rows/CallClosureSplice.lean` (concrete loop-head PC 0x800032dc, cursor/index
  register pins from the disasm).
- cost: none (no consumers); `closureParamsFold` (the storeChainList witness)
  stays, re-pointed at the splice carrier.
- proposal: gate-rule candidate: flag `∀ (pcf? : Nat → Nat)` /
  `∀ (p q : Nat)`-quantified PC arguments appearing INSIDE Triple-valued
  structure fields — independent-PC quantification over machine control points
  is wrong unless the predicate family is PC-agnostic.

## 2026-09-01 body-ih-no-caller-frame-slots (wave37 call crux, motive-family gap)
- missing: the `mExecSeq`/`SegExit` motive gives the body IH NO caller-stack
  discipline: `SegExit.memFrame` frames memory only OUTSIDE `[SL.lo, SL.hi)`,
  but the closure arm's caller-frame spill slots (`s5@1032(sp)`, `s3@1048(sp)`,
  `s7@1016(sp)`, `s6@1024(sp)`, the sret buffer `sp+144`, the body-block ptr
  spill `0(sp)`) are INSIDE SL. So `CallClosureGeom.ret`'s discharger cannot
  derive the spill slots' survival across the recursive body from the IH — the
  restore loads (`ld s3,1048(sp)` … in the retCopy seg) read values the motive
  does not pin. Every recursive arm with a post-IH restore has this gap
  (same class as seqfor-motive-rows "motives lack sp/ABI").
- workaround: kept `ret` as a NAMED residual field (law 2) with the gap
  documented on it; no motive change attempted (global M4-stack statement
  change, exec-side lane).
- cost: `ret`/`emptyBypass` (and every sibling arm's return seam) stay
  undischargeable until the motive family carries a stack-window clause.
- proposal: add to `SegEntry`/`SegExit` a per-call stack cursor `sp` with
  `SegExit` framing `[spBody, sp)` only (callee scribbles strictly BELOW the
  caller's frame) — the standard stack-discipline invariant; thread it once
  through TermSimAssembly's motives (the same amendment lane that fixed the
  scaffold p/q motives).

## 2026-09-01 exec-eval-stagepre-frameshift-and-nonuniform (wave38 exec-class verdict)
- missing: the 6 exec-eval EvalChildStages fields (stmtExpr/stmtRet/stmtVarInit/
  stmtIfCond/stmtWhileCond/flCond) produce `JalPreBundle child` but from
  `SEntryC`/`FEntryC` at exec_stmt/for_loop arm PCs. Two hard obstructions, both
  machine-confirmed from disasm this wave:
  (1) FRAME SHIFT: exec_stmt lowers sp by only 176 (`addi sp,sp,-176` @0x80003fe0),
      NOT 1088. `JalPreBundle` HARDWIRES `x2 = sp - 1088#64` + spill slots at
      sp-8..sp-32 + `subsret ∈ [sp-1088, sp-32]`. Satisfiable only by instantiating
      JalPreBundle's ghost `sp := (exec x2) + 1088` and then PROVING exec_stmt's own
      176-byte spill layout (ra@168 s0@160 s1@152 s2@144 s3@136) maps into the
      JalPreBundle spill-window fields `read64 mcall (sp-8/-16/-24/-32)`. That
      reconciliation is genuinely per-frame Lean, NOT a clone of the eval battery
      (blockB_assign_stagePre uses eval_expr's OWN sp-1088).
  (2) NON-UNIFORM HEADS: the exec-eval arm heads are NOT one shape. Surveyed:
      stmtExpr 0x80004170 `ld a2,8(s0);addi a0,sp,16;mv a3,s3;mv a1,s1;jal` (4-instr);
      0x8000403c `ld;mv a3,s3;addi a0,sp,80;mv a1,s1;jal` (mv/addi SWAPPED);
      0x800040d8 `ld a2,16(s0);beqz a2,…;mv a1,s1;mv a3,s3;addi a0,sp,104;jal` (has a
      NULL-CHECK BRANCH mid-head + 16-offset ld);
      0x80004120 similar with beqz; 0x800041e8 `ld;mv;mv;addi` (addi LAST);
      0x800042dc `mv a3,s3;mv a1,s1;addi a0,sp,16;jal` (NO ld — a2 preset);
      0x800044b4 (interp_run) s1-based entirely different. So even a generator
      would need a per-arm instruction-order + optional-branch + optional-ld schema.
- workaround: NONE (deferred; only the eval-side 3-step class was in scope + closed
  by gen_stagepre.py this wave).
- cost: each of the 6 is a distinct 4-5-instr `_es` site battery (mv reflection via
  addi rd,rs,0 + sign_extend 0) + the frame-shift reconciliation + (for 2 of them) a
  beqz null-branch peel. ~450-500 lines each, ~5 truly-distinct sub-shapes.
- proposal: a SECOND generator `gen_exec_stagepre.py` over a RICHER schema
  {armPC0, head = ordered list of {ld off | addi buf | mv rd rs} + optional leading
  beqz, jalPC, callee, node} feeding a shared `execFrameShift` lemma
  (`JalPreBundle` at `sp := x2+1088` from an exec_stmt-layout spill map). The
  frame-shift lemma is the reusable core; build it ONCE (hand, over stmtExpr), then
  the generator fans the head-order variants. Precondition: the frame-shift lemma
  must be proved feasible first (it is the real risk, not the mv sites).

## 2026-09-01 segentry-no-caller-spill-image (wave38 call crux, motive-family gap — the DUAL of body-ih-no-caller-frame-slots)
- missing: an ENTRY-side clause pinning pre-spilled caller-saved images in `m0`.
  The closure `ret` routes restore `s7` from `1016(sp)` (`ld s7,1016(sp)` at
  `0x800033b0` / `0x80003970`), but that slot was written at `0x800031cc` — the
  ARG-LOOP entry, BEFORE `callDispatchPC` — so its content (`= g x23`, the arm
  ghost's s7) is a fact about the ∀-quantified `m0`, underivable inside the
  `mCall` row: `SegEntry` links nothing between `m0` and `g`, yet
  `SegExit@callJoinPC.frame` demands `regs x23 = g x23` after the machine
  restores from `m0[sp+1016..]`.  For an (m0, g)-inconsistent instantiation the
  route lands the wrong s7 ⇒ the `ret` residual (and hence the closure `mCall`
  discharge) is unsatisfiable at full strength.  (`s5@1032`/`s3@1048` are FINE:
  spilled INSIDE the span, carried through `BodyHandoff`; only pre-span spills
  have this gap.)
- workaround: the wave-38 `ret`-route shape carries a NAMED premise
  `hS7Image : read64 m0 (sp+1016) = g x23`-shaped (doc'd at the field); no
  second global surgery attempted this wave (the sanctioned amendment was the
  exit-side stack-window clause).
- cost: the closure `ret` discharger stays conditional on one per-arm image
  premise; every arm whose restore slot predates its motive span will pay it.
- proposal: the ENTRY-side sibling of `stackScratchTop`: a table
  `entrySpillImage : Nat → List (Nat × Register)` (entry PC ↦ (sp-offset, ABI
  reg) pairs) + a `SegEntry` named field `spillImage` pinning
  `read64 m0 (sp+off) = (g R).toNat` for each tabled pair — vacuous (empty
  list) at untabled entry PCs, exactly the wave-38 pattern; producers of
  `SegEntry` at `callDispatchPC` (the arm-level `CallArmSpec` splice, which
  KNOWS the `0x800031cc` spill) supply it.

## 2026-09-01 genseg-jal-rows-zero-pin-loads (wave38 span (a) prep)
- missing: `scripts/genseg.py`'s `bridgeOfSeg`-shaped (jal) rows hardcode
  `lds = []` in BOTH the `ChainFacts` hypothesis and the `evalBlocks` normal
  form.  `MemFacts`' load pins are `bs.getD i 0#8` (BlockMem), so an empty lds
  entry pins the loaded bytes to ZERO — a loads-containing jal row (e.g. the
  committed `callClosureEnvNewCallBridge`, `ld a0,8(a3)` = cd->env ≠ 0) is
  UNDISCHARGEABLE as stated: its consumer must prove the pointer bytes are 0.
  The `segToTriple`-shaped rows are fine (lds is a real parameter there).
- workaround: the wave-38 hand span (`rows/CallClosureDispatchStage.lean`)
  threads `lds` parametrically through `bridgeOfSegFramed` (which already takes
  it); the Gen bridge rows with loads are left as-is (their jal seams are still
  named residuals, so nothing landed consumes the zero-pins yet).
- cost: every generated jal row whose body loads memory must be re-emitted
  with a parametric lds before its seam can be discharged; silent
  wall-at-discharge-time otherwise.
- proposal: genseg.py: emit `(lds : List (List (BitVec 8)))` as a binder on
  jal rows exactly as on segToTriple rows (the emitter already does it for the
  latter — one code path to unify).
- RESOLVED (2026-09-01, wave39, uncommitted): `emit_jal_row` now threads the
  `(lds : ...)` binder and replaced every literal `[]` (SegEvalState.init /
  ChainFacts / bridgeOfSeg / hjalSeam / conclusion).  Re-emitted the 5 affected
  Gen jal rows (AssignArmEntry/AssignArmStage/CallArmCalleeEval/
  CallClosureEnvDefineCall/CallClosureEnvNewCall — the only jal rows whose body
  loads memory); the other 3 jal Gen rows (ValueNullCall/DriveSpill/
  FnArmMallocCall) have no loads and were left.  Theorem names KEPT (statements
  only GAIN lds generality); all 5 + all 3 consumers (CallClosureSplice,
  CallClosureFoldStage, CallClosureDispatchStage) GREEN + axiom-clean.  Consumers
  reference the Gen `*Seg`/`*L` only (0 refs to the Gen `*Bridge`), so the
  zero-pin was latent, never yet discharged — no landed proof changed meaning.

## 2026-09-01 fnArmGeom-hArm-diagonal-phic-only (wave39 evalFnSim assembly)
- missing: `fnArmGeom_hArm_of_seam` (`FnArmGeomReduce.lean`) has ONE closures-map
  parameter `φc'`, used for BOTH the `EvalEntry` front (via `armEntry_widen`) and
  the `PreEpilogueV` exit.  It therefore only produces the DIAGONAL
  `Triple (EvalEntry … φc' …) (PreEpilogueV … φc' …)`.  But `FnArmGeom.hArm`
  (`ArmSpecBridge`) needs the OFF-DIAGONAL `Triple (EvalEntry … φc …)
  (PreEpilogueV … φc' …)` — entry at the PRE-alloc map `φc`, exit at the widened
  `φc'` (the closures array grows by one across the `.fn` arm).  `EvalEntry.store`
  = `StoreRepr … φc st.store` genuinely depends on the closures map, so the two are
  not defeq; the gap is a `StoreRepr … φc st.store → StoreRepr … φc' st.store`
  entry-rebase (φc ⊆ φc' over `st.store.closures.size`, the OLD store references
  no fresh index) — the closures-side analog of the φf-rebase in
  `CallClosureEnvNewMarshal` (`storeRepr … φf` through `PhiExtends φf φf'`).
- workaround: NONE landed.  `eval_fn_row` (the recursor hFn slot) ALREADY EXISTS
  and is green in `rows/CallRows.lean` (routes to `evalFnSimD` over `FnResid`); the
  hFn slot is filled.  The open work is the `FnResid` SUPPLIER (no provider yet):
  assemble `FnArmSpec` from the seam pipeline.  The whole pipeline is green MODULO
  this one entry-rebase + the two off-path bundles + hfr/hcl + EvalRecWiden.
- cost: without the rebase lemma, `fnArmGeom_hArm_of_seam` cannot feed
  `FnArmGeom.hArm` directly; any FnResid provider must either add the φc-entry
  rebase as a named premise or prove the one-closure StoreRepr mono.  Every future
  allocating-EvalE leaf (only `.fn` today, but the pattern) pays the same.
- proposal: `storeRepr_phic_mono : StoreRepr m N A φf φc s → PhiExtends φc φc'
  s.closures.size → StoreRepr m N A φf φc' s` (old store unaffected by a fresh
  closure index), OR generalize `fnArmGeom_hArm_of_seam` to two maps `φc`/`φc'`
  with an entry-rebase premise, so it produces `FnArmGeom.hArm` verbatim.
- RESOLVED 2026-09-01 (wave40, uncommitted): `Vsa/Sim/rows/StoreReprPhicRebase.lean`
  landed `storeRepr_phic_mono` — but the FULLY-GENERAL version is FALSE (a frame
  binding `.closure ca` with `ca ≥ s.closures.size` reads `φc ca` under `φc`,
  `φc' ca` under `φc'`, and `PhiExtends` says NOTHING at those indices → the two
  `ValueRepr`s can disagree). The honest lemma carries the well-formedness invariant
  `StoreClosuresBounded s` (named-field structure: every frame-value closure ref is
  `< s.closures.size` — it was returned by an earlier `allocClosure`). Under it,
  `storeRepr_phic_mono` holds: `ValueRepr` mentions `φc` ONLY in the `.closure` case
  and `PhiExtends` pins the bounded refs; every other `StoreRepr` field uses `φc` at
  indices `< size`. `hEntryRebase` is now DISCHARGED in `fnResid_of_pipeline_wf`
  (FnResidSupply.lean) via `(fun _ hsr => storeRepr_phic_mono hWF hpc hsr)`. Reusable
  by every future allocating-EvalE leaf. All green + axiom-clean.

## 2026-09-01 native-call-segentry-wrapper (wave39-native #49)
- missing: the native branch residuals `NativeAssertOkSpec` / `NativePrintSpec`
  / `NativePrintlnSpec` (`Vsa/Sim/EvalCallNative.lean`, `EvalCallPrint.lean`)
  are FULL `Triple (CallEntryP … callDispatchPC) (CallExitP … callJoinPC)` over
  the WHOLE spec-store representation (StoreRepr/OutRepr/memFrame/φ). Building
  them needs three abstractions that do NOT exist: (1) a native-entry-dispatch
  seam `CallEntryP → SegEntry(native arm)` (the `beq kind==5 taken` + arm ABI
  marshal, analogue of the closure `CallClosureDispatchStage`); (2) the `jalr a6`
  native-addr resolution lemma `ValueRepr (.native f) → read64 m (fvAddr+16) =
  N.addr f ⇒ a6 = N.addr f` (extract from StoreRepr — NOT yet a lemma; the only
  `N.addr` facts are injectivity in ValueEqualSpec/EqNeDispatchSeg); (3) the
  native-fn-body Triple as a StoreRepr/OutRepr-preserving span (assert:
  value_truthy+value_null, store+out unchanged; print/println: the char loop as
  a `Triple.loop` composing per-char HTIF `OutRepr` appends via
  htif_store_putchar + value_print's %lld render path).
- workaround: NONE — stopped. The per-site batteries EXIST and are ready
  (`NativeWrapperSites` `site_*_nw` for the 0x80003254 dispatch + 0x800039e0
  arm; `NativeAssertSites` `site_*_na` for the whole native_assert body;
  `Native_print`/`Native_println` code pins; `value_null_spec`/
  `value_truthy_spec` callee contracts). But the StoreRepr-preserving
  SegEntry→SegExit wrapper is the BULK — the same character/scale as the closure
  `Call` crux (waves 22-37), i.e. multi-wave, not one. Hand-threading it here
  would be exactly the "work beside a missing abstraction" the discipline
  forbids (Law 3).
- cost: if hand-rolled per-native: ~200-line bespoke SegEntry→SegExit machine
  Triple EACH (×3), plus a re-derivation of the shared dispatch/join wrapper 3×.
- proposal: factor the native-branch wrapper ONCE as
  `nativeArmSplice : (native-fn-body Triple over SegEntry(nativeArm)→SegExit at
  the arm return) → Triple (CallEntryP callDispatchPC) (CallExitP callJoinPC)`
  (the native analogue of the closure `callClosureSim` decomposition:
  entry-dispatch seam ≫ arm body ≫ join), + a standalone `nativeAddr_of_valueRepr`
  lemma (jalr a6 resolution). Then each native = the fn-body Triple only:
  assertOk ≈ value_truthy≫value_null leaf; print/println ≈ loopFromBody over the
  char loop with an OutRepr-append invariant (chain_out threading). With that
  wrapper the three contracts become instantiations, not bespoke builds.

## 2026-09-01 jalprebundle-spill-window-vestigial-so-execframeshift-EASY (wave40 execFrameShift core)
- missing: nothing — this is a POSITIVE finding that dissolves the wave-38
  frame-shift obstruction. `evalEntry_of_jalPrefix` (ArmSegSplit.lean:143-251)
  DESTRUCTURES `hslotRa/hslotS0/hslotS1/hslotS2` (the `read64 mcall (sp-8/-16/
  -24/-32)` spill-window facts) and `hspSLhi` from its `hpre` bundle but NEVER
  USES them: the child `EvalEntry.spill_defined` is built from REGISTER facts
  (`hx8_1`/`hs1_1`/`hx18_1` = the post-jal x8/x9/x18 values), not the memory
  slots. `landedN_eentryC_of_jalPrefix`/`landedN_eentryC_of_preBundle` just wrap
  `evalEntry_of_jalPrefix`, so those five JalPreBundle premises are DEAD for the
  divergence-fold entry.
- consequence: the wave-38 "FRAME SHIFT" obstruction (`exec-eval-stagepre-
  frameshift-and-nonuniform`) is NOT a blocker for the eval-CHILD exec fields.
  The exec_stmt arm (e.g. stmtExpr @0x80004170) calls eval_expr with x2 = the
  exec frame's own lowered sp (execSp-176), never lowering by 1088. Instantiate
  JalPreBundle's ghost `sp := execSp - 176 + 1088` so `sp - 1088 = execSp-176`
  matches the jal-time x2; the geometry facts (stackOK-ish bounds, operand
  ExprRepr @aOperand, StoreRepr survival over [SL.lo, sp)) are all satisfiable
  from ExecEntry's own geometry (ExecEntry.stackOK gives `176+1088` headroom).
  The five dead spill-window premises are discharged by ANY witness (the exec
  frame's ra/s0/s1/s2 slots at execSp-176+{168,160,152,144}, or trivially since
  they are never read). NO ExecJalPreBundle twin, NO per-frame spill-layout
  reconciliation needed — the wave-38 cost estimate (~450-500 lines/arm + frame
  reconciliation) was pessimistic because it assumed the spill-window was
  load-bearing.
- workaround: none needed; building stmtExpr end-to-end this wave to confirm.
- proposal: (a) prune the dead premises from `evalEntry_of_jalPrefix`/`JalPreBundle`
  in a future cleanup (they inflate every stagePre supplier); (b) the exec-eval
  stagePre generator over the non-uniform heads is now UNBLOCKED — the frame-shift
  core is a ghost re-parametrization, not a lemma.

## 2026-09-01 execframeshift-survival-window-is-a-named-premise-not-derivable (wave40)
- missing: `ExecEntry.store_survives` frames only `[SL.lo, sp_exec)` (the exec
  frame). `JalPreBundle` (instantiated with sp := esp+1088 = sp_exec+912) demands
  StoreRepr survival over the LARGER `[SL.lo, esp+1088)`, whose extra region
  `[sp_exec, sp_exec+912)` is the CALLER's frame — untouched by the exec arm but
  NOT covered by `ExecEntry.store_survives`. There is no lemma reducing the
  wide-window survival to the narrow one (the windows are not nested the tolerant
  way: an m' differing in [sp_exec, esp+1088) escapes ExecEntry's clause).
- workaround: carry the wide-window survival as a NAMED premise of the exec
  stagePre supplier (`blockB_stmtExpr_stagePre`), exactly as the eval side gets
  its `store_survives` window from `ArmEntryK`/`EvalEntry` (whose sp IS the frame
  top = JalPreBundle.sp). The M6 layout caller — which knows the full stack/arena/
  AST geometry — supplies it; StoreRepr survives ANY C-stack change because the
  store lives in the arena (disjoint from `[SL.lo, esp+1088)` via the arena
  disjunct `esp+1088 ≤ A.lo`, also a JalPreBundle field). This is NOT a workaround
  around a false goal — it is the correct layer for the fact.
- cost: each of the 6 exec-eval stagePre suppliers carries one wide-window
  survival premise (~1 line) + the arena/AST disjointness at esp+1088 (already
  JalPreBundle fields). Trivial vs the wave-38 estimate.
- proposal: a reusable `execEvalFrameSurvives` helper: from `ExecEntry`'s arena/
  AST/stack layout facts + `esp+1088 ≤ A.lo`, produce the wide-window StoreRepr
  survival via `storeRepr_agreeP` (all per-object footprints land in the arena/AST,
  disjoint from `[SL.lo, esp+1088)`). Build once; the 6 arms reuse. For THIS wave
  it is a named premise (the frame-shift core is proved; the survival helper is a
  separable follow-up).

## 2026-09-01 execframeshift-REAL-obstruction-is-jalSite-loaded-predicate-not-frame (wave40 CRUX)
- missing: `JalPreBundle.hjalSite` (and its consumer `evalEntry_of_jalPrefix`'s
  `hjalSite`) is typed `… → Eval_exprLoaded σ.mem → … ∃ Step firing the jal`.
  On the EVAL side the recursive `jal eval_expr` lives INSIDE eval_expr's own text
  (0x80003164..0x80003fe0), so `Eval_exprLoaded` supplies its 4 instruction bytes.
  On the EXEC side the `jal eval_expr` at 0x80004180 lives in exec_stmt's text —
  its bytes come from `Exec_stmtLoaded`, and 0x80004180 is NOT covered by ANY
  `eval_exprChunk`. So the `hjalSite` closure, given only `Eval_exprLoaded σ.mem`,
  CANNOT fire the exec-arm jal (`site_80004180_es` needs `Exec_stmtLoaded`). This
  is the ACTUAL blocker for the 6 exec-eval fields — NOT the frame offset (that is
  a ghost rebase, confirmed easy) and NOT the survival window (a named premise).
  MACHINE-CHECKED: grep shows 0x80004180 absent from Eval_exprLoaded's chunks;
  `site_80004180_es` consumes `Exec_stmtLoaded`.
- workaround: build an `ExecJalPreBundle` TWIN (identical to `JalPreBundle` but
  `hjalSite` typed with `Exec_stmtLoaded σ.mem`; the CHILD-entry field
  `Eval_exprLoaded mcall` stays — the child eval frame still needs eval text) + a
  variant marshalling bridge `execEvalEntry_of_jalPrefix` (a clone of
  `evalEntry_of_jalPrefix` passing `Exec_stmtLoaded` to the site) →
  `landedN_eentryC_of_execPreBundle`. The `*_split` corollaries
  (`stmtExpr_split` etc.) already reduce the field to `JalPreBundle e`; the twin
  needs a sibling `stmtExpr_split'` landing at `EEntryC` through the exec bridge.
- cost: ONE cloned bridge lemma (~110 lines, `evalEntry_of_jalPrefix` with the
  jalSite loaded-predicate swapped) + a thin `ExecJalPreBundle` def + a
  `landedN_eentryC_of_execPreBundle`. The 6 exec arm-head cuts then land at
  `ExecJalPreBundle` instead of `JalPreBundle`; everything else (frame rebase,
  survival premise, mv/ld sites) is as designed. NOT the ~450-line/arm wave-38
  estimate — the twin is shared across all 6.
- proposal: `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix` in a new
  `ArmSegSplitExecEval.lean`; the wave-38 `execFrameShift` core = (ghost rebase +
  survival premise + the loaded-predicate twin). Two of three pieces are trivial;
  the twin is the only real (but mechanical, shared) construction.

## 2026-09-01 segentry-spillimage-field-blocked-by-frozen-generic-producer (wave40 item 1)
- missing: the prescribed SEAT for the entry-side spill-image clause — a new
  named field on `Scaffold.SegEntry` guarded by a per-entry-PC table (the
  exact dual of the wave-38 `SegExit.stackWin`) — is UNLANDABLE this wave:
  `ArmSegSplitSeg.segEntry_of_jalPrefix` constructs `SegEntry` by structure
  literal at a ∀-QUANTIFIED `entryPC` (line ~95), so a mandatory contentful
  field cannot be supplied there without adding an
  `entrySpillImage entryPC = none` hypothesis (the wave-38 `segExit_extend`
  escape) — and `ArmSegSplit*` (plus the `SegPreBundle` plumbing in
  `ArmSegSplitNonEval` and its suppliers in `ArmStagesWave34`) is FROZEN
  (sibling-owned) this wave.  Structure-field defaults cannot rescue it (the
  vacuity proof needs the concrete PC).
- workaround: the SAME table + PC-indexed clause landed in
  `InductionScaffold.lean` (`entrySpillImage` / `gGpr` / `EntryImage`,
  vacuous-at-untabled-PCs, byte-level LE matching `CallerSpillSlots`), but
  SEATED as ONE hypothesis on the `mCall` motive BODY
  (`TermSimAssembly.mCall`: `EntryImage callDispatchPC g m0 → Triple …`) —
  signature-free (all recursor/TermCases references are fully applied, the
  scaffold-motive-independent-pq precedent); unfolding producers re-threaded
  (CallRows native rows intro-ignore; CallClosureRow threads it into
  `CallClosureGeom.ret`).
- cost: the clause is `mCall`-scoped, not `SegEntry`-global: a future arm
  whose restore slot predates its motive span (the class the ledger predicts)
  needs its own motive-body hypothesis until the field is hoisted; the
  eventual `CallArmSpec` supplier must supply `EntryImage` when instantiating
  the `mCall` IH (it can: it owns the `0x800031cc` spill).
- proposal: when the `ArmSegSplit*` freeze lifts, hoist `EntryImage` from the
  `mCall` hypothesis to a `SegEntry` field (the clause is already stated
  against `(entryPC, g, m0)`; the hoist is mechanical: add the field, give
  `segEntry_of_jalPrefix`/`SegPreBundle` the `= none` hypothesis, drop the
  motive hypothesis).

## 2026-09-01 evalchildstages-6-exec-fields-mistyped-JalPreBundle-amend-to-ExecJalPreBundle (wave40)
- missing: `EvalChildStages`'s 6 exec-eval fields (stmtExpr/stmtRet/stmtVarInit/
  stmtIfCond/stmtWhileCond/flCond) are typed `SEntryC … → LandedN 1 (JalPreBundle
  child)`, but the exec arm's `jal eval_expr` lives in exec_stmt text and can ONLY
  produce `ExecJalPreBundle` (the `Exec_stmtLoaded`-typed seam). So the fields are
  UNSATISFIABLE as typed (machine-checked: `JalPreBundle.hjalSite` demands firing
  the jal from `Eval_exprLoaded`, impossible at 0x80004180).
- workaround: AMENDED (Law 4 — mis-typed spec) the 6 fields in
  `Vsa/Sim/ArmSegSplitEval.lean` to `… → LandedN 1 (ExecJalPreBundle child)`, and
  switched their `armResidGap_evalChildFields` discharge from `stmtExpr_split`/… to
  the exec twins `stmtExpr_split'`/… (in `ArmSegSplitExecEval`). The OUTPUT type of
  `armResidGap_evalChildFields` (the conjunction of `→ EEntryC`) is UNCHANGED, so no
  downstream consumer is affected; only the 6 field SUPPLIERS change — which is
  exactly the exec stagePre suppliers this wave builds. The 8 eval-side fields
  (unary/binaryL/…/argsHead) keep `JalPreBundle` (their jal IS in eval text).
- cost: a contained structure amendment + import of `ArmSegSplitExecEval` into
  `ArmSegSplitEval`; the wave-34 partial builders (`evalChildStages_*_wired`) must
  re-type their 6 exec-eval `∀`-params from `JalPreBundle` to `ExecJalPreBundle`
  (mechanical). Sibling files that consume `armResidGap_evalChildFields`'s output
  are untouched.
- proposal: the exec-eval fields are structurally an exec-side family; a future
  refactor could split `EvalChildStages` into `EvalArmChildStages` (8, JalPreBundle)
  + `ExecArmChildStages` (6, ExecJalPreBundle). For now the in-place re-type suffices.

## 2026-09-01 argshead-exprrepr-of-head-arg-node-not-in-loopinv (wave41-argshead)
- missing: the `argsHead` field `AEntryC (e::es) → LandedN 1 (JalPreBundle e)` needs
  `ExprRepr mcall aOperand e` (the head arg NODE's repr) in its target `JalPreBundle`,
  but NEITHER `AEntryC` (ApproxArmReseat.lean:122 — bare `SegEntry ... argLoopPC`, no
  arg-node field despite the doc claiming "the abstract node fact carries the arg-list
  correspondence") NOR `CallArgLoopInv` (CallClosureSplice.lean:79 — carries the
  evaluated PREFIX `vsPre` slot reprs + the call `node` pointer, but NOT `ExprRepr` of
  the REMAINING arg nodes) carries it. The machine reads the head arg node from
  `16(s0)` (args array base) + `8*i` (0x800031dc `ld a2,16(s0)`; 0x800031e8 `add
  a2,a2,a4` with a4 = 8*i; 0x800031f4 `ld a2,0(a2)`) — so the head node addr is
  `read64(mem, argsArrayBase + 8*i)` and its `ExprRepr` is an ARG-VECTOR correspondence
  fact analogous to `EvalArgs`'s `ArgVecRepr` (but for the arg NODES, not the evaluated
  VALUES). This fact is genuinely upstream (established when the EX_CALL arm materialises
  the args-array pointer at 0x800031dc's `s0`), not projectable from either entry.
- workaround: name it as a field of the `argsHead` dispatch residual
  `ArgsHeadDispatch` (the analog of `CallArmDispatch`) — the residual bridges
  `AEntryC`'s bare SegEntry to `CallArgLoopInv (vsPre=[])` AND supplies the head-arg
  node's `ExprRepr` (+ the args-array read + its geometry). NOT a workaround that
  bypasses a law: it is the honest upstream (matching how `CallArmDispatch` supplies
  `ExprRepr … f` for the callee node). Consumed by `argsHead_field_of_dispatch`.
- cost: the arg-node `ExprRepr` correspondence stays a named premise until a future
  `ArgNodeVecRepr`-carrying arg-loop invariant subsumes it (would also serve
  `EvalArgs.cons`). One residual, doc'd.
- proposal: extend `CallArgLoopInv` with an `argNodes : ∀ i, i < n → ExprRepr mem
  (argsArrayBase + read...) (argExprs[i])` field (the arg-NODE-vector correspondence);
  then argsHead consumes it directly and `EvalArgs.cons`/`callArgs` reuse it. Deferred
  (would edit the crux-owned CallClosureSplice.lean structure — out of this lane).

## 2026-09-01 argshead-body-stagepre-is-bridgeOfSeg-not-site-battery (wave41-argshead)
- missing: prior notes (wave38 genstagepre ITEM 3) treated argsHead's body span
  (0x800031dc→jal@0x80003220, ~16 instrs) as needing a hand site_* battery like the
  3-instr arm heads (blockB_call_stagePre etc.). It does NOT: the body is a plain
  straight-line span ending in a jal — the LITERAL shape `bridgeOfSeg` (BridgeSeg.lean)
  factors ("straight-line body ≫ CALL"). The GEN `loopHeadArgSetupBridge` is the exact
  template. So argsHeadBodyBridge = #derive_case seg + bridgeOfSeg (one ChainOK decide),
  NOT 16 site lemmas. This is the discipline-correct route and it LANDED green.
- workaround: NONE needed — used the mandated abstraction. The only residuals are the
  JalPreBundle marshalling (ArgsHeadStagePre) + the AEntryC→loop-head dispatch
  (ArgsHeadDispatch), both honest named premises.
- cost: the JalPreBundle marshalling from bridgeOfSeg's GHolds/writeLog output is still
  per-arm (~150 lines, same shape as blockB_call_stagePre's last third), threading the
  arg-array reads as `lds` tied to CallArgLoopInv.node + the head-node ExprRepr.
- proposal: a `stagePreOfBridge` combinator — bridgeOfSeg output (GHolds out.regs +
  writeLog out.log + ABI frame at a jal PC) → JalPreBundle, parametrized by {aOperand
  projection, sret offset, the geometry side-condition list}. Would close argsHead's
  ArgsHeadStagePre AND re-seat blockB_call/assign/logical stagePre (the site-battery
  ones) on the seg layer. The geometry list is the non-uniform part (same blocker
  gen_stagepre hit); likely 1 template + regeneration. Flagged for coordinator.

## 2026-09-01 exec-mailmerge-5-arms-landed-no-generator (wave41 execmm, plan #2)
- missing: NOTHING new — the 5 exec-eval arm-head cuts (stmtRet/stmtVarInit/
  stmtIfCond/stmtWhileCond/flCond) are now LANDED by hand off the wave-40 model
  `blockB_stmtExpr_stagePre`, each riding the already-landed
  `execEvalEntry_of_jalPrefix` + `ExecJalPreBundle` bridge (`ArmSegSplitExecEval`)
  and the `*_split'` field splits. Files: `rows/StmtRetArmStagePre.lean`,
  `rows/StmtVarInitArmStagePre.lean`, `rows/StmtIfCondArmStagePre.lean`,
  `rows/StmtWhileCondArmStagePre.lean`, `rows/FlCondArmStagePre.lean` +
  `ExecCondArmSites.lean` (the if/while/for `_es` site batteries, which did not
  exist; stmtRet/stmtVarInit sites were already landed).
- workaround: NONE — this closes the class the obs
  `exec-eval-stagepre-frameshift-and-nonuniform` (wave38) deferred. Its two
  "obstructions" both dissolved: (1) frame-shift is the ghost `JalPreBundle.sp :=
  esp+1088` rebase, ALREADY solved in wave40's model; (2) non-uniform heads = just
  a per-arm 5-tuple {armPC0, ld-offset (8 vs 16), buf-offset, jal imm, mv/addi
  order} + optional beqz-nottaken peel (3 of 5 arms). Each blockB landed FIRST TRY
  from the model with only those knobs turned.
- cost: ~230-260 lines per arm blockB (~1250 total) + ~16 site lemmas (~600 lines).
  Verified `lake env lean` green + `#print axioms` ⊆ {propext,Classical.choice,
  Quot.sound} for all 10 theorems + all sites.
- proposal: gen_stagepre.py was NOT extended (CLAUDE.md mandate says extend IF ≥3
  heads uniform). VERDICT: heads are NON-uniform (instr order permutes, ld-offset
  varies, 3/5 have a mid-head beqz), and gen_stagepre.py targets a DIFFERENT shape
  (the EVAL 3-step `ld+addi+sd→jal` producing `JalPreBundle`, not the exec 4-6-step
  `ld[+beqz]+mv/mv/addi→jal` producing `ExecJalPreBundle`). A generator would need a
  full ordered-instruction-list + optional-beqz schema — more machinery than the 5
  one-shot instances. The TRUE shared abstraction is `execEvalEntry_of_jalPrefix` +
  `ExecJalPreBundle` (the frame-shift/marshalling bridge), which IS landed and IS
  reused by name in all 5. No code-gen template is justified here.
> divergence board: 13/14 (the 6th exec-eval field stmtExpr was wave40; these 5
  complete the EvalChildStages exec-twin fields modulo the per-arm dispatch
  residuals StmtRet/VarInit/IfCond/WhileCond/FlCondArmDispatch — the blockA→ArmEntryK
  bridge + child-payload/wide-window facts, same residual class as stmtExpr's
  StmtExprArmDispatch).

## 2026-09-01 naexit-lacks-abi-frame-clause (wave41-native #26)
- missing: `naExit` (`Vsa/Sim/EvalCallNative2.lean:220`) — the post of the
  landed `nativeAssertInternal` internal run — pins ONLY `x2 = fsp` among the
  callee-saved registers.  It has NO ABI-frame clause, although the machine
  fact is TRUE (the epilogue `0x80002e5c..0x80002e70` reloads ra/s0/s1/s2 from
  the frame spills, and no other callee-saved is touched) and the proof
  TRACKED every callee-saved value through all 33 sites (`hx8_1`/`hx9_1`/
  `hx18_1` chains) — the clause was simply not stated.  The `nativeArmSplice`
  join (`rows/NativeArmSplice.lean`) needs `NativeBodyPost.frame` (callee-saved
  except `s7` back to the ghost `g`) to rebuild `SegExit.frame` at `callJoinPC`.
- workaround: named typed premise `NativeAssertInternalAbi`
  (`rows/NativeBodyAssert.lean`) = the ABI-framed variant of
  `nativeAssertInternal` (same `naEntry`, post = `naExit` ∧ the
  `AbiPreservedNoise` tie to `g_na` re-established).  All other marshalling
  (naEntry construction, naExit → NativeBodyPost rebuild) is landed against it.
- cost: `nativeAssertOkSpec` stays conditional on this ONE premise; every
  future consumer of `nativeAssertInternal` needing a frame pays again; the
  print/println internal runs (unbuilt) must NOT repeat the omission.
- proposal: amend `naExit` with one clause
  `frame : ∀ R, AbiPreservedNoise R → c.σ.regs.get? R = g R` (naEntry already
  carries the same tie, so the amendment is ~1 line of statement + threading
  the tracked per-site register facts through the epilogue — the values are
  already in the proof).  EvalCallNative2 is outside wave-41 file ownership;
  coordinator amendment discharges `NativeAssertInternalAbi` verbatim.

## 2026-09-01 nonra-gpr-dispatch-duplicated-jal-jalr (wave41-native #26)
- missing: a factored "every GPR in 1..31 except rd survives one linking step"
  lemma over a class-generic `sigmaPost_*` observation.  `jalStep_of_obs`
  (BridgeSeg.lean) and the new `jalrStep_of_obs` (rows/NativeAddrResolve.lean)
  each carry an IDENTICAL 30-branch `match n` dispatch (obs_jal_other vs
  obs_jalr_other per GPR, 8 decides each) — only the obs consumer differs.
- workaround: mirrored the 30-branch block once more (second instance).
- cost: ~35 lines + 240 decides per future linking-step class (e.g. a
  jalr-to-non-x1-rd seam); two instances exist now — factor before a third.
- proposal: `nonRa_of_frame : (∀ R, (rd::noiseRegs)-avoidance → get? R = get? R)
  → ∀ n ∈ 1..31, n ≠ idx rd → gprGet-transport` over `StepFrameOut` (whose
  `of_alu/of_jal/of_jr` already package the per-class frame), so each class's
  JalStep glue is ONE StepFrameOut + one generic GPR-dispatch lemma.

## 2026-09-01 rowpost-drops-sailoutput-blocks-outrepr (wave42-cruxmarsh #4)
- missing: the `#derive_case`/`segToTriple` row `Post` shape (`GoodState ∧
  mem = writeLog ∧ PC ∧ GHolds`) DROPS the `σ'.sailOutput = σ.sailOutput` fact
  that `segEval_sound` proves and `segToTriple`'s internal `hpost` could carry —
  its signature simply omits it.  Every CallClosure* span row (FoldBack /
  RetClass / NormalJoin / BodyExit) is defined this way.  Re-assembling any of
  these row-Posts into `SegExit`/`SegEntry`/`CallParamFoldInv` (item-1 carrier
  marshalling) requires `OutRepr` at the new state, which `outRepr_of_sailOutput_eq`
  supplies ONLY from a `sailOutput` equation the Post does not expose.
- workaround: NONE yet — marshalling these Posts to a carrier needs the
  sailOutput carry; without it OutRepr cannot transport.  (A memory-only span
  never touches sailOutput, so the fact is TRUE, just not surfaced.)
- cost: without the carry, every carrier re-assembly lemma (there are ~6 seams
  in the crux tail alone, and this shape is every future span→carrier marshal)
  must re-derive sailOutput from scratch — but the row Post has discarded the
  witness, so it is UNDERIVABLE at the Post; the fix must be at the Post/`hpost`.
- proposal: add `c.σ.sailOutput = σentry.sailOutput` (or directly an
  `OutRepr c.σ st → OutRepr` transport clause) to the row `Post` defs and thread
  `segEval_sound`'s `hout` through `segToTriple`'s `hpost` (ONE extra hypothesis;
  additive — existing `hpost` callers ignore it).  Then a `segExit_of_rowPost`
  combinator marshals any memory-framed row Post + transported StoreRepr into
  `SegExit` uniformly.

## 2026-09-01 notwritten-frame-clauses-not-stepframeout (wave42-nativefin #1)
- missing: the per-callee `NotWritten*` frame clauses (`NotWrittenT`
  value_truthy, `NotWrittenV` value_null, `NotWrittenVE`/`NotWrittenVEStr`
  value_equal, ...) are ad-hoc ∧-towers of `(rd == R) = false` diseqs, NOT
  `StepFrameOut`-shaped, so composing a callee sub-run into a whole-run
  `StepFrameOut` chain needs a hand adapter per callee (build the write-set
  list, re-derive each conjunct from the `∀ r ∈ W` avoidance).
- workaround: wrote the two adapters inline in `nativeAssertInternal`'s exit
  frame (`sfoT`/`sfoN`, ~8 lines each, 10/9 `hav _ (by decide)` conjuncts).
- cost: ~8 lines + one membership `decide` per conjunct, per callee spec
  consumed inside any whole-run frame; two instances now (truthy/null), a
  third appears the moment another `value_*` callee is threaded through a
  framed run (value_print/value_equal in the print body are next).
- proposal: `stepFrameOut_of_notWritten (W : List Register)` — one lemma per
  `NotWritten*` family (or restate the families as `∀ r ∈ W, (r == R) = false`
  in the first place) so a callee spec's frame clause IS a `StepFrameOut W`
  and sub-runs splice into `chain_frame_out` folds with zero adapter code.

## 2026-09-01 native-fnbody-marshal-shape (wave42-nativefin #2)
- missing: ONE parametric "callee-internal-run contract → NativeBody boundary"
  marshal.  Wave 41's `nativeBodyAssert` (naEntry construction + naExit→Post
  rebuild) and wave 42's print/println legs are the same proof shape.
- workaround: wave 42 factored the OUTPUT pair once (`nativeBodyOut` in
  `rows/NativeBodyPrint.lean`, parametric over `outApp`/entry PC/`Extra` —
  print and println are instances), but `nativeBodyAssert` still stands on its
  own bespoke `naEntry`/`naExit` ∧-tower boundary instead of the named-field
  `NativePrintEntry`/`NativeFnOutExit` pair.
- cost: the assert sibling duplicates ~80 lines of boundary rebuild; any
  fourth native (or a reseat of assert) pays it again.
- proposal: reseat `naEntry`/`naExit` on `NativePrintEntry`/`NativeFnOutExit`
  (outApp := "", plus assert's truthy/argc extras in the `Extra` rider) and
  retire `nativeBodyAssert`'s bespoke marshal onto `nativeBodyOut`.

## 2026-09-01 nonevalchild-jal-exec_stmt-arms-uniform (wave43 lane nonevalmm, plan #6)
- missing: no generator for the NonEvalChildStages jal-exec_stmt staging arms. The
  4 SEntryC-landing fields (stmtIfThen/stmtWhileBody/stmtForInit/for-body) share ONE
  shape: #derive_case seg (straight-line arm head: some mv/ld setup) + bridgeOfSeg
  (jal exec_stmt @0x80003fe0) + IfThenArmHeadInv/IfThenArmStagePre/IfThenArmDispatch
  residual trio + `*_field_of_dispatch` composer landing at ExecStmtPreBundle. They
  differ ONLY in: (a) body instr list, (b) jal callPC/link, (c) the child-node read
  offset (ld a1,16(s0) etc.), (d) the parent Stmt ctor + spec-side hyps in the field.
- workaround: hand-write each from the argsHead/StmtIfThen template (~110 lines each,
  landed FIRST TRY). stmtIfThen LANDED (rows/StmtIfThenArmStagePre.lean).
- cost: ~110 lines × 4 arms; but each is a mechanical rename of the template, one
  ChainOK decide, no new theory. The residuals (StagePre marshalling + Dispatch) stay
  named premises identically shaped — a future consumer discharges the 4 uniformly.
- proposal: extend gen_stagepre.py with a `jal-exec_stmt SEntryC` template class
  (5-tuple: seg-instr-list TOML + callPC/link + read-offset + child Stmt selector),
  emitting the seg+bridge+trio+composer — OR (cheaper) a Lean macro
  `#nonEvalStmtArm <name> <seg> <callPC> <link>` generating the trio+composer over a
  supplied seg/bridge. The 7 SegPreBundle-landing fields are a SECOND uniform class
  (segEntry_of_jalPrefix, interior j/b control) deserving its own template.

## 2026-09-01 layout-dispatch-slot-pins (wave43 layoutgen, plan#5 leg1 — LANDED)
- missing: NONE (this is an abstraction-landed note, not a gap). The per-arm
  jump-table slot pins (`KindSlotPinned k armPC m`) were being carried as premises
  per leaf/arm row down to the M6 Layout, one hand-decoded `.rodata` byte battery
  per tag (int carried via EvalEntry.int_slot; bool/null/var/str each a bespoke
  `*SlotPinned` theorem).
- workaround: NONE. Extended `scripts/gen_layout.py` to read the whole 11-slot
  dispatch table (base 0x80019f58) from the ELF and emit `groundSlot_0..10` (one
  `KindSlotPinned k armPC m` per ExprKind tag) into `rows/LayoutJumpTableGen.lean`,
  self-verifying (lake+sorryAx+axiom-audit) with an arm-PC cross-check against the
  9 known anchors. `fnSlot_grounded` (rows/FnArmSeamSupply) consumes groundSlot_10
  for the fn arm.
- cost: paid ONCE (generator run). Any arm still threading its own hand `*SlotPinned`
  can now be reseated on `groundSlot_<k>` (slots 5 EX_ASSIGN + 6 EX_BINARY were
  previously unpinned and are now covered too).
- proposal: reseat the existing bespoke `BoolSlotPinned`/`NullSlotPinned`/
  `VarSlotPinned`/`StrSlotPinned` theorems (EvalBoolSim/EvalNullSim/EvalVarSim/
  EvalStrSim) onto the generated `groundSlot_<k>` and delete the hand decodes; add
  `gen_layout.py`'s dispatch-pin output to CLAUDE.md's generator row.

## 2026-09-01 ifstmt-then-else-tail-redispatch-not-jal (wave43 lane nonevalmm, plan #6)
- missing: the `.ifStmt` then/else arms do NOT recurse via `jal exec_stmt`. In the
  binary (`experiments/disasm.txt`, if-arm @0x800041e8), after eval cnd + value_truthy,
  the TRUE branch does `ld s0,16(s0); j 0x80004014` (reload s0:=then-node, JUMP back to
  the dispatch-loop head @0x80004014, post-prologue) — a TAIL re-dispatch in the SAME
  frame, NOT a fresh `jal exec_stmt`. The FALSE branch (@0x800042cc region) similarly.
  So `NonEvalChildStages.stmtIfThen`/`stmtIfElse` land at `ExecStmtPreBundle t`/`e`
  (which REQUIRES a `jal exec_stmt` callPC with hjaltgt callPC+jalImm=execStmtEntry) —
  but the machine reaches the then/else child via a `j` to 0x80004014 (interior
  post-prologue re-entry), reusing the frame. The `ExecStmtPreBundle` bundle's
  jal-site premise is thus NOT the literal machine shape for if-then/else.
- workaround: NONE yet for if-then/else. Only landed the arms that genuinely `jal
  exec_stmt`: stmtWhileBody@0x80004074 (loops back via bne). The other 3 jal-exec_stmt
  sites (0x800041c4=block/seq iter, 0x80004254=for?, 0x800042b8=for-body?) still to map.
- cost: if-then/else fields (2 of 11) need either (a) a SegPreBundle-style twin that
  lands at the 0x80004014 re-dispatch head with s0:=child-node (a DIFFERENT bridge:
  `j`-terminated, target=dispatch head, same frame — the exec_stmt prologue is skipped),
  or (b) an amendment to the field type to reflect tail re-dispatch. The `landedN_
  sEntryC_of_preBundle`/`ExecStmtPreBundle` machinery assumes a fresh jal+prologue.
- proposal: a `ExecStmtTailPreBundle`/`execEntry_of_jTailRedispatch` twin: `j
  0x80004014` (dispatch head, post-prologue, same sp) with s0:=child-node StmtRepr →
  SEntryC child (the prologue already ran; SEntryC's ExecEntry needs sp lowered +
  spill slots, which the CURRENT frame already has since it's a tail call at the same
  depth). This is the honest machine shape for if-then/else (and likely block-seq).
  Surfaced per Law 4 — NOT worked around with a false ExecStmtPreBundle attribution.

## 2026-09-01 nonevalchild-remaining-8-shape-map (wave43 lane nonevalmm, plan #6)
- missing: a per-arm machine-shape map for the 8 unlanded `NonEvalChildStages` fields
  (+3 SqEntry +flStep) showing WHY each does not fit its declared pre-bundle target.
  The 3 that DO fit (`stmtWhileBody`@jal 0x80004084, `stmtForInit`@jal 0x80004254,
  `flBody`@jal 0x800042b8) landed cleanly as straight-line-seg + bridgeOfSeg to
  `jal exec_stmt` + 2 named residuals (`rows/Stmt{WhileBody,ForInit}ArmStagePre.lean`,
  `rows/FlBodyArmStagePre.lean`, all green+axiom-clean, wired in
  `nonEvalChildStages_wave43_wired`). The OTHER 8:
    * `stmtIfThen`/`stmtIfElse` — TAIL re-dispatch (`ld s0,16/24(s0); j/bnez 0x80004014`),
      NOT `jal exec_stmt`. Target `ExecStmtPreBundle` (needs fresh jal+prologue) is the
      WRONG shape. (already filed: `ifstmt-then-else-tail-redispatch-not-jal`.)
    * `stmtWhileLoop` — loop RE-ENTRY of the same while node via `bne a0,a5,0x80004034`
      (0x8000408c), a backward branch to the loop-head block, NOT a fresh jal exec_stmt.
    * `callArgs`/`argsTail` — land at `SegPreBundle argLoopPC` (arg loop head
      0x800031dc); reached by post-f-eval fallthrough / `j`-back, NOT a jal whose
      target IS argLoopPC. `SegPreBundle` (via `segEntry_of_jalPrefix`) hardcodes a
      jal-site premise (`callPC+jalImm=entryPC`) — the arg loop head is an INTERIOR
      fallthrough/branch target, no jal jumps to it.
    * `callC` — lands at `SegPreBundle calleeBodyPC`; the callee body is entered by
      `jalr` (closure dispatch), not a `jal` with static imm=entryPC — again the
      SegPreBundle jal-site model does not match `jalr`.
    * `stmtForLoop`/`flLoop` — land at `SegPreBundle forCondPC` (for-cond 0x8000426c),
      reached by `j 0x8000426c`/step-`j`, a branch target not a jal target.
    * SqEntry `stmtBlock`/`callBody`/`seqHead` — land at `SqLoopHeadPreBundle` =
      `SegEntry @interpLoopHeadPC(0x8000448c) + Reflect c' env ss`. Needs the `Reflect`
      abstraction WITNESS (crux/IterSeam boundary, plan #4), plus a SegEntry at an
      interp_run loop head reached by branch — not a jal twin. The ArmSegSplitNonEval
      doc itself flags these as "NOT a bare jal→SegEntry".
    * `flStep` — evaluates the for STEP expr via `jal eval_expr`@0x800042e8 in the
      EXEC frame (sp-176), but `flStep_split` (ArmSegSplitEval) hardcodes target
      `JalPreBundle` (sp-1088 eval-frame convention). The exec-frame step arm needs
      the wave-41 ghost re-parametrization (sp:=esp+1088) landing at `ExecJalPreBundle`
      + `execEvalEntry_of_jalPrefix` — but the split combinator wants plain
      `JalPreBundle`. SEAM MISMATCH: flStep_split's pre-bundle type is eval-frame, the
      machine arm is exec-frame. (like the wave-38 exec-eval-frameshift, unresolved
      for flStep because the combinator target is not ExecJalPreBundle.)
- workaround: NONE — did not force false pre-bundle attributions (Law 4). Landed only
  the 3 genuine jal-exec_stmt arms (prior session; re-verified green+axiom-clean).
- cost: the 8 remaining fields stay `∀`-premises of `nonEvalChildStages_mk` /
  `divFamily_of_armStageComponents`; the divergence board stays at its wave-42 count
  for the non-eval side + 3 fields wired. Each unlanded arm needs a NEW bridge shape
  (j-tail-redispatch to dispatch head; branch-entry SegEntry; jalr-callee SegEntry;
  exec-frame JalPreBundle re-parametrization) or a field-type amendment — statement
  surgery, not template instantiation.
- proposal: (a) `execEntry_of_jTailRedispatch` twin (j to 0x80004014 post-prologue,
  same frame) for if-then/else + stmtWhileLoop; (b) a `segEntry_of_branchEntry` /
  `segEntry_of_jalrEntry` variant of `segEntry_of_jalPrefix` dropping the static-jal
  premise for the 4 SegPreBundle interior arms; (c) flStep_split re-typed to
  `ExecJalPreBundle` (or a dedicated `flStep_split'` twin) so the exec-frame step arm
  composes via `execEvalEntry_of_jalPrefix`; (d) the Reflect witness (plan #4) for the
  3 SqEntry fields. All four are one small statement-shaped item each — the same
  cadence as the 3 landed arms, but each needs a new named twin first.

## 2026-09-01 callparamfold-carrier-n-unreachable (wave 43, lane cruxdefine — the 8th statement falsity)
- missing: a machine-honest fold-exit seam. `callClosureEntrySplice`'s premise
  family (`rows/CallClosureSplice.lean`, wave 37) demands `hFoldSeam : ∀ k < n,
  Triple (carrier k) (carrier (k+1))` and `hFoldToHandoff : Triple (carrier n)
  (BodyHandoff)`, with `carrier k` pinned at the loop-head PC `0x800032dc`. The
  params-fold is a DO-WHILE (disasm 3358-3384): the head is entered exactly n
  times (k = 0..n-1); after the LAST `env_define` the back-edge
  `bne s6,a5 @0x8000331c` compares `8·n` with `8·n` and FALLS THROUGH to
  `0x80003320` — `carrier n` (PC = head) is never reached, so the k = n-1 seam
  is machine-undischargeable and `hFoldToHandoff`'s source is dead.
  Machine-checked obstruction: `foldBackLoop_facts_last_false` /
  `foldDefineReturn_last_false` (`rows/CallCruxMarshal3.lean`) — the loop-row
  `ChainFacts` at the last param is UNINHABITED (its bne-TAKEN guard reduces to
  `8·(k+1) != 8·(k+1) = true`).
- workaround: NONE — amended within-wave (Law 4, 8th precedent):
  `hFoldSeam` re-ranged to `k + 1 < n` (the mid-loop back-edges) and
  `hFoldToHandoff` re-sourced at `carrier (n-1)` (the LAST iteration owns
  staging ≫ env_define ≫ exit-polarity back-edge ≫ value_null ≫ body entry);
  composition via `storeChainList` at `n-1`. No downstream consumers existed
  (grep: comments only).
- cost: the `hFoldToHandoff` supplier now carries one full fold iteration
  (staging + env_define + exit row) instead of a bare exit hop — that is the
  machine truth, not an artifact.
- proposal: none needed beyond the amendment; `callParamFoldSeamStep`
  (CallCruxMarshal2 §5) already discharges exactly the amended `k+1 < n` range
  (its `FoldDefineReturn` is uninhabited at `k+1 = n`, consistently).

## 2026-09-01 segexit-frame-preepilogue-x8-unrestored (wave 44, lane normalroute)
- missing: `SegExit @ callJoinPC` (= `CallExitP`, `CallEntry.lean`) states its
  `frame` field `∀ R, AbiPreservedNoise R → c.σ.regs.get? R = g R` at
  `exitPC = callJoinPC = 0x800033ec`, but that PC is the FIRST instruction of
  the shared eval_expr epilogue (`0x800033ec ld ra,1080(sp) ; 0x800033f0 ld
  s0,1072(sp) ; 0x800033f4 ld s2,1056(sp) ; 0x800033f8 mv a0,s1 ; 0x800033fc
  ld s1,1064(sp) ; 0x80003400 addi sp,+1088 ; 0x80003404 ret`).  The callee-
  saved restores (ra/s0/s2/s1/sp) run AFTER `callJoinPC`, so at the join NONE of
  them equal `g R` yet.  The `.normal` route reaches the join via
  `callClosureNormalDepthBridge ≫ value_null ≫ callClosureNormalJoinRow`
  (`0x80003954..0x80003974`), which restores ONLY s3/s5/s7 (x19/x21/x23) — it
  does NOT restore x8 (s0, `= AbiPreserved`, `= AbiPreservedNoise`).  On the
  body loop x8=s0 is the ExecSeq loop counter (`0x80003344 addi s0,s0,1`), so at
  `callJoinPC` x8 = the body statement count, NOT `g x8` (the caller's EX_CALL
  node ptr, `CallArgLoopInv.node`).  Hence `SegExit.frame` at `callJoinPC` is
  UNSATISFIABLE for x8 on the normal route — and equally for ra/s1/s2/sp, all
  restored only inside the epilogue.  THE 9TH STATEMENT FALSITY.
- workaround: NONE.  Landed the machine-checked obstruction
  `segExitJoin_frame_x8_false` (`rows/CallCruxMarshal5.lean`, Law 4): from a
  `SegExit @ callJoinPC` whose `frame` pins x8 and the route fact `x8 = cnt`
  with `g x8 = node`, `cnt ≠ node` ⇒ False.
- root cause: the skeleton `SegExit` (InductionScaffold.lean) was designed with a
  post-epilogue register frame (mirroring `EvalExit`, whose `pc` is the
  RETURNED-TO target `BitVec.update (r+..) 0`, i.e. AFTER `ret`), but
  `CallExitP`/`motive_*` instantiate `exitPC := callJoinPC` = the PRE-epilogue
  join.  The exit PC and the frame clause disagree about whether the epilogue
  has run.
- proposal (amendment, analogous to the wave-38 `stackWin` guard): either
  (a) move the `Call`/EX_CALL exit PC PAST the epilogue to the RETURNED-TO caller
  target (the `EvalExit.pc` shape — but the skeleton has no `r` return-addr
  ghost), OR (b) restrict `SegExit.frame` to the registers ACTUALLY restored at
  a PRE-epilogue join.  Recommended: keep `exitPC = callJoinPC` and weaken
  `frame` to a tabled `joinRestored : Nat → Register → Bool`-guarded clause
  (parallel to `stackScratchTop`/`stackWin`): at `callJoinPC` the restored set is
  {s3,s5,s7} (the normal route) resp. the ret route's set, NOT all AbiPreserved.
  The full callee-saved restoration is the epilogue's job, provable ONLY at the
  returned-to config — which is where the CALLER's arm (`armTail`/`EvalExit`)
  already re-establishes `g`.  So the join `SegExit.frame` should pin only the
  registers the join itself restores (x2 anchor via the untouched-sp fact, plus
  s3/s5/s7), and the epilogue closes the rest at the caller boundary.

## 2026-09-01 lwu-missing-from-block-decoder (wave44 valueprint lane, value_print dispatch head)
- missing: `MKind`/`decodeM` (Vsa/Sim/BlockMem.lean + BlockDecode.lean, the
  block-reflection layer that `#derive_case`/SegEval runs on) has NO `lwu`
  case (LOAD group covers only lw=funct3-2, ld=3, lbu=4; lwu=6 is absent). The
  value_print dispatch head at 0x80002908 is `lwu a5,0(a0)` (reload the
  ValueKind unsigned) — the FIRST body instruction of the jump-table span, so
  the whole dispatch head cannot be a `#derive_case` seg as-is. (The DecodeTable
  lemma for the word 00056783 EXISTS — this is purely the SegEval MKind gap,
  the same class as the wave-38 `xori` addition.)
- workaround: NONE yet (stopped at the seg build). Semantically `lwu` here =
  `lw`: the kind is < 6 so the loaded 32-bit value is non-negative and zero-
  vs sign-extension agree; but SegEval's `runGM`/`wvalM` have no `.lwu` arm to
  even fold, so I cannot silently substitute `.lw` in a `#derive_case` block
  (mkLine derives the kind from the word via decodeM, which returns `none` ⇒
  the block falls to the `.addi 0 0 0` junk default and the seg VC is wrong).
- cost: every jump-table dispatch that reloads an unsigned sub-word (value_kind
  dispatch is the idiom — value_print here, and value_equal/value_kind_name use
  the SAME `lwu a5,0(a0)` at 0x80002908-adjacent addresses) hits this. Until
  `.lwu` lands in MKind, these dispatch heads must be hand `Steps` chains
  (the ValueEqualSpec.lean legacy idiom) instead of segs — exactly the
  regression CLAUDE.md's header warns against.
- proposal: add `MKind.lwu` (coordinator-level, mirrors the wave-38 xori add):
  decodeM LOAD `funct3=6 → some (.lwu, rd, rs1, 0, immI)`; wvalM/astOfM `.lwu`
  = zero-extend the 32-bit load (astOfM → instruction.LOAD lwu shape); runGM
  reads the same `lds` positional bytes as `.lw` but zero- not sign-extends;
  ldsRunM consumes one load like `.lw`; ChainFacts decode leaf uses the
  existing DecodeTable lemma. Then value_print's dispatch head is a clean seg.

## 2026-09-01 snprintf-frame-generic (wave44 errsegs lane, SnprintfContract probe)
- missing: a FORMAT-GENERIC snprintf frame/footprint contract. The only landed
  snprintf spec (`snprintf_lld_spec`, SnprintfSpec42) is the byte-EXACT `"%lld"`
  capstone (fixed format 0x800192c0, renders intToString). `SnprintfContract`
  (JmpSpec.lean:1450) needs snprintf's frame property (writes ⊆ [dst,dst+n),
  jmp_buf [inp+16,inp+128) preserved, output-neutral, ghost frame) for TWO calls
  in `runtime_error` (0x80002dc8, 0x80002de4) whose formats are the caller-inherited
  fmt and a fixed non-%lld fmt 0x80019318 — NEITHER is %lld.
- workaround: NONE (did not build SnprintfContract; out of the errseg decode lane's
  scope). Documented the 4-piece breakdown in experiments/logs/wave44-errsegs.md.
- cost: whoever discharges SnprintfContract (M3/error-tail lane) must either
  (a) re-verify snprintf twice at two non-%lld formats byte-exactly (enormous, and
  the byte content is UNUSED — the post only needs footprint disjointness), or
  (b) invent the frame contract from scratch.
- proposal: `SnprintfFrameContract (dst n : BitVec 64) : Prop` = "snprintf(dst,n,·,·)
  terminates leaving GoodState/tick/minstret, writes only within [dst.toNat, dst.toNat+n),
  is output-neutral (sailOutput unchanged), and preserves NotWrittenJmp regs" — a
  format-AGNOSTIC frame lemma. The footprint reasoning already exists inside
  snprintf_lld_spec's residual ledger; factor it OUT of the byte-exact rendering so
  both the %lld capstone and the two runtime_error calls consume the SAME frame fact.

## 2026-09-01 armdispatch-class-split (wave44-armdispatch)
- missing: the "12 open `*ArmDispatch` residuals" are NOT one class.  Only 7 are
  jump-table-dispatch-dischargeable (rich-entry-headed: `AssignArmDispatch`/
  `CallArmDispatch` off `EvalEntry` + the five `Stmt*ArmDispatch` off
  `ExecEntry`) — all 7 are now DISCHARGED by the two wave-44 combinators
  (`evalArmDispatch_of_slot`/`execArmDispatch_of_slot`, rows/ArmDispatchCombinator*).
  The other 5 (`FlCondArmDispatch`, `FlBodyArmDispatch`, `WhileBodyArmDispatch`,
  `ForInitArmDispatch`, `ArgsHeadDispatch`) are headed by `FEntryC`/`AEntryC` =
  `SegEntry` ∃-packs at a GHOST interior `entryPC` (`InductionScaffold.SegEntry`
  pins only PC/store/out/frame/budgets — no node address, no arg-reg ABI, no
  StmtRepr), so there is NO machine run a slot pin could drive: the missing
  general fact is a RICHER interior-entry predicate (or per-interior-PC
  `SegEntry → arm-head` seg rows) — the standing SegEntry-opacity gap, not the
  dispatch-ladder gap.
- workaround: NONE (stopped; the 5 stay named residuals).
- cost: any future "arm-dispatch fan-out" plan that counts these 5 into the
  slot-combinator class will re-discover this; the divergence/loop lanes pay
  the SegEntry enrichment instead.
- proposal: enrich `SegEntry` (or land per-interior-point twins: forCondPC /
  argLoopPC entries with GHolds + node-addr fields, like `FlBodyArmHeadInv`
  already is) and route the 5 through `LandedN 0` re-packagings; the wave-43
  `*ArmHeadInv` defs are the model.

## 2026-09-01 blockA_k-x13-loss-now-parametric (wave44-armdispatch)
- missing: `blockA_k`/`ArmEntryK` still drop the liveness of `a3`(x13) at the
  arm entry (dispatch never writes a3; ArmEntryK's frame covers only
  callee-saveds).  Already noted per-arm by `BinArmExtras.x13_pres`; wave 44
  generalizes the SAME closure into `EvalArmHeadExtras.x13_pres` (parametric in
  armPC) rather than fixing blockA_k, because appending a conjunct to the
  LANDED `ArmEntryK` ∧-tower breaks every positional destructure downstream.
- workaround: the named `x13_pres` closure field (one per Group-A extras
  record, shared by assign/call).
- cost: one un-machine-checked liveness premise per eval composite arm, until
  a blockA_k widening (or an ArmEntryK named destructurer + appended field +
  one rebuild) lands.
- proposal: an `blockA_k_x13` twin concluding `ArmEntryK ∧ (∃ w, x13 = some w)`
  (21 `obs_*_other'` threads, mechanical), or the ArmEntryK-tower-to-structure
  refactor R6 already wants.

## 2026-09-01 lookupG-evalBlocks-value-peel-missing (wave44 lane bridgetwins)
- missing: a peel lemma for reading a COMPUTED CONSTANT register value out of a
  symbolic-pin `evalBlocks` fold: `lookupG n (evalBlocks bs (SegEvalState.init L
  lds)).regs = some <closed value>` when `x n` is written only by closed-operand
  instructions (`li`/`auipc`/`addi rd,rd,imm`). Symbolic `by rfl` blows the
  elaborator (stack overflow / maxRecDepth even at 100000 — the `sign_extend` of
  a negative 12-bit imm plus the auipc fold whnf's through Int on 2^64-scale
  literals); `by decide` is blocked by the free ghost pins elsewhere in the list;
  the ∃-extraction trick (`⟨_, rfl, by decide⟩`) leaves the value term still
  mentioning the symbolic `stepGM` tower, so it is not closed. The existing peel
  layer (`srcVal_runGM_ne`/`srcval_peel`, SegFrameFactsAuto) peels PRESERVED pins
  through `runGM` bodies, not WRITTEN-constant values through `evalBlocks` chains.
- workaround: rows keep their posts GHolds-abstract (the landed wave-43 row
  shape) and machine-check the constant at a GROUND instantiation
  (`stmtIfThenTail_a4_computed` in `rows/StmtIfThenArmStagePre.lean`: ghosts:=0,
  one kernel `decide`, ~1s). The symbolic `x16 = 8` case DOES close `by rfl`
  (small positive imm — no Int churn), so shallow constants stay in posts.
- cost: consumers of a row's computed-constant registers (here the
  `ExecDispatchEntry.a4 = stmtJumpTableBase` staging) must re-derive the value
  from `GHolds` + the ground lemma + a ghost-independence argument, per site;
  every future row whose span rematerializes an `auipc`-based table pointer
  (jump-table dispatch heads) pays again.
- proposal: `lookupG_evalBlocks_const (n) (bs) (h : writersOf n bs are
  closed-operand) : ∀ L lds, lookupG n (evalBlocks bs (SegEvalState.init L
  lds)).regs = lookupG n (evalBlocks bs (SegEvalState.init [] [])).regs` — the
  ghost-independence peel (structural induction like `srcVal_runGM_ne`, never
  reducing the fold), composed with ONE ground `decide` on the pin-free fold.

## 2026-09-01 segopacity-two-subclasses-fieldlevel (wave45-segopacity)
- missing: SHARPENS `armdispatch-class-split`. The 5 SegEntry-opacity residuals
  are TWO sub-classes with DIFFERENT missing facts (the wave-44 entry lumped
  them). (1) OPAQUE-entry — `ArgsHeadDispatch`/`FlCondArmDispatch`/
  `FlBodyArmDispatch` off `AEntryC`/`FEntryC` = bare `SegEntry`
  (fields verified: good/tick/pc/store/out/mem/frame/depth_budget/arena_budget
  ONLY). The arm-head bundle (`CallArgLoopInv`) needs argc(a5)/idx(a6)/env(a3) —
  CALLER-saved, not even ghost-pinned by `AbiPreservedNoise` — plus node(s0)/
  interp(s2) tied to SEMANTIC arg-array/interp values (not the ghost `g`), plus
  the head-arg `ExprRepr` and `argc = (e::es).length` (pure arg-vector facts,
  zero `SegEntry` source). `SegEntry → CallArgLoopInv` is machine-grounded
  NON-DERIVABLE. (2) RICH-entry — `WhileBodyArmDispatch`/`ForInitArmDispatch`
  off `SEntryC` = `ExecEntry`@`exec_stmt`-entry `0x80003fe0`; the arm-head at
  `0x80004074`/`0x80004248` needs the recursive cond-eval + `value_truthy`
  branch (or env_new + init-load) SPAN, which is unbuilt M4 arm-seg content
  (grep-verified: no landed seg/bridge/Steps spans `0x80003fe0 → 0x80004074`).
  ALSO checked (this was an explicit wave-45 hypothesis): the crux marshal
  carriers `CallCruxMarshal2-4` are the CALLEE param-define fold
  (`CallParamFoldInv`), NOT the arg-EVAL loop head — they do NOT produce
  `CallArgLoopInv`, so `ArgsHeadDispatch` is NOT unblocked by them.
- workaround: NONE (stopped; landing enriched-carrier+adapter pairs in owned
  `rows/SegOpacity*.lean` would only RELOCATE the ∃-pack — the enriched premise
  needs its own producer with the same missing facts; Law 3 "5 near-identical
  carriers = factor first"). No file created.
- cost: any wave-46 "route the 5 through enriched carriers" plan that puts the
  carrier in a NEW rows/ file re-discovers that the fix must land at the entry
  DEFINITION or the entry PRODUCER (both non-owned): `AEntryC` def enrichment /
  `callArgs_field_of_dispatch` pin-threading for Args; `FEntryC`→for-cond-arm-
  head twin (ExecArmEntryK) for FlCond; the M4 while/for arm spans for
  FlBody/WhileBody/ForInit.
- proposal: (Class 1) an `ArgLoopEntry`/`ForCondEntry` twin of `AEntryC`/
  `FEntryC` carrying `CallArgLoopInv`/`ExecArmEntryK` (not `SegEntry`), threaded
  from the producer that HAS the pins (`CallArgsSetupInv` already carries
  store/out/budgets at `0x800031d8`; extend it with the arg-loop reg pins + head
  `ExprRepr` and stop collapsing to `SegEntry`). (Class 2) the recursive-arm
  span segs (`SEntryC → cond-jal`, `value_truthy-nonzero → body-head`) belong to
  the divergence/loop lane, keyed on the already-given `EvalE`/`allocFrame`
  hypotheses spliced via callSeg/BridgeSeg.

## 2026-09-01 io-contracts-buffering-falsity (gen_fn de-risk pass, main session)
- missing: a stream-state abstraction between the IO contracts and
  `Vsa.Machine.output`. The three wave-44 contracts in
  `rows/ValuePrintContract.lean` (FprintfLldContract/FwriteContract/
  FputsContract) post `Vsa.Machine.output c.σ = out0 ++ frag` at RETURN, but
  `output` = raw `String.join σ.sailOutput.toList` and stdout is LINE-BUFFERED
  (`_isatty`@0x80000110 is `slti a0,a0,3` → 1 for fds 0-2 → newlib `__SLBF`,
  malloc'd buffer via `__swsetup_r`/`__smakebuf_r`): `fputs("null",stdout)`
  returns with the bytes in the FILE buffer, NOT in sailOutput. The contracts
  are unprovable as stated — latent falsity #10, found statically before any
  proof consumed them.
- workaround: NONE (stopped; statement amendment required before Lane-1 fan-out).
- cost: if unamended, every gen_fn-derived summary for the fputs/fwrite/fprintf
  DAG would contradict the named contracts mid-splice — a stalled-lane class
  bug (cf. the reverted wave-45 amendment lanes).
- proposal: `StreamRepr` named-field structure (FILE flags/buf base/pos/end read
  off the static `_impure_ptr` reent + the pending byte string) + `conOut σ S =
  output σ ++ S.pending`; re-state the three contracts as `conOut' = conOut ++
  frag`; per-line flush facts from `__sfvwrite_r`'s `memchr '\n'` arm; the
  endToEnd output claim is UNAFFECTED because `exit`@0x80004764 drains the
  buffer (`__call_exitprocs` then `jalr a5` = reent `__cleanup` → `_fflush_r`
  → `__swrite`) so `pending = ""` at the final state.

## 2026-09-01 mkind-io-census (gen_fn de-risk pass, main session)
- missing: 13 MKind cases the io DAG needs — census over
  _write/_write_r/__swrite/_putc_r/_fputc_r/__sfvwrite_r/_fputs_r/_fwrite_r/
  shims/__swsetup_r/__smakebuf_r/_fflush_r/__sflush_r/locks/__sinit/std/
  _cleanup_r: andi×52 lh×30 sh×15 lui×14 lhu×13 ori×11 or×5 and×5 addw×4
  srai/sraiw/srl/srliw×1. Even `_write` (the HTIF leaf) uses `or`; `__swrite`
  uses lh/sh/lui/and/andi. Pseudo-ops covered (mv/li/sext.w/not/negw/zext.b).
- workaround: NONE (prerequisite D0 of experiments/gen-fn-tooling-plan.md).
- cost: without it, every io-DAG seg attempt fails at decodeM; per-site
  StepObs hand batteries (the snprintf-era regression) would be the only path.
- proposal: mail-merge clone of the xori/slliw/lwu precedents
  (BlockMem constructor + decodeM branch + astOfM + width/fold rows + rfl
  example; lh/lhu/sh = width-2 twins of exec_lbu_bm/exec_sb_bm).

## 2026-09-01 stringify-bool-doc-swap (probe pass 2, main session)
- missing: ELF-byte ground-truthing for doc-comment address↔literal claims.
  `rows/StringifySpec.lean`'s bool-arm doc said "true"@80019010 /
  "false"@80019008; objdump .rodata shows 19008="true", 19010="false" (both
  the stringify AND value_print bool arms default a1/a0=19010 and reassign to
  19008 on the fall-through = true case). Doc FIXED in place; no machine
  statement carried the swap yet — but any prover writing byte pins from the
  prose would have produced falsity #11.
- workaround: n/a (doc corrected; ELF bytes recorded in gen-fn-tooling-plan.md).
- cost: a stalled amendment lane, had it reached a statement.
- proposal: gen_layout.py/gen_image_pins.py-style generators as the ONLY
  source for literal-address pins (never prose); extend gen_image_pins.py
  expected-bytes table to cover the value_print/stringify literal pool.

## 2026-09-01 wentry-width-set-hardcoded (gen_fn D0 mail-merge, mkind agent)
- missing: a single named predicate for the reflected write-log entry width set.
  `wlogM_width` (LoopStep.lean:77) and its duplicate `wlogM_widths`
  (SegFrameFactsAuto.lean:175) state every `WEntry` width `= 1 ∨ = 4 ∨ = 8`,
  and that disjunction is threaded VERBATIM (rcases arms + typed ascriptions)
  through BlockAdapter.lean:34/51/72, SegFrameFactsAuto.lean:319,
  ReprStackSurvival.lean:118/159/171, BlockLogic.lean:574,
  rows/EvalEqNeFront.lean:102, rows/EvalDivRow.lean:126.  Adding the width-2
  store kind `.sh` (proven: experiments/probe-sh-width2.lean) falsifies both
  theorems as stated; there is no per-arm fix.
- workaround: NONE (agent stopped per Law 4 and reported the obstruction);
  amendment {1,4,8}→{1,2,4,8} being landed as a dedicated synchronous pass.
- cost: ~8-file synchronous edit per width addition, forever, until named.
- proposal: `WEntryWidthOK : Nat → Prop` abbrev (or a `widths` list constant)
  used by wlogM_width + every consumer, so a new store width is a one-line
  change + the new `writeMapN` disjoint branch.

## 2026-09-01 goodstate-htif-tohost-overpin (HtifStepObs putchar Step layer, htif-stepobs agent)
- missing: a `GoodState` that survives the console-putchar tohost store.
  `GoodState.htif_tohost` (Vsa/Sim/GoodState.lean:49) pins the VALUE
  `some (BitVec.ofNat 64 tohostAddr)` (= 0x8001ad00, the post-init value),
  but the machine's putchar transition (mem_write_value_tohost_putchar,
  Vsa/Sim/HtifLift.lean:187) ends its insert tower with
  `htif_tohost := zeros (n := 64)` (= 0#64). So GoodState is provably FALSE
  after the first putchar store — machine-checked as
  `not_goodState_sigmaPutcharFinal` in Vsa/Sim/HtifStepObs.lean. No consumer
  ever uses the pinned value: every HTIF store lemma takes
  `hth : … htif_tohost = some th` with th ARBITRARY (HtifLift putchar/exit,
  probe, ErrorTail). The pin was never exercised because the only previously
  proven tohost store (exit) HALTS in the same stepOnce.
- workaround: NONE forced; delivered everything except the `GoodState σ'`
  conjuncts: stepOnce/Step/stepObs putchar lemmas land WITHOUT the GoodState
  clause (tick_clock_char inputs derived from GoodState σ through the write
  frame instead of GoodState of the post-state), plus the falsity proof.
- cost: `stepObs_tohost_putchar` cannot re-establish the loop invariant's
  GoodState conjunct; every _write-loop consumer is blocked on the amendment;
  wrappers must be revisited (one-line each) once GoodState is amended.
- proposal: amend `GoodState.htif_tohost` to `∃ v, σ.regs.get? Register.htif_tohost = some v`
  (presence-only, exactly like mip/mtime/…); consumers change from
  `hG.htif_tohost` to `obtain ⟨th, hth⟩ := hG.htif_tohost` (all already
  th-generic). Then `goodstate_sigmaPutcharFinal` + the GoodState conjuncts
  here become the standard insert_nonpinned/frame proof.

## 2026-09-01 isnonpinned-htif-tohost-stale (HtifStepObs GoodState re-add, sandbox /tmp/vsa-probe)
- missing: post-amendment (`GoodState.htif_tohost` now `∃`-shaped), `Frame.lean`'s
  `isNonPinned` still classifies `htif_tohost` as pinned, so
  `GoodState.insert_nonpinned` cannot be chained through the putchar tower's two
  `htif_tohost` inserts (no single-insert `GoodState` preservation lemma for
  `htif_tohost`).
- workaround: `goodstate_sigmaPutcharFinal` in `Vsa/Sim/HtifStepObs.lean` is a
  field-by-field `constructor` proof (untouched fields via the
  `get?_sigmaPutcharFinal` 7-diseq frame, touched `∃`-fields via explicit
  witnesses), instead of a 10-link `insert_nonpinned` chain + `of_regs_eq` like
  `goodstate_sigmaPost_store`.
- cost: ~140 lines / ~190 decides once in HtifStepObs; ANY future lemma that
  inserts into `htif_tohost` (other HTIF mailbox stores) pays it again.
- proposal: when the GoodState amendment lands in main, also move `htif_tohost`
  from the pinned match-arm of `isNonPinned` to nonpinned and flip
  `insert_nonpinned`'s `htif_tohost` case from `P` to `E`; then
  `goodstate_sigmaPutcharFinal` collapses to the standard insert chain.

## 2026-09-01 chain-facts-no-op-after-have (gen_fn P1 fold, main session)
- missing: robustness (or a loud failure) in `chain_facts` (ChainFactsTac.lean)
  when ANY tactic step precedes it: with a `have` in the local context the
  tactic SILENTLY leaves the whole `ChainFacts` goal untouched (no error), so
  downstream bullets hit the unsplit goal with baffling defeq failures.
  Minimal repro: cf-mem3 probe — `have hx : (1:Nat) = 1 := rfl` before
  `chain_facts hcode with ...` → 0 leftover-goal descent; without the have →
  full descent to the MemFacts leaf. Also fires when the loaded-image
  hypothesis itself is have-bound (`have hcode := hg.code`).
- workaround: call chain_facts as the FIRST tactic; pass the loaded-image
  hypothesis as a lemma PARAMETER; move all `have`s after it (into the
  leftover-goal bullets).
- cost: ~90 min of blind bisection this session; will recur for every gen_fn
  facts lemma author.
- proposal: make cfSolve fail loudly when it closes nothing, and fix the
  underlying local-context sensitivity (likely the walker's use of the goal's
  mvar context when applying generated lemma names).

## 2026-09-01 seg-guard-close-symbolic-pins (gen_fn P2, FnWriteRFold)
- missing: a seg_guard_close variant whose tail is caller-supplied instead of
  `<;> decide` — guards over SYMBOLIC pins (here `beq a0,a5` with a0 = ghost
  `len`) reduce fine under its simp-set but cannot be decided; also a
  packaged "seg log is empty ⇒ writeLog collapses" brick (`rfl` directly on
  `writeLog (mImage g) segLog = mImage g` native-overflows the unifier when
  the memory is itself a writeLog def — it unfolds both sides into
  ExtHashMap internals).
- workaround: inlined seg_guard_close's fixed simp-set + manual finish
  (rw computed-literal + beq_eq_false_iff_ne + the fact); added local
  writeLog_nil + per-seg `<seg>_log_nil : (evalBlocks …).log = [] := rfl`
  lemmas and rw-chained them before the mem field.
- cost: ~12 lines per symbolic-pin guard and 3 lines + 1 rw-chain per
  store-free seg, re-paid by every gen_fn fold with a branch twin or a
  read-only seg over a reified store image (every call-wrapper P2-shape fn).
- proposal: `seg_guard_reduce` (the simp-set, no decide tail, leaves the
  reduced comparison) in SegReadback; `segLog_nil`-emission in gen_fn.py per
  store-free seg + a `mem_of_framedPost_nilLog` one-liner in
  SegToTripleFramed.

## 2026-09-01 io-buffering-falsity-RETRACTED (empirical run, main session)
- missing: nothing — CORRECTION of `io-contracts-buffering-falsity` above,
  which is WRONG. `main.c:155` is `setvbuf(stdout, NULL, _IONBF, 0)` — the
  FIRST statement of main (jal setvbuf@0x800058c0 at 0x800045ac): stdout is
  explicitly UNBUFFERED in this binary. EMPIRICALLY CONFIRMED in the Sail
  model (lean_riscv_emulator on /tmp-built test ELFs; proof ELF untouched,
  sha256 b146c6ed… verified): `print(1); <runtime error>` emits "1" BEFORE
  the stderr message (immediate visibility); `print(7)`+clean-exit emits "7";
  all four value_print arms emit exact expected bytes ("truehi3false\n").
  The wave-44 contracts' `output = out0 ++ frag`-at-return posts are TRUE.
- workaround: n/a. StreamRepr/conOut amendment CANCELLED (plan b item 0
  rewritten). The io contracts' precondition instead pins the stdout FILE
  state as left by main's setvbuf (__SNBF; part of the main-init image the
  induction already parameterizes).
- cost: none incurred — caught before any proof consumed the wrong amendment.
  LESSON: static libc-source reasoning about runtime configuration is not
  evidence; the emulator harness (exact model, ~10s/run) is, and is now the
  t5 falsity-tester mechanism.
- proposal: t5 recipe = craft .wl → build ELF in a /tmp COPY of c/ (NEVER in
  c/ — proof ELF is sacred, keep the sha256 guard) → lean_riscv_emulator →
  compare sailOutput/exit. Test every RUN-1-consumed statement this way.

## 2026-09-01 field-claims-empirical-sweep (t5 harness, main session)
- missing: nothing — POSITIVE sweep results, recorded so RUN-1/RUN-2 lanes
  know these statements are empirically grounded (t6.elf, exact model):
  StrConcat "ab"+"cd"→"abcd"; String order "a"<"b" T, "ab"<"b" T, "a"<"ab" T,
  "b"<="a" F, "x"=="x" T (strcmp-sign ↔ String.lt DIRECTION CONFIRMED for the
  order bridge); anonymous closure print → fwrite "<fn>"@0x800192d0 4B (the
  inner-beqz route, covered by FwriteContract); hDivOv: INT64_MIN/-1 prints
  -9223372036854775808 (wrap CONFIRMED); (-7)%3 = -1 (tdiv-parity ✓);
  runtime-error exit code 70 ✓ ("FAILURE: 70", t4).
- workaround: n/a.
- cost: n/a.
- proposal: keep /tmp/wl-test + the t*.elf battery as the standing t5 corpus;
  extend with a case per RemainingWork field before RUN 2 assembly.

## 2026-09-01 bridge-row-ra-pin-unfillable-hRaOut (t2 genseg framed emission)
- missing: a bridgeOfSeg/bridgeOfSegFramed variant for spans that READ `ra`
  (spill prologues: `sd ra,k(sp)` forces `x1` into the entry pin list L, so
  `1 ∈ keysG (evalBlocks …).regs` and the row's `hRaOut : KeysAvoidRa out.regs`
  is FALSE — the jal overwrites x1, so `gholds_of_jal` rightly refuses).
- workaround: none needed for the live span — the gen_fn P2 fold
  (rows/FnWriteRFold.lean) covers `_write_r`'s prologue via segRowFramed + a
  separate stepObs_jal seam; the t2 regression artifact
  (scripts/arms/writeRPrefixFramed.toml) emits the framed row anyway as a
  compile-shape exercise (green + axiom-clean, hypothesis vacuous, .lean not
  kept).
- cost: any future jal-terminated span that spills `ra` cannot use the bridge
  rows at all and must fall back to the fn-fold shape; nothing warns at
  emission time.
- proposal: `bridgeOfSegRa` (or a `dropKey 1` pre-pass in bridgeOfSeg[Framed])
  that deletes the stale x1 binding from the exposed out-bundle instead of
  demanding `KeysAvoidRa`; plus a genseg-side warning when reg 1 is pinned on
  a jal arm.

## 2026-09-01 leaf-resid-forall-ghost-falsity (fleet B1-leaves, hInt/hNull/hBool/hStr)
- missing: the geometry-conditioned leaf-residual supplier layer. The four
  `TermResidualsCore` leaf fields (`hInt`/`hNull`/`hBool`/`hStr`, skeleton holes
  `SkelH{Int,Null,Bool,Str}`) ∀-close their `*LeafResid` over ALL layout ghosts
  (`g N A SL φf φc sp r sret m0` and, for null/bool/str, an unconstrained
  `c : Config`) with a bare conjunction body. The `TermBundles.lean` assembly
  table assigns every leaf `TermShared.geom : ImageGeom N A SL` (G-class), but
  the statements carry NO such premise, and the TSV-named supplier `GeomFrom`
  does not exist anywhere in `Vsa/` (only the `TermAssembly.lean` doc comment).
  Consequences, machine-checked in
  `experiments/fleet/obstructions/B1_leaves_obstructions.lean` (green,
  axiom-clean, 1.6s):
  * `SkelHNull`/`SkelHBool`/`SkelHStr` are **FALSE** (`skelH*_false`): each
    residual asserts its sret-vs-`value_*`-code disjointness conjunct for
    ARBITRARY `sret`; `sret := 0x800027f0 / 0x80002800 / 0x80002820` (inside
    the respective code windows) refutes them outright — no machine
    construction needed, both disjuncts fail by `decide`.
  * `SkelHInt` is unprovable as stated: its body is
    `LeafWiden = Widen (EvalExit …) … (stackFoot SL)` whose `pres`/`surv`
    quantify over EVERY `EvalExit` config; `EvalExit` is exactly the predicate
    that forgets both (its `memFrame` leaves `[SL.lo,sp) ∪ A` ∪ sret-padding
    presence unconstrained; `StoreRepr.frames_arena` places frames in `A` with
    nothing relating `A` to `[SL.lo,SL.hi)` for ∀-ghosts). `skelHInt_of`
    machine-checks the exact gap = two named premises `IntLeafPres`/`IntLeafSurv`.
- workaround: NONE (stopped per Law 4; obstruction file + this entry).
- cost: the whole B1 batch (4 fields) blocked; every other batch whose Resid
  ∀-closes geometry conjuncts over ghosts (e.g. B5's `BrkResid` asserts
  `StmtSlotPinned k armPC m0` for arbitrary `m0`, false at `m0 = ∅`) will hit
  the same wall.
- proposal: amend the `*LeafResid` statements to take the geometry as premises
  (`ImageGeom N A SL` + a populated-`m0`/write-chain fact, the `hMcallPop`
  analog) — the rows already destructure the conjuncts, so the amendment is
  local to `rows/TermRouting.lean` defs + the skeleton regen; OR re-land the
  leaf sims at `EvalExitD` directly (the writeMap chain inside
  `evalIntSim`'s proof knows `pres`/`surv`; the abstract `EvalExit` does not),
  making the widener residual disappear entirely.

## 2026-09-01 b2-resid-fields-refutable (fleet B2-unary-logic worker)
- missing: an entry-linkage hypothesis in the ∀-closed `TermResidualsCore`
  Resid fields. `NegResid`/`NotResid`/`OrTrueResid`/`AndFalseResid`/
  `OrFalseResid`/`AndTrueResid` (rows/TermRouting.lean) quantify over ALL
  ghosts (`N A SL sp r sret aEnv aExpr a* m0`, and for the logical four an
  unconstrained `c : Config`) with only the two operand `read64`/`ExprRepr`
  hypotheses, yet their conclusions (`NegExtras` etc.) demand entry-only
  geometry: `sp_headroom : SL.lo + 3264 ≤ sp.toNat`, `op_lo`, the
  `KindSlotPinned` static-image pins, and `hMcallPop` (total `m0` at
  `mcall := m0`). Nothing supplies these — the holes are REFUTABLE, so
  `TermResidualsCore L` is uninstantiable as stated.
- workaround: NONE (per law 4). Landed machine-checked refutations instead:
  `Vsa/Sim/rows/Field_hNeg.lean` (`field_hNeg_refuted`, shared witness
  `b2WitMem` = 24-byte concrete ExtHashMap with two `.null` nodes) + sibling
  `Field_hNot/hOrTrue/hAndFalse/hOrFalse/hAndTrue.lean` consuming it, each
  via `sp_headroom` at `sp = 0#64`.
- cost: the whole B2 batch (and, by the same shape, likely B1's LeafWiden
  `pres`/`surv` fields and every other ∀-closed Resid) cannot go green until
  the field statements are amended; every fleet worker on these fields will
  rediscover this.
- proposal: amend each Resid to take the entry as a hypothesis — e.g.
  `∀ …, EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv
  aExpr m0 c → … → NegExtras … ∧ …` (the rows already HAVE the entry config
  in scope at the consumption site, cf. `eval_neg_row`'s `hc`), or split each
  Extras into (a) Layout-derivable static pins (`KindSlotPinned` from
  `Loaded L`) + (b) an ArmEntryK widening supplied by `blockA_k`, as the
  NegExtras doc comment already anticipates. Precedent: Trichotomy
  falsity → amendment (`Vsa/While/StmtDispatch.lean`).

## 2026-09-01 exec-resid-slot-pins-uninhabited (fleet B5-execarms)
- missing: the exec-side residual bundles (`ExecCaseGeom`, `ExecExprGeom`,
  `ExecRetGeom`, `ExecRetNullGeom`, `ExecVarNullGeom`, `ExecVarInitGeom`,
  `IfNoneGeom`, `WhileFalseGeom`, `IfTrueGeom`, `IfFalseGeom`) put
  `StmtSlotPinned k armPC m0` (and the table/stack disjunct) UNCONDITIONALLY
  under a ∀-quantified `m0 : Mem` (and ∀ SL/sp) in the `*Resid` defs consumed
  by `TermResidualsCore.hS*`.  At `m0 = ∅` the slot-pin's byte lookups are
  `none`, so every such `*Resid` — hence every skeleton hole
  `SkelHSExpr/…/SkelHSIfFalse` and hence `TermResidualsCore L` itself — is
  PROVABLY FALSE (machine-checked: `Vsa/Sim/rows/B5ExecArmObstructions.lean`,
  `skelHS*_false`, 11 fields).  The slot pin (and disjointness) must be
  CONDITIONED on the pinned image (byte-pin premises per `gen_layout.py`'s
  `groundSlot_k` idiom, or a `Loaded L`-derived hypothesis on `m0`) — i.e. the
  residual statement needs amendment; a worker cannot land these fields.
- workaround: NONE — falsity proofs landed as the machine-checked obstruction
  (Law 4 precedent: Trichotomy), fields skipped.
- cost: all 14 B5 fields blocked; B1-B4/B6-B8 fields whose residuals embed the
  same unconditional-∀-m0 slot-pin/glue shape are equally uninhabited
  (eval-side `KindSlotPinned` twins should be audited before those batches
  burn time).
- proposal: amend the `*Geom`/`*Resid` layer to take the jump-table byte pins
  as named premises (the `groundSlot_k` supplier shape) or restate the
  residual ∀ over `m0` satisfying a named `RodataPinned m0` predicate; then
  the wave-43 generated pins discharge `hslot` and only `hGlue` remains open.

## 2026-09-01 loop-geom-self-referential-oracles (fleet B5-execarms)
- missing: `BlockGeom`/`ForStartGeom`/`WhileGeom` (fields `hSBlock`,
  `hSForStart`, `hSWhileBreak`) have no slot pin but demand the loop knot
  itself as unconditional ∀-ghost oracles: `hstep : ∀ …, ExecSeqStep …` /
  `ExecForStep …` / `ExecWhileStep …` over ALL `stM/m00/out00/stMid/stFin/
  status` (arbitrary, unlinked to any derivation), and `hWhileIH`/`hForIH` =
  the FULL while/for statement simulation Triple.  Supplier would be the
  statement-sim capstone being assembled — self-referential; no landed lemma
  can discharge them field-wise.
- workaround: NONE — skipped with this named obstruction.
- cost: 3 B5 fields undischargeable until the Geom layer threads the loop IH
  from the recursor (as the eval-side `armResidGap_of_stages` does) instead of
  demanding it ∀-ghost-closed inside the residual.
- proposal: restate the loop Geoms with the IH/step oracles as per-derivation
  premises (recursor-supplied, like `mExecS` minor-premise IHs), not
  ∀-quantified fields of the residual.

## 2026-09-01 seq-motive-independent-pq-no-code (fleet B6-loopseq)
- missing: any dischargeable form of the `mExecSeq` motive Triple
  (TermSimAssembly.lean:178): it quantifies entry PC `p` and exit PC `q`
  INDEPENDENTLY while `SegEntry` (InductionScaffold.lean:150) pins no code
  byte — so the off-diagonal (`ofNat p ≠ ofNat q`) span is unprovable from
  the hypothesis set (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.{zeroStep_segSpan_forces_pc_eq,
  skelHSeqNil_offdiag_must_step}`).  The `TermAssembly.hSeqNil` supplier note
  ("`execSeqNil` seg-identity, `_row` wrap trivial") is stale — identity
  suppliers cover only the diagonal.  This is the `scaffold-motive-independent-pq`
  disease on the `ExecSeq` motive, unfixable by the identity-PC amendment
  (consumers need `p = execSeqLoopPC ≠ q = execSeqContPC`).
- workaround: NONE — batch fields hSeqNil/hSeqConsNormal/hSeqConsAbrupt
  skipped; `rows/SeqForRows.lean` rows + named resids
  (`SeqNilResid`/`SeqConsNormalResid`/`SeqConsAbruptResid`) stay the carriers.
- cost: 3 of the 7 B6 skeleton holes undischargeable until amended; every
  future worker sent at them will re-derive this.
- proposal: amend `mExecSeq` to pin the decoded PCs
  (`execSeqLoopPC`/`execSeqContPC`, the only instantiation consumers use) or
  add a code-image field to `SegEntry` (the pending sentryc/segexit re-land is
  the natural vehicle); then providers come from `execSeqLoop` + an
  `ExecSeqExit`→`SegExit` upgrade (needs `memFrame`/`stackWin` carried by the
  engine exit, currently absent).

## 2026-09-01 forloop-motive-identity-pc-store-mutation (fleet B6-loopseq)
- missing: any dischargeable form of the `mForLoop` motive: it is an
  identity-PC `SegEntry st p → SegExit st' p` span, but EVERY `ForLoop`
  constructor mutates the spec state (cond eval / body exec / full iteration),
  so a zero-step discharge forces the unchanged `m0` to represent both
  `st.store` and `st'.store` (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.zeroStep_forSpan_forces_rerepresentation`) and
  a stepping discharge is barred by the code-free `SegEntry`.  This is the
  DUAL `scaffold-some-motive-unsatisfiable` shape that got
  `mExecInit`/`mForCond`/`mExecStep` amended to `True`; `mForLoop` kept the
  span form and inherited the disease.  Also re-confirmed the
  `rows/SeqForRows.lean` engine seam: `execForLoopBody`'s `ExecEntry`/`ExecExit`
  admit no adapter to/from `SegEntry`/`SegExit` in either direction.
- workaround: NONE — batch fields hFlCondFalse/hFlBodyBreak/hFlBodyRet/hFlLoop
  skipped; `Vsa.Sim.Rows.ForResid` stays the named carrier.
- cost: 4 of the 7 B6 skeleton holes undischargeable until amended.
- proposal: either amend `mForLoop` to honest distinct loop-head/loop-exit PCs
  + code linkage, or (cheaper, matching how `execForStartSim` actually routes
  the real work through the `ExecForStep` oracle) amend `mForLoop` to `True`
  like its three scaffold siblings IF no consumer projects it — a consumer
  census like the wave-45 §0 grep is the first step.

## 2026-09-01 recursion-stack-budget-class (falsity #13 analysis, run1 coordinator)
- missing: a recursion-sound stack-budget invariant in the entry-condition
  layer. `EvalEntry.stackOK = StackOK SL sp (1088+1088)` is a CONSTANT, but
  each eval recursion level consumes 1088 bytes (eval_expr frame), so the
  child's entry demands `SL.lo + 3264 ≤ sp` at the parent — underivable from
  the parent's own 2176.  This is exactly why every recursive-case Extras
  bundle (`NegExtras.sp_headroom : SL.lo + 3264 ≤ sp.toNat`, the AddResid
  `SLloSp`, …) parks the fact as an ∀-closed oracle — the class the fleet
  refuted (falsity #12).  Threading `EvalEntry` into the Resids (the ITEM
  ZERO brief shape) removes REFUTABILITY but not UNDERIVABILITY: the
  amended `EvalEntry → NegExtras` is unprovable (2176 < 3264).  Worse, the
  un-amended `EvalIH` itself is FALSE at expression depth ≥ 3 under a tight
  `SL` (entry `sp − SL.lo = 2176`: level-3 frame `[SL.lo−1088, SL.lo)` writes
  OUTSIDE `[SL.lo, sp)`, violating the exit memFrame clause) — analytic
  refutation; a machine-checked witness would need a 3-deep concrete arm run
  (not cheaply constructible tonight; recorded as the named obstruction).
  Ledger precedent: `armsegsplit-marshalling-fact-built` (2026-08-31) already
  recorded the extras as "NOT projectable from EvalEntry(parent)".
- workaround: NONE (Law 4).  Amendment (ITEM ZERO phase B, this run):
  budget-index the entry conditions with ZERO signature changes —
  (1) `StackLayout` gains a `perCall : Nat` field (per-call-level budget);
  (2) mutual `Expr.stackNeed`/`Stmt.stackNeed : … → Nat` (structural frame
  bytes; call bodies accounted via the `perCall` term, NOT structurally);
  (3) `EvalEntry.stackOK : StackOK SL sp (e.stackNeed + (maxCallDepth − d) *
  SL.perCall + 1088)` (ExecEntry likewise over `s`), + new entry fields
  `StoreBodiesBound st.store SL.perCall` and `Expr.BodiesBound e SL.perCall`
  (fn-literal bodies fit the per-call budget; store invariant survives
  define/alloc since bodies are program subterms);
  (4) monotone bridge `stackOK_ge : … → StackOK SL sp 2176` keeps every
  existing consumer proof one lemma away;
  (5) the child-entry construction sites (armTail_rec/ArmSegSplit*) now
  DERIVE the child stackOK by arithmetic — the sp_headroom oracles are
  DELETED from the Extras/Resid layer.
  Top-level: the concrete `Layout.atInterpRun` carries `StackOK SL* sp₀
  (p.stackNeed …)` — "properly loaded" includes the stack fitting the
  program; InterpSim's ∀-L shape is unchanged (maxCallDepth-cap precedent).
- cost: the fleet's 20 refuted fields + the ~10 oracle-parked recursive
  residuals are all uninhabitable/underivable until this lands; it gates the
  whole RUN-1 field campaign.
- proposal: land as ITEM ZERO phase B in /tmp/vsa-itemzero-sandbox, COW
  agents per family, sweep-validate, apply to main in one motion with the
  Resid entry-threading (phase A) and the B5/B6 slot-pin + motive amendments
  (phases C/D).

## 2026-09-01 leaf-resid-forall-ghost-falsity (fleet B1-leaves, hInt/hNull/hBool/hStr)
- missing: the geometry-conditioned leaf-residual supplier layer. The four
  `TermResidualsCore` leaf fields (`hInt`/`hNull`/`hBool`/`hStr`, skeleton holes
  `SkelH{Int,Null,Bool,Str}`) ∀-close their `*LeafResid` over ALL layout ghosts
  (`g N A SL φf φc sp r sret m0` and, for null/bool/str, an unconstrained
  `c : Config`) with a bare conjunction body. The `TermBundles.lean` assembly
  table assigns every leaf `TermShared.geom : ImageGeom N A SL` (G-class), but
  the statements carry NO such premise, and the TSV-named supplier `GeomFrom`
  does not exist anywhere in `Vsa/` (only the `TermAssembly.lean` doc comment).
  Consequences, machine-checked in
  `experiments/fleet/obstructions/B1_leaves_obstructions.lean` (green,
  axiom-clean, 1.6s):
  * `SkelHNull`/`SkelHBool`/`SkelHStr` are **FALSE** (`skelH*_false`): each
    residual asserts its sret-vs-`value_*`-code disjointness conjunct for
    ARBITRARY `sret`; `sret := 0x800027f0 / 0x80002800 / 0x80002820` (inside
    the respective code windows) refutes them outright — no machine
    construction needed, both disjuncts fail by `decide`.
  * `SkelHInt` is unprovable as stated: its body is
    `LeafWiden = Widen (EvalExit …) … (stackFoot SL)` whose `pres`/`surv`
    quantify over EVERY `EvalExit` config; `EvalExit` is exactly the predicate
    that forgets both (its `memFrame` leaves `[SL.lo,sp) ∪ A` ∪ sret-padding
    presence unconstrained; `StoreRepr.frames_arena` places frames in `A` with
    nothing relating `A` to `[SL.lo,SL.hi)` for ∀-ghosts). `skelHInt_of`
    machine-checks the exact gap = two named premises `IntLeafPres`/`IntLeafSurv`.
- workaround: NONE (stopped per Law 4; obstruction file + this entry).
- cost: the whole B1 batch (4 fields) blocked; every other batch whose Resid
  ∀-closes geometry conjuncts over ghosts (e.g. B5's `BrkResid` asserts
  `StmtSlotPinned k armPC m0` for arbitrary `m0`, false at `m0 = ∅`) will hit
  the same wall.
- proposal: amend the `*LeafResid` statements to take the geometry as premises
  (`ImageGeom N A SL` + a populated-`m0`/write-chain fact, the `hMcallPop`
  analog) — the rows already destructure the conjuncts, so the amendment is
  local to `rows/TermRouting.lean` defs + the skeleton regen; OR re-land the
  leaf sims at `EvalExitD` directly (the writeMap chain inside
  `evalIntSim`'s proof knows `pres`/`surv`; the abstract `EvalExit` does not),
  making the widener residual disappear entirely.

## 2026-09-01 b2-resid-fields-refutable (fleet B2-unary-logic worker)
- missing: an entry-linkage hypothesis in the ∀-closed `TermResidualsCore`
  Resid fields. `NegResid`/`NotResid`/`OrTrueResid`/`AndFalseResid`/
  `OrFalseResid`/`AndTrueResid` (rows/TermRouting.lean) quantify over ALL
  ghosts (`N A SL sp r sret aEnv aExpr a* m0`, and for the logical four an
  unconstrained `c : Config`) with only the two operand `read64`/`ExprRepr`
  hypotheses, yet their conclusions (`NegExtras` etc.) demand entry-only
  geometry: `sp_headroom : SL.lo + 3264 ≤ sp.toNat`, `op_lo`, the
  `KindSlotPinned` static-image pins, and `hMcallPop` (total `m0` at
  `mcall := m0`). Nothing supplies these — the holes are REFUTABLE, so
  `TermResidualsCore L` is uninstantiable as stated.
- workaround: NONE (per law 4). Landed machine-checked refutations instead:
  `Vsa/Sim/rows/Field_hNeg.lean` (`field_hNeg_refuted`, shared witness
  `b2WitMem` = 24-byte concrete ExtHashMap with two `.null` nodes) + sibling
  `Field_hNot/hOrTrue/hAndFalse/hOrFalse/hAndTrue.lean` consuming it, each
  via `sp_headroom` at `sp = 0#64`.
- cost: the whole B2 batch (and, by the same shape, likely B1's LeafWiden
  `pres`/`surv` fields and every other ∀-closed Resid) cannot go green until
  the field statements are amended; every fleet worker on these fields will
  rediscover this.
- proposal: amend each Resid to take the entry as a hypothesis — e.g.
  `∀ …, EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv
  aExpr m0 c → … → NegExtras … ∧ …` (the rows already HAVE the entry config
  in scope at the consumption site, cf. `eval_neg_row`'s `hc`), or split each
  Extras into (a) Layout-derivable static pins (`KindSlotPinned` from
  `Loaded L`) + (b) an ArmEntryK widening supplied by `blockA_k`, as the
  NegExtras doc comment already anticipates. Precedent: Trichotomy
  falsity → amendment (`Vsa/While/StmtDispatch.lean`).

## 2026-09-01 exec-resid-slot-pins-uninhabited (fleet B5-execarms)
- missing: the exec-side residual bundles (`ExecCaseGeom`, `ExecExprGeom`,
  `ExecRetGeom`, `ExecRetNullGeom`, `ExecVarNullGeom`, `ExecVarInitGeom`,
  `IfNoneGeom`, `WhileFalseGeom`, `IfTrueGeom`, `IfFalseGeom`) put
  `StmtSlotPinned k armPC m0` (and the table/stack disjunct) UNCONDITIONALLY
  under a ∀-quantified `m0 : Mem` (and ∀ SL/sp) in the `*Resid` defs consumed
  by `TermResidualsCore.hS*`.  At `m0 = ∅` the slot-pin's byte lookups are
  `none`, so every such `*Resid` — hence every skeleton hole
  `SkelHSExpr/…/SkelHSIfFalse` and hence `TermResidualsCore L` itself — is
  PROVABLY FALSE (machine-checked: `Vsa/Sim/rows/B5ExecArmObstructions.lean`,
  `skelHS*_false`, 11 fields).  The slot pin (and disjointness) must be
  CONDITIONED on the pinned image (byte-pin premises per `gen_layout.py`'s
  `groundSlot_k` idiom, or a `Loaded L`-derived hypothesis on `m0`) — i.e. the
  residual statement needs amendment; a worker cannot land these fields.
- workaround: NONE — falsity proofs landed as the machine-checked obstruction
  (Law 4 precedent: Trichotomy), fields skipped.
- cost: all 14 B5 fields blocked; B1-B4/B6-B8 fields whose residuals embed the
  same unconditional-∀-m0 slot-pin/glue shape are equally uninhabited
  (eval-side `KindSlotPinned` twins should be audited before those batches
  burn time).
- proposal: amend the `*Geom`/`*Resid` layer to take the jump-table byte pins
  as named premises (the `groundSlot_k` supplier shape) or restate the
  residual ∀ over `m0` satisfying a named `RodataPinned m0` predicate; then
  the wave-43 generated pins discharge `hslot` and only `hGlue` remains open.

## 2026-09-01 loop-geom-self-referential-oracles (fleet B5-execarms)
- missing: `BlockGeom`/`ForStartGeom`/`WhileGeom` (fields `hSBlock`,
  `hSForStart`, `hSWhileBreak`) have no slot pin but demand the loop knot
  itself as unconditional ∀-ghost oracles: `hstep : ∀ …, ExecSeqStep …` /
  `ExecForStep …` / `ExecWhileStep …` over ALL `stM/m00/out00/stMid/stFin/
  status` (arbitrary, unlinked to any derivation), and `hWhileIH`/`hForIH` =
  the FULL while/for statement simulation Triple.  Supplier would be the
  statement-sim capstone being assembled — self-referential; no landed lemma
  can discharge them field-wise.
- workaround: NONE — skipped with this named obstruction.
- cost: 3 B5 fields undischargeable until the Geom layer threads the loop IH
  from the recursor (as the eval-side `armResidGap_of_stages` does) instead of
  demanding it ∀-ghost-closed inside the residual.
- proposal: restate the loop Geoms with the IH/step oracles as per-derivation
  premises (recursor-supplied, like `mExecS` minor-premise IHs), not
  ∀-quantified fields of the residual.

## 2026-09-01 seq-motive-independent-pq-no-code (fleet B6-loopseq)
- missing: any dischargeable form of the `mExecSeq` motive Triple
  (TermSimAssembly.lean:178): it quantifies entry PC `p` and exit PC `q`
  INDEPENDENTLY while `SegEntry` (InductionScaffold.lean:150) pins no code
  byte — so the off-diagonal (`ofNat p ≠ ofNat q`) span is unprovable from
  the hypothesis set (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.{zeroStep_segSpan_forces_pc_eq,
  skelHSeqNil_offdiag_must_step}`).  The `TermAssembly.hSeqNil` supplier note
  ("`execSeqNil` seg-identity, `_row` wrap trivial") is stale — identity
  suppliers cover only the diagonal.  This is the `scaffold-motive-independent-pq`
  disease on the `ExecSeq` motive, unfixable by the identity-PC amendment
  (consumers need `p = execSeqLoopPC ≠ q = execSeqContPC`).
- workaround: NONE — batch fields hSeqNil/hSeqConsNormal/hSeqConsAbrupt
  skipped; `rows/SeqForRows.lean` rows + named resids
  (`SeqNilResid`/`SeqConsNormalResid`/`SeqConsAbruptResid`) stay the carriers.
- cost: 3 of the 7 B6 skeleton holes undischargeable until amended; every
  future worker sent at them will re-derive this.
- proposal: amend `mExecSeq` to pin the decoded PCs
  (`execSeqLoopPC`/`execSeqContPC`, the only instantiation consumers use) or
  add a code-image field to `SegEntry` (the pending sentryc/segexit re-land is
  the natural vehicle); then providers come from `execSeqLoop` + an
  `ExecSeqExit`→`SegExit` upgrade (needs `memFrame`/`stackWin` carried by the
  engine exit, currently absent).

## 2026-09-01 forloop-motive-identity-pc-store-mutation (fleet B6-loopseq)
- missing: any dischargeable form of the `mForLoop` motive: it is an
  identity-PC `SegEntry st p → SegExit st' p` span, but EVERY `ForLoop`
  constructor mutates the spec state (cond eval / body exec / full iteration),
  so a zero-step discharge forces the unchanged `m0` to represent both
  `st.store` and `st'.store` (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.zeroStep_forSpan_forces_rerepresentation`) and
  a stepping discharge is barred by the code-free `SegEntry`.  This is the
  DUAL `scaffold-some-motive-unsatisfiable` shape that got
  `mExecInit`/`mForCond`/`mExecStep` amended to `True`; `mForLoop` kept the
  span form and inherited the disease.  Also re-confirmed the
  `rows/SeqForRows.lean` engine seam: `execForLoopBody`'s `ExecEntry`/`ExecExit`
  admit no adapter to/from `SegEntry`/`SegExit` in either direction.
- workaround: NONE — batch fields hFlCondFalse/hFlBodyBreak/hFlBodyRet/hFlLoop
  skipped; `Vsa.Sim.Rows.ForResid` stays the named carrier.
- cost: 4 of the 7 B6 skeleton holes undischargeable until amended.
- proposal: either amend `mForLoop` to honest distinct loop-head/loop-exit PCs
  + code linkage, or (cheaper, matching how `execForStartSim` actually routes
  the real work through the `ExecForStep` oracle) amend `mForLoop` to `True`
  like its three scaffold siblings IF no consumer projects it — a consumer
  census like the wave-45 §0 grep is the first step.

## 2026-09-01 recursion-stack-budget-class (falsity #13 analysis, run1 coordinator)
- missing: a recursion-sound stack-budget invariant in the entry-condition
  layer. `EvalEntry.stackOK = StackOK SL sp (1088+1088)` is a CONSTANT, but
  each eval recursion level consumes 1088 bytes (eval_expr frame), so the
  child's entry demands `SL.lo + 3264 ≤ sp` at the parent — underivable from
  the parent's own 2176.  This is exactly why every recursive-case Extras
  bundle (`NegExtras.sp_headroom : SL.lo + 3264 ≤ sp.toNat`, the AddResid
  `SLloSp`, …) parks the fact as an ∀-closed oracle — the class the fleet
  refuted (falsity #12).  Threading `EvalEntry` into the Resids (the ITEM
  ZERO brief shape) removes REFUTABILITY but not UNDERIVABILITY: the
  amended `EvalEntry → NegExtras` is unprovable (2176 < 3264).  Worse, the
  un-amended `EvalIH` itself is FALSE at expression depth ≥ 3 under a tight
  `SL` (entry `sp − SL.lo = 2176`: level-3 frame `[SL.lo−1088, SL.lo)` writes
  OUTSIDE `[SL.lo, sp)`, violating the exit memFrame clause) — analytic
  refutation; a machine-checked witness would need a 3-deep concrete arm run
  (not cheaply constructible tonight; recorded as the named obstruction).
  Ledger precedent: `armsegsplit-marshalling-fact-built` (2026-08-31) already
  recorded the extras as "NOT projectable from EvalEntry(parent)".
- workaround: NONE (Law 4).  Amendment (ITEM ZERO phase B, this run):
  budget-index the entry conditions with ZERO signature changes —
  (1) `StackLayout` gains a `perCall : Nat` field (per-call-level budget);
  (2) mutual `Expr.stackNeed`/`Stmt.stackNeed : … → Nat` (structural frame
  bytes; call bodies accounted via the `perCall` term, NOT structurally);
  (3) `EvalEntry.stackOK : StackOK SL sp (e.stackNeed + (maxCallDepth − d) *
  SL.perCall + 1088)` (ExecEntry likewise over `s`), + new entry fields
  `StoreBodiesBound st.store SL.perCall` and `Expr.BodiesBound e SL.perCall`
  (fn-literal bodies fit the per-call budget; store invariant survives
  define/alloc since bodies are program subterms);
  (4) monotone bridge `stackOK_ge : … → StackOK SL sp 2176` keeps every
  existing consumer proof one lemma away;
  (5) the child-entry construction sites (armTail_rec/ArmSegSplit*) now
  DERIVE the child stackOK by arithmetic — the sp_headroom oracles are
  DELETED from the Extras/Resid layer.
  Top-level: the concrete `Layout.atInterpRun` carries `StackOK SL* sp₀
  (p.stackNeed …)` — "properly loaded" includes the stack fitting the
  program; InterpSim's ∀-L shape is unchanged (maxCallDepth-cap precedent).
- cost: the fleet's 20 refuted fields + the ~10 oracle-parked recursive
  residuals are all uninhabitable/underivable until this lands; it gates the
  whole RUN-1 field campaign.
- proposal: land as ITEM ZERO phase B in /tmp/vsa-itemzero-sandbox, COW
  agents per family, sweep-validate, apply to main in one motion with the
  Resid entry-threading (phase A) and the B5/B6 slot-pin + motive amendments
  (phases C/D).

## 2026-09-01 err-reach-span-vs-m4-edge (err lane, 42 hsite reachability residuals)
- missing: an M4 arm-sim ERROR-EDGE reachability span, per error branch — a
  `Triple SpanPre (SpillArmPre/SetupArmPre S m0 L lds <seg> pc0 pcJal …)` where
  `SpanPre` is a real reachable interpreter-entry predicate and the post is the
  error block-entry (`pc0` just before the `jal runtime_error`). No landed arm-sim
  produces one: EvalNegSim/EvalNotSim/exec arms model the SUCCESS branch only; the
  error branch (e.g. value-not-int → jal) is never threaded to a reachability.
  All 42 error links reduce to exactly one such span apiece (shared per PC).
- workaround: NONE for the spans themselves (genuinely M4, out of err-lane reach).
  Built the COMPOSITION abstraction `reachJal_of_span` (Vsa/Sim/rows/ErrReachSpan.lean,
  green+axiom-clean) so a span drops straight in: it composes an arbitrary
  reach-to-pc0 span with the landed `spill*/setup*_toJalErr` seg into `ReachJal … c`,
  generalizing `reachJal_of_armBranch` (= the span:=Triple.rfl case, machine-checked).
- cost: without the spans, the 42 collector fields ErrArmLinks(.16)/ErrArmLinksB(.26)
  stay open; every future M4 arm-sim lane pays a bespoke reach-to-pc0 per error branch
  unless the arm-sim exposes its error edge as this named span shape.
- proposal: have the M4 eval/exec arm-sims, when they take the error branch, EXPORT
  the reached config as `Triple <arm-entry-pre> (SpillArmPre/SetupArmPre …)` (post =
  the existing block-entry predicate) — then `reachJal_of_span` closes the link with
  zero extra error-side work. One span per distinct PC (19) serves all 42 hsites.

## 2026-09-01 leaf-resid-forall-ghost-falsity (fleet B1-leaves, hInt/hNull/hBool/hStr)
- missing: the geometry-conditioned leaf-residual supplier layer. The four
  `TermResidualsCore` leaf fields (`hInt`/`hNull`/`hBool`/`hStr`, skeleton holes
  `SkelH{Int,Null,Bool,Str}`) ∀-close their `*LeafResid` over ALL layout ghosts
  (`g N A SL φf φc sp r sret m0` and, for null/bool/str, an unconstrained
  `c : Config`) with a bare conjunction body. The `TermBundles.lean` assembly
  table assigns every leaf `TermShared.geom : ImageGeom N A SL` (G-class), but
  the statements carry NO such premise, and the TSV-named supplier `GeomFrom`
  does not exist anywhere in `Vsa/` (only the `TermAssembly.lean` doc comment).
  Consequences, machine-checked in
  `experiments/fleet/obstructions/B1_leaves_obstructions.lean` (green,
  axiom-clean, 1.6s):
  * `SkelHNull`/`SkelHBool`/`SkelHStr` are **FALSE** (`skelH*_false`): each
    residual asserts its sret-vs-`value_*`-code disjointness conjunct for
    ARBITRARY `sret`; `sret := 0x800027f0 / 0x80002800 / 0x80002820` (inside
    the respective code windows) refutes them outright — no machine
    construction needed, both disjuncts fail by `decide`.
  * `SkelHInt` is unprovable as stated: its body is
    `LeafWiden = Widen (EvalExit …) … (stackFoot SL)` whose `pres`/`surv`
    quantify over EVERY `EvalExit` config; `EvalExit` is exactly the predicate
    that forgets both (its `memFrame` leaves `[SL.lo,sp) ∪ A` ∪ sret-padding
    presence unconstrained; `StoreRepr.frames_arena` places frames in `A` with
    nothing relating `A` to `[SL.lo,SL.hi)` for ∀-ghosts). `skelHInt_of`
    machine-checks the exact gap = two named premises `IntLeafPres`/`IntLeafSurv`.
- workaround: NONE (stopped per Law 4; obstruction file + this entry).
- cost: the whole B1 batch (4 fields) blocked; every other batch whose Resid
  ∀-closes geometry conjuncts over ghosts (e.g. B5's `BrkResid` asserts
  `StmtSlotPinned k armPC m0` for arbitrary `m0`, false at `m0 = ∅`) will hit
  the same wall.
- proposal: amend the `*LeafResid` statements to take the geometry as premises
  (`ImageGeom N A SL` + a populated-`m0`/write-chain fact, the `hMcallPop`
  analog) — the rows already destructure the conjuncts, so the amendment is
  local to `rows/TermRouting.lean` defs + the skeleton regen; OR re-land the
  leaf sims at `EvalExitD` directly (the writeMap chain inside
  `evalIntSim`'s proof knows `pres`/`surv`; the abstract `EvalExit` does not),
  making the widener residual disappear entirely.

## 2026-09-01 b2-resid-fields-refutable (fleet B2-unary-logic worker)
- missing: an entry-linkage hypothesis in the ∀-closed `TermResidualsCore`
  Resid fields. `NegResid`/`NotResid`/`OrTrueResid`/`AndFalseResid`/
  `OrFalseResid`/`AndTrueResid` (rows/TermRouting.lean) quantify over ALL
  ghosts (`N A SL sp r sret aEnv aExpr a* m0`, and for the logical four an
  unconstrained `c : Config`) with only the two operand `read64`/`ExprRepr`
  hypotheses, yet their conclusions (`NegExtras` etc.) demand entry-only
  geometry: `sp_headroom : SL.lo + 3264 ≤ sp.toNat`, `op_lo`, the
  `KindSlotPinned` static-image pins, and `hMcallPop` (total `m0` at
  `mcall := m0`). Nothing supplies these — the holes are REFUTABLE, so
  `TermResidualsCore L` is uninstantiable as stated.
- workaround: NONE (per law 4). Landed machine-checked refutations instead:
  `Vsa/Sim/rows/Field_hNeg.lean` (`field_hNeg_refuted`, shared witness
  `b2WitMem` = 24-byte concrete ExtHashMap with two `.null` nodes) + sibling
  `Field_hNot/hOrTrue/hAndFalse/hOrFalse/hAndTrue.lean` consuming it, each
  via `sp_headroom` at `sp = 0#64`.
- cost: the whole B2 batch (and, by the same shape, likely B1's LeafWiden
  `pres`/`surv` fields and every other ∀-closed Resid) cannot go green until
  the field statements are amended; every fleet worker on these fields will
  rediscover this.
- proposal: amend each Resid to take the entry as a hypothesis — e.g.
  `∀ …, EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv
  aExpr m0 c → … → NegExtras … ∧ …` (the rows already HAVE the entry config
  in scope at the consumption site, cf. `eval_neg_row`'s `hc`), or split each
  Extras into (a) Layout-derivable static pins (`KindSlotPinned` from
  `Loaded L`) + (b) an ArmEntryK widening supplied by `blockA_k`, as the
  NegExtras doc comment already anticipates. Precedent: Trichotomy
  falsity → amendment (`Vsa/While/StmtDispatch.lean`).

## 2026-09-01 exec-resid-slot-pins-uninhabited (fleet B5-execarms)
- missing: the exec-side residual bundles (`ExecCaseGeom`, `ExecExprGeom`,
  `ExecRetGeom`, `ExecRetNullGeom`, `ExecVarNullGeom`, `ExecVarInitGeom`,
  `IfNoneGeom`, `WhileFalseGeom`, `IfTrueGeom`, `IfFalseGeom`) put
  `StmtSlotPinned k armPC m0` (and the table/stack disjunct) UNCONDITIONALLY
  under a ∀-quantified `m0 : Mem` (and ∀ SL/sp) in the `*Resid` defs consumed
  by `TermResidualsCore.hS*`.  At `m0 = ∅` the slot-pin's byte lookups are
  `none`, so every such `*Resid` — hence every skeleton hole
  `SkelHSExpr/…/SkelHSIfFalse` and hence `TermResidualsCore L` itself — is
  PROVABLY FALSE (machine-checked: `Vsa/Sim/rows/B5ExecArmObstructions.lean`,
  `skelHS*_false`, 11 fields).  The slot pin (and disjointness) must be
  CONDITIONED on the pinned image (byte-pin premises per `gen_layout.py`'s
  `groundSlot_k` idiom, or a `Loaded L`-derived hypothesis on `m0`) — i.e. the
  residual statement needs amendment; a worker cannot land these fields.
- workaround: NONE — falsity proofs landed as the machine-checked obstruction
  (Law 4 precedent: Trichotomy), fields skipped.
- cost: all 14 B5 fields blocked; B1-B4/B6-B8 fields whose residuals embed the
  same unconditional-∀-m0 slot-pin/glue shape are equally uninhabited
  (eval-side `KindSlotPinned` twins should be audited before those batches
  burn time).
- proposal: amend the `*Geom`/`*Resid` layer to take the jump-table byte pins
  as named premises (the `groundSlot_k` supplier shape) or restate the
  residual ∀ over `m0` satisfying a named `RodataPinned m0` predicate; then
  the wave-43 generated pins discharge `hslot` and only `hGlue` remains open.

## 2026-09-01 loop-geom-self-referential-oracles (fleet B5-execarms)
- missing: `BlockGeom`/`ForStartGeom`/`WhileGeom` (fields `hSBlock`,
  `hSForStart`, `hSWhileBreak`) have no slot pin but demand the loop knot
  itself as unconditional ∀-ghost oracles: `hstep : ∀ …, ExecSeqStep …` /
  `ExecForStep …` / `ExecWhileStep …` over ALL `stM/m00/out00/stMid/stFin/
  status` (arbitrary, unlinked to any derivation), and `hWhileIH`/`hForIH` =
  the FULL while/for statement simulation Triple.  Supplier would be the
  statement-sim capstone being assembled — self-referential; no landed lemma
  can discharge them field-wise.
- workaround: NONE — skipped with this named obstruction.
- cost: 3 B5 fields undischargeable until the Geom layer threads the loop IH
  from the recursor (as the eval-side `armResidGap_of_stages` does) instead of
  demanding it ∀-ghost-closed inside the residual.
- proposal: restate the loop Geoms with the IH/step oracles as per-derivation
  premises (recursor-supplied, like `mExecS` minor-premise IHs), not
  ∀-quantified fields of the residual.

## 2026-09-01 seq-motive-independent-pq-no-code (fleet B6-loopseq)
- missing: any dischargeable form of the `mExecSeq` motive Triple
  (TermSimAssembly.lean:178): it quantifies entry PC `p` and exit PC `q`
  INDEPENDENTLY while `SegEntry` (InductionScaffold.lean:150) pins no code
  byte — so the off-diagonal (`ofNat p ≠ ofNat q`) span is unprovable from
  the hypothesis set (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.{zeroStep_segSpan_forces_pc_eq,
  skelHSeqNil_offdiag_must_step}`).  The `TermAssembly.hSeqNil` supplier note
  ("`execSeqNil` seg-identity, `_row` wrap trivial") is stale — identity
  suppliers cover only the diagonal.  This is the `scaffold-motive-independent-pq`
  disease on the `ExecSeq` motive, unfixable by the identity-PC amendment
  (consumers need `p = execSeqLoopPC ≠ q = execSeqContPC`).
- workaround: NONE — batch fields hSeqNil/hSeqConsNormal/hSeqConsAbrupt
  skipped; `rows/SeqForRows.lean` rows + named resids
  (`SeqNilResid`/`SeqConsNormalResid`/`SeqConsAbruptResid`) stay the carriers.
- cost: 3 of the 7 B6 skeleton holes undischargeable until amended; every
  future worker sent at them will re-derive this.
- proposal: amend `mExecSeq` to pin the decoded PCs
  (`execSeqLoopPC`/`execSeqContPC`, the only instantiation consumers use) or
  add a code-image field to `SegEntry` (the pending sentryc/segexit re-land is
  the natural vehicle); then providers come from `execSeqLoop` + an
  `ExecSeqExit`→`SegExit` upgrade (needs `memFrame`/`stackWin` carried by the
  engine exit, currently absent).

## 2026-09-01 forloop-motive-identity-pc-store-mutation (fleet B6-loopseq)
- missing: any dischargeable form of the `mForLoop` motive: it is an
  identity-PC `SegEntry st p → SegExit st' p` span, but EVERY `ForLoop`
  constructor mutates the spec state (cond eval / body exec / full iteration),
  so a zero-step discharge forces the unchanged `m0` to represent both
  `st.store` and `st'.store` (machine-checked:
  `Vsa.Sim.B6LoopSeqObstruction.zeroStep_forSpan_forces_rerepresentation`) and
  a stepping discharge is barred by the code-free `SegEntry`.  This is the
  DUAL `scaffold-some-motive-unsatisfiable` shape that got
  `mExecInit`/`mForCond`/`mExecStep` amended to `True`; `mForLoop` kept the
  span form and inherited the disease.  Also re-confirmed the
  `rows/SeqForRows.lean` engine seam: `execForLoopBody`'s `ExecEntry`/`ExecExit`
  admit no adapter to/from `SegEntry`/`SegExit` in either direction.
- workaround: NONE — batch fields hFlCondFalse/hFlBodyBreak/hFlBodyRet/hFlLoop
  skipped; `Vsa.Sim.Rows.ForResid` stays the named carrier.
- cost: 4 of the 7 B6 skeleton holes undischargeable until amended.
- proposal: either amend `mForLoop` to honest distinct loop-head/loop-exit PCs
  + code linkage, or (cheaper, matching how `execForStartSim` actually routes
  the real work through the `ExecForStep` oracle) amend `mForLoop` to `True`
  like its three scaffold siblings IF no consumer projects it — a consumer
  census like the wave-45 §0 grep is the first step.

## 2026-09-01 recursion-stack-budget-class (falsity #13 analysis, run1 coordinator)
- missing: a recursion-sound stack-budget invariant in the entry-condition
  layer. `EvalEntry.stackOK = StackOK SL sp (1088+1088)` is a CONSTANT, but
  each eval recursion level consumes 1088 bytes (eval_expr frame), so the
  child's entry demands `SL.lo + 3264 ≤ sp` at the parent — underivable from
  the parent's own 2176.  This is exactly why every recursive-case Extras
  bundle (`NegExtras.sp_headroom : SL.lo + 3264 ≤ sp.toNat`, the AddResid
  `SLloSp`, …) parks the fact as an ∀-closed oracle — the class the fleet
  refuted (falsity #12).  Threading `EvalEntry` into the Resids (the ITEM
  ZERO brief shape) removes REFUTABILITY but not UNDERIVABILITY: the
  amended `EvalEntry → NegExtras` is unprovable (2176 < 3264).  Worse, the
  un-amended `EvalIH` itself is FALSE at expression depth ≥ 3 under a tight
  `SL` (entry `sp − SL.lo = 2176`: level-3 frame `[SL.lo−1088, SL.lo)` writes
  OUTSIDE `[SL.lo, sp)`, violating the exit memFrame clause) — analytic
  refutation; a machine-checked witness would need a 3-deep concrete arm run
  (not cheaply constructible tonight; recorded as the named obstruction).
  Ledger precedent: `armsegsplit-marshalling-fact-built` (2026-08-31) already
  recorded the extras as "NOT projectable from EvalEntry(parent)".
- workaround: NONE (Law 4).  Amendment (ITEM ZERO phase B, this run):
  budget-index the entry conditions with ZERO signature changes —
  (1) `StackLayout` gains a `perCall : Nat` field (per-call-level budget);
  (2) mutual `Expr.stackNeed`/`Stmt.stackNeed : … → Nat` (structural frame
  bytes; call bodies accounted via the `perCall` term, NOT structurally);
  (3) `EvalEntry.stackOK : StackOK SL sp (e.stackNeed + (maxCallDepth − d) *
  SL.perCall + 1088)` (ExecEntry likewise over `s`), + new entry fields
  `StoreBodiesBound st.store SL.perCall` and `Expr.BodiesBound e SL.perCall`
  (fn-literal bodies fit the per-call budget; store invariant survives
  define/alloc since bodies are program subterms);
  (4) monotone bridge `stackOK_ge : … → StackOK SL sp 2176` keeps every
  existing consumer proof one lemma away;
  (5) the child-entry construction sites (armTail_rec/ArmSegSplit*) now
  DERIVE the child stackOK by arithmetic — the sp_headroom oracles are
  DELETED from the Extras/Resid layer.
  Top-level: the concrete `Layout.atInterpRun` carries `StackOK SL* sp₀
  (p.stackNeed …)` — "properly loaded" includes the stack fitting the
  program; InterpSim's ∀-L shape is unchanged (maxCallDepth-cap precedent).
- cost: the fleet's 20 refuted fields + the ~10 oracle-parked recursive
  residuals are all uninhabitable/underivable until this lands; it gates the
  whole RUN-1 field campaign.
- proposal: land as ITEM ZERO phase B in /tmp/vsa-itemzero-sandbox, COW
  agents per family, sweep-validate, apply to main in one motion with the
  Resid entry-threading (phase A) and the B5/B6 slot-pin + motive amendments
  (phases C/D).

## 2026-09-01 stringify-native-name-mismatch (bridges lane, run1)
- missing: the concat-side renderer is NOT `Value.display`. `binOpSem .add`
  (Vsa/While/Semantics.lean:261) renders BOTH operands with `Value.display`,
  but the machine's `stringify` (interp.c:101, `default: strcpy(buf,
  "<native fn>")`) drops the native's NAME, while `value_print` (value.c:66,
  `"<native fn %s>"`) keeps it. `Value.display .native .print = "<native fn
  print>"` matches value_print ONLY. EMPIRICALLY CONFIRMED (t5 emulator,
  /tmp/wl-test tests/bridge_stringify.wl + bridge_native_print.wl):
  `println("x" + println)` → `x<native fn>` (machine) vs spec `x<native fn
  println>`; `println(println)` → `<native fn println>` (display correct on
  the print path). All other constructors agree byte-for-byte on BOTH paths
  (Atrue / falseB / nullC / 12D / `<fn foo>` / anon `<fn>`).
- workaround: NONE yet (Law 4). Consequence: `StrConcatCellResid` /
  `StrConcatHeapResid` / `eval_binary_row`'s hStrAddL/hStrAddR (and
  TermAssembly's fields) are FALSE as stated whenever the non-str operand is
  `.native` (falsity class: spec-side rendering bug, Trichotomy precedent).
- cost: the concat cells cannot be discharged for native operands; every
  consumer of `binOpSem .add`'s str arm carries the false rendering.
- proposal: amendment — add `Value.catDisplay (s : Store) : Value → String`
  = `display` except `.native _ => "<native fn>"`, and amend `binOpSem .add`
  str arm to `some (.str (l.catDisplay s ++ r.catDisplay s))`; rethread the
  finitely many `.display`-in-concat statements (BinStrCells, StringifySpec,
  StrConcatHeap, BinDispatchRow hStrAddL/R, TermAssembly fields). display
  stays as-is for value_print/printArgs (empirically right there).

## 2026-09-01 fanout-whnf-explosion-blocks-entry-and-io (run1 coordinator)
- missing: the entry-amendment fan-out (ITEM ZERO B1 across every recursive
  arm sim) and the io DAG's __sfvwrite_r both stall on the SAME class — a
  guard/geometry `whnf` through a store reified over a `writeLog`-def memory
  (the "P2 explosion"): a `decide`/`omega`/`simp` that must reduce the large
  EvalEntry/store structure blows the unifier (seg-guard-close-symbolic-pins
  and seg_frame_facts-crossblock are prior instances). TWO worker agents died
  to the 600s watchdog on it tonight (io F4; itemzero recursive-arm fan-out).
- workaround: the itemzero PRIMARY amendment IS green (Vsa/Sim/InterpEntry.lean
  amended EvalEntry + inhabit probe `itemzero_neg_sp_headroom` axiom-clean —
  proves the budgeted `stackBudget` DERIVES the fleet-refuted `SL.lo+3264≤sp`,
  falsity #13 cured on the primary structure). The BLOCK is only the fan-out:
  ~30 arm-sim construction sites each need the 3 budget conjuncts forwarded,
  and each forwarding proof hits the whnf wall unless the fact is ascribed
  BEFORE any EvalEntry projection reaches the tactic (the probe's technique:
  bind `hc.stackBudget.1` to a `have` with an explicit type, never `omega` on
  a raw projection). Preserved as replayable patches:
  experiments/wip/{itemzero-b1-amendment.patch (3367 lines),
  io-lane-partial.patch (9863 lines)}.
- cost: endToEnd stays CONDITIONAL on RemainingWork tonight — the record is
  inhabitable-in-principle (probe) but not yet inhabited (fan-out blocked);
  ErrWork blocked on the 42 M4 error-edge spans (separate, err-lane verdict).
- proposal: complete the fan-out with the ascribe-before-project discipline
  baked into a `budget_forward` tactic/lemma (one `StackOK.mono` +
  `stackNeed` one-level-unfold per site), applied mechanically — NOT via a
  general `omega` that whnf's the entry. Then regen skeleton + census.

## 2026-09-02 store-bodies-eval-preservation (wave 47a B1 fan-out, main)
- missing: the spec-side preservation lemma family
  `EvalE st d env e st' v → StoreBodiesBound st.store P → e.bodiesBound P →
   StoreBodiesBound st'.store P` (mutual with ExecS/EvalArgs). B1's budget
  layer states the invariant (`Vsa/While/StackNeed.lean` doc comments say
  "preserved by define/allocFrame/allocClosure") but nobody has PROVED the
  judgment-level preservation.
- workaround: every RIGHT-child site (blockB_binary's R conjuncts, the 10
  binary-op row Goal towers, blockC_andTrue/orFalse via the
  AndTrueExtras/OrFalseExtras `store_bodiesR` field, MidArmRightMarshal,
  blockA_binaryArm_budgeted's `hstoreBodiesR` premise) threads
  `StoreBodiesBound st'.store perCallBudget` as a NAMED premise/field.
- cost: one extra named residual per two-child arm (~8 sites today); the
  recursor-row layer that instantiates these towers will have to supply it at
  every two-child case until the preservation lemma lands.
- proposal: `Vsa/While/StackNeedPreserve.lean` — mutual induction over
  EvalE/ExecS/EvalArgs proving StoreBodiesBound preservation (+ the `.fn`
  seeding case from `Expr.bodiesBound`), then delete the threaded premises by
  deriving at the recursor rows (they hold the EvalE derivations + entry
  invariant).

## 2026-09-01 b3-bincell-resids-refutable (ITEM ZERO sandbox audit)
- missing: derivation/entry conditioning in `BinIntCellResid`/`BinEqCellResid`
  (rows/BinDispatchRow.lean), the eval-side twins the B5 obstruction note asked
  to audit.  CONFIRMED same falsity class, two independent ways: (a) the
  size-stability conjuncts `st'.store.frames.size = st''.store.frames.size`
  are asserted for ∀-quantified UNRELATED `st' st''` (refute with 0-frame vs
  1-frame states — no memory witness needed); (b) `BinArmExtras.sproom :
  SL.lo + 4352 ≤ sp.toNat` and `slot6 : KindSlotPinned 6 … m0` are ∃-invariant
  entry-side conjuncts refuted at `sp = 0` / `m0 = ∅`.  So Skel
  `hIAdd…hIGe`/`hEq`/`hNe` (11 fields) are ALL refutable as stated.
- workaround: NONE applied — fields classified (needs shape 1 + the two
  `EvalE` derivations as hypotheses); amendment DESIGNED but not landed (the
  `eval_binary_row` dispatcher consumes the residual at ~12 cell sites; the
  row has `a`/`a_1`/`hc` in scope at every site, so threading is mechanical).
- cost: any fleet worker dispatched at B3/B4 before the amendment lands will
  re-derive the refutations.
- proposal: amend `BinIntCellResid`/`BinEqCellResid` exactly like the B2
  Resids (leading `EvalEntry` + derivation hypotheses), regen the dispatcher.

## 2026-09-01 seq-motive-multi-pair-census (ITEM ZERO sandbox)
- missing: nothing — a CORRECTION of fleet B6's amendment proposal
  (`seq-motive-independent-pq-no-code` proposed pinning
  `p = execSeqLoopPC / q = execSeqContPC` as "the only instantiation consumers
  use"; the coordinator design doc's Phase D repeats it).  Machine-grep
  census: landed consumers instantiate `mExecSeq` at THREE distinct PC pairs —
  `(0x8000448c, 0x80004514)` interp_run loop (EntryHalts/TermEntry/EntrySeams),
  `(0x80003354, 0x80003378)` closure-body loop (rows/CallClosureRow),
  `(0x800041a4, 0x8000409c)` block-arm loop (BlockGeom seam).  Pinning would
  break EntryHalts + the crux.
- workaround: n/a — the landed amendment keeps `∀ p q` and guards the motive
  with the table-driven `SeqSpanGround p q m0` (`seqLoopImage` maps exactly
  the three pairs to `Interp_runLoaded`/`Eval_exprLoaded`/`Exec_stmtLoaded`),
  the `mCall`/`EntryImage` wave-40 precedent.
- cost: none; recorded so nobody re-lands the pin.
- proposal: extending the proof to a new statement-loop copy = one
  `seqLoopImage` table line.

## 2026-09-01 code-free-segentry-args-call-spans (ITEM ZERO sandbox audit)
- missing: the `SeqSpanGround` ground-table idiom for the OTHER fixed-PC
  `SegEntry → SegExit` motives: `mEvalArgs` (evalArgsLoopPC→evalArgsContPC)
  and `mCall` (callDispatchPC→callJoinPC) still have code-free `SegEntry`
  entries — a supplier of `ArgsNilResid`/`ArgsConsResid`/the native call rows
  cannot derive a machine step from the hypothesis set (the same B6
  obstruction, at fixed PCs; mCall's wave-40 `EntryImage` guard pins a SPILL
  image, not code bytes).  Not refutable (Triples are vacuous without an
  entry witness), so lower priority than falsity #12, but the discharge
  campaign will hit it.
- workaround: NONE (out of ITEM-ZERO scope; the three named shapes only).
- cost: the args/call span suppliers will stall exactly like fleet B6 did.
- proposal: add table entries mapping (evalArgsLoopPC, evalArgsContPC) and
  (callDispatchPC, callJoinPC) ↦ `Eval_exprLoaded` and guard
  `mEvalArgs`/`mCall` with the same `SeqSpanGround` shape.

## 2026-09-01 sandbox-external-resync-stomp (ITEM ZERO sandbox, incident)
- missing: isolation of validation sandboxes from the main-repo sync/harvest
  machinery.  /tmp/vsa-itemzero-sandbox was re-synced FROM main at ~20:26-20:33
  while the ITEM-ZERO agent was mid-validation: all Vsa source amendments
  reverted, observations entries lost, olean tree replaced with main's —
  AFTER the full downstream sweep had validated the amendment green (133
  modules) but BEFORE the refutation-failure battery completed.  Untracked
  files (logs, evidence) survived.
- workaround: the complete amendment was reconstructed as a deterministic
  replay bundle (/tmp/itemzero-apply, mirrored in the clone at
  experiments/itemzero-apply) with the sweep log as validation evidence.
- cost: the post-amendment refutation-failure battery run was voided (its
  results were against main's reverted environment); ~30 min of regen CPU.
- proposal: sandboxes get a sentinel file the sync respects, or syncs use
  rsync --exclude per an agreed manifest; validation agents should snapshot
  their diffs OUTSIDE the clone at each landing (now done).

## 2026-09-01 fn-summary-posts-lack-callee-saved-keeps (run1 io lane, /tmp/vsa-io-lane)
- missing: the landed whole-function summary posts (`WriteFnPost`/`WriteRFnPost`/
  `SwFnPost`, rows/Fn*Fold.lean) preserve only `ra/sp/gp/s0` — no `s1..s11`.
  Every io-DAG caller holds s-regs live across its callee seam
  (`__sfvwrite_r` keeps s1-s6 across `jalr fp->_write` = `__swrite`;
  `__sflush_r` keeps s0-s3; `_fputs_r`/`_fwrite_r` keep s0-s3 across
  `__sfvwrite_r`), so the landed summaries are unconsumable at those seams.
- workaround: NONE taken — amending the three pilots (the Law-3 move):
  ONE new ghost `sv : SRegs` (named-field s1..s11 bundle, def in
  SegToTripleFramed.lean beside `segRowFramed` + `sKeepL : SRegs → GRegs`),
  `sregs : GHolds c.σ (sKeepL g.sv)` field in each Pre/Post, keep lists
  extended `++ sKeepL g.sv` (keysG stays a literal → FrameOK still ONE decide).
  Template scripts/genfn_templates/counted_loop_fold.lean.tmpl updated to
  match so future gen_fn --fold output carries the keeps.
- cost: ~1 session-hour re-threading 3 fold files + olean regen; every fold
  landed WITHOUT the keeps would have paid a re-land later (caught at the
  first real consumer, before any io fold was stated).
- proposal: gen_fn fold emission should ALWAYS emit the full callee-saved
  keep set (ra/sp/gp/s0 + sKeepL) in summary posts — ABI preservation is what
  makes a summary spliceable; a post without it is a dead end.

## 2026-09-01 gen-transport-monolithic-obtain-explodes (run1 io lane)
- missing: gen_transport.py emitted the whole-module transport as ONE
  `obtain ⟨h0, …, h1243⟩ := h` over the full byte-conjunction — on the first
  big module (`__sfvwrite_r`, 311 instrs / 1244 bytes) elaboration blows past
  18 minutes (the pilots were ≤136 bytes, where the quadratic anonymous-
  constructor destructure was invisible).
- workaround: none used — generator restructured to PER-CHUNK transports
  (`<fn>Chunk<i>_of_agree_lo`, 64-wide obtain each, matching gen_code_lemmas'
  own chunking) + a top combiner; each lemma is pilot-sized again.
- cost: ~25 min of wall-clock discovery + 3 killed lean processes.
- proposal: applied directly in scripts/gen_transport.py (chunked emission is
  now the only mode); keep per-lemma elab budget in mind for EVERY generator
  that scales with function size — chunk at the same 16-instr boundary
  gen_code_lemmas uses.

## 2026-09-02 chainfacts-inblock-store-then-load-whnf-bomb (run1 io lane, main)
- missing: an in-block store-then-load transport for `ChainFacts` pins goals.
  When a block stores BEFORE it loads (`__sfvwrite_r` `dec8F`: 4 spills then
  `ld s1,0(s4)`), the `ld`'s `MemFacts` memory is the `stepMemM`-threaded
  store tower; `show LPins8 (<base image>) …` forces `isDefEq` between the
  `writeMap8` tower and the named base image — whnf of two abstract
  `ExtHashMap.insert` towers → elaborator STACK OVERFLOW (no error location;
  the in-block twin of the seg-frame-facts cross-block deep recursion).
- workaround: none — landing `pin8_peel_sd` (peel ONE disjoint 8-byte store
  image off a `Pin8`, `getElem_writeMap8_disjoint` per byte) beside
  `lpins8_of_pin8` in rows/FnSfvwriteFold.lean; goal shape: `show LPins8 _
  (<clean addr>) …` (memory stays a metavar — never respelled), `rw` the addr
  lemma, `lpins8_of_pin8`, peel outermost-store-first, close on the base image.
- cost: the io-lane session died here (stack overflow with no location, file
  left mid-flight); ~1h diagnosis by truncation bisect.
- proposal: promote `pin8_peel_sd` to WriteLogNF/ValueSpec beside
  `getElem_writeMap8_disjoint` when a second consumer appears; chain_facts doc
  should warn that pins goals after in-block stores are TOWER goals.

## 2026-09-02 leafwiden-entry-gap-persists (fleet B1-leaves re-attempt, post-a46b7ab)
- missing: a supplier for the `LeafWiden` conclusion of the AMENDED (entry-
  conditioned) leaf residuals.  The amendment closed the fleet's refutation
  witnesses (m0 = ∅ / sp = 0 / sret-in-code now contradict `EvalEntry`), but
  `LeafWiden = Widen (EvalExit …) … (stackFoot SL)` quantifies over EVERY
  config `c'` satisfying the bare `EvalExit`, and `EvalEntry` constrains only
  the ENTRY config `c` and `m0`.  Two independent gaps: (1) `pres` needs
  `MemExtends m0 c'.σ.mem`, but `EvalExit.memFrame` carves out
  `[SL.lo, sp) ∪ [A.lo, A.hi) ∪ [sret, sret+24)` — an exit config with a
  presence-dropped byte there still satisfies `EvalExit`; no `EvalEntry` field
  reaches `c'`.  (2) `surv` needs `StoreRepr` survival under rewrites of the
  FULL `stackFoot SL = [SL.lo, SL.hi)`, but `EvalEntry.store_survives`'s
  footprint is only `[SL.lo, sp) ∪ [sret, sret+24)` — the caller-stack strip
  `[sp.toNat, SL.hi)` (nonempty whenever `StackOK`'s `sp ≤ SL.hi` is strict)
  and the arena drift `memFrame` permits on `A` are both uncovered; the
  `EvalExit.store` route needs A/AST/strings ∩ `[SL.lo,SL.hi)` = ∅, absent.
- workaround: NONE — fields skipped; gap machine-checked as named premises in
  `experiments/fleet/obstructions/B1_leaves_reattempt.lean`
  (`LeafEntryGap`, `skelH{Int,Null,Bool,Str}_of_entryGap`).
- cost: B1 stays 0/4; any worker re-dispatched on these fields re-derives this.
- proposal: EITHER (a) re-land the four leaf sims to conclude `EvalExitD`
  directly from their write chains (they already prove `MemExtends` + the
  survival witness internally — `EvalIntSim2.lean:835-844`) and restate the
  residuals without the `Widen`-over-bare-`EvalExit` shape, OR (b) widen
  `EvalEntry.store_survives` to the full stack region + drop the arena
  carve-out from leaf `EvalExit.memFrame` (leaves allocate nothing), making
  `LeafEntryGap` dischargeable.

## 2026-09-02 evalentry-missing-nbs-callee-geom (fleet B1-leaves re-attempt)
- missing: entry-side suppliers for the null/bool/str CALLEE geometry the
  amended `{Null,Bool,Str}LeafResid` still assert about `c.σ.mem`/`SL`/`sp`/
  `sret`: `Value_{null,bool,str}Loaded`, `{Null,Bool,Str}SlotPinned`, the
  sret-vs-`value_*`-window and window-vs-stack disjointness, and the tag-3/2/1
  jump-table-slot stack disjointness.  `EvalEntry` carries ONLY the int-pilot
  geometry (`value_int_code`, `int_slot`, `sret_vicode_disjoint`,
  `vicode_stack_disjoint`, `table_stack_disjoint` at slot 0); the value_null/
  bool/str windows `[0x800027ec,0x8000282c)` and table slots +4..+16 are
  independent byte/layout facts (e.g. `sret = 0x800027e0` satisfies every
  `EvalEntry` sret conjunct yet straddles the value_null window).
- workaround: NONE — fields skipped; the exact residual geometry is pinned as
  `{Null,Bool,Str}GeomOfEntry` premises in
  `experiments/fleet/obstructions/B1_leaves_reattempt.lean`.
- cost: hNull/hBool/hStr undischargeable regardless of the LeafWiden fix.
- proposal: the `GeomFrom`/`TermShared.geom` supplier layer the TSV already
  names — widen `InterpCodeLoaded` to the whole `value_*` text + a
  `KindSlotPinned`-family table pin + one stack/sret-vs-interp-image
  disjointness field in `EvalEntry` (the `EvalNullEntry`-minus-`EvalEntry`
  delta, stated once, drawn by all three rows).

## 2026-09-02 leaf-reseat-blocked-on-entry-footprint (wave 47d, B1-leaves re-seat on main)
- missing: an entry-side supplier for store survival over the CALLER STRIP
  `[sp.toNat, SL.hi)`.  The re-seat per proposal (a) of
  `leafwiden-entry-gap-persists` was attempted and is INSUFFICIENT alone: the
  survival witness the leaf sims prove internally
  (`EvalIntSim2.lean:836-859`, `hagree6`/`hstoreSurv6`) is the entry
  `store_survives` transported through the spill chain, footprint
  `[SL.lo, sp) ∪ sret-window` — but the motive-fixed `EvalExitD`/`Widen`
  survival clause is at `stackFoot SL = [SL.lo, SL.hi)` (and must be: the
  recursive caller's post-sub-call writes land in `[sub_sp, sp)`).  The strip
  `[sp, SL.hi)` is covered by NOTHING: `StoreRepr` pins only frames/closures
  to the arena (`frames_arena`/`closures_arena`); binding-name strings and
  `fn_expr` AST nodes are region-unpinned, so no disjointness route.
- workaround: NONE — fields NOT discharged.  Verdict machine-checked in
  `experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean`:
  `EntryStackSurv` (the widened-footprint entry survival) + `LeafExitPin`
  (the block-interface re-land: `MemExtends m0` + no-arena-drift mem pin) are
  JOINTLY SUFFICIENT — `skelH{Int,Null,Bool,Str}_of_pins` are record fills
  given them (+ the independent null/bool/str callee geometry).
- cost: B1 leaves stay 0/4; any re-dispatch on proposal (a) alone re-derives
  this refutation.
- proposal: TWO-PART amendment, both halves mandatory: (1) widen
  `EvalEntry.store_survives` footprint `[SL.lo, sp)` → `[SL.lo, SL.hi)`
  (+ the matching `ExecEntry.store_survives`, `ExecEntry.lean:267` — exec→eval
  bridges construct `EvalEntry` from it).  Measured fan-out @ eb2a139:
  `store_survives :=` at 15 construction sites in 13 files, 43 use sites; use
  sites weaken (wide ⇒ narrow, one mono lemma), construction sites must supply
  the wider fact — ITEM-ZERO-scale wave, needs a fleet.  (2) re-land the four
  leaf sims' block interfaces (`ArmEntryK`/`PreEpilogueV` gain the
  `LeafExitPin` conjuncts; `blockD_v`'s `Q : Mem → Prop` parameter,
  `EvalSimCommon.lean:297+`, already transports them across the epilogue for
  free) and restate the leaf residuals without the `Widen`-over-bare-`EvalExit`
  shape.  Geometry gap (`evalentry-missing-nbs-callee-geom`) unchanged.

## 2026-09-02 entry-footprint-amendment-conduit-fanout (wave 47e, EntryStackSurv landing)
- missing: a SINGLE named store-survival predicate reused by every interface on
  the entry→child-entry supply chain.  The `EvalEntry.store_survives` footprint
  amendment (`sp` → `SL.hi`) was measured at 15 ctor sites / 43 field-use sites,
  but the survival fact ALSO flows through ~a dozen INLINE ∧-tower literals
  (`blockA_k` pre, `ArmEntryK`, `armTail_v`/`armTail_rec`/`armTail_rec_es` pres,
  the `ArmSegSplit*` bundles, `ExecBlock`, `LoopHeadDispatchGeom`,
  `ApproxArmReseat` twins, the 2 `ExecRecCommon` `hstoreSurv` premises) — each
  restating the window inline, so the amendment had to be applied at every
  conduit, not just the named fields.
- workaround: widened each inline literal in place (same one-line ¬-implication
  fix at each seam; children get EASIER — sub-sret windows are absorbed by
  `[SL.lo, SL.hi)`).  Helpers `storeSurvSp`/`EvalEntry.store_survives_sp`/
  `ExecEntry.store_survives_sp` recover the old form where an sp-window
  consumer remains.
- cost: ~25 files hand-touched instead of the measured 13; a full-cone regen.
- proposal: name the predicate ONCE (`StoreSurvives N A SL φf φc S sret m`
  := ∀ m', agreement outside `[SL.lo,SL.hi)` ∪ sret-window → `StoreRepr m'`)
  and re-seat the towers on it, so the NEXT footprint change is one def.

## 2026-09-02 strleafgeom-payload-ast-region (wave 47f, GeomFrom callee-geometry layer)
- missing: an AST-region supplier for the `.str`-literal PAYLOAD facts of
  `StrLeafGeom` — under `EvalEntry … (.str s) … c`, that every `p` with
  `read64 c.σ.mem (aExpr.toNat + 8) = some p` satisfies `p ≠ 0`,
  `p + s.length < SL.lo ∨ sp.toNat ≤ p`, and the sret-window disjointness.
  `ExprRepr`'s `.str` constructor (`Vsa/MemRepr.lean`) carries only
  `read64` + `CString` — NO region facts — and the facts mention `SL`/`sp`/
  `sret`, so no per-node repr amendment alone can carry them; child entries
  are built for arbitrary SUBexpressions, so the fact must cover every
  `.str` node reachable in the program AST (an AST-arena invariant), not just
  the entry node.
- workaround: NONE for the facts themselves — pinned as the ONE named premise
  `StrPayloadGeom` (`rows/Field_hStr.lean`); the CODE/SLOT half of
  `StrLeafGeom` is now discharged from the amended `EvalEntry`
  (`field_hStr_of_payload`), so `hStr`'s residual shrank from 7 conjuncts to
  the 2 payload ones.
- cost: `hStr` stays NOT_FOUND in the census (hNull/hBool flip); any lane
  needing str-leaf entry payload geometry re-derives nothing but must thread
  `StrPayloadGeom`.
- proposal: an AST-region bundle — an `ExprRegion` invariant (all AST nodes +
  their string payloads live in `[AST.lo, AST.hi)`, one `EvalEntry` field
  `ast_region : ExprRegion …` + `AST`-vs-stack/sret disjointness literals),
  with `ExprRepr`-determinism (`read64` pins `p` uniquely) turning the
  per-node facts into projections. Same amendment shape as wave 47f's
  `nbs_pins` (entry field + child transport via stack-confined writes).

## 2026-09-02 strpayloadgeom-supplier-verdict (wave 47g, bounded StrPayloadGeom-supplier task)
- missing: same gap as `strleafgeom-payload-ast-region` — RE-SURVEYED for a
  supplier and machine-checked NONE EXISTS on main: `ExprRepr.str`
  (`Vsa/MemRepr.lean`) = `read32`+`read64`+`CString` only (`p = 0` not even
  excluded); `StoreRepr` `A.contains` covers frames/closures ONLY (the AST is
  not a store object); `ProgramRepr`/`StmtArrayRepr` are pure pointer-chase;
  `Layout.atInterpRun` (`Vsa/Refinement.lean`) is fully abstract. No
  `A.contains`/region fact anywhere mentions AST nodes or string payloads.
- workaround: NONE (Law 4). Landed the gap as ONE named premise
  `EvalEntryStrAstRegion` + named-field `StrPayloadIn` (`rows/Field_hStr.lean`)
  — the `.str`-root projection of the proposed `ast_region` `EvalEntry` field,
  stated in the TRANSPORT-CLOSED whole-stack form (`hi ≤ SL.lo ∨ SL.hi ≤ lo`),
  so child entries (`sp - 1088` scribble, in-stack `subsret`) are absorbed —
  and machine-checked `field_hStr_of_astRegion : EvalEntryStrAstRegion →
  ∀ st s, StrLeafResid st s` (green, axiom-clean).
- cost: `hStr` stays NOT_FOUND (census 3/58); the amendment wave inherits zero
  geometry rework — it must supply ONLY the premise (entry field + hereditary
  `ExprNodesIn` mirror of `ExprRepr` with memory-agreement transport + the
  4 child-entry construction sites + the ~35-file conduit threading, the 47f
  `nbs_pins` shape; top-level supply is a parse-arena/Layout fact, M6).
- proposal: unchanged from `strleafgeom-payload-ast-region`; the interface is
  now LANDED, so the amendment's target statement is pinned in code.

## 2026-09-02 entry-needs-complete-audit-and-ground-interface (wave 47h)
- missing: the COMPLETE entry-side need set (three serial EvalEntry amendments
  47e/f/g each added one class; a fourth was named; Law 3 demanded the factor).
  Audited from every machine-checked source (obstruction verdicts, Field_h*
  conditional discharges, all 55 NOT_FOUND fields' residual carriers):
  entry-suppliable = N1 full eval table pins + N2 stmt table pins/disjointness
  + N3 AST region + N4 arena literals + N5 result-slot-in-stack; everything
  else is X-class (residual statements, block re-lands, motive layer, callee
  seams) — table in `experiments/entry-needs-audit.md`.  NEW Law-4 finding:
  the `hMcallPop` totality oracle (∀ mcall agreeing off-stack, TOTAL on Nat)
  is unsuppliable by ANY amendment — no finite `Mem` is total (machine-checked
  `experiments/fleet/obstructions/McallPopTotality.lean`, pigeonhole via
  `size_erase`; instantiating `mcall := m0` already demands `m0` total).  Its
  honest fix is a residual re-statement (presence on the dead-byte window),
  and it blocks hNeg/hNot/the logical four INDEPENDENTLY of geometry.
- workaround: NONE needed for the interface — LANDED green+axiom-clean+wired:
  `Vsa/Sim/MemRegion.lean` (`ExprIn`/`StmtIn` hereditary region mirror,
  structural not inductive, reads conditional so child projection is direct;
  `exprIn_agreeP`/`stmtIn_agreeP` transports; pairs with the LANDED
  `AstTransport.exprRepr_agreeP` — `ExprFp ⊆ [lo,hi)` bridge is the one
  bounded follow-up), `Vsa/Sim/rows/LayoutStmtTableGen.lean` (GENERATED
  `groundStmtSlot_0..8`, gen_layout.py extended; all 9 stmt slots decode to
  the pinned `execArm*` PCs), `Vsa/Sim/EntryGround.lean` (`KindTablePins`/
  `StmtTablePins`/`AstRegionPins`/`StmtRegionPins`/`RetSlotGeom` bundled as
  ONE `EvalGround`/`ExecGround` each + `survive_stack` transports),
  `Vsa/Sim/rows/EntryGroundRows.lean` (record-fill discharges:
  `strAstRegionBody_of_ground` = the exact `EvalEntryStrAstRegion` ∃-body so
  hStr closes at insertion; `execGround_caseGeom_brk/cont` + generic
  `execGround_slot_window`; `kindTablePins_of_bytes`/`stmtTablePins_of_bytes`
  M6 suppliers off the generated pins).
- cost: the INSERTION (one `ground` field per entry) is NOT applied — it is
  the measured fleet-scale fan-out (15 ctor sites / the 26-file `NBSPins`
  conduit / ~304-file regen, map in the audit §D), beyond one lane with one
  lean process; census stays 3/58 until it lands.
- proposal: dispatch the insertion as the next fleet wave with the audit §D
  map; every site's supply term is pre-proved here, so it is pure record
  plumbing.  No future wave should touch EvalEntry/ExecEntry beyond inserting
  `ground` — the audit shows no sixth entry-suppliable class exists.

## 2026-09-02 child-ground-at-same-windows (47i recovery, arm-dispatch conduits)
- missing: (a) `EvalGround.child_node` — re-cut the ground to a CHILD node at
  the SAME `(sp, sret)` windows (identity re-cut; `child_params` over-demands
  `subsret+24 ≤ sp`, false for the parent's own sret which sits ABOVE `sp`);
  (b) `exprIn_call_callee` — the `.call` callee `ExprIn` projection (kit had
  binary/logical/assign/stmt-expr only).
- workaround: NONE — both added to `Vsa/Sim/EntryGroundKit.lean` this wave;
  the arm-dispatch combinators (`evalArmDispatch_of_slot`/
  `execArmDispatch_of_slot`) instead carry the child ground as a NEW
  `ExtrasRecord.ground` field (supplier-side), transported/`child_params`-re-cut
  inside the combinator.
- cost: the Group-A/B dispatch residual suppliers (M6 layout wave) must now
  fill `ground` per row — they will use exactly (a)+(b) plus
  `stmtIn_expr_child` on the entry's `EvalEntry.ground`/`StmtRegionPins`.
- proposal: when the M6 supplier wave lands, fill the extras `ground` fields
  through `child_node`/`child_at`; exec rows also need the eval-side
  `KindTablePins` half from `kindTablePins_of_bytes` (NOT in `ExecGround`).

## 2026-09-02 exec-leaf-record-fill-gated-on-X3 (Wave 0 0a, wave 48a)
- missing: hSBrk/hSCont are NOT record-fills post-`ExecEntry.ground`-insertion,
  contra `design/singletons.md` §S-exec-leaf. `execGround_caseGeom_brk/_cont`
  supply only slot+table halves of `ExecCaseGeom`; the `ExecLeafWiden` conjunct
  is X3 (block re-land). Machine-checked: the plain unpinned `ExecLeafWiden` is
  NOT `ExecEntry`-derivable (`ExecExit.memFrame` forgets in-`[SL.lo,sp)`
  presence). Probe: /tmp/w0probe/Probe.lean.
- workaround: NONE for the flip. Landed the SAFE half — the exec twin of the
  47e eval-leaf payoff (`Vsa/Sim/rows/ExecLeafD.lean`): `ExecLeafMemPin`,
  `ExecExitPinned`, `ExecLeafWidenP`, `execLeafWidenP_of_entry` (PROVED from the
  entry alone at `PhiExtends.refl`, axiom-clean), `execExitD_of_pinnedExecExit`.
- cost: the flip now needs ONE bounded block re-land — `execBrkSim`/`execContSim`
  concluding the pin (facts exist: `ExecBrkCont.lean:726` `hmemframe6`, `:495`
  `hmem7e`; only `pres` = MemExtends needs the spill-presence chain threaded) +
  moving brk/cont `ExecCaseGeom`/`execBrkSimD`/`execContSimD` to the pinned
  family (mirroring `evalIntSimD` using `LeafWidenP`).
- proposal: dispatch that re-land as the exec-leaf task; `field_hSBrk`/`_hSCont`
  are then one-liners off `execLeafWidenP_of_entry` + `execGround_caseGeom_*`.

## 2026-09-02 spec-driver-call-opacity (invgen relational batch, gap-1 closure)
- missing: the general spec-trace driver (scripts/spec_trace_driver.lean.tmpl) is
  an EXECUTABLE mirror of the WHILE relation (Semantics.lean is relational Prop,
  not runnable), and it evaluates `.call` OPAQUELY — it emits the call-site event
  but never descends into the callee body. So on any `.wl` with a called function
  (scope.wl `fn shadow`, functions.wl, rec_fib.wl) the machine trace has strictly
  MORE stmt/expr events than the spec trace (the callee's ret/binary/etc.), giving
  spurious per-kind count mismatches (e.g. hInitStore: machine ret=1, spec ret=0).
- workaround: the relational miner aligns by (kind, ordinal) and only flags a
  CONTRADICTION on value-repr disagreement of an ALIGNED event, never on a
  kind-count divergence — so call-opacity does NOT produce false falsity claims.
  Kind-count divergence is reported as an informational signal, not a contradiction.
- cost: relational coverage on env-seam call cases (hCall*, hSVarInit) is limited
  to the pre-call prefix events; the callee-body conjuncts (the crux hCallClosure
  depth/budget relations) are NOT minable until the driver models call descent
  (needs a store/closure model — the executable Call relation, non-trivial).
- proposal: extend the driver's `.call` to push a frame and execute the closure
  body under a depth counter (mirrors env_new + ExecSeq); this also unlocks the
  depth/store-size conjuncts the stackBudget ladder wants. Scoped out of this
  batch (design-time; ZERO-LLM mechanical run only).

## 2026-09-02 value-repr-needs-arm-exit-probe (invgen loop-arm relational)
- missing: a value-repr conjunct `gprGet a0 = reprOf(spec value)` needs the
  machine to probe the BOXED RESULT pointer (a0 at the arm EXIT, after
  value_int/value_bool boxes the computed value) and read back its payload.
  The eval DISPATCH PC 0x80003164 reads the node KIND word; the a2+8 word there
  is the node's operand field (an AST pointer), not the value — so a value-repr
  probe at dispatch produces SPURIOUS mismatches (e.g. hIAdd logical#2 machine
  24 = operand ptr vs spec 2 = bool-true).
- workaround: DISABLED payload/value-repr conjunct mining for the loop-arm and
  value-box-tail clusters; the kind bridge (read32[node]&0xff = kindOfExpr) is
  the solid mined fact those cases carry. No false CTIs emitted.
- cost: value-repr (the Approx `reprOf` conjunct — the highest-value stage-3
  target) is NOT mined this batch; only the kind/slot bridges are.
- proposal: add an arm-exit probe point per arm (the PC after the value_* jal
  returns, dumping a0 + read64[a0+8] payload) and align it to the spec vint/vtag
  at the corresponding eval event. One extra trace PC per arm; mechanical.

## 2026-09-02 execblocka-memextends-unexposed (wave 48b / X3 exec-leaf re-seat)
- missing: `execBlockA` (`ExecBrkCont.lean`) does NOT expose `MemExtends m0 ment`
  (presence monotonicity of the arm-entry memory over the entry `m0`).  Its output
  `ExecArmEntryK` carries only the m0-*agreement* frame (`∀k ¬(SL.lo≤k<sp)→
  ment[k]?=m0[k]?`), which is silent on presence INSIDE the stack window.  The
  eval twin (`blockA_k`, `EvalSimCommon.lean:907`) DOES expose `MemExtends m0
  ment` — the asymmetry is the whole X3 gap: it blocks the exec-leaf pin `pres`
  (`ExecLeafMemPin.pres`), hence hSBrk/hSCont.
- workaround: named it as one typed premise `ExecArmMemExt st status` (the exit
  pin `ExecLeafMemPin`) and built the ENTIRE pinned re-seat around it
  (`rows/ExecLeafPin.lean`, axiom-clean).  Fields `field_hSBrk`/`field_hSCont`
  discharge MODULO it.  STOPPED short of the amendment (Law 4).
- cost: the amendment lands `MemExtends m0 ment` into the SHARED `ExecArmEntryK`
  ∧-tower → ~10-file positional-destructure fan-out (ExecBrkCont/ExecDispatch/
  ExecRecCommon + 6 Stmt*ArmStagePre rows) + `PreExecEpilogue` twin.  ITEM-ZERO
  scale.  Every future exec-leaf/rec case that wants presence pays it once here.
- proposal: amend `execBlockA` to thread `MemExtends m0 ment` (trans of the 5
  prologue `memExtends_writeMap8` over `hmem2e..hmem6e`, already in-proof) and
  append it as the LAST conjunct of `ExecArmEntryK`; mechanically extend the ~10
  full destructures with one trailing binder + the 2 constructions (execBlockA,
  execDispatch — dispatch writes no memory so `ment = c.σ.mem`, `MemExtends.refl`)
  with one term.  Then `ExecArmMemExt` is a one-liner and hSBrk/hSCont flip to
  6/58 with zero further proof.  This is the exec `EntryStackSurv`/`LeafExitPin`
  analog — a dedicated wave, NOT a bounded gate.

## 2026-09-02 execarmmemext-exit-not-entry (wave 48c / exposure landed, flip still blocked)
- missing: the wave-48b proposal above was HALF right.  The `ExecArmEntryK`
  `MemExtends m0 ment` exposure is now LANDED (execBlockA + execPrologue/
  execDispatch + ExecDispatchReady + all 8 tower consumers threaded, green+
  axiom-clean).  But it is NOT sufficient to flip hSBrk/hSCont: `ExecArmMemExt
  st status` is stated over the POST-EPILOGUE exit (`ExecExit → ExecLeafMemPin
  SL sp m0 c'.σ.mem`), whose `pres = MemExtends m0 c'.σ.mem` is about the EXIT
  memory, not the arm-entry `ment`.  A bare `ExecExit` does NOT carry presence
  (only `memFrame` = arena/retslot-excluded agreement), so `∀ ExecExit → pin` is
  provably underivable — CONFIRMED by construction (ExecExit has no `pres`/
  `memExt` field; ExecEntry/ExecExit grep clean).
- workaround: NONE for the flip (Law 4).  Landed the mandated general exposure;
  hSBrk/hSCont stay `hole`/NOT_FOUND (census UNCHANGED 4/58 — honest).
- cost: the flip needs the presence threaded to the EXIT, i.e. `execBlockA`'s
  `MemExtends m0 ment` (now available) carried through the arm `li a0` (mem
  unchanged) AND the SHARED `execBlockD` epilogue (pure loads, `cD.σ.mem =
  ment`) into an `ExecExitPinned` conclusion — the exact eval-side move
  (`evalIntSimP` concludes `EvalExit ∧ LeafMemPin`; `IntLeafResid`@`LeafWidenP`;
  `field_hInt = leafWidenP_of_entry hc`).  Blast radius: `execBlockD` has 7
  recursive-case callers (ExecVarDecl/ExecExprRet/ExecVarNull/ExecIf/ExecWhile
  /…) whose `m0` baseline is post-sub-call `cG.σ.mem` — strengthening its
  conclusion breaks all; OR add `pres` to `ExecExit` (~20 constructions incl
  Call/Native marshalling that DO write arena).  Either is a genuine ≤1-session
  wave, not a bounded single-lean-process gate (recursor-wiring green-tree risk).
- proposal: dedicated wave X3-c: (1) `execBrkSimPinned`/`execContSimPinned` in
  ExecBrkCont concluding `ExecExitPinned` — needs `cD.σ.mem = ment` exposed from
  execBlockD (add it as a light conjunct on the brk/cont path ONLY, or a
  standalone `execBlockD_memEq` lemma over its pure-load steps); (2) re-state
  `BrkResid`/`ContResid` at `ExecLeafWidenP` (pinned, `ExecCaseGeom` variant);
  (3) re-point `exec_brk_row`/`exec_cont_row` to the pinned `execBrkSimD`; (4)
  `field_hSBrk`/`field_hSCont := execLeafWidenP_of_entry hc` (drop the premise).
  Mirrors Field_hInt.lean exactly.  THEN 6/58.

## 2026-09-02 X3-c-LANDED (wave 48d, execBlockD presence transport)
- missing: (RESOLVED) the exec-leaf pin was recovered from a bare `ExecExit`
  (`ExecArmMemExt`) — provably underivable (wave-48c obstruction). The eval
  precedent (47e) never did that: it CARRIES presence through the epilogue.
- workaround: NONE — landed the mandated general move, mirroring eval exactly.
  (1) `execBlockD` gained `Q : Mem → Prop` (pre `∧ Q mpre`, post `∧ Q c.σ.mem`,
  transported by `hmem7e` across the memory-pure epilogue) — exec twin of
  `blockD_v`'s `Q`. (2) `execBrkSim`/`execContSim` now CONCLUDE `ExecExitPinned`
  (brk via `Q := ExecLeafMemPin SL sp m0` through execBlockD; cont inline), pin =
  ⟨arm `MemExtends m0 ment`, arena-inclusive arm frame `hmemframe`⟩. (3) moved
  `ExecLeafMemPin`/`ExecExitPinned` UPSTREAM to `ExecBrkCont.lean` and
  `ExecLeafWidenP`/`execLeafWidenP_of_entry`/`execExitD_of_pinnedExecExit` into
  `ExecCaseGeom.lean` (dodging the ExecLeafD↓ExecCaseGeom↓ExecBrkCont cycle);
  `ExecCaseGeom` now carries the PINNED widener; `execBrkSimD`/`execContSimD`
  re-point at `execExitD_of_pinnedExecExit`. (4) `field_hSBrk`/`field_hSCont`
  are now PREMISE-FREE (widener from `execLeafWidenP_of_entry hc`, slot/table
  from `hc.ground`). `ExecArmMemExt` DELETED.
- cost: ~1 lean-process/file; zero recursor-tree re-threading (the change is
  confined to the brk/cont leaf bundle — recursive cases use `ExecRecCaseGeom`,
  untouched). NO fourth rung emerged — the eval-mirror hypothesis HELD.
- proposal: (DONE) the presence-transport `Q` is now on both `blockD_v` (eval)
  and `execBlockD` (exec); any future leaf epilogue reuses the same shape.

## 2026-09-02 crux-depth-counter-is-runtime-not-sp-nesting (invgen crux depth-descent)
- missing: nothing broken — a DESIGN-RELEVANT fact for the hCallClosure crux `d`.
  The closure-call depth trace (clo_depth.wl, /tmp/rl-trace/cruxDepth_trace.jsonl)
  shows the machine `call_depth` counter at `8(s2)` (read/bumped at `0x8000329c`,
  DECREMENTED on return via `--call_depth`) is a RUNTIME quantity tracking the
  currently-active closure-call chain — it is NOT the sp-static lexical nesting
  (which also counts top-level `println` frames and does not unwind on sibling-
  call return). So `reconstructed_sp_depth != call_depth` across sibling calls is
  EXPECTED, not a falsity. The crux's spec `d` (a_3 : d < maxCallDepth) == this
  COUNTER. Within one pure recursion chain they move in lockstep (mined: countdown
  d=0..4, per-descent sp delta CONSTANT 1264 = evalFrame+execFrame).
- workaround: the crux miner (scripts/mine_crux_ladder.py) isolates pure-recursion
  chains (d increments by 1 with sp descending) to report the clean per-level
  ladder, and annotates the counter-vs-sp divergence as expected rather than
  flagging it as a contradiction.
- cost: none; the miner's R3 was initially mis-flagged as a mismatch then corrected.
- proposal: the crux invariant should index the budget ladder by the machine
  call_depth counter (the spec d), NOT an sp-reconstruction — StackNeed already
  does (`(maxCallDepth - d) * perCallBudget`). Mined constants MATCH: per-descent
  eval frame 1088 = evalFrame, recursion level 1264 = evalFrame+execFrame, all
  <= perCallBudget 6144; StackOK.child carries 1088 through the ladder axiom-clean
  (/tmp/crux_budget_probe.lean). Design VALIDATED, no amendment needed.

## 2026-09-02 binarmextras-overquant-blocks-both-cures (wave 48e X2 entry-carry)
- missing: an entry-derivable `BinArmExtras`. Cure A (int/eq cells) was specced
  as "add `EvalEntry` hyp to `BinIntCellResid`/`BinEqCellResid`, value paths
  relight verbatim". BUT `BinIntCellResid` packs a whole `BinArmExtras`, three
  of whose fields are the SAME over-quantified `∀m`/`∀mcall` shape prove-unary
  machine-refuted for the 6 unary residuals:
  `mem_ext : ∀m, (∀a ¬(SL.lo≤a<sp)→m[a]?=m0[a]?) → MemExtends m0 m`,
  `frame_pop` (presence on [sp-1120,sp)), `x13_pres`. `EvalEntry`'s finite pins
  do NOT force [SL.lo,sp) populated, so these are FALSE as ∀-conclusions —
  machine-checked `experiments/fleet/obstructions/BinArmExtrasMemExtOverquant.lean`
  ({propext,Classical.choice,Quot.sound}). So the int-cell prover's slot6-only
  refutation UNDER-reported: cure A as literally stated cannot relight the cells;
  the root cause is IDENTICAL to cure B's `∀mcall` pair.
- workaround: NONE (stopped, Law 4). Harvested the machine-checked obstruction.
- cost: the "add EvalEntry hyp only" recipe would loop forever — the amended
  `BinIntCellResid` is still false. Any agent re-attempting cure A pays it again.
- proposal: `blockA_binaryArm` ALREADY produces `MemExtends m0 ment` intrinsically
  (`blockA_k`'s 2nd output, `EvalIntSim2.lean:324` `_hpresM`), so `BinArmExtras.mem_ext`
  is REDUNDANT — DROP it and consume `_hpresM`. Same restatement class as cure B:
  drop the 3 `∀m`/`∀mcall` closures from `BinArmExtras` (`mem_ext`/`frame_pop`/
  `x13_pres`) and the 2 from each unary/logic `*Resid`, thread the concrete
  post-dispatch `ment`/`mcall` (a writeMap extension of `m0`) from
  `blockA_binaryArm`/`blockB_unary` output. Multi-file cone: `BinArmExtras` +
  `blockA_binaryArm(_budgeted)` + 11 `binRow_*` + 10 `eval*Sim` + 6 unary sims.
  Feasible (the intrinsic facts exist) but NOT a one-field tweak; not landable
  green in a single bounded pass without a broken-tree window.

## 2026-09-02 binarmextras-mem_ext-redundant-framepop-x13-are-new-rungs (wave 48f drop-and-thread)
- missing: (1) a NEW entry-ground frame-window presence field (`m0` populated on
  `[sp-1120,sp)`, honest footprint `[subsret+4,+8) ∪ [subsret+16,+24)`, subsret=sp-944);
  (2) a `blockA_k`/`ArmEntryK` widening that tracks `x13`(a3) live across the dispatch
  span `0x80003164→0x800034e8`. These are the true blockers of the 11 int/eq cells +
  6 unary/logic residuals, NOT the over-quant `mem_ext` closure 48e flagged.
- workaround: NONE for the two new rungs (STOPPED per Law 4). DID land the one clean
  redundancy: DROPPED `BinArmExtras.mem_ext` and threaded `blockA_k`'s intrinsic
  `_hpresM : MemExtends m0 ment` in `blockA_binaryArm` — the 48e "thread the concrete
  fact" move, which holds for mem_ext ONLY. Zero downstream churn (all consumers take
  `BinArmExtras` as a hypothesis, never project `.mem_ext`); census unchanged 6/58.
- cost: any agent re-attempting the "drop frame_pop/x13_pres + thread block output"
  cure pays a dead end: machine-checked `BinArmExtrasFramePopNewRung.lean` shows
  `frame_pop` is refutable as an isolated field and the dead sub-result bytes are
  unconstrained by ValueRepr / unwritten by the prologue ⇒ their presence reduces to an
  `m0` fact absent from EvalGround. `x13_pres` reduces to a config-liveness fact absent
  from ArmEntryK. Neither is a "thread the existing block fact" move.
- proposal: TWO rungs, in dependency order. (A) `EvalGround`/`EvalEntry` frame-presence
  field `∀a∈[sp-1120,sp), ∃b, m0[a]?=some b` (or the tighter dead-byte footprint) —
  supplies `frame_pop`'s concrete instance for `ment`/`mcall` via the memframe; then the
  B2 `EvalEntry`-hypothesis carry (X2 design) makes `BinIntCellResid` buildable modulo
  (B). (B) `blockA_k` widening: emit `∃w, c1.regs x13 = some w` as a 3rd output (the
  dispatch span 0x80003164→0x800034e8 provably never writes a3) — supplies `x13_pres`.
  With BOTH + the B2 carry, all 11 int/eq cells + the 6 unary/logic residuals' presence
  conjuncts relight. Each is a genuine statement/widening change, one bounded pass each.

## 2026-09-02 bin-cures-interlock-atomic-wave (wave 48g — the three cures do not decompose)
- missing: an ATOMIC landing of all three int/eq cures. Deep cone tracing shows they
  interlock and none is a standalone bounded gate:
  (1) x13 is LOAD-BEARING — `blockB_binary` reads a3 at arm entry and SPILLS it
  (`sd a3,0(sp)` → `writeMap8 ma (sp-1088) (sdData_val aEnvReg)`, EvalBinSim.lean~424,
  the env arg to the RIGHT sub-call), so `BinArmExtras.x13_pres` is NOT droppable; its
  honest form is `blockA_k` emitting `∃w, c'.x13=some w`, which changes blockA_k's output
  ∃-tower → all 18 blockA_k callers + the DOUBLED `EvalArmHeadExtras` combinator
  (ArmDispatchCombinator.lean:108/216) re-thread, AND needs a new `EvalEntry.x13_defined`
  field (blockA_k's pre-tower is reconstructed from EvalEntry fields, ArmEntryWiden.lean:75
  confirms EvalEntry carries no x13). (2) `frame_pop`'s presence is over the POST-sub-call
  memory `mcall` (SubEvalReturn, EvalNegSim2.lean:120/blockC_neg), NOT entry `m0` — the dead
  sub-result bytes are populated by the sub-`value_int` 24-byte buffer write, so the honest
  discharge is INSIDE the sim cone (SubEvalReturn), not a bounded `EvalGround` field; the
  ground-field alternative (48f proposal) needs an UNVERIFIED top-level `m0`-totality supplier
  on `[SL.lo,sp)` = a possible NEW falsity (the census's whole guard). (3) cure 1 (entry-carry)
  is a def change to BinIntCellResid/BinEqCellResid that forces skeleton regen + TermAssembly +
  dispatcher + 11 rows + 10 sims; alone it relights 0 (slot6/frame_pop/x13_pres still
  unprovable without 2+3). EvalGround appears in ~40 files (every survive_stack/child_*/
  transport_offstack + construction site carries any new field).
- workaround: NONE (STOP, Law 4). Landing any ONE cure relights 0 fields; the whole is a
  ~30-file broken-tree window with an unverified ground dependency, not a bounded lean-process
  gate. Machine-checked evidence: `experiments/fleet/obstructions/BinCuresInterlock48g.lean`
  (`field_hIAdd_still_refuted` axiom-clean — the int/eq cell is STILL false as stated, so no
  false lemma entered the tree; census honest 6/58).
- cost: any agent attempting a partial landing pays a broken tree (the output-tower change
  cascades through all binary consumers) OR an unsound ground field (cure-2 m0-totality).
- proposal: land as ONE wave in strict order with the tree GREEN only at the end: (0) verify
  `m0`-totality on `[SL.lo,sp)` from the M6 image OR re-route frame_pop's discharge through
  SubEvalReturn's buffer-write presence (preferred — no new ground field); (A) `EvalEntry.x13_defined`
  + thread x13 σ1..σ19 in blockA_k (mirror the ha1_* a1 chain) + emit as blockA_k 3rd output +
  update all 18 callers' output-tower destructure; (B) discharge frame_pop/x13_pres in
  blockA_binaryArm + EvalArmHeadExtras from (0)/(A), DROP both closures from BOTH extras
  structs, re-thread the 11 rows + 10 sims; (C) entry-carry on BinIntCellResid/BinEqCellResid,
  skeleton regen, relight 17. Estimated ≥2-3 bounded sessions or one long coordinated worktree
  pass; NOT a single-lean-process gate.

## 2026-09-02 fuzzer-descend-live-negresid (statement_fuzz --descend, tool task)
- missing: the `--descend` nested-quantifier mode independently machine-refutes
  HEAD's `Vsa.Sim.rows.TermRouting.NegResid` `mem_ext` conjunct
  (`∀ mcall, agree-off-[SL.lo,sp) → MemExtends m0 mcall`) — the SAME falsity as
  experiments/fleet/obstructions/UnaryLogicMemExtOverquant.lean. The raw ∀-mcall
  pair is byte-identical to 17773c4^ (pre-48e); wave 48f only dropped the
  BinArmExtras copy, not the TermRouting NegResid/NotResid/OrTrue/… copies.
- workaround: NONE (analysis-only; the descent probe reports it, does not gate).
- cost: the 6 unary/logical Resid in TermRouting.lean are STILL false as stated;
  any hand-prover instantiating them will refute (the obstruction files already
  did). Whoever lands eval_neg_row/eval_not_row/… will hit this.
- proposal: apply the wave-48f cure to TermRouting — carry the ONE structured
  post-call mcall's MemExtends/presence as a field (thread `_hpresM` from
  blockB), NOT ∀-mcall. `python3 scripts/statement_fuzz.py --acceptance-v2`
  will flip the live-head verdict to SURVIVED once done.

## 2026-09-02 fuzzer-v2-overfit (coordinator uncontaminated test)
- missing: GENERALIZATION in statement_fuzz --descend. The adversary builders
  key on the historical term forms, not the guard-shape semantics: novel
  probes with the same disease (agree-off-window → in-window demand) at fresh
  windows/demands/shapes ALL return SURVIVED, including two provably-false
  ones (experiments/fuzz-battery/NovelProbe.lean: NovelResidA/C false,
  NovelResidB true). v2's acceptance was contaminated (trained and tested on
  the same statements). v2 = regression guard for the 2 known instances ONLY.
- workaround: none needed yet — the hand-prover + Lean-refutation path remains
  the authority; v2 still catches recurrences of the two known forms.
- cost: false confidence if --descend SURVIVED is read as "no nested falsity".
  Verdicts from --descend must be read as "no KNOWN-pattern falsity".
- proposal: (a) v2.1: generic builder — detect any hyp `∀k, G k → m0[k]? =
  mq[k]?`, COMPUTE the uncovered address set from G, build the adversary
  generically; (b) the REAL fix is the SMT layer (countermodel search needs
  no builders — this is why the Z3 push is right): its acceptance MUST
  include experiments/fuzz-battery/NovelProbe.lean (uncontaminated: A,C →
  countermodel found + Lean-replayed; B → no model / valid-in-fragment).

## 2026-09-02 io-flush-loops-dead-on-ELF (invgen io machine-loop pass)
- missing: the flush/drain LOOP invariants that SEEDS-io S1 (`_fflush_r`/`__sflush_r`) posits as MINABLE — they are not, because the loop bodies are DEAD CODE on the proof ELF. stdout is unbuffered (main.c setvbuf _IONBF ⇒ `_flags`=0x10009, `_p`=`_bf._base`, `_w`=0 at every flush), so the drain `while(p<end)` at 0x8000ebf0/0x8000ec10 (the jalr→_swrite) NEVER iterates: the buffer is always empty at flush time.
- workaround: seeded S1 as the DEGENERATE-DRAIN instance (written=0, out unchanged, end=base) — a real SURVIVED fact, plus the mined FILE-field T1 constants. Also mined S2 (io_swbuf_r single-byte put, 6 calls, cursor+1) and S4 (io_sbprintf synthetic FILE, concrete fields) outright. 4 targets (io_putc_r/io_fputc_r/io_fwrite_r top-level io_fflush) are UNREACHABLE — 0 events on every print driver.
- cost: the S1 candidates cannot carry a nontrivial loop stride until/unless a BUFFERED-stdout ELF is added to the corpus; the interesting drain arithmetic (S1's `written=(p-base)`, out=out0++bytes[base,p)) is unexercised. For the real proof this is fine — the interp only ever hits the unbuffered path, so the degenerate invariant is the true postcondition. Flagging in case a future consumer expects a mined per-iteration drain stride and finds only the k=0 instance.
- who: invgen io machine-loop pass (wave 45). Candidate .lean files: experiments/invariants/io_{fflush_r,sflush_r,swbuf_r,sbprintf,vfprintf_r,fputs_r}.lean — all elaborate axiom-clean + statement_fuzz --descend SURVIVED.

## 2026-09-02 smt-refute-canonical-replay (smt_check.py SMT layer)
- missing: no general "Z3 model → verbatim Lean witness" transport for the
  over-quant Mem-window fragment. Z3's countermodels legitimately use
  2^64-scale BitVec values (ANY in-window point refutes the shape), and the
  raw agree-off-window arithmetic proof at those numbers is unwieldy in Lean.
- workaround: `scripts/smt_check.py --refute` uses Z3 only to CERTIFY the class
  is refutable (negation SAT); the auto-generated `¬P` Lean replay instantiates
  the CANONICAL small witness of the same class (window [lo,lo+16), one lethal
  byte at A=lo, m=∅ deletes it), model-guided only for `lo`. All 4 acceptance
  refutations (headroom / ∀-mcall MemExtends / presence / BinArmExtras.mem_ext)
  replay green + axiom-clean this way.
- cost: the replay certificate is class-canonical, not a faithful transcription
  of Z3's exact model. Sound for REFUTED-REPLAYED (a machine-checked ¬P is a ¬P
  regardless of which witness), but a consumer wanting the EXACT Z3 witness must
  read the printed model, not the probe. Opaque-constrained models are correctly
  NOT replayed (REFUTED-MODULO-OPAQUE).
- proposal: a `bv2int`-aware small-model extractor (Z3 `(minimize)` / soft
  bounds) that returns a genuinely small model when one exists, so the replay
  can transcribe verbatim; only fall back to canonical-witness when the class
  is inherently large-scale. Not built (acceptance passes without it).

## 2026-09-02 trace-unreachability-is-not-proof (coordinator refutation)
- missing: a reachability-verdict standard. The io miner marked 4 cases
  unreachable from ITS drivers; print(null) empirically refutes io_fwrite_r
  (null arm → fwrite → _fwrite_r, "nullnull" in the model), and the exit
  flush chain runs _fflush_r degenerately on EVERY program. Trace absence is
  driver-coverage-relative, never a proof of deadness.
- workaround: BATCH-REPORT verdicts corrected in place.
- cost: had REMAINING.md struck those suppliers, hCallPrint's null route
  would have hit a missing supplier at proof time.
- proposal: closing any supplier as dead requires (a) static call-graph
  unreachability from the live entries (disasm caller grep — cheap), or
  (b) driver coverage over ALL value kinds + exit paths. Add a
  full-kind driver (all 6 kinds + assert + error) to the standing t5 corpus
  as the reachability floor. putc_r/fputc_r remain dead-candidates pending
  the static check.

## 2026-09-02 smt-encoder-novelty-gap (coordinator uncontaminated test)
- missing: novel-form coverage in smt_check.py's Python encoder. History
  battery: full PASS (auto countermodels, 4 Lean replays). Uncontaminated
  battery (fuzz-battery/NovelProbe.lean): RecursionError on A/B, ENCODE-GAP
  on C — LOUD failures (safe, unlike v2's silent SURVIVED) but the
  generalization claim is unvalidated. The Python statement-parser is the
  bottleneck; the dump_smt_lib export-tactic route (elaborated-Expr walking,
  coordinator note in invariant-gen-plan) is the structural fix.
- cost: none silent; ENCODE-GAP/crash verdicts cannot be mistaken for green.
- proposal: encoder v2 = Lean-side dump_smt_lib tactic; hard acceptance =
  history battery + NovelProbe + a --gen-battery fresh sample (once v2.1's
  generator lands). No generality claims except via uncontaminated tests.
- RESOLVED 2026-09-02: encoder v2 LANDED (experiments/smt/DumpSmtLib.lean elab
  command + SmtReplaySupport.lean pop-lemmas; smt_check.py reworked with Python
  fallback + [enc:lean|python] tags). ALL gates PASS: (a) history --acceptance
  4/4 Lean replays; (b) NovelProbe A/C REFUTED-REPLAYED axiom-clean, B NOT-
  REFUTED; (c) --gen-battery fresh 10-sample 10/10 across seeds {3,7,11,99,123}.
  Key abstraction (Law 3): ONE universal agree-window replay witness (m0={A↦V},
  mq=∅ differ only at uncovered A; per-guard k≠A by omega) — cover-topology AND
  conclusion-kind agnostic; range-pinned C-shape uses a pop-populated m0. See
  invariant-gen-plan '## SMT encoder v2: export tactic'.

## 2026-09-02 fuzzer-v21-semantic-rule (statement_fuzz --semantic/--gen-battery)
- missing: (was) a GENERALIZATION of --descend. v2's ADVERSARY_BUILDERS keyed on
  historical term forms → overfit (fuzzer-v2-overfit). Now LANDED: the
  uncovered-address SEMANTIC RULE (scripts/statement_fuzz.py, --semantic).
  Guards→ℕ-IntervalSet algebra (pos/neg/multi-window, ∧=∩, hyps=∪), demands→
  (addr,kind∈{presence,value,agree,extends}), coverage=interval arithmetic;
  adversary = m0 corrupted at the uncovered demand address (erase/insert),
  agree-proofs discharged from guard shape by omega, m0=in-probe `crange`
  constant map. No name/form matching. Plus --gen-battery N: self-generates N
  probe PAIRS with ground truth by construction, un-trainable (fresh sample/run).
- workaround: NONE — the 2-row table is replaced by the rule for the literal
  fragment; the OLD builders are retained ONLY as the --acceptance-v2 baseline
  (pre-48f symbolic-window forms).
- cost: none new. Acceptance ALL green: NovelProbe A/C REFUTED axiom-clean +
  B SURVIVED; --gen-battery 20 = 40/40 on fresh seeds; --acceptance-v2 no
  regression; pre-48f still refuted.
- proposal: BOUNDARY — the rule owns the LITERAL address-map fragment. Guards
  with SYMBOLIC outer bounds (SL.lo, sp.toNat) are reported SURVIVED-as-SMT-
  territory (honest, positive) and remain the countermodel-search layer's job;
  the pre-48f live forms are those. The SMT layer subsumes both by pinning outer
  binders + negation-SAT; until it lands the retained builders cover the 2 known
  live symbolic forms. Non-address-map demands (ValueRepr/CString/reg-liveness)
  = SMT territory too.

## 2026-09-02 v21-fresh-probe-verdict (coordinator post-landing check)
- v2.1 semantic rule VERIFIED on a genuinely-fresh 3-window agree-demand
  probe (fuzz-battery/FreshTriWin.lean, written after v2.1 landed): analysis
  found the uncovered address correctly; probe-emitter lacks the agree-kind
  demand template → honest UNDECIDABLE (sorryAx surfaced, never silent).
  True twin SURVIVED. Backlog: agree-demand refuter template (small).
  Standing rule: each validation round uses a FRESH hand probe; used
  batteries are spent as evidence of generality.

## 2026-09-02 replay-emitter-lag (coordinator fresh-probe check, encoder v2)
- verdict: the SEARCH layer is general (Z3 SAT on both fresh falsities,
  FreshTriWin + FreshValDemand; true twin VALID) — the REPLAY generator is
  template-bound (both → ENCODING-GAP, loud, sorryAx surfaced). Same
  gap-class as v2.1's agree-demand emitter. Across all three validator
  generations: detection generalizes, auto-certification lags.
- operating mode until closed: search-layer flags are ACTIONABLE (the model
  pinpoints the witness); the Lean refutation is written by hand/agent in
  ~5 lines from the flagged witness. No silent verdict exists in any tool.
- backlog (one bounded task, not urgent): generalize the replay generator —
  synthesize map literals + discharge obligations from the MODEL generically
  (decide/omega), not from shape templates. Acceptance: the spent batteries
  + fresh-per-round probes.

## 2026-09-02 cegis-cure-generator (scripts/cegis_cure.py, tool task)
- missing: an automated "discover the cure" step. Waves 47e–48g found each
  amended Resid/field statement BY HAND. `scripts/cegis_cure.py` closes the CTI
  loop over STATEMENTS: given a (possibly-false) Prop it enumerates a bounded
  TEMPLATE SPACE of amendments — (i) entry-conditioning, (ii) quantifier repair
  (∀-ghost→footprint-bounded ∃), (iii) guard repair (agree-off-W→agree-on-W'
  over the interval algebra), (iv) conjunct deletion (block output supplies it),
  (v) oracle re-homing — filters them in cost order (syntactic elab → Z3
  --refute → v2.1 semantic rule → mined-artifact cross-check), ranks survivors
  by minimal-edit/premise-penalty, and writes experiments/cures/<field>.md with
  per-filter evidence + which landed assets each relights.
- workaround: N/A (tool landed). ACCEPTANCE (history-as-ground-truth,
  experiments/cegis/Accept{A,B,C}_*.lean reconstructing pre-47i NegResid /
  pre-48f BinArmExtras.mem_ext / the ∀-mcall pair): the landed cure appears at
  RANK 1 in all three (entry-conditioning / deletion / guard-repair+quant-repair).
  KEY FILTER-SEMANTICS FINDING: smt_check `--refute` gives false-positive
  REFUTED-MODULO-OPAQUE / ENCODING-GAP on the AMENDED (true) symbolic-window
  forms (opaque `True`; Z3-SAT-but-replay-sorry'd = spurious SAT) — only
  `REFUTED-REPLAYED` (machine-checked ¬P) is a genuine drop; MODULO-OPAQUE and
  ENCODING-GAP must be KEPT and deferred to the semantic filter. The semantic
  rule DOES bite on literal-window falsity (negative control: a NovelResidA-shape
  candidate is DROPPED, "adversary found at uncovered demand"), so the CTI
  channel is live, not a rubber stamp.
- cost: on symbolic-window Resids (SL.lo/sp.toNat outer-quantified) both Z3 and
  the semantic rule report "SMT territory / covered" and defer — so the tool
  ranks by template+edit-cost, it does NOT machine-refute the amended candidate
  there. That is the documented address-map-fragment boundary, not a tool bug;
  the enumeration is the containing space, the ranking is the heuristic.
- LIVE VALUE TEST (current still-false BinIntCellResid, wave-48g interlock's
  target): top candidate = ENTRY-CONDITIONING = the 48g recipe's cure (C)
  ("entry-carry on BinIntCellResid"). The report ALSO flags via the
  `extras-bundle-entry-pins` defect that the opaque `BinArmExtras` packs the
  over-quant closures (frame_pop/mem_ext/x13_pres) = the interlock (recipe A+B),
  which are inside-the-∃ block-output-threading moves, NOT single-statement
  edits — so the tool honestly does not claim to synthesize them. Matches the
  recorded recipe: cure C alone relights 0; A+B need the sim-cone/blockA_k work.
- proposal: (a) an LLM-rank stub is wired (`--llm-rank`, no API calls) for the
  structured-candidate synthesis the mining can't do (∃-body shaping); (b) a
  descent-into-∃ conjunct scanner would let (iv)/(iii) reach the BinArmExtras
  sub-fields once they are inlined as named-field structures (the 0a restatement
  wave) rather than opaque bundles.

## 2026-09-02 cegis-acceptance-contamination (coordinator calibration)
- the cegis_cure acceptance (3× rank-1 history rediscovery + 48g live match)
  is CONTAMINATED: the tool's inputs included the docs describing those
  cures. Its demonstrated value: correct ranking, honest interlock deferral,
  live negative control, the REFUTED-REPLAYED-only drop rule.
- CLEAN validation = PROSPECTIVE: run cegis on the un-cured clusters
  (env-seam, exec-arm Geom statements), commit the sealed suites under
  experiments/cures/ BEFORE any cure wave touches them; the landed cures
  later confirm/refute the predictions. Fold prospective runs into each
  cure wave's prep step.

## 2026-09-02 smt-joint-interlock-validation (tool task — smt_check --joint)
- missing: an INTERLOCK validator. `smt_check.py --refute/--validate` test ONE
  conjunct in isolation, so they PASS the exact cures 48e/48f/48g caught by hand:
  a per-statement filter cannot see that (i) the 48e entry-carry cure leaves
  frame_pop/x13 unsupplied by the available producer post, nor (ii) that an
  x13_pres DELETION makes the struct too weak for blockB_binary's a3 spill (a
  weaker Prop has no countermodel of its own → smt/semantic filters pass it).
- workaround: NONE — BUILT the joint layer. `smt_check.py` gains `--joint-inhabit`
  (all conjuncts SAT together under entry hyps; UNSAT=killer, all-opaque→
  UNKNOWN-OPAQUE), `--producer-check`/`--producer-traces` (post⇒each conjunct,
  APPROX from mined traces), `--consumer-check` (struct⇒each harvested demand),
  and `--joint` acceptance (gates a-d, 48e/48g as ground truth — ALL PASS:
  a=producer-check flags frame_pop+x13 under entry-only carry; b=frame_pop
  ground-field cure producer-FAILS; c=x13-deletion consumer-FAILS; d=48g recipe
  joint-SAT + no producer/consumer failure). Wired into `cegis_cure.py` as
  FILTER 3b (`filter_joint`, `--demands`): drops a candidate whose amended
  structure consumer-check-FAILS a load-bearing projection. Reuses the existing
  `_discover_struct` field-explosion — no new encoder fragment.
- cost: fixtures model the interlock in the encodable fragment (window presence /
  headroom / x13-as-presence-bit), NOT the full ValueRepr/ExprRepr opaque cone;
  those conjuncts report MODULO-OPAQUE honestly (never a silent pass). Real
  BinArmExtras run needs its mk-chain to encode past the opaque geometry fields.
- proposal: point `--joint`/`filter_joint` at the LIVE `BinArmExtras` (via
  `_discover_struct`) once its opaque geometry conjuncts get fragment encodings,
  and harvest real consumer `.field` projection sites for `--demands`.
