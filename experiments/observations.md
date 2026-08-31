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
