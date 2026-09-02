# Entry-needs audit — the complete EvalEntry/ExecEntry need set (wave 47h)

Three serial EvalEntry amendments landed this run (47e `EntryStackSurv`
footprint, 47f `NBSPins` callee geometry, 47g `EvalEntryStrAstRegion` named
premise) and a fourth was named.  Law 3: factor before the fourth.  This audit
collects EVERY remaining entry-side need from the machine-checked sources —
the fleet obstruction verdicts (`experiments/fleet/obstructions/*.lean`), the
`field_h*_of_*` conditional discharges (`Vsa/Sim/rows/Field_h*.lean`), the
observation ledger entries, and the statements of all 55 NOT_FOUND census
fields (their `*Resid`/`*Geom`/`*Extras` carriers) — so the NEXT entry
amendment is the LAST one.

Sources read (machine-checked artifacts, not prose): `B1_reseat_footprint_
verdict.lean`, `B1_leaves_reattempt.lean` (via its restatements), the amended
`NegResid`/`NotResid`/logical-four (`rows/TermRouting.lean`), `NegExtras`
(`EvalNegSim3.lean:63`), `BinIntCellResid`/`BinEqCellResid`
(`rows/BinDispatchRow.lean:719`), `VarLeafResid` (`rows/EvalVarRow.lean:59`),
`ExecCaseGeom` (`rows/ExecCaseGeom.lean:102`), `ExecExprGeom`/`ExecRetGeom`/…
(`rows/ExecRecRows.lean`), `IfNoneResid`…`WhileResid`
(`rows/ExecDispatchRows.lean`), `SeqNilResid`/… (`rows/SeqForRows.lean`),
`StrPayloadGeom`/`EvalEntryStrAstRegion` (`rows/Field_hStr.lean`), the current
`EvalEntry` (`InterpEntry.lean:288`) and `ExecEntry` (`ExecEntry.lean:207`)
field sets, and `StackOK` (`Alloc.lean:49`).

## A. Entry-suppliable needs (THE batched amendment)

| # | Need | Consuming fields | Derivable from | Amendment shape |
|---|------|------------------|----------------|-----------------|
| N1 | **Full eval jump-table pins** — `KindSlotPinned k (armPC k)` for ALL tags 0-10, not the per-wave trickle (`int_slot` tag 0, `nbs_pins` tags 1-3) | hVar (slot 4, `VarLeafResid`), hAssign (5), hIAdd…hIGe/hEq/hNe (6, `BinArmExtras.slot6`), hOrTrue/hAndFalse/hOrFalse/hAndTrue (7), hNeg/hNot (8, `NegExtras.slot8`), hCall/hArgsNil/hArgsCons (9), hFn (10) | `Loaded L` rodata bytes via the GENERATED `LayoutJumpTableGen.groundSlot_0..10` (wave 43; byte-pin-conditioned) | `KindTablePins m` named-field bundle (`∀ k < 11` form), ONE `EvalEntry.ground` sub-field; transport = 44-byte table-window agreement (`table_stack_disjoint` already whole-table since 47f) |
| N2 | **Stmt jump-table pins** — `StmtSlotPinned k (execArm k)` for ALL stmt tags 0-8 + whole-table stack disjointness `[0x80019fb8, +36)` | ALL 14 exec-arm fields: hSBrk/hSCont (`ExecCaseGeom.hslot/htableStk`), hSExpr/hSRet/hSRetNull/hSVarNull/hSVarInit (`Exec*Geom`), hSIfNone/hSIfTrue/hSIfFalse/hSWhileFalse/hSBlock/hSForStart/hSWhileBreak | `Loaded L` rodata; slot bytes VERIFIED against all nine landed `execArm*` PCs this audit (base-relative sign-extended, table @`0x80019fb8`); generator = `gen_layout.py` extension (`LayoutStmtTableGen`, landed this wave) | `StmtTablePins m` bundle + `stmt_table_stack_disjoint` literal in `ExecEntry.ground` |
| N3 | **AST-region invariant** — hereditary "every node + string payload of `e` lives in `[lo,hi)`", region disjoint from stack/sret/arena, in RAM above HTIF | hStr (EXACTLY `EvalEntryStrAstRegion`, discharge pre-checked by `field_hStr_of_astRegion`); hNeg/hNot (`NegExtras.expr_survives/expr24*/op_*`); logical four; hIAdd…hNe (`BinArmExtras` operand geometry); hVar/hAssign (name-string vs stack, `VarLeafResid` conj 1); hStrAddL/R + hStrLt/Le/Gt/Ge (payload-string region); exec arms' node geometry (`ExecRetGeom` etc. once conditioned) | NOWHERE on main (47g verdict: ExprRepr/StoreRepr/ProgramRepr/Layout all region-free); top-level supply = M6 parse-arena Layout fact | `ExprIn`/`StmtIn` structural mirror of `ExprRepr` (`Vsa/MemRegion.lean`, landed this wave) + `AstRegionPins`/`StmtRegionPins` `∃ lo hi` bundles in `Eval/ExecGround`; children by projection (payload-pointer clauses are `∀ p, read64 … →` so child extraction is DIRECT, no determinism lemma) |
| N4 | **Arena geometry literals** — `A.hi ≤ SL.lo ∨ sp ≤ A.lo`, `A` vs eval-code, `A` vs value_* text | hNeg/hNot (`NegExtras.arena_stk/arena_code/vi_arena`), logical four, hIAdd…hNe (`BinArmExtras`), hVar (sret-vs-arena, derivable from N4+N5) | ghost-instantiation constants at M6 (heap vs linker stack vs text) | 3 literal fields in `EvalGround` (exec twin: arena_stack + arena vs exec code) |
| N5 | **sret/retslot whole-stack membership** — `SL.lo ≤ sret ∧ sret+24 ≤ SL.hi` (`NegExtras.sret_inSL`); exec `aRet` slot geometry (align/RAM/HTIF/scribble-disjoint, `ExecRetGeom`) | hNeg/hNot, logical four, B3/B4 cells; hSRet/hSRetNull | top level: interp_run's result buffer is a stack local; children: `subsret = sp - 944` in-stack by `stackOK` arithmetic | literal fields in `EvalGround`/`ExecGround` (exec: `RetSlotGeom` sub-bundle) |

Already-derivable record fills (NO amendment needed — established by this
audit): `sp_headroom` 3264/4352-class (from 47a `stackBudget` +
`stackNeed_ge` arithmetic), `sp16`/`sp_SLhi` (`StackOK` conjuncts 3/2),
`SLhi_ram` (`stack_ram`), `code_stk` (`code_stack_disjoint`),
`vicode_stk`/`table_stk` (47f widened literals), size-stability +
`StoreBodiesBound` conjuncts (ITEM ZERO), the whole NBS geometry (47f).

## B. NOT entry-suppliable (Law 4 — named, excluded from the amendment)

| # | Need | Consuming fields | Why not entry-suppliable | Honest supplier |
|---|------|------------------|--------------------------|-----------------|
| X1 | `hMcallPop` **memory-totality oracle** `∀ mcall, (agrees m0 off-stack) → ∀ a : Nat, ∃ b, mcall[a]? = some b` | hNeg, hNot, hOrTrue, hAndFalse, hOrFalse, hAndTrue (and the B3/B4 cells' analogous presence needs) | REFUTABLE for every finite `Mem` (`Std.ExtHashMap` has finitely many keys; no entry field about `m0` constrains the ∀-quantified `mcall` inside the stack window, and no finite map is total on `Nat`) — machine-checked `experiments/fleet/obstructions/McallPopTotality.lean` | residual re-statement: presence hypothesis on the actual dead-byte window (`[subsret+4,+8) ∪ [subsret+16,+24)`), supplied by the consumer's concrete `writeMap8` chain via `MemExtends`; pairs with a `mem` presence field ONLY on the read footprint |
| X2 | **B3/B4 entry-conditioning** — `BinIntCellResid`/`BinEqCellResid` are still ∀-ghost-closed (no `EvalEntry` hypothesis; refutable per `b3-bincell-resids-refutable`) | hIAdd…hIGe, hEq, hNe (11 fields) | residual-STATEMENT layer, not an entry field; the entry facts (N1/N3/N4) only apply after the conditioning lands | the designed B2-shape amendment of `rows/BinDispatchRow.lean` (~12 cell sites, `hc` already in scope) |
| X3 | **Exec widener `pres`** — `Widen` over bare `ExecExit` (`ExecLeafWiden`/`ExecRecWiden`) needs `MemExtends m0` for EVERY exit config | all 14 exec-arm fields (the `ExecCaseGeom`/`Exec*Geom` widener conjunct) | the exact exec twin of the B1 `LeafEntryGap`: `ExecExit.memFrame` permits presence-dropped bytes in its carve-out; no entry field reaches the ∀-quantified exit config | the 47e eval procedure re-run on the exec side: exec pinned sims + `LeafExitPin` twin through the exec block interfaces |
| X4 | **Loop IH / step oracles** (`BlockGeom.hstep`, `ForStartGeom`, `WhileGeom.hWhileIH/hForIH`) | hSBlock, hSForStart, hSWhileBreak | self-referential: the oracle IS the statement-sim capstone (`loop-geom-self-referential-oracles`) | recursor-threaded per-derivation premises (the `armResidGap_of_stages` shape) |
| X5 | **Seq/args/call span code-grounding + engine-exit upgrade** | hSeqNil, hSeqConsNormal, hSeqConsAbrupt, hArgsNil, hArgsCons, hCallPrint/Println/AssertOk | `SegEntry` motive layer (`SeqSpanGround` landed for seq; `mEvalArgs`/`mCall` table entries still missing; `ExecSeqExit→SegExit` upgrade needs engine memFrame) | table extension + engine exit re-land (`code-free-segentry-args-call-spans`) |
| X6 | **Callee-contract glue** (env_get_found linkage, env_define splice, value_null bridge, native print/println/assert bodies, strConcat/stringify, StrCmpOrderBridge, div/mod seams) | hVar, hAssign, hSVarInit, hSVarNull, hSRetNull, hCallPrint*, hCallAssertOk, hStrAddL/R, hStrLt…Ge, hDivOv, hCall, hFn | callee spec seams (`TermCallees` layer), orthogonal to the entry | per-arm splice work (existing campaign lanes) |
| X7 | **hCallClosure crux** | hCallClosure | whole-premise by design (depth crux) | sibling-owned row |
| X8 | **hInitStore / hEpilogueSpill / hDivCorr** | themselves | not `EvalEntry`/`ExecEntry` needs at all (interp_run prologue/epilogue + divergence family) | `InterpInitStoreRepr` / `EpilogueSpill` / `DivCorrFamily` |

## C. The batched amendment (design)

ONE sub-structure per entry — `EvalEntry.ground : EvalGround …`,
`ExecEntry.ground : ExecGround …` (`Vsa/Sim/EntryGround.lean`):

```
EvalGround m SL A sp sret aExpr e :=
  { table      : KindTablePins m                     -- N1
    ast        : AstRegionPins m SL A sret aExpr e   -- N3 (∃ lo hi bundle)
    arena_stack: A.hi ≤ SL.lo ∨ sp ≤ A.lo            -- N4
    arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
    arena_vi   : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
    sret_inSL  : SL.lo ≤ sret ∧ sret + 24 ≤ SL.hi }  -- N5
ExecGround m SL A sp aRet aStmt s :=
  { table / table_stack (N2), ast : StmtRegionPins (N3), arena_stack,
    arena_code (exec text), aret : RetSlotGeom (N5) }
```

Everything in the bundle is transport-closed under stack∪sret-confined writes
(`EvalGround.survive_stack`, one call per seam — the 47f `NBSPins` threading
shape), and child grounds are projections (`ExprIn` child clauses are `∀ p,
read64 → …`, applied directly to the site's payload read).

## D. Fan-out map (measured) and what landed this wave

Field insertion breaks the entry ctor sites and requires the ground to ride
the marshalling towers to reach them.  Measured on main @520cb62:

* ctor sites: 15 `store_survives :=` sites, 13 files (`EvalRecCommon:316`,
  `ExecRecCommon:247`, `ExecBlock:322`, `ArmSegSplit:196`,
  `ArmSegSplitExec:160`, `ArmSegSplitExecEval:163`, `ArmSegSplitTwins:316/516`,
  `SeqHeadStages:97` (trivial field-copy retype), `LoopHeadDispatch:351`
  (TOP-LEVEL supply point — grounds from the `Loaded L` image),
  `CallCruxMarshal4:384/516`, `EvalVarRow`/`TermRouting`/`FnResidSupply`
  construct VARIANT entries only — unaffected).
* conduit: the 26 files currently carrying `NBSPins` (the exact seam list =
  `grep -rln NBSPins Vsa/` — armTail_rec/_es, JalPreBundle/ExecJalPreBundle,
  MidArm{Combinator,FieldIH,FieldWire}, UnaryArmCallee/LogicalArmCallee, the
  6+2 `*ArmStagePre` towers, `ArmDispatchCombinator{,Exec}`,
  StagePreSuppliers{,2}) + full-cone regen (~304 files).

That is a 47e/f-scale fleet wave per side.  THIS wave (single lane, one lean
process) landed the complete amendment INTERFACE so the insertion wave is
plumbing with zero proof risk:

1. `Vsa/Sim/MemRegion.lean` — `ExprIn`/`StmtIn` (+ list/opt companions), the
   region-agreement transport, and the root/child projections.  The
   REPRESENTATION transport already exists (`AstTransport.exprRepr_agreeP`
   over the exact footprint `ExprFp` — the `NegExtras.expr_survives` doc
   comment predates it); `expr_survives`-class residuals discharge by
   `ExprIn`-bounding the footprint (`ExprFp ⊆ [lo,hi)`, ONE bridging mutual
   induction, bounded follow-up) then `exprRepr_agreeP`.
2. `scripts/gen_layout.py` + `Vsa/Sim/rows/LayoutStmtTableGen.lean` — the
   stmt-table `groundStmtSlot_0..8` pins, generated from the ELF (N2 ground
   truth).
3. `Vsa/Sim/EntryGround.lean` — `KindTablePins`/`StmtTablePins`/
   `AstRegionPins`/`StmtRegionPins`/`RetSlotGeom`/`EvalGround`/`ExecGround`
   + transports + the machine-checked record-fill theorems
   (`evalEntryStrAstRegion_of_ground` ⇒ hStr discharges the moment the field
   lands; `execCaseGeom_ground_half` ⇒ every exec arm's slot/table conjuncts
   discharge; `negExtras geometry-half` fills).
4. `experiments/fleet/obstructions/McallPopTotality.lean` — the X1 refutation.

## E. Verdict

* No fifth SHAPE of entry amendment exists: the complete entry-suppliable set
  is N1-N5, now bundled as ONE `ground` field per entry with pre-proved
  suppliers and consumers.  Every other open need is X-class (residual
  statements, block re-lands, motive layer, callee seams) — entry amendments
  cannot help them, so no future wave should touch `EvalEntry`/`ExecEntry`
  beyond inserting `ground`.
* The insertion itself (ctor sites + conduit + regen) is the mapped mechanical
  wave above — fleet-scale, dispatched next.
