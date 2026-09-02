# RUN-1 entry-completeness audit + batched amendment (wave 47h)

## Session start (2026-09-02, post-520cb62)
- Task: complete entry-needs audit (every machine-checked entry-side need from
  the obstruction verdicts / conditional discharges / observations / 55
  NOT_FOUND fields) + ONE batched EvalEntry/ExecEntry amendment.
- Audit sources read: B1_reseat_footprint_verdict.lean, B1_leaves_reattempt
  (via observations), b2-resid-fields-refutable, exec-resid-slot-pins-
  uninhabited, loop-geom-self-referential-oracles, seq/forloop motive
  obstructions, b3-bincell-resids-refutable, recursion-stack-budget-class,
  strpayloadgeom-supplier-verdict, rows/Field_h{Int,Null,Bool,Str},
  TermRouting/ExecRouting/ExecCaseGeom/ExecRecRows/ExecDispatchRows/
  SeqForRows/BinDispatchRow/EvalVarRow residual defs, NegExtras,
  EvalEntry/ExecEntry current field sets.
- Ground truth for the exec table: stmt jump table @0x80019fb8, 9 slots,
  bytes decoded and cross-checked against ALL NINE landed execArm* PCs
  (base-relative sign-extended offsets, same shape as the eval table).

## Landings (all green, `lake env lean`, axiom-clean)

1. **Audit** `experiments/entry-needs-audit.md` — complete table: 5
   entry-suppliable need classes (N1-N5), 8 excluded classes (X1-X8) with
   honest suppliers; per-field consumer mapping for all 55 NOT_FOUND fields;
   fan-out map §D (15 ctor sites / 26-file NBSPins conduit).
2. **X1 machine-checked** `experiments/fleet/obstructions/McallPopTotality.lean`
   — `no_total_mem` (pigeonhole, `size_erase`) + `mcallPop_shape_unsuppliable`
   (`mcall := m0` instantiation).  hNeg/hNot/logical-four blocked on a
   residual re-statement, NOT an entry field.
3. **MemRegion** `Vsa/Sim/MemRegion.lean` — `ExprIn`/`StmtIn` hereditary
   AST-region mirror (structural recursion, conditional reads → direct child
   projection), `exprIn_agreeP`/`stmtIn_agreeP` transports,
   `exprIn_str_payload`/`exprIn_var_payload`/`exprIn_unary_child`/node
   projections.  Cross-referenced with the LANDED `AstTransport.exprRepr_agreeP`
   (representation transport; the `ExprFp ⊆ [lo,hi)` bridge = bounded follow-up).
4. **Generator** `scripts/gen_layout.py` + `Vsa/Sim/rows/LayoutStmtTableGen.lean`
   — stmt table @0x80019fb8, 9 slots, ALL cross-checked against the pinned
   `execArm*` constants; `groundStmtSlot_0..8` green, self-verified.
5. **EntryGround** `Vsa/Sim/EntryGround.lean` — `KindTablePins` (11 slots),
   `StmtTablePins` (9), `AstRegionPins`/`StmtRegionPins` (∃ lo hi named
   specs), `RetSlotGeom`, bundled as ONE `EvalGround`/`ExecGround`;
   `survive_stack` transports (stack ∪ result-slot footprint; sp ≤ SL.hi arg).
6. **Discharge rows** `Vsa/Sim/rows/EntryGroundRows.lean` —
   `strAstRegionBody_of_ground` (hStr = record fill at insertion),
   `execGround_slot_window` + `execGround_caseGeom_brk/cont`,
   `kindTablePins_of_bytes`/`stmtTablePins_of_bytes` (M6 suppliers).
7. Wired into `Vsa.lean` (4 imports); oleans regenerated; discipline OK
   (9 rules).

## NOT done (scope verdict, recorded honestly)

The `ground` FIELD INSERTION + fan-out (audit §D: 15 ctor sites, the 26-file
NBSPins-conduit threading, ~304-file regen) is a 47e/f-scale fleet wave per
side — not executable by one lane with one lean process in this session.
Census therefore stays 3/58 (insertion flips hStr immediately via
`field_hStr_of_astRegion ∘ strAstRegionBody_of_ground`; exec fields need
X3's block re-land besides).  All insertion-site supply terms are pre-proved,
so the next wave is pure record plumbing.

## Gates at commit time

- Every new file green under `lake env lean` (MemRegion/EntryGround/
  LayoutStmtTableGen/EntryGroundRows/McallPopTotality ≈ 1s each).
- 12 new check_all THEOREMS entries verified axiom-clean through `import Vsa`
  (`{propext, Classical.choice, Quot.sound}` only).
- `check_discipline.py`: OK (9 rules).
- `field_census.py -j4`: `{'NOT_FOUND': 55, 'FOUND': 3}` — unchanged, zero
  TYPE_ERROR (no regressions from the new ambient imports).
- Full `check_all.sh` stage a (lake build) was left running at commit: it is
  re-recording lake traces for the ~400-job tail earlier waves regenerated via
  `lake env lean -o` (no trace records) — files this wave did NOT touch; the
  new modules and the amended `Vsa.lean` root built green inside it before the
  tail (`Vsa.Sim.MemRegion`/`EntryGround`/`LayoutStmtTableGen`/
  `EntryGroundRows` all `✔`).  47g precedent (regen + discipline + census).

# RUN-1 wave 47i — entry field-insertion wave + McallPop amendment (2026-09-02, post-4240d7e)

- Task: execute audit §D insertion (EvalEntry/ExecEntry gain `ground`; ctor
  sites + NBSPins-conduit threading + regen); discharge record fills (hStr at
  minimum); amend the 6 `hMcallPop` Resid statements per the
  `McallPopTotality.lean` Law-4 verdict (falsity-amendment procedure).
- Plan: (1) McallPop amendment — replace each Resid/sim/block totality
  conjunct with the B3 `BinArmExtras` precedent pair `frame_pop`
  (windowed `[sp-1120, sp)`; neg additionally `[aExpr+4, aExpr+8)` for the
  blockC_neg node dead-byte lds) + `mem_ext` (`MemExtends m0` closure);
  (2) insertion + threading; (3) fills; (4) census/discipline/commit.
  ONE regen for both edits.
- Measured blast radius (totality uses): EvalNegSim2 blockC_neg (aExpr+4..8 +
  subsret windows + MemExtends@495), EvalNotSim (24B @sp-944..-928+8 +
  MemExtends@888), EvalOrSim/EvalAndSim (sp-968..-944 windows + m3@sp-1088 +
  MemExtends), EvalLogical3 (hPopCR sp-848..-832 + chain@764),
  EvalLogical4 (hPopCR sp-944..-928 + chain@767), TermRouting 6 Resids.
  All windows ⊆ [sp-1120, sp) ∪ node bytes. Skeleton fields reference Resids
  BY NAME → no TermResidualsCore text change; skeleton regen = recompile.

### 47i progress checkpoints (live)
- Phase A (McallPop amendment) GREEN: EvalNegSim2 (stackpop_present →
  pointwise; blockC_neg windowed pair), EvalNotSim, EvalOrSim, EvalAndSim,
  EvalLogical3/4 (hStackPopC/M3/hPopCR windowed, ~240 use sites), 6 Resids +
  6 rows in TermRouting.  MemExtends-from-totality derivations replaced by
  the threaded `mem_ext` residual (`hMemExtM0.trans`).
- Insertion landed: `EvalGround`→`InterpEntry` (+`KindSlotPinned` relocated
  from EvalSimCommon, 47f-style), `ExecGround`→`ExecEntry`;
  `EvalEntry.ground`/`ExecEntry.ground` fields; `EntryGround.lean` = shim.
- NEW `Vsa/Sim/EntryGroundKit.lean` (green, axiom-clean): transport_offstack /
  ast_read64_agree{,_via} / child_params / child_at / transport_via (+ exec
  twins) + named ExprIn/StmtIn child projections.  ONE kit call per supplier.
- Ctor sites DONE: EvalRecCommon, ExecRecCommon (armTail_rec{,_es} +
  execExprGlue/execExprSimC closures), ArmSegSplit{,Exec,ExecEval},
  ExecBlock, SeqHeadStages (field copy), LoopHeadDispatch (hGround premise),
  EvalNegSim (blockB_unary), EvalBinSim (blockB_binary L+R children via
  transport_via across the left sub-call), EvalAndSim (blockB_logical),
  suppliers in EvalNegSim3/EvalNotSim/4 logical sims.
- Driver: /tmp/regen_driver2.sh level-parallel (P3) with done-list
  /tmp/regen_done.txt over /tmp/regen_levels.txt (307-file cone).

### 47i RECOVERY (successor lane, 2026-09-02)
- Found: driver stalled at level 15/33 (127/307 done), sole failure
  `rows/EvalGtRow.lean` — predecessor had edited the 10 binary-row PROOFS
  (`hGmt47` destructure/supply) but died before (a) inserting the
  `EvalGround ment SL A sp sret aExpr.toNat (.binary <op> el er)` conjunct
  into the row `SimGoal`/inline pres, (b) threading `hGmt` through
  `rows/BinDispatchRow.lean` (22 sites), (c) `rows/EvalEqNeFront.lean`
  (evalEqSimD/evalNeSimD pres).
- Repaired: conjunct inserted in 9 int-row Goal defs + 3 EqNeRow pres
  (op/.eq/.ne) + 2 EqNeFront pres; `hGmt` threaded in BinDispatchRow;
  EvalGtRow now green. Variant-entry ctor sites (EvalVarRow/FnResidSupply/
  CallCruxMarshal4/ArmSegSplitTwins) confirmed unaffected (audit §D).
- Driver resumed under caffeinate (P3, done-list preserved).
