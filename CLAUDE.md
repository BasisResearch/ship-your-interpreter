# Proof discipline — the exponentiating layer is MANDATORY

This repo proves a RISC-V interpreter binary correct. Proof effort here went
subexponential exactly when work was done by hand beside an abstraction that
already existed (measured: a fully-decode-tabled region accumulated four
hand-rolled site batteries because the surrounding files modeled the legacy
idiom). The layer below is not advisory. `scripts/check_all.sh` stage a4
(`scripts/check_discipline.py` + `scripts/discipline_rules.tsv`) FAILS new
files that bypass it.

Before ANY proof work: run `scripts/abs_inventory.sh` and reuse by name.

## Mandatory tool per task shape

| Task shape | Use (never hand-roll) |
|---|---|
| WHOLE FUNCTION (multi-block: branches, loops, calls, tail-j, tohost seams) | `scripts/gen_fn.py --fn <f> --entry <pc> [--fold]` — emits the block arms + (recognised counted-loop shape) the derived `FnSummary` fold; fold combinators `FnSummary.{seq,callSplice,tailJump}` + `segRowFramed` (`Vsa/Sim/FnSummary.lean`, `SegToTripleFramed.lean`; model fold: `rows/FnWriteFold.lean`); rule R9 catches hand-rolled multi-seg function files |
| Straight-line OR branch/jump-terminated span | `#derive_case` seg + `segToTriple` (br/j/jr terminators are in-model; model: `Vsa/Sim/EnvDefSeg.lean` — 58 hand lines → 14, `EnvDefBridges4.lean` for branch-ended rows) |
| Span ending in a CALL (`jal`) | `BridgeSeg.bridgeOfSeg` + `jalStep_of_obs` (the jal seam is deliberately outside `TKind`) |
| Call span requiring HTIF or other non-ABI register preservation | `bridgeOfSegFull` + `jalCallFacts_of_obs` (`BridgeSegFull.lean`); retain the complete reflected register frame on the actual call endpoint |
| ABI register frame on a run | `FrameMeta.abiFrame_of_wrChain` (one `decide`) — NEVER per-site frame threading |
| Memory-frame / footprint post | `FrameMeta.memFrame_of_chain` / `bblocks_sound_framed` |
| Framed variant of a callee spec | FrameMeta metatheorems over its reflected chain — NEVER re-run the chain with a ghost conjunct |
| Call splice (prefix ≫ callee ≫ suffix) | `callSeg`/`callSegConseq` (`DeriveCallSeg`) |
| Loop | `loopFromBody` (`DeriveLoop`) / the `LoopSteps` shapes |
| Error-site Triple | `#derive_error_site` table row |
| Recursor case row | the `gen_*_row.py` generators + TSV (TermRouting/ExecRouting/BinDispatchRow) |
| Exit widening | `LeafWiden`/`ExecRecWiden`/`EvalRecWiden`/`blockD_v_phic` |
| Store↔frame marshalling | `foundSt_of_storeRepr` / `frameRepr_append` |
| Payload-disjointness premise on a copied value | `Vsa.Sim.ValuePayload v s` (`ReprCopy.lean`) guards `valueRepr_copy`/`valueRepr_copy_of_writeWindow` and `SubExecReturnR` — NEVER quantify `∀ p s, read64 … = some p → …` over an unconditioned string (false for int payloads) |
| Load / byte-read obligation | TOTAL reads (`bytesT{1,2,4,8}`, `exec_*_tot`/`_totv`, `LPins*` as total-read equalities, `site_*_tot`/`_totb` from `gen_sites.py`) — the model's `readByte` is `getD 0`, so NEVER demand `m[a]? = some b` for a byte a proof does not already own; if the VALUE matters, thread the write fact (`valueRepr_copy_total`) |
| Scalar RAM access policy and single-access reads | `pmaCheck_ram_scalar`, `RamReadChecks.of_good`, `checked_mem_read_single_of_ram` (`RamReadPolicy`/`RamReadSingle`/`RamReadData`); `split_access_scalar` and `scalarChunkFacts` supply the split plan and chunk geometry |
| Scalar RAM reads including misalignment and granule crossings | `checked_mem_read_ram_scalar` (`RamReadScalar`); `read_ram_total`/`bytesT_extract` supply total byte slices, `splitReadAccum_bytesT` proves reassembly, and `untilFuelM_sequence` supplies the state-preserving loop trace |
| Scalar virtual reads and LOAD execution without data alignment | `vmem_read_ram_scalar` (`RamReadVirtual`), `execute_load_ram_scalar` (`RamReadLoad`), and value-named `exec_load_ramv`/`exec_*_ramv` (`RamReadValue`); `split_on_page_boundary_ram` discharges the actual page-split computation, including page crossings. `BlockMem.MemFacts` consumes these rules without load alignment |
| Saved word from a reflected write log | `read64_of_writeLog_at`, `InterpSpillReads.transport` (`InterpSpillReads.lean`); retain read facts from the actual segment result through its memory frame |
| Byte presence through actual writes | `memExtends_applyW`, `memExtends_writeLog`, `memExtends_setjmpBuf` (`MemPresence`); `ReadyPrefixFacts.stack_bytes` derives reached stack presence from the initial boundary |
| Reflected load facts and loaded value from one complete word | `wordLoadFacts_of_read64` (`WordLoadData.lean`); consume the named `facts` and `value` projections |
| NEW post/entry predicate | named-field `structure ... : Prop where` (model: `FoundSt`/`GeomFacts`/`FrameCalc`) — NEVER an anonymous ∃/∧ tower |
| Consuming a LANDED ∃/∧ tower | write ONE named destructuring lemma beside the tower's def and consume through it — never `.2.2.2.2` positional chains |
| Exclusive/shared ownership composition and local memory framing | `SeparationLogic.sep`, `Hoare.frame`, `frame_machine` (`Vsa/Sim/SeparationLogic*.lean`); reuse runtime ownership adapters rather than reconstructing split algebra |
| Entry-independent allocation geometry and store bounds | `HeapOwnershipGeometry` and `StoreInvariant`; runtime ownership must not import the allocator-operation bundle `HeapOps` |
| Shared-byte preservation through existing-name updates | `EnvDefineOwnedUpdatePost.shared_agree` from `envDefineUpdateFromHit_of_runtime_owned`; `EnvDefineUpdatePost.agree_outside` supplies the exact value-slot frame |
| Additional facts from the actual recursive child result | `EvalIHWith`, `ReturnedWith`, `armTail_rec_with`, and `blockB_unary_with`; ordinary wrappers project the same execution, and `EvalPayloadIH` retains the returned value's exact indirect coverage |
| Stack presence and result words after both binary children | `blockB_binary_memory` retains `BinaryReturnMemory` through `ReturnedWith`; `blockB_binary` projects the same execution, and integer tails consume the reached memory facts |
| Actual binary operand register and respilled kind | `blockB_binary_data` retains `BinaryReturnLoads` with memory facts in `BinaryReturnData`; `.int_readback` and `.kind_readback` derive tail inputs from the represented value |
| Reflected equality operand copies | `valueRepr_of_reflected_copy` and `eqFrontData_of_readback` consume `ValuePayloadCovered` for the actual operands; use reached `BinaryArmFrame` and `BinaryReturnLoads` for dispatch inputs |
| Equality identity and return maps | `ValueEqualityIdentity.of_store` uses allocated operand bounds; `value_equal_spec_full_identity` consumes only the compared pair. `EqTailData` selects one operand/store map with row-entry prefix agreement; `EqNeOp.DispatchPost.readback` exposes named copy facts |
| Coherent recursive results and ownership | `ReturnRepr` indexes values, ownership, and store survival by one selected map pair; import `CoherentReturnFrame` for `.bind` through the actual child frame. Keep return data below segment syntax. `EvalReturn`/`EvalReturnIH` retain the actual exit; `.coherent_of_bounded` applies only to references within the entry prefix |
| The recursive eval motive (what a child expression hands its parent) | `TermSimAssembly.mEvalE := EvalReturnIH TrivialOwned` (`EvalReturn.lean`): `.run` lands `EvalReturn` = widened exit + ONE selected map pair (`.repr.selected`); consumers needing only the exit take `.forget`. Producers: `pinnedLeafReturn`/`eval*SimR` (leaves), `evalReturn_of_exit_id` + `LeafReturnWiden` (var), `EvalIH.coherent_of_bounded` (+ `binOpSem_closuresBounded`) for int/bool/str results, `armReturn_of_facts` (= `blockD_v_return` from `EpilogueEntryFacts` at the arm's selected pair) for the allocating `fn`/`call` arms — NEVER a per-row `VarInitCoherent`-style coherence premise |
| Shared pinned-leaf supplier | `pinnedLeafReturn` produces the coherent return; `pinnedLeafExitD` projects it for int/null/bool/string rows |
| Selected maps through the shared eval epilogue | `blockD_v_return` retains the producer's result/store maps and ownership, then indexes them by the caller's entry prefixes. `blockD_v_rec` projects `blockD_v_rec_coherent` at the same endpoint |
| Separation assertions through machine effects | `StableUnder.assertion`/`.separated` and `SeparationLogic.FramedTriple.frame` connect owned read support to the existing effect calculus; `frame_machine` and `envNewSuccess_frame` consume them |
| Owned store return suppliers | `ReturnRepr.of_heapOwned` derives survival from allocated/shared-byte exclusion; `EnvDefineOwnedReturnPost.coherent` applies it to the actual completed update |
| Indirect payload coverage under footprint inclusion | `ValuePayloadCovered.mono` (`ValuePayloadCoverage`); use `valueRepr_copy_total_exact` with the actual value instead of quantifying over unrelated strings |
| Truthiness after a total value copy | `truthyHeaderRepr_of_valueRepr`, `truthyHeaderRepr_copy_total`, and `value_truthy_header_spec`; logical-not and all four logical cases consume ordinary `EvalIH`, without indirect payload or closure-map premises |
| Recursive eval helper code and table pins | Retain `EvalCallSupport` in `EvalGround.eval_call` and `ExecGround.eval_call`; use `transport_stack` and `transport_frame` for the actual writes and recursive exits |
| Shared unary entry geometry | `UnaryExtras` and `EvalEntry.unaryExtras`; `NegExtras` specializes arithmetic negation, while `EvalEntry.notExtras` derives the logical-not callees from retained code support |
| Shared binary entry geometry | `EvalEntry.binaryExtras` (`BinaryEntry.lean`) derives both operand pointers, their preservation, static geometry, and 3,264-byte headroom; generated integer and equality rows consume it at the actual entry |
| Binary integer-tail geometry and field suppliers | `EvalEntry.binaryReturnToken`, `.binaryReturnImage`, and `.binaryPostGeom` retain the actual source token, fixed image, and result geometry; `IntegerCellSuppliers` closes all nine integer-tail supplier fields through the existing adapters |
| Static operator slots and helper code | `FixedBytesLoaded.slotPinned` factors bounded slot extraction; `FixedRodataLoaded.slotPinned` and its operator specializations consume the generated image. Generate helper projections with `gen_fixed_image.py`, not byte batteries |
| Shared logical entry geometry | `LogicalShortExtras` and `LogicalFallthroughExtras`; `EvalEntry.logicalShortExtras` and `.logicalFallthroughExtras` derive both operators' geometry from the represented children and retained code support |
| Closure-body bounds after evaluating a child | `StoreBodiesBound.afterEvalE` reuses `.afterExecS` through the expression-statement constructor; use the actual child derivation rather than assuming unchanged store sizes |
| Saved registers and ghost frame at a binary arm | `BinaryArmFrame.of_entry` derives named facts from `ArmEntryK.destruct`; post suppliers take this reached frame as a hypothesis |
| Initial eval helper support from the fixed binary | `evalCallSupport_of_fixedImage` uses generated text projections and `fixedRodata_evalTableBytes`; use `gen_transport.py --exact-range` when only a callee's code interval is preserved |
| String-literal result pointer and payload coverage | `value_str_spec_full_exact`, `blockC_str_exact`, `evalStrSimP_exact`, and `StrReturnPin` retain the actual pointer; `evalStrPayloadIH` derives whole-stack coverage from the original entry ground |
| Generic entry to the string leaf | `EvalStrEntry.of_entry`; the generated string row and payload-IH producer share this conversion |
| Owned payload pointers through value copies | `ValueOwned.copy_total` (`RuntimeOwnershipCopy`); `EnvDefineOwnedUpdatePost.value_owned` consumes the actual three-word update copy |
| Whole-store ownership after an existing-name update | `HeapOwned.defineHit` (`RuntimeOwnershipDefine`) and `EnvDefineOwnedUpdatePost.heap_owned`; source invariants supply binding uniqueness and closure-index bounds |
| Return from the exact existing-name update | `EnvDefineUpdatePost.restore` executes the shared epilogue; `EnvDefineOwnedUpdatePost.finish` retains the semantic store advance, ownership, and shared-byte agreement |
| Shared bytes versus allocator-private metadata | `Reserved.outsidePrivate` and `shared_agree_realloc_of_private`; derive live-extent exclusion from the actual allocator invariant and retain private-write coverage outside the arena |
| Owned-store survival under memory agreement | `HeapOwned.transport`, `StoreOwned.repr_transport`, `StoreArraysReady.transport` (`RuntimeOwnershipTransport.lean`); `ExprFp.agree_iff` preserves pointer-dependent closure footprints |
| Entry-side ground fact (jump-table pin / AST-node/string region / arena/result-slot geometry) | `EvalGround`/`ExecGround` (`EntryGround.lean`; region layer `MemRegion.lean`, repr transport `AstTransport.lean`, generated pins `Layout*TableGen`) |
| Exact AST read coverage, child selection, and geometry | `exprReadFields`/`stmtReadFields`, `*ReprWithin.fieldCovers`/`.child` (`MemReprReadFields`), `AstReadGeometry.of_covered`; legacy region adapters in `MemRegionWithin` |
| Entry-independent shared read geometry and stack frames | `SharedReadDomain`, `AstReadGeometry.of_domain`, `SharedReadDomain.agree_stack` (`AstReadGeometryCore.lean`); the runtime ownership adapter remains in `AstReadGeometry.lean` to avoid entry import cycles |
| Owned AST children and indexed arrays | `StmtReprWithin.exprChild`/`.child`, function/call/block projections (`MemReprReadChildren`); `*ReprWithin.pointers` + `PointerArrayWithin.get` (`MemReprReadArrays`) |
| Initial statement read and actual dispatch | `ReadyRuntimeFacts.stmtReadAccess`, `OwnedLoopHeadFacts.firstRead` (`InitialAstReads`); `readyInitialDispatch_owned` (`InitialDispatch`) |
| Initial result-slot call and ownership | `readyInitialNull_owned` (`InitialNullOwned`); `InitialNullFacts.preservation` retains the prefix frame, and `OwnedInitialNullFacts.saved`/`.access` retain argument words and exact AST reads |
| First statement call from the initial boundary | `readyInitialExec_owned` (`InitialExecCall`); `OwnedInitialNullFacts.argsData` supplies both reads, `ReadyPrefixFacts.globals` preserves the environment pointer, and `OwnedInitialExecFacts.store_survives_stack` derives store framing from the initial ledger |
| First statement entry assembly | `OwnedInitialExecFacts.execEntry` (`InitialExecEntry.lean`); actual execution supplies machine fields and exact tag geometry. Hereditary AST ground and source stack/body bounds remain explicit internal obligations |
| Statement arm that evaluates ONE child expression (`expr`, `ret e`, `varDecl x e`, `if`/`while` condition, the for-loop condition in-frame) | `EvalChildArm` (`Vsa/Sim/EvalChildArm.lean`): ONE descriptor + `Cert` (decided) + `EntryCert` (jump-table tag, prologue entries only) + `Sem s e` (constructor projections); `EvalChildArm.dispatch` (from `ExecEntry`) and `dispatch_of_armState` (from an `ArmState`, e.g. `ArmState.ofForLoopReady` at the for-loop head) land the child `EvalEntry` with the parent `Carrier`; `exitKit_at_exit` recovers the parent at the child's `EvalExitD`; `normalExitPre_of_exit` + `normalExitTail` (`ExecNormalExitTail.lean`) close a normal completion. Instances ~120 lines (`rows/EvalChildArm{While,If,Expr,Ret,VarInit,ForCond}.lean`); rule R10 catches a hand-reflected arm prefix. Residual shape for such a field: `structure XCaseGeom … where dispatch … resume …` (models `Rows.ExprCaseGeom`, `RetCaseGeom`, `VarInitCaseGeom`, `IfNoneCaseGeom`); closed fields `rows/Field_hSExprClosed.lean`, `rows/Field_hSIfNoneClosed.lean`, `rows/Field_hSIfBranchClosed.lean`, `rows/Field_hFlCondFalseClosed.lean`; a resume that re-dispatches in-frame (if branches) instantiates the ghost memory as the reached memory and rebases with `Rows.execExitD_rebaseMem`; a route's `auipc`/`addi` readback unfolds the register fold (`if_route_a4`), never `rfl` |
| Statement arm that CALLS `exec_stmt` on a child statement in-frame (loop bodies) | `StmtChildArm` (`Vsa/Sim/StmtChildArm.lean`): descriptor + `Cert` + `Sem s sc`; `dispatch_of_armState` (from an `ArmState` at the arm PC) lands the child `ExecEntry` with the parent `Carrier`; `exitKit_of_exit` recovers the parent at the child's `ExecExitD`; `ExitKit.toRouteReady` hands the status in `a0` to a reflected route; `normalExitPre_of_routeHead`/`retExit_of_routeHead` close the exits. In-frame continuations use `FrameFacts` (parent frame at any in-frame point; `.transport`, `.afterExit`, `EvalChildArm.frameFacts_at_exit`), `ArmState.of_routeHead`, `LoopFrame` (memory bookkeeping for the final `execExitD_rebaseMem`/`execExitD_rebaseMaps`). Instance `rows/ForLoopArms.lean` (body call, step arm, seven routes); closed fields `rows/Field_hFlBodyClosed.lean`; rule R11 catches a hand-reflected statement-child prefix |
| Statement arm that CALLS a runtime helper in-frame (`value_null` bridges of `ret;`/`var x;`, `env_define` at the declaration tail, `env_new` at the block/for arms) | `HelperCall` (`Vsa/Sim/HelperCall.lean`): descriptor (`headPC`, reflected prefix, `jal` PC/imm, callee `entry`) + `Cert` (decided + the generated `site_<jalPC>_hc` from `scripts/helper_call_sites.tsv`); `parked_of_armState` (from an `ArmState`) / `parked_of_ready` (from a `RouteReady`, keys `callL`) land `Parked` at the callee entry; ONE adapter per callee turns the callee contract into `Return` (= `RouteReady` at the link PC + footprint): `nullReturn_of_parked` (`HelperCallNull.lean`, over `value_null_spec_full`), `envDefineReturn_of_parked` (`HelperCallEnvDefine.lean`, over the NAMED `EnvDefineContract`), `envNewReturn_of_parked` (`HelperCallEnvNew.lean`, over the NAMED `EnvNewContract`: fresh frame + extended map `EnvNewFresh`); continue with `RouteHead.toRouteReady`, `FrameFacts.afterStackHelper`/`.afterExit`, `normalExitPre_of_routeHead`, `retSlotResume` (`rows/RetSlotCopy.lean`, the shared retslot copy + status-3 epilogue), `envDefineTail_run` (`rows/EnvDefineCall.lean`, the shared declaration tail). `armState_of_entry_kind` reaches any arm by tag. Instances ≈150–330 lines (`rows/Field_hSRetNullClosed.lean`, `rows/Field_hSVarNullClosed.lean`, `rows/Field_hSVarInitClosed.lean`, `rows/Field_hSForStartClosed.lean` → `ExecInitReady`, `rows/BlockArmEnvNew.lean` → `ExecSeqEntryI .blockBody` via `routeK_of_ready` (routes that rewrite `s3`) and `bytesVal_lw_wordLds4`/`blez_guard_*` (the count `lw` + `blez`)); rule R12 catches a hand-reflected helper prefix. Copied values: `copy3_total`/`copy3_frame` + `PayloadOffWindow` (NEVER quantify over unconditioned strings) |
| Keep-set-framed seg row over a register ghost (untouched registers + output through a straight-line block, e.g. a helper's update block/epilogue) | `segRowKeepGhost` + `KeepGhost P g outp` (`rows/EnvDefineTailFramed.lean`; instances `updateStoreLiveRowKeep`/`envDefineEpilogueRowKeep`); a call seam that must keep the output uses `bridgeOfSegFull` (`rows/EnvDefineScanCallOut.lean`) — NEVER re-run `segEval_sound` per row to recover a dropped register or the output stream |
| Reflected route from ANY parked return (status/truthiness key in `a0`, five frame registers) | `TruthyCopy.RouteReady` + `route_of_ready` (or `route_of_gholds` for a custom register list) → `RouteHead`; producers `TruthyReturn.toRouteReady`, `StmtChildArm.ExitKit.toRouteReady`, `EvalChildArm.routeReady_of_exit` |
| Retslot copy after a value-returning child (`ret e`) or the null bridge (`ret;`) | `rows/RetSlotCopy.lean`: `retSlotResume` (from ANY route-ready state at `0x80004138` + `FrameFacts`) and `retResume_of_payload` (from the child's exit); the only residual is `PayloadOffWindow` (payload outside the retslot window) — supply it from ownership + an arena/retslot fact, never by quantifying over unconditioned strings |
| Condition copy + `value_truthy` + branch route after a condition child returns (`while`, `if`, `for`) | `TruthyCopy` (`Vsa/Sim/TruthyCopy.lean`): descriptor (copy seg, `jal value_truthy` PC/imm) + `Cert D T`; `copyReady_of_exitKit` (24-byte copy to `esp+16`, park at the helper), `truthyReturn_of_copyReady` (the truthiness bit), `route_of_truthyReturn` (any reflected route from the return, may reload `s0`; framed by `abiButS0`), `normalExitPre_of_route`. Instances `rows/TruthyCopy{While,If,For}.lean` (routes are `#derive_case` segs + one facts theorem each); the `ForCond`/`ExecStep` motives carry the condition's/step's eval IH (`ForCondIH`/`ExecStepIH`), so for-loop rows consume them directly; the `jal value_truthy` sites are generated (`scripts/truthy_copy_sites.tsv` → `TruthyCopySites.lean`) |
| String-comparison cell (`hStrLt`/`hStrLe`/`hStrGt`/`hStrGe`: dispatch ≫ kind check ≫ `strcmp` ≫ rejoin ≫ sign tail ≫ `value_bool` box) | `StrCmpCell` (`Vsa/Sim/StrCmpCell.lean`): ONE descriptor `StrCmpOp` + decided `Cert` per operator, `binStrCmpCell_of` supplies the field from the two shared residuals `StrCmpOperandsSupply`/`StrLeftSurvivesSupply`; the op-independent middle is `StrCmpSeam` (`strCmpTailReady_of_kindEntry`), the dispatch is `evalBinopChain_run`; instances `rows/StrCmpCellInstances.lean` (~50 lines each); rule R13 catches a hand-reflected seam |
| NEW fact about a child's execution (footprint, payload ownership, shared-byte agreement) | an IH CLAUSE on the tower (plan task 0): declare it in `scripts/ih_clauses.tsv` (`gen_ih_clause.py` emits the `EvalIHWithM` motive + one named `Residuals` field per recursor case, `rows/IHClause_<Name>.lean`), prove its SHAPE once over `MemFootprint` (`IHClauseFootprintMeta.lean`) and its per-case steps generically (`IHClauseGeneric.lean`), wire with `exact:`; check with `scripts/ih_clause_status.py`. NEVER edit `mEvalE`/`EvalExitD`/a landed row's post in place |
| Exact write set of an arm (what a row's execution changes in memory) | the footprint sibling: `MemFootprint`/`FootFam`/`noArenaFoot`/`EvalIHF F` (`ExitFootprint.lean`), heads `blockB_{binary,unary,logical}_footprint`, cells `blockC_<cell>_footprint` (landed theorem = projection), epilogue `blockD_v_rec_footprint`, rows `rows/Eval<Op>RowFootprint.lean` (`binRow_<op>F`, `eval<Arm>IHF`); consume through `EvalIHF.regionPreserved`/`.cstringSurvives` — NEVER quantify survival over all memory pairs (`hVlSurv` shape) |
| Residual supplier development check | `python3 -B -m scripts.proof_slice` previews and checks selected dependencies, exact declaration axioms, and an explicit supplier at its inherited field type; keep the full census and integration gates |

## Laws

1. Elaboration budget: NEVER raise `maxHeartbeats`/timeouts. A heartbeat bump
   or whnf timeout means the construction is wrong — check ground literals
   first (a wrong `sigmaPost` literal manifests as a timeout), then use more
   abstraction. One small `decide` per fact; reflect on the first-order
   write-log, never whnf Sail state; emit terms, not tactic scripts.
2. No `sorry`/`axiom`/`native_decide`/`bv_decide`. A genuine gap is a NAMED
   typed premise with a doc comment saying what supplies it.
3. If work feels duplicated/mechanical, STOP and report it — that is a signal
   an abstraction is missing. Build the abstraction (or name it precisely),
   then instantiate. Two similar proofs = factor before writing the third.
3b. Record missing facts and machine-checked obstructions in
   `experiments/smt/PROOF_CLOSURE_PLAN.md` before continuing. Name the affected
   declaration, its missing supplier, and the evidence.
4. If a plan step is infeasible, return the machine-checked obstruction, not a
   workaround (precedent: the `Trichotomy` spec bug was FOUND as a falsity
   proof, then fixed by amendment — `Vsa/While/StmtDispatch.lean`).
5. Use the private incremental build in `TOOLING.md`, with one compiler at a
   time. Never `lake build` locally or use LSP tools. Keep outputs outside the
   repository. Axioms of every new theorem ⊆ {propext, Classical.choice, Quot.sound}.
6. Complexity must be HIDDEN by shape, not navigated by hand. If you find
   yourself counting conjuncts (`h.2.2.2.2…`), tracking positional indices, or
   re-deriving where a fact sits inside a tower, STOP: the statement wants a
   named-field structure (new defs) or a named destructurer (landed defs).
   Positional navigation is fragile (reorders shift every index), slow to
   elaborate, and burns your turns — gate rules R6/R7 enforce this.

## Extending the discipline

- New enforced rule: append a TSV line to `scripts/discipline_rules.tsv`
  (id, glob, regex or `COUNT>N:needle`, message). No code changes.
- Genuine exception: `-- discipline: allow(<rule-id>) <justification>` on or
  above the line — visible and auditable.
- Legacy files are listed in `scripts/discipline_grandfather.txt`; shrink it
  as proofs are re-seated on the layer. Never add new files to it casually.
- New abstraction landed? Add it to the table above and, if bypassable by
  hand, add a rule that catches the hand version.

## Documentation

- State the current design, commands, and proof obligations. Omit discussion
  history, prior drafts, and caveats answering objections absent from the text.
- Keep proof status in `experiments/smt/PROOF_CLOSURE_PLAN.md`. Link to it
  instead of maintaining parallel progress lists.
- Keep usage instructions in `README.md`, `TOOLING.md`, and this file.
  Write generated reports outside the repository. Use Git for completed
  session history.
- Remove superseded prompts and unused backups after checking consumers.
  Preserve tool inputs, proof premises, provenance, and unresolved obligations.
