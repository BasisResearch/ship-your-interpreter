# Wave 39 — M6 lane (#54 ErrShared + error links; #55 M6 close: Layout emitter + capstone threading)

HEAD bf453e5, tree clean at start. Assembly lane.

## Plan
1. ErrShared instantiation (SC = SnprintfContract, HT = ErrorTailChain) — check inhabitation.
2. M6 geometry emitter: Layout structure (Vsa/Refinement.lean:54 — `atInterpRun : Config → Nat → Nat → Prop`, fully abstract) + concrete instantiation from linker-script ground truth; scripts/gen_layout.py.
3. Thread capstone → Vsa/Sim/EndToEnd.lean with RemainingWork named-field structure.
4. Wiring lines for check_all (returned, not applied).

## Notes so far
- `TermResiduals` read (Vsa/Sim/TermAssembly.lean:70-320). Field census in progress.
- `Layout` = ONE abstract field `atInterpRun`. "Layout decides" must mean the concrete
  instantiation (symbol addresses / entry PC pinning) — need to find intended concrete def.
- ErrShared (rows/ErrorRouting.lean:55): g/inp/ra0/s*-saved/spv/m0 + SC : SnprintfContract …
  + out + HT : ErrorTailChain ra0 ExitStorePreExit out.

## Progress
- [x] TermAssembly split: `TermResidualsCore` (all term/div fields) + `TermResiduals extends TermResidualsCore` adding hErrFam. Zero consumer re-threading (parent projections). GREEN, axioms clean.
- [x] `Vsa/Sim/rows/ErrFamilyAssembly.lean` GREEN axiom-clean:
  - `ErrSharedInputs` (named fields: g/inp/s*/spv/m0/out + SC + hEntryOut + frameIC + segMain(OPEN) + segCrt0(OPEN) + geomEP) + `.toShared : ErrShared` at ra0=0x80004428 via errorTailChain_of_segments ∘ (interpContSeg_of, exitPrologSeg).
  - `errFamily_ofArmLinks`: ALL 42 routed hsites discharged by errLinkA_* (16) + errLinkB_* (26); stragglers = hBadClosure + hTopAbrupt (non-jal passthroughs) only.
  - `ErrWork` record + `errFamily_ofWork : ErrFamily Ly`.
- ErrShared status: SC (SnprintfContract) OPEN (M3); MainErrorSeg/Crt0ExitSeg OPEN (M6 decode); InterpContSeg + ExitPrologSeg LANDED conditional on InterpContFrame/ExitPrologGeom; ExitStoreHalts LANDED (exitStoreHalts, ErrorTail.lean).
- Next: gen_layout.py + LayoutGround.lean (ground LayoutInstance constants vs nm of c/while-riscv-htif.elf; interpRunLayout ALREADY the concrete Layout, landed+wired), then EndToEnd.lean.

## TermResiduals field-by-field status (post-split; core = TermResidualsCore)
| field(s) | status | supplier |
|---|---|---|
| hInt/hNull/hBool/hStr | OPEN oracle | LeafWiden/GeomFrom leaf geometry (rows landed; Resid value-paths open) |
| hNeg/hNot | OPEN | EvalRecCommon/blockB_unary (arm head landed; blockC residual) |
| hOrTrue/hAndFalse | OPEN | logical short-circuit geometry |
| hOrFalse/hAndTrue | OPEN | logical fall-through geometry (fresh ladder per elab-wall notes) |
| hVar | OPEN | VarLeafResid; env_get_found contract LANDED, eval-var call bridge open |
| hAssign | OPEN (whole-arm oracle) | env_define composed (EnvDefCompose); no evalAssignSim yet |
| hIAdd/hISub/hIMul/hIDiv/hIMod/hILt/hILe/hIGt/hIGe | OPEN cells | Eval*Row block-reflected rows landed; BinIntCellResid value-paths open |
| hEq/hNe | OPEN cells | value_equal_spec_full LANDED; EvalEqNeRow front wiring |
| hStrAddL/hStrAddR | OPEN | StrConcatCellResid — blocked on stringify spec (concat front closed to plumbing) |
| hStrLt/Le/Gt/Ge | OPEN | StrCmpOrderBridge (String.lt spec-layer gap) + StrArmMachineResid |
| hDivOv | OPEN | wrap-semantics div row |
| hArgsNil | OPEN (near-free) | seg-identity at args loop PC |
| hArgsCons | OPEN | per-iter body oracle + loopFromBody |
| hCallPrint/hCallPrintln/hCallAssertOk | OPEN | native contracts (task #7) |
| hCall | OPEN | CallArmSpec + widen |
| hFn | OPEN | EX_FN 2 named seams (task #18; AllocClosureContract inhabited) |
| hCallClosure | CRUX OPEN (sibling lane) | rows/CallClosureRow; wave-37 crux composed, spans task #20 |
| hSExpr/hSRet/hSRetNull/hSVarNull/hSBrk/hSCont/hSVarInit | OPEN oracles | Exec*Geom (execVarNullSimD landed via WidenMeta) |
| hSIfNone/hSWhileFalse/hSIfTrue/hSIfFalse/hSBlock/hSForStart/hSWhileBreak | OPEN | exit-sim geometry / measures |
| hFlCondFalse/hFlBodyBreak/hFlBodyRet/hFlLoop | GAP (no rows) | for-loop arms (TermGuards.forMeasure) |
| hSeqNil | essentially LANDED | execSeqNil wrap (still a field — trivial to close) |
| hSeqConsNormal/hSeqConsAbrupt | OPEN | execSeqLoop (seqMeasure) |
| hInitStore | OPEN-reduced | driveToLoopHead_interpRunLayout landed modulo hSpill + span premises |
| hEpilogueSpill | OPEN | epilogue restore-block ChainFacts |
| hDivCorr | OPEN-reduced | DivCorrFamily; ArmStages fold, board 7/14 eval + cut-shaped rest (task #19) |
| hErrFam | NOW SUPPLIED | errFamily_ofWork ∘ ErrWork (this wave) — no longer a raw whole-family gap |
| (scaffolds hInit*/hFc*/hEs*) | UNCONDITIONAL | ScaffoldRows (True motives) |

## Deliverables landed this wave
- Vsa/Sim/TermAssembly.lean: TermResidualsCore/TermResiduals extends split (GREEN, olean regen'd, DeriveMetaDemo consumer verified green).
- Vsa/Sim/rows/ErrFamilyAssembly.lean (NEW, GREEN, axiom-clean): ErrSharedInputs(+toShared), errFamily_ofArmLinks (42/42 via errLinkA/B), ErrWork, errFamily_ofWork.
- scripts/gen_layout.py (NEW) + Vsa/Sim/rows/LayoutGround.lean (GENERATED, self-verified 10/10 axiom audits, no sorryAx): LayoutInstance constants tied to nm of c/while-riscv-htif.elf (interp_run/main/eval_expr/exec_stmt/runtime_error/_exit/__stack_top/__stack_size/tohost) + ground_atInterpRun shape pin. NOTE: jumpTableBase 0x80019f58 is .rodata (no symbol) — not nm-groundable, stays hand-pinned in LayoutInstance.
- Vsa/Sim/EndToEnd.lean (NEW, GREEN, axiom-clean): RemainingWork (extends TermResidualsCore + errWork : ErrWork); interpSim_ofWork; endToEnd : RemainingWork interpRunLayout → InterpSim interpRunLayout; endToEnd_refinement.
- Discipline gate: my 4 files clean; the only failures are the sibling's uncommitted MemcpySpecFramedWord.lean (pre-existing in their lane).

## Wiring lines (for coordinator; NOT applied)
Vsa.lean (after the rows/ErrArmLinksB import block):
  import Vsa.Sim.rows.ErrFamilyAssembly
  import Vsa.Sim.rows.LayoutGround
  import Vsa.Sim.EndToEnd
scripts/check_all.sh axiom list:
  Vsa.Sim.ErrSharedInputs.toShared                 # ErrFamilyAssembly (ErrShared instantiated once: exit tail from 4 segments at ra0=0x80004428; open inputs = SC + MainErrorSeg + Crt0ExitSeg)
  Vsa.Sim.errFamily_ofArmLinks                     # ErrFamilyAssembly (42/42 routed hsites fed from the generated errLinkA/errLinkB families; stragglers = hBadClosure/hTopAbrupt passthroughs)
  Vsa.Sim.errFamily_ofWork                         # ErrFamilyAssembly (ErrFamily from the ONE ErrWork record)
  Vsa.Sim.LayoutGround.ground_atInterpRun          # LayoutGround (GENERATED: concrete Layout program-point shape tied to the interp_run ELF symbol)
  Vsa.Sim.LayoutGround.ground_interpRunCode        # LayoutGround (GENERATED: interp_run code region = [interp_run, main) from nm)
  Vsa.Sim.LayoutGround.ground_stackSL              # LayoutGround (GENERATED: C-stack region from __stack_top/__stack_size)
  Vsa.Sim.LayoutGround.ground_tohostAddr           # LayoutGround (GENERATED: tohost cell from nm)
  Vsa.Sim.EndToEnd.interpSim_ofWork                # EndToEnd (InterpSim L from the ONE RemainingWork record, any layout)
  Vsa.Sim.EndToEnd.endToEnd                        # EndToEnd (THE end-to-end theorem at the concrete interpRunLayout — the live progress meter)
  Vsa.Sim.EndToEnd.endToEnd_refinement             # EndToEnd (full behavioral correspondence at the concrete layout)
