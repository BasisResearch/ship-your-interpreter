# corpus-fuzzer log

Bounded-task deliverables A (remaining-case corpus) + B (statement fuzzer).
Scope: scripts/ + experiments/ only; nothing enters a proof (pre-proof
validation, like the ELF emulator harness).

## A. Remaining-case machine corpus — `scripts/gen_corpus.py`

- 97 cases → `experiments/corpus/*.md` + `experiments/corpus/INDEX.md`.
- Imports (does NOT fork) `scripts/gen_fn.py`'s `build_cfg`/`classify_loop`/
  `Block`; budgets lifted for analysis-only whole-fn CFGs. Regenerate at will:
  `python3 scripts/gen_corpus.py`.
- Enumeration sources: 55 census NOT_FOUND fields (field-census.tsv) with
  assembly_skeleton.tsv supplier notes + documented arm PCs (eval/stmt/vp jump
  tables from rows/Layout*Gen); the 16-fn io flush chain (run1-brief.md DAG);
  19 distinct error jal sites (m5_error_routing.tsv); 6 value_print arms.
- Per case: disasm slice, CFG, terminator/loop class, calls with LANDED/NONE
  summary status (grepped from Vsa/**.lean), reg/mem outcome sketch, consuming
  record field(s).
- Cluster tally: loop-arm 36, error-jal-seam 19, io-loop-fold 16, env-seam 13,
  straight-span 6, loop 2, {io-fold, leaf-slot, str-seam, value-box-tail,
  oracle-no-span} 1 each.

## B. Statement fuzzer — `scripts/statement_fuzz.py`

- Drift-proof: runs Lean once to `trace_state` the unfolded Prop, parses the
  ∀-telescope, synthesizes lethal witnesses per binder type (sp=0#64, SL=⟨0,0⟩,
  m0=finite fuzzMem, BitVec=0#64, operand=40#64), emits a `¬ P` probe with a
  `first|` cascade over projection paths, and machine-checks via `lake env lean`.
  REFUTED ⟺ axiom-clean ⊆ {propext,Classical.choice,Quot.sound}; a `sorryAx`
  or unbuildable entry-pin hyp ⇒ SURVIVED (the amendment worked). z3 detected
  at /opt/homebrew/bin/z3 for non-`decide` arithmetic side-conditions.
- Real-Prop check: current `SkelHNeg` (amended, EvalEntry-pinned) → SURVIVED,
  correct — the sp=0 witness no longer bites.

(runs appended below)

## statement_fuzz.py run

- `IoWriteMined.IoWriteInvCandidate` → **UNDECIDABLE** — telescope not discoverable

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMutant` (file exec_brk_bridge.lean) → **UNDECIDABLE** — ['<struct fields undiscoverable>']

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMined` (file exec_brk_bridge.lean) → **UNDECIDABLE** — ['<struct fields undiscoverable>']

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMined` (file exec_brk_bridge.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMutant` (file exec_brk_bridge.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run


### Acceptance run (hermetic 2865529→main amendment model)

**Must REFUTE (pre-amendment holes):**
- `PreNeg` → **REFUTED** — (axiom-free)
- `PreAndFalse` → **REFUTED** — (axiom-free)
- `PreOrTrue` → **REFUTED** — (axiom-free)

**Must SURVIVE (amended fields):**
- `AmdNeg` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdNeg' depends on axioms: [sorryAx]
- `AmdAndFalse` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdAndFalse' depends on axioms: [sorryAx]
- `AmdOrTrue` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdOrTrue' depends on axioms: [sorryAx]

**Acceptance: refuted 3/3 pre (need ≥3), survived 3/3 amended → PASS**

## statement_fuzz.py run


## statement_fuzz.py run

- `Probe` (file fuzz_probe.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `BadProbe` (file fuzz_false.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `StmtDispatchResidAmended` (file fuzz_execarm.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide), (by decide)⟩)

## statement_fuzz.py run

- `LeafResidAmended` (file fuzz_leaf.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `WInvStructured` (file fuzz_io.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide), (by decide)⟩)

## statement_fuzz.py run

- `ErrSeamResid` (file fuzz_errseam.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `VParmArmResid` (file fuzz_vparm.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide), (by decide)⟩)

## statement_fuzz.py run

- `FnResid` (file fuzz_fn.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide), (by decide)⟩)

## statement_fuzz.py run

- `ErrArmResid` (file fuzz_errarm.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [sorryAx] (ghost witness ⟨(by decide), (by decide), (by decide)⟩)

## statement_fuzz.py run


## statement_fuzz.py run

- `Vsa.Sim.ExecLeafMemPin SL sp m0 m` → **UNDECIDABLE** — telescope not discoverable

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMined` (file exec_brk_bridge.lean) → **SURVIVED** — 'VsaFuzzFileProbe.probe' depends on axioms: [sorryAx]

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMutant` (file exec_brk_bridge.lean) → **SURVIVED** — 'VsaFuzzFileProbe.probe' depends on axioms: [sorryAx]

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMined` (file exec_brk_bridge.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `ExecBrkBridge.brkArmMutant` (file exec_brk_bridge.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIAdd.mined` (file hIAdd.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIAdd.mutant` (file hIAdd.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAndFalse.mined` (file hAndFalse.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAndFalse.mutant` (file hAndFalse.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAndTrue.mined` (file hAndTrue.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAndTrue.mutant` (file hAndTrue.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hArgsCons.mined` (file hArgsCons.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hArgsCons.mutant` (file hArgsCons.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hArgsNil.mined` (file hArgsNil.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hArgsNil.mutant` (file hArgsNil.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAssign.mined` (file hAssign.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hAssign.mutant` (file hAssign.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCall.mined` (file hCall.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCall.mutant` (file hCall.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallAssertOk.mined` (file hCallAssertOk.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallAssertOk.mutant` (file hCallAssertOk.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallClosure.mined` (file hCallClosure.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallClosure.mutant` (file hCallClosure.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallPrint.mined` (file hCallPrint.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallPrint.mutant` (file hCallPrint.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallPrintln.mined` (file hCallPrintln.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hCallPrintln.mutant` (file hCallPrintln.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hDivOv.mined` (file hDivOv.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hDivOv.mutant` (file hDivOv.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hEpilogueSpill.mined` (file hEpilogueSpill.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hEpilogueSpill.mutant` (file hEpilogueSpill.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hEq.mined` (file hEq.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hEq.mutant` (file hEq.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hFn.mined` (file hFn.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hFn.mutant` (file hFn.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIAdd.mined` (file hIAdd.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIAdd.mutant` (file hIAdd.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIDiv.mined` (file hIDiv.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIDiv.mutant` (file hIDiv.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIGe.mined` (file hIGe.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIGe.mutant` (file hIGe.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIGt.mined` (file hIGt.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIGt.mutant` (file hIGt.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hILe.mined` (file hILe.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hILe.mutant` (file hILe.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hILt.mined` (file hILt.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hILt.mutant` (file hILt.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIMod.mined` (file hIMod.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIMod.mutant` (file hIMod.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIMul.mined` (file hIMul.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIMul.mutant` (file hIMul.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hISub.mined` (file hISub.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hISub.mutant` (file hISub.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hInitStore.mined` (file hInitStore.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hInitStore.mutant` (file hInitStore.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNe.mined` (file hNe.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNe.mutant` (file hNe.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNeg.mined` (file hNeg.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNeg.mutant` (file hNeg.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNot.mined` (file hNot.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hNot.mutant` (file hNot.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hOrFalse.mined` (file hOrFalse.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hOrFalse.mutant` (file hOrFalse.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hOrTrue.mined` (file hOrTrue.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hOrTrue.mutant` (file hOrTrue.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSBlock.mined` (file hSBlock.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSBlock.mutant` (file hSBlock.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSBrk.mined` (file hSBrk.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSBrk.mutant` (file hSBrk.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSCont.mined` (file hSCont.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSCont.mutant` (file hSCont.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSExpr.mined` (file hSExpr.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSExpr.mutant` (file hSExpr.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSForStart.mined` (file hSForStart.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSForStart.mutant` (file hSForStart.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfFalse.mined` (file hSIfFalse.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfFalse.mutant` (file hSIfFalse.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfNone.mined` (file hSIfNone.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfNone.mutant` (file hSIfNone.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfTrue.mined` (file hSIfTrue.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSIfTrue.mutant` (file hSIfTrue.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSRet.mined` (file hSRet.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSRet.mutant` (file hSRet.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSRetNull.mined` (file hSRetNull.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSRetNull.mutant` (file hSRetNull.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSVarInit.mined` (file hSVarInit.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSVarInit.mutant` (file hSVarInit.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSVarNull.mined` (file hSVarNull.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSVarNull.mutant` (file hSVarNull.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSWhileBreak.mined` (file hSWhileBreak.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSWhileBreak.mutant` (file hSWhileBreak.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSWhileFalse.mined` (file hSWhileFalse.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSWhileFalse.mutant` (file hSWhileFalse.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqConsAbrupt.mined` (file hSeqConsAbrupt.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqConsAbrupt.mutant` (file hSeqConsAbrupt.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqConsNormal.mined` (file hSeqConsNormal.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqConsNormal.mutant` (file hSeqConsNormal.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqNil.mined` (file hSeqNil.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hSeqNil.mutant` (file hSeqNil.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStr.mined` (file hStr.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStr.mutant` (file hStr.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrAddL.mined` (file hStrAddL.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrAddL.mutant` (file hStrAddL.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrAddR.mined` (file hStrAddR.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrAddR.mutant` (file hStrAddR.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrGe.mined` (file hStrGe.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrGe.mutant` (file hStrGe.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrGt.mined` (file hStrGt.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrGt.mutant` (file hStrGt.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrLe.mined` (file hStrLe.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrLe.mutant` (file hStrLe.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrLt.mined` (file hStrLt.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hStrLt.mutant` (file hStrLt.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hVar.mined` (file hVar.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hVar.mutant` (file hVar.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.minedRecur` (file crux_relations.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.minedNest` (file crux_relations.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.budgetMutant` (file crux_relations.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.minedLadder` (file crux_relations.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.constMutant` (file crux_relations.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.minedFrameGrowth` (file crux_relations.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide)⟩)

## statement_fuzz.py run

- `InvGen_cruxRelations.frameMutant` (file crux_relations.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide)⟩)

> COORDINATOR GUIDANCE (fuzzer v2 descent, in answer to your design question):
> Your fallback mechanism is correct BUT split the verdicts — do not report a
> plain SURVIVED when the outer guard was undischargeable:
> 1. REFUTED — full-statement descent went through (outer witnesses + guard
>    discharged + nested adversary + concl refuted). The gold verdict.
> 2. CONJUNCT-REFUTED-ISOLATED — when outer hyps (EvalEntry etc.) cannot be
>    discharged at chosen witnesses: extract the nested ∀-conjunct AS A
>    STANDALONE Prop (outer ghosts parameterized at adversary values) and
>    refute THAT. Not a whole-statement falsity (the entry hyp may constrain
>    the ghosts), but exactly the 48b/48f early-warning pattern — the isolated
>    frame_pop refutation predicted the real blocker. Report it as a WARNING
>    verdict for prover attention, never silently.
> 3. SURVIVED — descent RAN and adversaries failed.
> 4. SURVIVED-OUTER-GUARDED — descent could NOT run (guard undischargeable);
>    explicitly says "nested body untested at depth ≥2". Distinct from 3.
> Acceptance-v2 note: the pre-48f targets are UNGUARDED (that's why hand
> refutation worked) — they must land in verdict 1. The current amended ones
> should land in 3 or 4, and a 4 is fine there (entry-guarded is the design).

## statement_fuzz.py run

- `VsaAcceptV2.PreMemExt` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run


### Acceptance-v2 run (nested-quantifier descent)

**Must REFUTE (pre-48f over-quantified conjuncts):**
- `PreMemExt` → **REFUTED** (builder=memext)
- `PrePresence` → **REFUTED** (builder=presence)

**Must SURVIVE (post-48f/48g guarded survivors):**
- `CurMemExt` → **SURVIVED**
- `CurPresence` → **SURVIVED**

**Live HEAD `TermRouting.NegResid` mcall-pair probe:** SURVIVED (guarded at HEAD)

### Acceptance run (hermetic 2865529→main amendment model)

**Must REFUTE (pre-amendment holes):**
- `PreNeg` → **REFUTED** — (axiom-free)
- `PreAndFalse` → **REFUTED** — (axiom-free)
- `PreOrTrue` → **REFUTED** — (axiom-free)

**Must SURVIVE (amended fields):**
- `AmdNeg` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdNeg' depends on axioms: [sorryAx]
- `AmdAndFalse` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdAndFalse' depends on axioms: [sorryAx]
- `AmdOrTrue` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdOrTrue' depends on axioms: [sorryAx]

**Acceptance: refuted 3/3 pre (need ≥3), survived 3/3 amended → PASS**

**v1 regression check → PASS**

**Acceptance-v2 → PASS**

## statement_fuzz.py run


### Acceptance-v2 run (nested-quantifier descent)

**Must REFUTE (pre-48f over-quantified conjuncts):**
- `PreMemExt` → **REFUTED** (builder=memext)
- `PrePresence` → **REFUTED** (builder=presence)

**Must SURVIVE (post-48f/48g guarded survivors):**
- `CurMemExt` → **SURVIVED**
- `CurPresence` → **SURVIVED**

**Live HEAD `TermRouting.NegResid` mcall-pair probe:** REFUTED (live falsity: raw ∀-mcall still present)

### Acceptance run (hermetic 2865529→main amendment model)

**Must REFUTE (pre-amendment holes):**
- `PreNeg` → **REFUTED** — (axiom-free)
- `PreAndFalse` → **REFUTED** — (axiom-free)
- `PreOrTrue` → **REFUTED** — (axiom-free)

**Must SURVIVE (amended fields):**
- `AmdNeg` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdNeg' depends on axioms: [sorryAx]
- `AmdAndFalse` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdAndFalse' depends on axioms: [sorryAx]
- `AmdOrTrue` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdOrTrue' depends on axioms: [sorryAx]

**Acceptance: refuted 3/3 pre (need ≥3), survived 3/3 amended → PASS**

**v1 regression check → PASS**

**Acceptance-v2 → PASS**

## statement_fuzz.py run

- `InvGen_hIAdd.mined` (file hIAdd.lean) → **SURVIVED** — candidate inhabited (self-consistent) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_hIAdd.mutant` (file hIAdd.lean) → **REFUTED** — (axiom-free) (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_synthMcall.mined` (file inv_mcall.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_synthMcall.mutant` (file inv_mcall.lean) → **SURVIVED** — 'VsaFuzzFileProbe.refuted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] (ghost witness ⟨(by decide), (by decide)⟩)

## statement_fuzz.py run

- `InvGen_synthMcall.mined` → **REFUTED** (descent/memext, depth 2) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `VsaAcceptV2.PreMemExt` → **REFUTED** (descent/memext, depth 2) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run


### Acceptance-v2 run (nested-quantifier descent)

**Must REFUTE (pre-48f over-quantified conjuncts):**
- `PreMemExt` → **REFUTED** (builder=memext)
- `PrePresence` → **REFUTED** (builder=presence)

**Must SURVIVE (post-48f/48g guarded survivors):**
- `CurMemExt` → **SURVIVED**
- `CurPresence` → **SURVIVED**

**Live HEAD `TermRouting.NegResid` mcall-pair probe:** REFUTED (live falsity: raw ∀-mcall still present)

### Acceptance run (hermetic 2865529→main amendment model)

**Must REFUTE (pre-amendment holes):**
- `PreNeg` → **REFUTED** — (axiom-free)
- `PreAndFalse` → **REFUTED** — (axiom-free)
- `PreOrTrue` → **REFUTED** — (axiom-free)

**Must SURVIVE (amended fields):**
- `AmdNeg` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdNeg' depends on axioms: [sorryAx]
- `AmdAndFalse` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdAndFalse' depends on axioms: [sorryAx]
- `AmdOrTrue` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdOrTrue' depends on axioms: [sorryAx]

**Acceptance: refuted 3/3 pre (need ≥3), survived 3/3 amended → PASS**

**v1 regression check → PASS**

**Acceptance-v2 → PASS**

## statement_fuzz.py run

- `InvGen_io_fflush_r.IoFflushRInvCandidate` (file io_fflush_r.lean) → **UNDECIDABLE** — ['<struct fields undiscoverable>']

## statement_fuzz.py run

- `InvGen_io_fflush_r.IoFflushRInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `NovelResidA` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `NovelResidC` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `InvGen_io_sflush_r.IoSflushRInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `InvGen_io_sbprintf.IoSbprintfInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `InvGen_io_vfprintf_r.IoVfprintfRInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `InvGen_io_swbuf_r.IoSwbufRInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `InvGen_io_fputs_r.IoFputsRInvCandidate` → **SURVIVED** (descent depth 2: no adversary builder refuted a nested conjunct)

## statement_fuzz.py run

- `NovelResidA` → **UNDECIDABLE** (v2.1 found uncovered demand @0x90000 but probe did not close) — 'VsaFuzzSem.probe' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)

## statement_fuzz.py run

- `NovelResidC` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x100 ∉ cover [0,256)∪[512,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidA` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x90000 ∉ cover [0,589824)∪[589840,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)

## statement_fuzz.py run

- `NovelResidC` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x100 ∉ cover [0,256)∪[512,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run


### --gen-battery 3 (fresh sample, seed=1)

- GenProbe0_F [extends] truth=F demand@0x813e cover=[0,33086)∪[37182,∞) → SURVIVED [MISS]
- GenProbe0_T [extends] truth=T demand@0x0 cover=[0,110076)∪[110092,∞) → SURVIVED [OK]
- GenProbe1_F [present] truth=F demand@0xd15c cover=[0,53596)∪[57692,∞) → REFUTED [OK]
- GenProbe1_T [value] truth=T demand@0x1bb98 cover=[113560,146328)∪[229579,262347) → SURVIVED [OK]
- GenProbe2_F [agree] truth=F demand@0x0 cover=[11266,44034)∪[52428,52684) → PRED-FALSE-NOPROOF [MISS]
- GenProbe2_T [value] truth=T demand@0x0 cover=[0,221305)∪[221561,∞) → SURVIVED [OK]

**gen-battery: 4/6 correct → FAIL**

## statement_fuzz.py run


### --gen-battery 3 (fresh sample, seed=1)

- GenProbe0_F [extends] truth=F demand@0x813e cover=[0,33086)∪[37182,∞) → REFUTED [OK]
- GenProbe0_T [extends] truth=T demand@0x0 cover=[0,110076)∪[110092,∞) → SURVIVED [OK]
- GenProbe1_F [present] truth=F demand@0xd15c cover=[0,53596)∪[57692,∞) → REFUTED [OK]
- GenProbe1_T [value] truth=T demand@0x1bb98 cover=[113560,146328)∪[229579,262347) → SURVIVED [OK]
- GenProbe2_F [agree] truth=F demand@0x0 cover=[11266,44034)∪[52428,52684) → REFUTED [OK]
- GenProbe2_T [value] truth=T demand@0x0 cover=[0,221305)∪[221561,∞) → SURVIVED [OK]

**gen-battery: 6/6 correct → PASS**

## statement_fuzz.py run


### --gen-battery 20 (fresh sample, seed=7)

- GenProbe0_F [value] truth=F demand@0x0 cover=[49351,53447)∪[79088,111856) → REFUTED [OK]
- GenProbe0_T [present] truth=T demand@0x0 cover=[0,227355)∪[260123,∞) → SURVIVED [OK]
- GenProbe1_F [present] truth=F demand@0x0 cover=[64907,65163) → REFUTED [OK]
- GenProbe1_T [extends] truth=T demand@0x1c4c6 cover=[115910,115926) → SURVIVED [OK]
- GenProbe2_F [value] truth=F demand@0x277c5 cover=[0,161733)∪[161989,∞) → REFUTED [OK]
- GenProbe2_T [extends] truth=T demand@0x8097 cover=[32919,32935) → SURVIVED [OK]
- GenProbe3_F [agree] truth=F demand@0x2bf70 cover=[0,180080)∪[212848,∞) → REFUTED [OK]
- GenProbe3_T [extends] truth=T demand@0x2828e cover=[164494,168590)∪[221091,221107) → SURVIVED [OK]
- GenProbe4_F [agree] truth=F demand@0x0 cover=[141525,174293) → REFUTED [OK]
- GenProbe4_T [present] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe5_F [value] truth=F demand@0x1bee3 cover=[0,114403)∪[118499,∞) → REFUTED [OK]
- GenProbe5_T [agree] truth=T demand@0x0 cover=[0,260312)∪[260328,∞) → SURVIVED [OK]
- GenProbe6_F [present] truth=F demand@0x3e134 cover=[0,254260)∪[254516,∞) → REFUTED [OK]
- GenProbe6_T [extends] truth=T demand@0x6e93 cover=[28307,61075)∪[193595,197691) → SURVIVED [OK]
- GenProbe7_F [value] truth=F demand@0x2e8ac cover=[0,190636)∪[190652,∞) → REFUTED [OK]
- GenProbe7_T [present] truth=T demand@0x2049f cover=[132255,136351) → SURVIVED [OK]
- GenProbe8_F [extends] truth=F demand@0x3d7d9 cover=[0,251865)∪[284633,∞) → REFUTED [OK]
- GenProbe8_T [present] truth=T demand@0x0 cover=[0,107591)∪[111687,∞) → SURVIVED [OK]
- GenProbe9_F [value] truth=F demand@0x0 cover=[136899,140995) → REFUTED [OK]
- GenProbe9_T [value] truth=T demand@0x18fa8 cover=[102312,102568) → SURVIVED [OK]
- GenProbe10_F [agree] truth=F demand@0x3c725 cover=[0,247589)∪[251685,∞) → REFUTED [OK]
- GenProbe10_T [value] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe11_F [present] truth=F demand@0x0 cover=[251382,255478) → REFUTED [OK]
- GenProbe11_T [agree] truth=T demand@0x0 cover=[0,250626)∪[250882,∞) → SURVIVED [OK]
- GenProbe12_F [extends] truth=F demand@0x0 cover=[83286,83542)∪[242829,275597) → REFUTED [OK]
- GenProbe12_T [extends] truth=T demand@0x1d2b cover=[7467,7483)∪[183714,183970) → SURVIVED [OK]
- GenProbe13_F [value] truth=F demand@0x3954 cover=[0,14676)∪[18772,∞) → REFUTED [OK]
- GenProbe13_T [extends] truth=T demand@0x0 cover=[0,219683)∪[219939,∞) → SURVIVED [OK]
- GenProbe14_F [value] truth=F demand@0x0 cover=[9806,42574) → REFUTED [OK]
- GenProbe14_T [extends] truth=T demand@0x3c9b6 cover=[248246,248262) → SURVIVED [OK]
- GenProbe15_F [present] truth=F demand@0x1fcea cover=[0,130282)∪[130538,∞) → REFUTED [OK]
- GenProbe15_T [value] truth=T demand@0x0 cover=[0,33223)∪[65991,∞) → SURVIVED [OK]
- GenProbe16_F [present] truth=F demand@0x0 cover=[136101,136357)∪[250628,250884) → REFUTED [OK]
- GenProbe16_T [value] truth=T demand@0x1b396 cover=[111510,115606)∪[165664,165680) → SURVIVED [OK]
- GenProbe17_F [present] truth=F demand@0x0 cover=[132701,132957) → REFUTED [OK]
- GenProbe17_T [value] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe18_F [agree] truth=F demand@0xbcd0 cover=[0,48336)∪[52432,∞) → REFUTED [OK]
- GenProbe18_T [agree] truth=T demand@0x0 cover=[0,119828)∪[119844,∞) → SURVIVED [OK]
- GenProbe19_F [agree] truth=F demand@0x0 cover=[141791,142047) → REFUTED [OK]
- GenProbe19_T [present] truth=T demand@0x0 cover=[0,259319)∪[263415,∞) → SURVIVED [OK]

**gen-battery: 40/40 correct → PASS**

## statement_fuzz.py run


### --gen-battery 20 (fresh sample, seed=None)

- GenProbe0_F [value] truth=F demand@0x18b11 cover=[0,101137)∪[101153,∞) → REFUTED [OK]
- GenProbe0_T [value] truth=T demand@0x0 cover=[0,95889)∪[99985,∞) → SURVIVED [OK]
- GenProbe1_F [agree] truth=F demand@0x630f cover=[0,25359)∪[25615,∞) → REFUTED [OK]
- GenProbe1_T [extends] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe2_F [value] truth=F demand@0x0 cover=[144342,144358) → REFUTED [OK]
- GenProbe2_T [agree] truth=T demand@0x0 cover=[0,91649)∪[91665,∞) → SURVIVED [OK]
- GenProbe3_F [value] truth=F demand@0x26cae cover=[0,158894)∪[162990,∞) → REFUTED [OK]
- GenProbe3_T [value] truth=T demand@0x0 cover=[0,113883)∪[146651,∞) → SURVIVED [OK]
- GenProbe4_F [agree] truth=F demand@0x0 cover=[33969,38065) → REFUTED [OK]
- GenProbe4_T [present] truth=T demand@0x33f4a cover=[212810,216906) → SURVIVED [OK]
- GenProbe5_F [agree] truth=F demand@0x2dbb7 cover=[0,187319)∪[220087,∞) → REFUTED [OK]
- GenProbe5_T [agree] truth=T demand@0x0 cover=[0,79300)∪[79556,∞) → SURVIVED [OK]
- GenProbe6_F [extends] truth=F demand@0x0 cover=[65202,65218) → REFUTED [OK]
- GenProbe6_T [agree] truth=T demand@0x0 cover=[0,68125)∪[72221,∞) → SURVIVED [OK]
- GenProbe7_F [present] truth=F demand@0x3c3e3 cover=[0,246755)∪[279523,∞) → REFUTED [OK]
- GenProbe7_T [value] truth=T demand@0x0 cover=[0,4858)∪[37626,∞) → SURVIVED [OK]
- GenProbe8_F [present] truth=F demand@0x0 cover=[11676,11932)∪[192372,192388) → REFUTED [OK]
- GenProbe8_T [agree] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe9_F [present] truth=F demand@0x0 cover=[219468,223564) → REFUTED [OK]
- GenProbe9_T [value] truth=T demand@0x0 cover=[0,144091)∪[176859,∞) → SURVIVED [OK]
- GenProbe10_F [value] truth=F demand@0x0 cover=[229007,261775) → REFUTED [OK]
- GenProbe10_T [value] truth=T demand@0x3d21c cover=[250396,250412) → SURVIVED [OK]
- GenProbe11_F [value] truth=F demand@0x0 cover=[235543,268311) → REFUTED [OK]
- GenProbe11_T [extends] truth=T demand@0x0 cover=[0,183985)∪[216753,∞) → SURVIVED [OK]
- GenProbe12_F [agree] truth=F demand@0x0 cover=[245923,245939) → REFUTED [OK]
- GenProbe12_T [present] truth=T demand@0x4228 cover=[16936,16952)∪[107757,111853) → SURVIVED [OK]
- GenProbe13_F [present] truth=F demand@0x8131 cover=[0,33073)∪[37169,∞) → REFUTED [OK]
- GenProbe13_T [agree] truth=T demand@0x3e822 cover=[256034,256050) → SURVIVED [OK]
- GenProbe14_F [extends] truth=F demand@0x3c50c cover=[0,247052)∪[247068,∞) → REFUTED [OK]
- GenProbe14_T [agree] truth=T demand@0x4ee3 cover=[20195,52963)∪[135708,168476) → SURVIVED [OK]
- GenProbe15_F [present] truth=F demand@0x3d437 cover=[0,250935)∪[250951,∞) → REFUTED [OK]
- GenProbe15_T [present] truth=T demand@0x0 cover=[0,137346)∪[151767,∞) → SURVIVED [OK]
- GenProbe16_F [extends] truth=F demand@0x0 cover=[220947,225043) → REFUTED [OK]
- GenProbe16_T [present] truth=T demand@0x0 cover=[0,210934)∪[210950,∞) → SURVIVED [OK]
- GenProbe17_F [present] truth=F demand@0x1a845 cover=[0,108613)∪[108629,∞) → REFUTED [OK]
- GenProbe17_T [extends] truth=T demand@0x0 cover=[0,150990)∪[183758,∞) → SURVIVED [OK]
- GenProbe18_F [present] truth=F demand@0x0 cover=[108070,140838)∪[174635,174651) → REFUTED [OK]
- GenProbe18_T [agree] truth=T demand@0x0 cover=[0,7942)∪[12038,∞) → SURVIVED [OK]
- GenProbe19_F [present] truth=F demand@0x0 cover=[31255,64023)∪[125083,129179) → REFUTED [OK]
- GenProbe19_T [present] truth=T demand@0x0 cover=[0,189817)∪[189833,∞) → SURVIVED [OK]

**gen-battery: 40/40 correct → PASS**

## statement_fuzz.py run


### Acceptance-v2 run (nested-quantifier descent)

**Must REFUTE (pre-48f over-quantified conjuncts):**
- `PreMemExt` → **REFUTED** (builder=memext)
- `PrePresence` → **REFUTED** (builder=presence)

**Must SURVIVE (post-48f/48g guarded survivors):**
- `CurMemExt` → **SURVIVED**
- `CurPresence` → **SURVIVED**

**Live HEAD `TermRouting.NegResid` mcall-pair probe:** REFUTED (live falsity: raw ∀-mcall still present)

### Acceptance run (hermetic 2865529→main amendment model)

**Must REFUTE (pre-amendment holes):**
- `PreNeg` → **REFUTED** — (axiom-free)
- `PreAndFalse` → **REFUTED** — (axiom-free)
- `PreOrTrue` → **REFUTED** — (axiom-free)

**Must SURVIVE (amended fields):**
- `AmdNeg` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdNeg' depends on axioms: [sorryAx]
- `AmdAndFalse` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdAndFalse' depends on axioms: [sorryAx]
- `AmdOrTrue` → **SURVIVED** (naive witness rejected → survives) — 'VsaFuzzAcceptance.refute_AmdOrTrue' depends on axioms: [sorryAx]

**Acceptance: refuted 3/3 pre (need ≥3), survived 3/3 amended → PASS**

**v1 regression check → PASS**

**Acceptance-v2 → PASS**

## statement_fuzz.py run

- `NovelResidA` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x90000 ∉ cover [0,589824)∪[589840,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)

## statement_fuzz.py run

- `NovelResidC` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x100 ∉ cover [0,256)∪[512,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidA` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x90000 ∉ cover [0,589824)∪[589840,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)

## statement_fuzz.py run

- `NovelResidC` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x100 ∉ cover [0,256)∪[512,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run


### --gen-battery 20 (fresh sample, seed=99)

- GenProbe0_F [extends] truth=F demand@0x110e2 cover=[0,69858)∪[69874,∞) → REFUTED [OK]
- GenProbe0_T [extends] truth=T demand@0x19882 cover=[104578,137346)∪[196073,228841) → SURVIVED [OK]
- GenProbe1_F [agree] truth=F demand@0x0 cover=[106831,110927)∪[242266,242522) → REFUTED [OK]
- GenProbe1_T [value] truth=T demand@0x14957 cover=[84311,117079) → SURVIVED [OK]
- GenProbe2_F [extends] truth=F demand@0x2fb9 cover=[0,12217)∪[12473,∞) → REFUTED [OK]
- GenProbe2_T [extends] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe3_F [extends] truth=F demand@0x1b104 cover=[0,110852)∪[143620,∞) → REFUTED [OK]
- GenProbe3_T [present] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe4_F [agree] truth=F demand@0x164a0 cover=[0,91296)∪[91552,∞) → REFUTED [OK]
- GenProbe4_T [extends] truth=T demand@0x0 cover=[0,24996)∪[29092,∞) → SURVIVED [OK]
- GenProbe5_F [extends] truth=F demand@0x0 cover=[95014,95030)∪[202343,235111) → REFUTED [OK]
- GenProbe5_T [agree] truth=T demand@0x27dc9 cover=[163273,163529) → SURVIVED [OK]
- GenProbe6_F [present] truth=F demand@0x31185 cover=[0,201093)∪[205189,∞) → REFUTED [OK]
- GenProbe6_T [agree] truth=T demand@0x20cb9 cover=[134329,134345)∪[168084,200852) → SURVIVED [OK]
- GenProbe7_F [extends] truth=F demand@0x0 cover=[2260,6356)∪[101332,101588) → REFUTED [OK]
- GenProbe7_T [value] truth=T demand@0x0 cover=[0,181160)∪[213928,∞) → SURVIVED [OK]
- GenProbe8_F [agree] truth=F demand@0x21c7b cover=[0,138363)∪[171131,∞) → REFUTED [OK]
- GenProbe8_T [present] truth=T demand@0x0 cover=[0,55129)∪[59225,∞) → SURVIVED [OK]
- GenProbe9_F [extends] truth=F demand@0x0 cover=[154755,155011)∪[157139,161235) → REFUTED [OK]
- GenProbe9_T [value] truth=T demand@0x0 cover=[0,138832)∪[171600,∞) → SURVIVED [OK]
- GenProbe10_F [value] truth=F demand@0x0 cover=[251224,283992) → REFUTED [OK]
- GenProbe10_T [present] truth=T demand@0xeb3f cover=[60223,64319) → SURVIVED [OK]
- GenProbe11_F [value] truth=F demand@0x28d7c cover=[0,167292)∪[200060,∞) → REFUTED [OK]
- GenProbe11_T [extends] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe12_F [present] truth=F demand@0x0 cover=[103934,104190) → REFUTED [OK]
- GenProbe12_T [extends] truth=T demand@0x1187a cover=[71802,72058) → SURVIVED [OK]
- GenProbe13_F [agree] truth=F demand@0x1da3a cover=[0,121402)∪[121658,∞) → REFUTED [OK]
- GenProbe13_T [present] truth=T demand@0x12c2a cover=[76842,109610) → SURVIVED [OK]
- GenProbe14_F [extends] truth=F demand@0x0 cover=[42036,42292)∪[50838,51094) → REFUTED [OK]
- GenProbe14_T [agree] truth=T demand@0x14547 cover=[83271,83527)∪[164309,164325) → SURVIVED [OK]
- GenProbe15_F [value] truth=F demand@0x0 cover=[258182,290950) → REFUTED [OK]
- GenProbe15_T [present] truth=T demand@0x0 cover=[0,171418)∪[171434,∞) → SURVIVED [OK]
- GenProbe16_F [present] truth=F demand@0xc06c cover=[0,49260)∪[82028,∞) → REFUTED [OK]
- GenProbe16_T [agree] truth=T demand@0x0 cover=[0,94239)∪[98335,∞) → SURVIVED [OK]
- GenProbe17_F [value] truth=F demand@0x32aa6 cover=[0,207526)∪[240294,∞) → REFUTED [OK]
- GenProbe17_T [present] truth=T demand@0x10e84 cover=[69252,102020) → SURVIVED [OK]
- GenProbe18_F [value] truth=F demand@0x1637c cover=[0,91004)∪[91260,∞) → REFUTED [OK]
- GenProbe18_T [present] truth=T demand@0x0 cover=[0,∞) → SURVIVED [OK]
- GenProbe19_F [agree] truth=F demand@0x297a0 cover=[0,169888)∪[173984,∞) → REFUTED [OK]
- GenProbe19_T [agree] truth=T demand@0x0 cover=[0,153539)∪[153795,∞) → SURVIVED [OK]

**gen-battery: 40/40 correct → PASS**

## statement_fuzz.py run

- `NovelResidA` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x90000 ∉ cover [0,589824)∪[589840,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidC` → **REFUTED** (v2.1 uncovered-addr rule: demand @0x100 ∉ cover [0,256)∪[512,∞)) — axioms=Classical.choice, Quot.sound, propext

## statement_fuzz.py run

- `NovelResidB` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)

## statement_fuzz.py run

- `FreshTriWin` → **UNDECIDABLE** (v2.1 found uncovered demand @0xd0 but probe did not close) — 'VsaFuzzSem.probe' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## statement_fuzz.py run

- `FreshTriWinT` → **SURVIVED** (v2.1: every demanded address is covered by the agree-constraint union — sound)
