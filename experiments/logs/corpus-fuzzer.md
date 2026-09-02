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
