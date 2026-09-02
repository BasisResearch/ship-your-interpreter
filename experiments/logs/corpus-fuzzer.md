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
