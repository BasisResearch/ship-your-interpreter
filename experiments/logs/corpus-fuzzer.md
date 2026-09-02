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
