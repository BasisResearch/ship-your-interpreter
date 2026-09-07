# Proof closure plan

Prove `remainingWork_closed : RemainingWork interpRunLayout`, then discharge
the `RemainingWork` hypothesis of `endToEnd_refinement`.

## Status

**27 of 63 base fields certified; 36 remain.** `DivWork`, `ErrWork`, and the
final constructor remain open. The certified fields cover literals, unary and
logical operations, nine integer cells, break/continue, both initializers,
and all four while cases. Their shared entry and ownership suppliers still
need integration.

The last completed checkpoint passed 1,538 modules, 449 declaration axiom
audits, four boundary regressions, 200 Python tests, and six static/generator
checks. There are 56 inherited discipline findings. Receipt:
`/private/tmp/vsa-return-abstractions/receipt.json`.

Indexed child returns and the shared coherent epilogue now pass the full
1,539-module build and cache-fingerprint verification. Log:
`/private/tmp/vsa-indexed-child/integration.log`. The remaining axiom/boundary
checkpoint, full supplier search, and SMT/fuzzer campaigns are pending.
Recompute the census before changing the certified count.

## Remaining tasks, in dependency order

### 1. Finish recursive return and ownership contracts

- Migrate `TermSimAssembly.mEvalE` and the execution, sequence, and call
  producers to coherent returns. Wire `ReturnRepr.bind` into binary recursion
  so results, store representation, and ownership use one selected map pair.
- Supply `PreEpilogueOwned` at each actual producer endpoint. Fresh closures
  must retain their allocation map through `blockD_v_return`.
  `EqualityReturnMapObstruction` and `CoherentReturnObstruction` establish
  why independent witnesses and entry-prefix bounds cannot supply this.
- Replace legacy `EvalGround.ast`, `ExecGround.ast`, and `SeqArrayReadSafe`
  region assumptions with exact `ExprReprWithin`/`StmtReprWithin` coverage,
  indexed arrays, and `AstReadGeometry`. Keep the fixed AST domain inside the
  evolving `SharedReadDomain`; preserve its bytes through actual effects.
- Propagate `StoreArraysReady`, source store invariants, body/stack bounds,
  and distinct addresses for the three native functions through entries.
- Replace `VarCallLinkage.payloadDisj` and its unpinned `LeafWiden` premise
  with facts about the actual returned value and memory.

Reuse the implemented separation rules, `StableUnder`, `ReprDelta`,
`OutputDelta`, `CertifiedSegment`, and `RecursiveStepGeom` throughout.

### 2. Complete allocation and resource suppliers

- Relate the ownership ledger to concrete allocator state. Prove preservation
  through malloc, free, reuse, and realloc, including indirect bin-link writes
  and live allocation extents. Resolve the fixed `MallocContract.privFoot`
  assumption against those actual writes.
- Supply `env_new` from the actual allocation result and the existing
  `envNewSuccess_run`/`.frameRepr` suffix. Its universal geometry and
  nonexhaustion premises have checked obstructions; they need reached facts.
- Finish `HeapOwned.pushClosure` at post-build memory. Use `prune_of_exit`
  for full extent freshness and `fnArmClosureBuild_reads` for the header;
  retain old ownership, captured-environment validity, and shared AST coverage.
- Check `AllocBuildEntry.hOld` and `AllocBuildTailFacts.hOld`, which demand
  store survival under arbitrary arena changes. Replace that demand with
  preservation under the actual build writes. The obstruction and ownership
  drafts in `/private/tmp/vsa-indexed-child/` are unchecked.
- Complete copied-name, append/grow, frame, and closure allocation suppliers.
- Derive initial stack/body bounds and allocator capacity from a source
  resource bound over every finite execution prefix. Account for physical
  chunk overhead and fragmentation: a 32-byte request occupies 48 bytes.
  Connect the bound to `Loaded` and concrete allocator state.

### 3. Close sequence and for-loop recursion

- Close `hSeqSteps` for interpreter, closure-body, and block-body copies.
  Thread reached dispatch/resume carriers and whole-suffix invariants through
  empty, final, and continuing routes. Reuse `SeqSuffixGround` and the compiled
  closure return, normal-exit, and continuation lemmas.
- At closure child entry, derive `Exec_stmt` code, register presence
  (`x9`, `x20`, `x21`), header/array reads, and arena/stack geometry.
- Retain environment validity and machine geometry in `FEntryC`, `mForCond`,
  and `mExecStep`. `FlCondArmDispatchObstruction` refutes dispatch from the
  erased environment premise.
- Complete false-condition, body break/return, normal/continue, step, and
  next-iteration for-loop routes. Reuse the certified initializer and while
  suppliers after shared-contract integration.

### 4. Close the remaining terminating cases

| Family | Remaining work |
|---|---|
| Expressions | Variable lookup, assignment, constructor dispatch, equality/inequality, six string cells, and `hDivOv`. Equality needs coherent operand maps, allocated bounds, payload coverage, and native identity. |
| Arguments | Empty/nonempty loop assembly and `EvalArgsStep`; preserve spill slots `sp+24` and `sp+16`. Discharge the Lean supplier before removing SMT premise `argsLoopBoundAcrossCall`. |
| Calls and functions | `hCall`, `hCallClosure`, `hFn`; parameter bindings, depth bounds, allocation, and result marshalling. Complete the existing `CallClosureRow`/`CallClosureSplice` stage providers. |
| Native/output | Print, println, successful assert, `fprintf`/`_vfprintf_r`, `__swbuf_r`, `_putc_r`, and enclosing fputc folds. Preserve stdout/errno/HTIF state and output suffixes; reuse existing flush/write frames. |
| Statements | Expression statements, value/null returns, declarations, if branches, block allocation, for-start, and `hExecRouteCases`. |
| Entry/exit | `hInitStore`: extend the owned initial execution to the full loop entry. `hEpilogueSpill`: retain code, saved slots, and runtime state through the reached sequence exit. The universal exit widener is refuted in `/private/tmp/vsa-epilogue-audit/EpilogueSpillObstruction.lean`. |

### 5. Close divergence, errors, and final assembly

- Construct `DivWork`: loop-head representation, `Loaded` entry drive,
  iteration/re-entry, and the 29-arm approximate recursive dispatch.
- Construct `ErrWork`: loaded-program-indexed leaves, recursive error
  propagation, formatted error/exit tail, and top-level abrupt completion.
  Complete auxiliary `hCallTooMany` with its indexed child and signed count
  bridge; reuse the bad-closure impossibility proof.
- Construct all 63 `TermResidualsBase` fields, then `RemainingWork`, then the
  final refinement theorem. Remove the 56 inherited discipline findings.

## Validation and automation still to finish

- Export typed Lean authority for each query, field, span, stop, semantic
  relation, effect, dependency, and source hash. Replace duplicated Python
  allowlists for migrated contracts. Reject missing, duplicate, stale, or
  mismatched certificates.
- Connect certified effects to SMT rewriting and post-dependent slicing.
  Parse terms before rewriting. Retain preserved inputs as dependencies;
  memory framing alone does not establish noninterference between executions.
- Project summaries onto live registers, memory, output, status, store, and
  environment. Match recursive summaries to the typed induction hypotheses.
- Finish contract-driven Houdini mining, shared summaries, incremental Z3,
  and exact-fingerprint result caching. Require convergence before validation;
  report query sizes, symbols, solve times, and unsat cores.
- For each helper family, connect a finite SMT relation, independent Python
  oracle, and Lean semantic bridge. Cover environment operations, equality,
  truthiness, strings, allocation, boxing, and output.
- Compare actual ELF/Sail traces, SMT reflection, and the independent oracle.
  Check claimed register, memory-footprint, and output effects, including
  composition. Cover zero/one/many iterations, every status, argument and
  parameter boundaries, shadowing/update/miss, parent chains, and output
  prefixes/suffixes. Kill branch, boundary, effect, and semantic mutants.
- Complete the coverage ledger for 63 base fields, `DivWork`, `ErrWork`, and
  `hCallTooMany`. Record execution, SMT, oracle, mutation, Lean-bridge, and
  full-residual evidence independently, with explicit finite/composite/
  Lean-only/nonfinite capabilities.
- Rerun the full supplier search at exact inherited types and the complete
  library census. Preserve all four initial-boundary regression cases.

## Completion gates

Run against one frozen source snapshot. Partial checks do not close these gates.

| Gate | Required evidence |
|---|---|
| A — Emission | Fresh, complete emission of all 72 finite queries with typed capabilities and provenance. |
| B — SMT | Every executable semantic projection decided; no unknown, timeout, malformed query, inconsistent premise, or assumed validity. |
| C — Certificates | Query, field, span, theorem, footprint, and provenance mutations all rejected. |
| D — Fuzzing | Every claimed executable leaf covered; clean findings and all required mutants killed. |
| E — Semantic seams | Exact Lean theorem coverage for every non-SMT seam. |
| F — Termination | Compiled, hypothesis-free constructor for all 63 base fields. |
| G — Divergence/errors | Compiled `DivWork` and `ErrWork` for the concrete layout and loaded-program index. |
| H — Assembly | `remainingWork_closed : RemainingWork interpRunLayout`. |
| I — Refinement | `endToEnd_refinement remainingWork_closed` compiles; axioms limited to `propext`, `Classical.choice`, and `Quot.sound`. |
| J — Hygiene | Discipline and generator checks pass; unchanged ELF; no admitted proofs, extra axioms, `native_decide`, `bv_decide`, raised limits, stale objects, or repository-generated `.olean` files. |

## Execution rules

Follow [CLAUDE.md](../../CLAUDE.md) for proof discipline and
[TOOLING.md](../../TOOLING.md) for commands. Run the abstraction inventory
before proof work. Record each new contract gap beside its task, with the
affected declaration, missing supplier, obstruction evidence, and import
dependents. Update this plan in place; keep build transcripts in receipts.

Use one compiler or full solver/fuzzer campaign at a time. Preserve the private
cache `/private/tmp/vsa-full-build.sQd0gM` and resume it with `--resume`.
Check changed dependencies before consumers; run the all-source gate at a
completed residual or shared-interface checkpoint. Record fingerprints,
built/reused counts, exit status, log, and timing. Documentation edits need
no Lean rebuild.
