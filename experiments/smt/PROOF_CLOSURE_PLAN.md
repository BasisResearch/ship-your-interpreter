# Proof Closure and Acceleration Plan

## Objective

Construct an assumption-free `RemainingWork interpRunLayout`, derive
`endToEnd_refinement`, and validate every finite SMT projection against the
actual RISC-V interpreter with independent fuzzing. Z3 remains a design and
finite-validation tool. Lean remains the proof authority.

## Sources of truth

- `Vsa/Sim/EndToEnd.lean`: final theorem and `RemainingWork` boundary.
- `Vsa/Sim/TermAssembly.lean`: 63 term-side residual fields.
- `Vsa/Sim/SegEffect.lean`: current frame and relational triple stack.
- `Vsa/Sim/ExecWhileIndexed.lean`: indexed recursive-iteration prototype.
- `experiments/smt/ReflectResiduals.lean`: emitted machine queries,
  capabilities, extensions, certificates, and declared holes.
- `scripts/houdini_summary.py`: candidate mining and Z3 validation.
- `scripts/difftest.py`: independent trace, semantic, mutation, and effect
  checks.
- `scripts/residual_coverage_ledger.py`: evidence accounting.

## SMT/fuzzer baseline before the build repair

The last recorded emission reported the following. These measurements predate
the build repair below; full SMT and fuzz campaigns have not been rerun.

- 72 of 72 finite machine instances complete at 60 reflection rounds.
- 82 summaries: 60 mined, 21 assumed contracts, and 1 explicitly opaque.
- 54 residual capability rows: 51 have a semantic projection and 3 do not.
- The three without a semantic projection are `hSIfTrue`, `hSIfFalse`, and
  `hSForStart`.
- 66 fields are still explicitly marked as lacking the full Lean proposition.
- The 63 fields of `TermResidualsBase`, plus `DivWork` and `ErrWork`, remain the
  actual end-to-end construction surface. `hCallTooMany` is tracked separately
  as an indexed error subcase.
- The certified `hSWhileRetBodyReturn` and
  `hSWhileLoopBodyReturn` effects passed five independent concrete runs.
- `EnvValid` propagation compiles through `ExecDispatchRows` with only the
  standard project axioms.
- Recursive entries derive environment validity from the reached source state.

## Completion contract

### Completed work: 2026-09-05

The full Lean source build passes for **1,332/1,332 modules**, including modules
outside the `Vsa.lean` import closure and `VsaRun.lean`. Proof closure remains
incomplete. Native executable linking was not tested.

Completed proof additions:

- `ScaffoldRows.field_hInitNone` closes the empty-initializer residual.
- `ScaffoldRows.field_hInitSome` in `rows/Field_hInitSomeClosed.lean` closes the
  present-initializer residual using the actual child's `ExecIH`. Its dispatch,
  child-entry, store-body-bound preservation, and return-ready adapters compile.
- `StoreBodiesBound.afterExecS` proves preservation across statement execution.
- `execWhileBodyEntry_of_stage` supplies the while body child entry.
- `execWhileCondCopyReady_of_exitKit_exact`,
  `execWhileCondCopy_memExtends`, and its byte-population corollary compile.
- `callErr_badClosure_impossible` proves the indexed impossible-closure case.
- `ExecInitMapObstruction.lean` proves the fixed-map injectivity restriction.

Completed interface and build repairs:

- Recursive expression entries carry populated stack/result-slot bytes,
  environment validity, exact environment addresses, and required saved-register
  presence. Unary, binary, logical, and call adapters compile against them.
- Initializer exits select extended allocation maps. Initializer and loop
  carriers retain parent store-survival and stack/code geometry. Their write
  footprint includes the stack, arena, and return slot.
- Logical tails transport result-word population through the concrete memory
  extension.
- `CalleeFrame` supplies shared call-frame facts for `strlen`, `memcpy`, and
  the string-tail proofs.
- Stale routing records, closure indices, variable-call arguments, logical-arm
  code geometry, imports, and initializer return proofs are repaired.
- `FnSflushRSuffix.lean` proves stack restoration with bit-vector identities.
- Canonical generators/templates match the repaired interfaces. Assembly
  generation includes inherited fields: 63 base fields plus divergence.
  Round-trip and inheritance tests cover the generated assembly.

Build evidence:

- Private cache: `/private/tmp/vsa-full-build.sQd0gM`.
- Manifest: `build-private-manifest.json`; per-module transcripts: `logs/`.
- The documentation cleanup rebuilt 3 modules after comment-only edits and
  reused 1,329. Proof tokens were unchanged. A read-only fingerprint check
  found zero stale or missing modules.
- The `field_hInitSome` and end-to-end axiom logs contain only `propext`,
  `Classical.choice`, and `Quot.sound`. No build log reports `sorryAx` or errors.
- All 15 tooling tests pass. Generator checks, the forbidden-proof-token scan,
  and `git diff --check` pass. The proof ELF is unchanged; no repository
  `.olean` files were generated.
- The build-and-repair campaign lasted about 3 hours 9 minutes, including
  debugging and retries. A clean full rebuild has not been timed separately.

### Remaining work

- Finish while body-resume and the concrete while residual suppliers. Reuse the
  compiled body-entry and copy-frame theorems above.
- Complete sequence/for suppliers and the other residual families below.
  Reuse both initializer suppliers.
- Close `EvalArgsStep` with preservation of the argument-loop spill slots
  `sp+24` and `sp+16`. Reuse `evalArgsLoop`. The SMT premise
  `argsLoopBoundAcrossCall` depends on this open residual; discharge its Lean
  supplier before removing the premise.
- Supply reached `EnvValid st env` in `FlCondArmDispatch`, at the
  `FlCondArmStagePre.lean` producer.
- Complete the `fprintf`/`_vfprintf_r` output contracts and their call
  composition. The `snprintf` contracts cover `_svfprintf_r`. Successful
  assert composes `value_truthy` and `value_null`.
- Complete the planned effect/certificate, helper, SMT, fuzzer, and ledger work.
- Construct `TermResidualsBase`, `DivWork`, `ErrWork`, and
  `remainingWork_closed`. None of these complete constructors was produced.
  `endToEnd_refinement` still takes `RemainingWork` as a hypothesis.
- Resolve the discipline checker findings: 28 deep positional projections,
  18 existential-count flags, 11 handwritten site-proof flags, and one manual
  step-chain volume flag.
- Rerun the full SMT, independent fuzz, coverage, provenance, mutation, and
  final axiom gates after closure.

Recompute the field census before reporting proof completion counts.

### Required gates

| Item | Required outcome | Evidence required |
|---|---|---|
| A | Every finite query is generated from the current source and has a typed capability and provenance record. | Fresh emission; 72/72 complete; provenance check passes. |
| B | Every executable semantic projection is decided soundly. | Full Z3 run; no `unknown`, timeout, vacuous success, malformed query, or assumed result reported as valid. |
| C | SMT transformations use only exact Lean certificates. | Mutation tests for query, field, span, theorem, footprint, and provenance; every mutation fails closed. |
| D | The independent fuzzer covers every claimed executable leaf. | Clean phase-3b findings; required branch, boundary, effect, and semantic mutants killed. |
| E | Every non-SMT semantic seam has a Lean theorem. | Coverage ledger contains an exact theorem leaf; no prose-only or metadata-only coverage. |
| F | All 63 `TermResidualsBase` fields are constructed. | A compiled constructor with no additional hypotheses. |
| G | `DivWork` and `ErrWork` are constructed. | Compiled constructors for the concrete layout and loaded-program index. |
| H | The concrete `RemainingWork` record is constructed. | `remainingWork_closed : RemainingWork interpRunLayout`. |
| I | The final refinement theorem is unconditional. | `endToEnd_refinement remainingWork_closed` compiles; `#print axioms` contains only `propext`, `Classical.choice`, and `Quot.sound`. |
| J | Repository hygiene is preserved. | No `sorryAx`, `axiom`, `admit`, `native_decide`, `bv_decide`, recursion-limit workaround, stale artifact, or repository-generated `.olean`. |

## Abstraction stack

Add these abstractions beside the compiled interfaces and migrate one consumer
at a time. Each change must close a named residual or remove demonstrated
duplication. Shared-interface changes follow the incremental-build rules below.

### 1. Reified segment effects

Keep `FrameEffect` as the proof-facing denotation. Add a finite,
emitter-facing `SegmentEffect` descriptor:

```lean
inductive RegFrame
  | none
  | abi
  | explicit (regs : List Register)

inductive WriteRegion
  | interval (base : AddrExpr) (bytes : Nat)
  | guarded (guard : GuardExpr) (base : AddrExpr) (bytes : Nat)

structure SegmentEffect where
  regs : RegFrame
  writes : List WriteRegion
  outputPreserved : Bool
```

Define `SegmentEffect.denote : SegmentEffect -> FrameEffect`. Prove denotation
once. Do not teach Python the meaning of theorem names.

### 2. Certified segments

Pair the reified descriptor with the actual theorem:

```lean
structure CertifiedSegment (P Q : Config -> Prop) where
  effect : SegmentEffect
  machine : FramedTriple effect.denote P Q

structure CertifiedRSegment (R : A -> B -> Prop) (a : A) (b : B)
    (P Q : Config -> Prop) where
  effect : SegmentEffect
  run : FramedRTriple effect.denote R a b P Q
```

The query emitter accepts only a `CertifiedSegment` or `CertifiedRSegment`
whose indices are the exact emitted span and residual instance. This replaces
the duplicated Python query-name allowlists.

The existing `FramedRTriple` is appropriate when both semantic indices are
already fixed. Add a stronger endpoint-indexed layer for recursive design:

```lean
structure IndexedFramedRTriple
    (effect : FrameEffect) (Sem : A -> B -> Prop)
    (Pre : A -> Config -> Prop) (Post : B -> Config -> Prop) : Prop where
  run : forall a c, Pre a c -> exists b c',
    Sem a b /\ Post b c' /\ FramedSteps effect c c'
```

Prove consequence, sequential bind with an existential semantic midpoint,
branch sum, fold, and recursive cut rules. `CertifiedRSegment` should use this
layer when the result state, value, or status is selected by the machine run.

### 3. Effect composition

Give `SegmentEffect` a normalized `comp` whose denotation is
`FrameEffect.comp`. Lift it through `FramedSteps.comp`, `FramedTriple.seq`, and
`FramedRTriple.seq`.

Normalization should:

- intersect preserved-register masks;
- union and coalesce write regions;
- retain output preservation only when both components preserve output;
- preserve guards rather than widening guarded writes to arbitrary memory.

This makes a compound call, loop iteration, or epilogue export one certificate
instead of restating every frame fact.

Also add `EffectLe`, weakening, and branch join. A branch certificate preserves
only observations preserved by every reachable branch.

`FramedTriple` witnesses its postcondition and frame at the same endpoint.
Add a stability predicate:

```lean
def StableUnder (effect : FrameEffect) (P : Config -> Prop) : Prop :=
  forall c0 c1, P c0 -> FrameGuarantee effect c0 c1 -> P c1
```

Prove stability weakening and composition. Add reusable stability theorems for
loaded code, `StoreRepr`, `StoreInvariant`, AST/value representations,
`EnvValid`, phi extensions, stack/arena disjointness, spill slots, and output.
Then `FramedTriple.carry` consumes `StableUnder` directly instead of requiring
each caller to rebuild an anonymous proof.

### 4. Representation deltas

Factor the facts repeatedly threaded through recursive children into one
record:

```lean
structure ReprDelta (st0 st1 : SpecSt) (env : Addr)
    (phiF0 phiF1 phiC0 phiC1 : Addr -> Nat) where
  storeLe : StoreLe st0.store st1.store
  envValid : EnvValid st1 env
  frames : PhiExtends phiF0 phiF1 st0.store.frames.size
  closures : PhiExtends phiC0 phiC1 st0.store.closures.size
```

Add constructors from `EvalE`, `ExecS`, `ExecSeq`, `ForCond`, and `ExecStep`.
Add `refl`, `mono`, and `trans`. Carry `OutRepr` separately because output may
change while the store relation remains stable.

This record should replace repeated independent proofs of store monotonicity,
environment validity, and map extension.

Where full entry and exit predicates still repeat, add a `WorldRepr` carrier
containing `StoreRepr`, `OutRepr`, environment validity, allocation maps, and
the relevant heap/value representation. Keep adapters to the existing entry
structures. Do not rewrite every predicate at once.

### 5. Recursive child boundaries

Introduce one indexed child-boundary combinator. It couples:

- the source derivation;
- its induction hypothesis;
- the entry triple;
- the widened exit;
- its `ReprDelta`;
- its frame certificate.

Instantiate it for `EvalIH`, `ExecIH`, `ExecSeqIH`, `ForLoopIH`, and call-body
IHs. Do not erase status, result value, post-state, or selected phi maps into an
unrelated existential package.

### 6. Status-indexed recursive steps

Use `ExecWhileStepGeomI` as the first concrete instance. Once while compiles,
extract a generic `RecursiveStepGeom` with two exits:

- continuing status: `.normal` or `.cont`, producing a recursive-ready state;
- terminal status: `.brk` or `.ret`, producing a final exit.

Instantiate it for:

- while iteration;
- for condition/body/step iteration;
- sequence head/tail iteration;
- block execution over an allocated inner frame.

This should collapse `hSWhileBreak`, `hSWhileRet`, `hSWhileLoop`,
`hFlCondFalse`, `hFlBodyBreak`, `hFlBodyRet`, `hFlLoop`, and `hSeqSteps` into
instances of one composition argument.

### 7. Calls and allocation

Define a `CallPipeline` over certified relational segments:

```text
callee evaluation -> argument fold -> dispatch -> native/closure call
-> result marshalling -> common epilogue
```

Use a common `AllocationBridge` for:

- `Store.allocFrame` / `env_new`;
- `Store.allocClosure` / `malloc` plus closure header;
- phi-map extension and freshness;
- memory footprint and representation survival.

Use this stack for `hCall`, `hCallClosure`, `hFn`, `hSBlock`, and
`hSForStart`. `emptyValueNullRunFramed` is already a useful compound example.

### 8. Output deltas

Represent output changes as a compositional suffix relation:

```lean
structure OutputDelta (before after : Array String) (text : String) : Prop
```

Provide identity, append, and composition lemmas. Connect it once to
`OutRepr`. Use the same relation for `print`, `println`, `fputc`, and the native
output loops. This removes repeated array/string-join arguments.

### 9. Helper-to-Lean relations

Every helper gets one three-part contract:

- an executable finite relation used by SMT;
- an independent Python oracle used by the fuzzer;
- a Lean theorem connecting the relation to the semantic operation.

Required families include environment lookup/update, value equality,
truthiness, string comparison, string concatenation, frame allocation, closure
allocation, value boxing, and output append. A helper relation without the Lean
bridge remains a projection, not a closed residual.

## SMT acceleration

### Typed contract export

Emit a normalized contract record from Lean for each query:

```text
query identity
exact span and stop policy
precondition atoms
semantic relation atoms
segment effect
summary dependencies
Lean theorem witness
source provenance hashes
```

The consumer rejects missing, duplicated, stale, or mismatched records.

### Effect-aware rewriting

Before backward slicing:

- replace a certified preserved exit register with its entry value;
- replace a certified preserved output with its entry output;
- replace an exit memory read with the entry read only when its address is
  proved outside every write region under the current guard;
- discharge a pure frame conjunct directly from its Lean certificate.

Then run the existing post-specific dependency slicer. Never erase an input
merely because it is preserved. A same-run frame is not a cross-run
noninterference theorem.

### Projected summary signatures

Replace unconstrained `MState -> MState` summaries with signatures containing
only the observations live in the current post and certified effect:

```text
selected registers
selected memory bytes or regions
output delta
status/result shadow
store/environment shadow
```

Recursive summaries should expose an assume-guarantee boundary matching the
typed Lean IH. Do not unroll recursion indefinitely and do not treat an opaque
summary as a semantic bridge.

Parse SMT terms before semantic rewriting. Regex remains acceptable for
syntactic dependency discovery, but not for transformations justified by a
Lean effect theorem.

### Candidate mining

Generate candidates from the contract:

- frame equalities are proved facts, not Houdini candidates;
- mutable registers receive arithmetic and tag templates;
- write regions receive boundary, length, and preservation templates;
- `ReprDelta` supplies store-size, environment-validity, and phi-extension
  templates;
- recursive steps supply status partition and progress templates;
- helper contracts supply relation-specific templates.

Retain the agentic Daikon/Ivy loop: generate, refute, explain the model, refine
the candidate family, and rerun Houdini. Persist counterexamples by normalized
contract hash.

### Solver operation

- Canonicalize by span, stop policy, live projection, and certificate hash.
- Share mined summaries between residuals with the same canonical machine cut.
- Use one Z3 process with `push`/`pop` for conjuncts and candidates.
- Cache only `sat` and `unsat` under the exact source and contract hash.
- Treat every `unknown`, timeout, parser error, and inconsistent premise set as
  a failed gate.
- Record query size, live symbols, summary count, solve time, and unsat-core
  size to identify regressions.

## Fuzzer acceleration and strengthening

The fuzzer may use the emitted contract to choose tests. It must not use that
contract to compute the expected semantic answer.

### Three independent comparisons

For each executable leaf, compare:

1. the actual ELF trace;
2. the reflected SMT transition;
3. an independent Python semantic oracle.

Require exact agreement for every observation claimed by the contract.

### Effect-directed checks

- Compare every preserved register at entry and exit.
- Compare output when preservation is claimed.
- Sample memory immediately below, inside, and above each write region.
- Check every emitted direct write address and final byte.
- Validate composed effects against concatenated component traces.
- Mutate each protected observation and require the validator to reject it.

Effect frames authorize same-run comparisons only. They do not authorize
changing an entry value and expecting unrelated outputs to remain unchanged.

### Semantic and recursive checks

- Generate valid stores and environments, including parent chains, shadowed
  names, misses, updates, and append-only allocation.
- Segment traces at recursive call/return and loop re-entry points.
- Check each child boundary, status route, and `ReprDelta` independently.
- Generate zero, one, and multiple sequence/loop iterations.
- Exercise `.normal`, `.cont`, `.brk`, and `.ret` routes.
- Exercise empty and nonempty argument/parameter lists.
- Compare output prefixes and suffixes after every helper call.

### Coverage ledger

Make the ledger total over the actual completion surface. Add explicit
capability classes for Lean-only, composite-family, and non-finite obligations
instead of requiring scoped runs to hide the current 66-versus-54 inventory
mismatch.

For each field and semantic dimension, record separate leaves:

- machine execution covered;
- SMT projection valid;
- independent oracle covered;
- mutations killed;
- Lean bridge compiled;
- full residual theorem compiled.

No leaf may be inferred from another.

## Remaining proof families

`TermResidualsBase` currently has 63 fields:

| Family | Fields | Closure strategy |
|---|---:|---|
| Dispatch, leaves, logical, var/assign, binary/string | 31 | Use certified row combinators, helper relations, and common result marshalling. |
| Args/call/native/fn/closure | 7 | Use `CallPipeline`, `AllocationBridge`, output deltas, and recursive child boundaries. |
| Simple exec/status cases | 7 | Use one status/result epilogue abstraction. |
| If/block/for-start/while cases | 9 | Use recursive child boundaries and status-indexed step composition. |
| Init/for-loop/sequence boundaries | 7 | Instantiate `RecursiveStepGeom`; retain exact semantic indices. |
| Interpreter entry and epilogue | 2 | Prove the actual initial-store representation and exact interpreter restore chain. |

Then close:

- `DivWork`: reflected loop head, entry drive, iteration seam, and 29-arm
  approximate dispatch assembly.
- `ErrWork`: indexed loaded-program input, shared runtime-error tail, executable
  leaves, the spec-only bad-closure adequacy case, and top-abrupt path.
- `hCallTooMany`: the indexed error child boundary and signed count bridge.

`mExecInit` and `mForLoop` are now indexed semantic contexts. `mForCond` and
`mExecStep` remain trivial contexts, so their machine geometry must still be
provided explicitly. The sequence family has three indexed copies:
interpreter, closure body, and block body.

`hCallClosure` already has substantial geometric machinery in
`CallClosureRow` and `CallClosureSplice`. Replace the opaque whole-premise slot
with the geometric residual, then finish its stage providers.

## Proof-closing order

1. Reuse `execWhileBodyEntry_of_stage` and finish body-resume construction.
   Derive validity only at reached seams from `hCarrier.env_valid.afterEvalE hC` and
   `hBodyCarrier.env_valid.afterExecS hB`.
2. Compile `WhileExitCaseGeom` and `WhileLoopCaseGeom` suppliers.
3. Extract `ReprDelta` and `RecursiveStepGeom` from the compiled while proof.
4. Reuse them for `hSeqSteps` and the remaining for-loop fields. Use the compiled
   `field_hInitNone` and `field_hInitSome` for the initializer cases.
5. Land `AllocationBridge`; close block, for-start, function allocation, and
   closure allocation.
6. Land helper relations and `CallPipeline`; close var, assign, args, calls,
   closure calls, native calls, and output cases.
7. Close the leaf/logical/binary/string provider record using the existing rows
   and shared epilogues.
8. Close `hExecRouteCases`, `hInitStore`, and `hEpilogueSpill`.
9. Construct `DivWork` and `ErrWork` from their indexed supplier records.
10. Construct `remainingWork_closed` and derive `endToEnd_refinement`.
11. Run the full Lean, Z3, fuzzer, coverage, provenance, mutation, and hygiene
    gates against frozen current-source fingerprints. Reuse matching Lean
    objects; emit fresh SMT/fuzzer evidence for this snapshot.

## Mandatory incremental-build rules

1. Extend compiled proofs by default. Reuse existing theorems and add adapters
   or leaf suppliers. Do not rewrite shared interfaces for convenience.
2. Before a shared-interface change, record the blocked residual, concrete
   failure or obstruction, why an adapter is insufficient, and the affected
   import dependents. The integrator approves and owns the migration. Changes
   to the final statement or assumptions require explicit user approval.
3. Preserve `/private/tmp/vsa-full-build.sQd0gM` and its manifest across tasks
   and workers. All integration builds use `--resume` with this root. Never
   discard a valid cache or omit `--resume` to resolve an ordinary proof error.
4. In the proof-edit loop, compile the changed file against fingerprint-checked
   dependencies, with private objects first in `LEAN_PATH`. Refresh changed
   dependencies first. Keep speculative outputs separate from the validated
   cache. Documentation-only changes require no Lean compilation.
5. At a completed residual, shared-interface migration, or wave checkpoint,
   run the resumed all-source gate. It recompiles changed modules and their
   transitive import dependents; matching modules must be skipped. Run one
   compiler at a time. Do not use the all-source gate after every tactic edit.
6. Before any unexpectedly broad rebuild, inspect invalidation inputs. The
   driver fingerprints itself, `lakefile.toml`, `lake-manifest.json`, and
   `lean-toolchain`; changing any invalidates every module. Avoid incidental
   edits to these files during proof work. Never bypass a genuine mismatch.
7. A cold full rebuild requires a recorded reason: missing/corrupt cache,
   changed toolchain/build configuration, or an explicitly requested clean
   audit. Obtain user approval for a discretionary cold audit. A routine
   checkpoint or final closure audit uses matching cached objects.
8. Record the command, source/dependency fingerprints, built/skipped counts,
   exit status, log location, and wall time at each integration checkpoint.
   Separate compiler timing from debugging/retries. Report compiled modules
   separately from closed residuals. A failed gate reopens its affected scope.

Integration command, from the repository root:

```sh
python3 scripts/build_private.py \
  --output-root /private/tmp/vsa-full-build.sQd0gM \
  --include-executable --resume
```

The driver enforces source/dependency cache matching. The integrator enforces
the change-scope and checkpoint rules; workers must report any exception before
starting a build. If the private cache is lost, record that fact and create one
replacement root with `mktemp -d`, then retain it for subsequent resumes.

## Parallel execution

Use at most three workers plus the integrator. Permit only one Lean compiler or
full Z3/fuzzer campaign at a time. Assign files, not themes, so workers do not
edit the same module. The integrator owns shared interfaces and serialized
builds under the incremental-build rules above. Workers receive the stable
interface signatures and cache location with their file assignments. They must
request shared-interface changes and compiler access from the integrator.

### Wave 1: infrastructure and current critical path

- Integrator: reuse the compiled body entry, finish while body-resume, and
  serialise the incremental Lean gate.
- Worker A: add `SegmentEffect`, effect denotation, `EffectLe`, composition,
  branch join, and stability lemmas.
- Worker B: add typed certificate types and emission; migrate existing framed
  while/call examples.
- Worker C: add typed contract parsing, effect-aware SMT rewriting, fuzzer
  certificate mutations, and total ledger classes.

Gate: compiled certificate examples; fail-closed selfchecks; fresh route fuzz;
no duplicated query-name allowlist needed for migrated cases.

### Wave 2: semantic bridge families

- Integrator: extract `ReprDelta` and `RecursiveStepGeom`; close while and own
  the shared interfaces.
- Worker A: store/environment/frame/closure allocation bridges.
- Worker B: call/output/helper relations and independent oracles.
- Worker C: sequence/for suppliers and their focused SMT/fuzzer coverage.

Gate: focused Lean builds; focused Z3 projections; focused phase-3b mutation
coverage for every migrated family.

### Wave 3: residual providers

- Integrator: structured control and final provider assembly.
- Worker A: leaf/logical/arithmetic/string providers.
- Worker B: entry, divergence, and indexed error providers.
- Worker C: args/call/native/function/closure providers after the shared call
  interfaces land.

Gate: every `TermResidualsBase` field has a compiled supplier; `DivWork` and
`ErrWork` compile; the ledger contains no unowned field.

### Wave 4: final audit

The integrator alone freezes source hashes and runs:

1. serialised resumed Lean compilation into the retained private cache, with
   source/dependency fingerprints checked for every reused object;
2. fresh 72-query emission;
3. full Houdini/Z3 validation;
4. full independent differential fuzzing;
5. total residual coverage ledger;
6. `#print axioms` for the closed end-to-end theorem;
7. repository artifact and diff hygiene checks.

Any failure reopens its exact field. Broad green signals do not close unrelated
items.

## Non-goals

- Proving recursive Lean semantics solely in quantifier-free SMT.
- Treating traces as proofs.
- Treating an SMT projection as the full Lean residual.
- Accepting `unknown` as evidence.
- Exporting arbitrary theorem-name strings as certificates.
- Increasing recursion limits or adding trust-expanding proof shortcuts.

## Immediate next actions

1. Reuse `execWhileBodyEntry_of_stage` and the copy-frame theorems. Build
   `bodyResume` from the existing break, return, and loop framed routes.
2. Package the three while residual suppliers and run the resumed Lean gate.
3. Reconcile the field census with both compiled initializer suppliers. Assign
   only still-open sequence/for obligations.
4. Introduce the reified `SegmentEffect`/certificate layer around the proved
   routes.
5. Make the SMT checker consume the certificate for sound post rewriting and
   make the fuzzer mutation-test the same certificate independently.
