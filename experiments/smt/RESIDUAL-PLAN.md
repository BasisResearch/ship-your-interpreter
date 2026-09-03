# Closing the 52 residuals

Every residual is a Hoare triple `∀ c, Pre c → ∃ c', Steps c c' ∧ Post c'`, and the whole thing turns on `Steps`, the machine step relation buried inside it. So the plan is one pipeline over all 52. Reflect `Steps` to exact SMT, encode `Pre`/`Post` over the reflected state, fuzz for falsity before spending a proving session, and mine the loop invariants with autoprove.

## Where we are

The reflection engine is done. `ReflectSpan.lean` reflects `Steps` exactly over an `MState` datatype of memory plus registers, with no approximation left anywhere. Every instruction models exactly, immediates read off the full word, shifts go through the bitvector theory, `lui`/`auipc` corrected. Branches become `ite`, calls and loops become `MState → MState` summaries built from their own body reflection, and loops land as `define-fun-rec`. The `let`-shared DAG is what makes this usable. A seq-loop span that blew up to 1.3 GB as a duplicated tree shrinks to 86 KB once the states are shared.

Encodability is done too. `ReflectResiduals.lean` maps all 52 residuals to their spans, and every one reflects gap-free and DAG-sized. No residual carries an `ENCODE-GAP`.

The splice runs, on the frame conjunct. `#splice_all` builds `Pre(s0) ∧ ¬Post(state_exit)` per residual over the shared `MState`, and Z3 comes back 14 VALID, 38 UNKNOWN, 0 REFUTED. The 14 are the straight-line and call spans. The 38 unknowns are all loop-bearing, waiting on their invariant, and nothing refutes.

Three things remain. The fuller `Post` conjuncts, `ValueRepr`/`StoreRepr` survival, which splice through the same machinery with more conjuncts. The loop invariants that turn the 38 unknowns green. And the B2-carry amendment for the 11 int/eq residuals, which are refuted as stated (`RefutBatteryCur.lean`) until they carry `EvalEntry`.

## Non-straight-line spans

The 1.3 GB blowup taught us how control flow has to be reflected. A branch inlined its continuation into both arms and every callee inlined its body into an axiom, so a branchy loop span doubled at every fork. Two changes make it linear.

*Join-point merging.* A forward branch reconverges at its post-dominator. Reflect each arm only as far as that join, bind the two states to a `let`, and continue once from an `ite` over them. Term size then tracks the block count, not the branch depth.

*Summary sharing.* Reflect each callee and loop once into a named `define-fun`/`define-fun-rec` and reference it by application. The path reflector emits `(callee_t S)` at the call site, never the body, and the axiom is memoised, so a callee shared by ten sites reflects once.

*Loops.* `loop_t(S) = ite(loopcond_t S, S, loop_t (body S))` is the exact recursive effect. Z3 decides it with the loop invariant as the recursion's lemma, which is the mining step below, not an encoding gap.

## The pipeline, per residual

1. Read the span from the ground table (`seqLoopImage` and its per-class analogues).
2. `#reflect_exact` the span to `state_exit`.
3. Encode `Pre`/`Post` over `s0` and `state_exit`, structure-expanding the named-field predicates with `ValueRepr`/`StoreRepr`/`CString` as `define-fun-rec`.
4. Fuzz the statement first. A SAT countermodel is a false spec, amended before proving.
5. For loops, mine: `gen_trace` → `mine` → Houdini-select the invariant that closes the recursion, with the fuzzer guarding each clause.
6. Z3 on `Pre ∧ ¬Post`. UNSAT is valid.
7. Any refutation feeds back a spec amendment and a re-census.

## The 52, by class

*int/eq, 11, refuted, amend first.* `hIAdd … hNe`. Refuted at `m0:=∅`: the `∃`-body wants `KindSlotPinned 6`, absent from `∅`. Carry `EvalEntry` (the B2-carry, `evalEntry_supplies_slot6`), then the span is the binary arm through the `value_*` call. Reflect, validate. No loop.

*unary/logic, 6, entry-guarded.* `hNeg hNot hAnd* hOr*`. Already carry `EvalEntry`. The arm runs through `jal value_bool`. Reflect, validate; the fuzzer confirms they are not false.

*call/composition, 10.* `hCall hCallClosure hArgs* hSeqCons* hSeqNil hCallPrint*`. Call-splice spans on the recursive `eval_expr`/`exec_stmt` seam. `hArgsNil`/`hSeqNil` are `segIdentity`, trivial. The print ones reach the native `value_print` DAG, so reflect the callee once and validate.

*statement arms, 14.* `hSExpr hSBlock hSIf* hSRet* hSVar* hSWhile* hSForStart hAssign hVar`. Branches and loops. `hSIf*` are branches into a join. `hSExpr`/`hSBlock`/`hSeq` carry the statement loop (`seqLoopImage`), `hSWhile*`/`hSForStart` the control-loop heads. This is where the invariant mining lives.

*str, 6.* `hStrAdd* hStr{Ge,Gt,Le,Lt}`. The arm reflects, but the spec leans on a genuine `String.lt`/`Value.display` bridge (`StrCmpOrderBridge`). Fuzz the bridge on concrete strings; the strcmp-sign arithmetic validates; the order bridge stays a named premise, not a mined invariant.

*div, 2.* `hDivOv` is the `-2^63/-1` guard, pure arithmetic. `hDivCorr` is the `__divdi3` callee, so reflect once and validate the quotient/remainder relation.

*init/frame, 3.* `hEpilogueSpill` is a straight-line frame span, already green under frame-preservation Z3. `hInitStore` is the main-init image, entry ground, no `Steps`. `hFn` is the closure-literal arm, a call-splice validating `ClosureRepr`.

## Who owns what

- `ReflectSpan` reflects `Steps` for every span, exact and gap-free.
- `DumpSmtLib` structure-expands `Pre`/`Post` over the reflected state.
- `statement_fuzz` guards falsity before proving. It caught the 11 int/eq.
- autoprove/Houdini mine the loop invariants for the statement-arm and while/for classes.

## Order

1. Land the two scaling fixes. Without them the loop classes do not encode at usable size.
2. Amend the 11 int/eq, then re-census; they flip to provable.
3. The straight-line and call classes (unary, call, div, frame): reflect and validate, no invariants.
4. The loop classes: the invariant-mining campaign.
5. The str order bridge, the one genuine non-arithmetic premise.
