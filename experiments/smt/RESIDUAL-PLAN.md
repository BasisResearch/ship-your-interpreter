# Closing the 52 residuals with reflection + Z3 + fuzzing + mined invariants

Each residual is a Hoare triple `∀ c, Pre c → ∃ c', Steps c c' ∧ Post c'`. The
plan closes each one with the same four instruments: reflect `Steps` to exact SMT
(`ReflectSpan`), encode `Pre`/`Post` over the reflected state, fuzz the statement
for falsity before proving, and — for loops — mine the invariant with
autoprove/Houdini. Anything the fuzzer or Z3 refutes is a spec bug, amended
before it wastes a proving session.

## Non-straight-line spans: the two fixes the 1.3GB blowup forced

`reflectExact` is exact but duplicates work on control flow. A seq-loop span blew
up to 1.3 GB because every branch inlines its continuation into both arms and
every callee/loop body is inlined into its axiom. Two changes make it scale.

*Join-point merging.* A forward branch reconverges at its immediate
post-dominator. Reflect each arm only to that join PC, bind the two states to a
`let`, and continue once from an `ite` over them — not by duplicating the tail
into both arms. Term size becomes linear in the block count, not exponential in
the branch depth. The join PC is the first address both arms reach; compute it by
running the two arms' PC sets until they meet.

*Summary sharing.* Each callee/loop is reflected ONCE into a named
`define-fun`/`define-fun-rec` and referenced by application everywhere it occurs.
`emitExactAxioms` already keys on the symbol; the fix is to stop inlining the body
at each call site (the path reflector emits `(callee_t S)`, never the body) and to
memoise the axiom so a callee shared by ten sites is reflected once.

*Loops.* `loop_t(S) = ite(loopcond_t S, S, loop_t (body S))` is the exact
recursive effect (gap-free). Z3 decides it only with the loop INVARIANT as the
recursion's lemma — that is the autoprove/Houdini step below, not an encoding gap.

## The per-residual pipeline

1. **Span.** Read the residual's concrete span(s) from its ground table
   (`seqLoopImage` and the per-class analogues). Straight-line, call-splice,
   branch, or loop.
2. **Reflect.** `#reflect_exact` the span → `state_exit` (exact `MState`).
3. **Pre/Post.** Encode `SegEntry`/`SegExit` (or the arm's `Resid`) over `s0` and
   `state_exit` — structure-expand the named-field predicates (`DumpSmtLib`),
   with `ValueRepr`/`StoreRepr`/`CString` as `define-fun-rec` over the same state.
4. **Fuzz first.** Run `statement_fuzz.py` on the concrete witness bank; a SAT
   countermodel is a FALSE statement → amend before proving.
5. **Mine (loops only).** `gen_trace` → `segment` → `mine`/`mine_relational` →
   Houdini-select the invariant that closes the `loop_t` recursion; the fuzzer
   guards each clause against falsity; emit it as the `loopcond_t`/`loop_t` lemma.
6. **Validate.** Z3 on `Pre(s0) ∧ ¬Post(state_exit)`; UNSAT ⇒ valid.
7. **Amend.** Any refutation (fuzz or Z3) → update the spec, re-census.

## The 52 by class

**int/eq — 11, REFUTED, need a spec amendment first**
`hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe`.
Machine-refuted at `m0:=∅` (`RefutBatteryCur.lean`): the `∃`-body demands
`KindSlotPinned 6` absent from `∅`. Amend `BinIntCellResid`/`BinEqCellResid` to
carry `EvalEntry` (the B2-carry, validated by `evalEntry_supplies_slot6`), then
the span is the binary arm ≫ `value_*` call — reflect (call-splice), Z3-validate.
No loop; no invariant.

**unary/logic — 6, entry-guarded (not false)**
`hNeg hNot hAndTrue hAndFalse hOrTrue hOrFalse`. Already carry `EvalEntry`. Span
= the unary/logical arm (`hNeg` through `jal value_bool`). Reflect (call-splice),
Z3-validate. Fuzz confirms non-falsity.

**call/composition — 10**
`hCall hCallClosure hArgsCons hArgsNil hSeqConsNormal hSeqConsAbrupt hSeqNil
hCallPrint hCallPrintln hCallAssertOk`. Call-splice spans (the recursive
`eval_expr`/`exec_stmt` seam). `hArgsNil`/`hSeqNil` are `segIdentity` (empty
span, trivial). `hCallPrint*` reach the native `value_print` DAG — reflect the
callee summary once (shared), Z3-validate. No loops.

**statement arms — 14**
`hSExpr hSBlock hSIfTrue hSIfFalse hSIfNone hSRet hSRetNull hSVarInit hSVarNull
hSWhileBreak hSWhileFalse hSForStart hAssign hVar`. Branch/loop spans. `hSIf*` are
branches → join-point `ite`. `hSExpr`/`hSBlock`/`hSeq` carry the statement LOOP
(`seqLoopImage`) → `loop_t` define-fun-rec + MINED INVARIANT (the loop preserves
`StoreRepr` and advances the statement list). `hSWhile*`/`hSForStart` are the
control-loop heads → invariant on the loop counter + store. This class is the
main invariant-mining work.

**str — 6**
`hStrAddL hStrAddR hStrGe hStrGt hStrLe hStrLt`. Reflect the arm, but the spec
carries a genuine `String.lt`/`Value.display` bridge (`StrCmpOrderBridge`). Fuzz
the bridge on concrete strings; the arithmetic (strcmp sign) Z3-validates; the
order bridge is a named premise (no Mathlib), not a mined invariant.

**div — 2**
`hDivCorr hDivOv`. `hDivOv` is the `-2^63/-1` overflow guard — pure arithmetic,
Z3-validate directly. `hDivCorr` is the `__divdi3` callee summary — reflect once,
validate the quotient/remainder relation.

**init/frame — 3**
`hInitStore hEpilogueSpill hFn`. `hEpilogueSpill` is a straight-line frame span
(reflect + frame-preservation Z3, already demonstrated). `hInitStore` is the
main-init image (entry ground, no `Steps`). `hFn` is the closure-literal arm —
call-splice, validate `ClosureRepr`.

## What each instrument owns

- **ReflectSpan** — `Steps` for every span, exact, gap-free (with the two scaling
  fixes for branches/loops).
- **DumpSmtLib** — `Pre`/`Post` structure-expansion over the reflected state.
- **statement_fuzz** — falsity guard on every statement before proving; the 11
  int/eq were caught this way.
- **autoprove/Houdini** — the loop invariants (statement-arm + while/for class);
  Z3 certifies sufficiency, the fuzzer guards each clause, the kernel transcribes.

## Order

1. Land the two ReflectSpan scaling fixes (join points, summary sharing) — without
   them the loop classes don't encode at usable size.
2. Amend the 11 int/eq (B2-carry) — re-census, they flip to provable.
3. Straight-line/call classes (unary, call, div, frame) — reflect + Z3, no
   invariants.
4. Loop classes (statement arms, while/for) — the invariant-mining campaign.
5. str order bridge — the one genuine non-arithmetic premise.
