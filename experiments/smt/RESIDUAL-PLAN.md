# Closing the 52 residuals

Every residual is a Hoare triple `∀ c, Pre c → ∃ c', Steps c c' ∧ Post c'`, and
the whole thing turns on `Steps`, the machine step relation buried inside it. So
the plan is one pipeline over all 52. Reflect `Steps` exactly, encode `Pre`/`Post`
over the reflected state, fuzz for falsity before spending a proving session, and
mine the summary clauses that let the solver get through a call or a loop.

## Where we are

The encoder is `reflectBmc` (`ReflectSpan.lean`): bounded symbolic execution with
the **PC concrete**, a guard term per arrival, and a merge of every arrival at the
same PC in the same round. Merging is what keeps it linear — a diamond does not
double and a loop does not branch, it re-arrives at its header. A re-arrival
applies `loop_<h>` once and resumes at every exit edge of the whole natural loop,
so the post-loop code is reflected instead of dropped. Computed gotos resolve
against the three pinned AST-kind jump tables read out of the ELF; the arms they
resolve to are exactly the proof's `evalArm*`/`execArm*` constants.

**52 of 52 spans are COMPLETE** — the frontier empties inside the bound, so the
encoding is exact for the span, not merely bounded. `spans.tsv` records it per
residual, and nothing is reported VALID on a span that is not complete.

Everything is in the **bitvector theory**: 64-bit two's-complement registers and
addresses, a byte array indexed by a 64-bit address. Arithmetic wraps, as RV64
does. The `Int`-plus-`int2bv`/`bv2int` encoding it replaced both dropped
wraparound and modelled `addiw`/`addw`/`subw`/`*w` as their 64-bit siblings.

Exactly **two opaque symbols** survive: the indirect calls through a register at
`0x800039f4` and `0x80004784`, the native function pointers. They are in
`bmc/opaque.tsv`, and the driver EMPTIES their clause sets rather than assuming
them — an assumed-but-unproved clause is an axiom smuggled into every query that
mentions it. **Thirty summaries are assumed contracts** (`bmc/assumed-final.tsv`):
the `eval_expr`/`exec_stmt` recursion, which the residual carries as the
recursor's `EvalIH`/`mExecSeq` hypotheses, and the callees outside the
interpreter's own code (`value_*`, `strcmp`, `malloc`, …), which the Lean
development also does not re-derive — they are landed `TermCallees` specs or
named open premises.

## What the earlier reflector was actually reporting

The previous encoder classified a terminator by direction before `rd`, treated
every `jalr` as a return, and cut a back-edge by ending the path. Each defect
silently produced a verdict about something other than the residual's span.

* A backward `jal ra` is a CALL, not a loop back-edge. The two
  `jal ra, 0x80003164` inside the EX_BINARY arm made 38 spans reflect as one
  bogus `define-fun-rec`, which is the entire reason the loop classes came back
  UNKNOWN.
* `jalr x0, 0(rN)` for `rN ≠ ra` is a computed goto. The statement-arm spans
  ended seven instructions in, at `exec_stmt`'s dispatch header; their "VALID"
  frame verdicts were verdicts about that stub. `findRet` stopped a callee at the
  same place.
* Whatever followed a loop was dropped.
* `mkLine` falls back to `addi x0, x0, 0` on an unrecognised word, so an
  unmodelled instruction became a silent NOP. Over the whole image that is 30
  sites, all `sltiu`/`sltu`; two are inside `eval_expr`. Both are modelled now,
  and the whole 25336-instruction image reflects with **zero** unmodelled sites.

## The 52, by class — measured, not guessed

Loop-freeness is a measurement now (`spans.tsv`, before loop summarisation), and
it does not match the guess. **33 spans are loop-free, 19 are loop-bearing.**

*Loop-free, 33.* The 11 int/eq cells, the 6 str cells, `hDivCorr`/`hDivOv`, the 4
logical cells, `hVar`, `hAssign`, `hArgsNil`, `hEpilogueSpill`, `hInitStore`, and
— against the old class map — `hSExpr`, `hSRet`, `hSRetNull`, `hSVarInit`,
`hSVarNull`.

*Loop-bearing, 19.* `hNeg` and `hNot` (which the old map called straight-line),
the seven call/composition spans, `hFn`, `hSBlock`, the three `hSIf*`, the two
`hSWhile*`, `hSForStart`, and the three `hSeq*`.

## The B2-carry: landed

The 11 int/eq residuals were REFUTED as stated — at `m0 := ∅` the `∃`-body wanted
`KindSlotPinned 6`, absent from `∅`, and `RefutBatteryCur.lean` proves all 11
false in the kernel. They now carry `EvalEntry` as `Vsa.Sim.BinIntCell` /
`BinEqCell`, exactly as the 6 unary/logic siblings always did. `#sweep_refute`
re-census: **REFUTED 11 → 0** over all 58 fields. `B2CarryLanded.lean` is the
machine-checked record — 11 slot-verifies plus the obligation discharged at the
very `∅` witness that refuted the bare form.

## The str order bridge: landed

`strCmpOrderBridge_{lt,le,gt,ge}` are proved in `rows/StrCmpOrderClose.lean` over
`Vsa/While/StringOrder.lean`, axiom-clean and inside `check_all`'s 942-theorem
audit. The "one genuine non-arithmetic premise" is no longer a premise.

## Making it decidable

Getting a verdict at all took four measured steps, each after the previous one
failed (the numbers are from `callee_2147511240`, a 50 KB obligation):

1. **Matching loop.** `smt.qi.max_instances` turned a 25 s timeout into a 6.2 s
   `unknown` at exactly 10001 instantiations, and `qi.profile` named the
   quantifier: the frame clauses' inner `∀A` had no usable trigger and fired on
   every address in the memory chain. MBQI was NOT the problem — `mbqi=false`,
   `relevancy=0`, `arith.solver=6` and `macro_finder` all timed out identically.
2. **Pure bitvectors.** `bv-bit2core` was 19350 — the `Int`/`BitVec` bridge, not
   the problem size.
3. **Quantifier-free.** `let` hides the intermediate states, so a clause can only
   be stated `∀S`. Emitting the chain as top-level `declare-const` + equational
   `assert` (not `define-fun`, which macro-expands) names every state, so clauses
   ground-instantiate at exactly the sites the term applies them. QF_ABV.
4. **Drop the array theory for footprint properties.** Even quantifier-free,
   bit-blasting a 64-bit-addressed byte array hit 3.8 M `bv-bit2core` and 3.2 GB.
   But frame, `StoreRepr` survival and code preservation are all "this address
   was not written", and the encoder KNOWS every store address — so it is BV
   arithmetic over a few hundred addresses plus one clause per summary.

Houdini then reaches a fixpoint in **18 seconds** over 202 summaries × 6 clauses
(1020 checks, 120 dropped in round 0, 6 in round 1, only 4 of the 126 for
solver timeout rather than a genuine countermodel).

## Where the 52 stand

`bmc/verdicts.tsv`, five post conjuncts. Of the summaries, 192/201 carry
`sp_restore`/`ra_restore`/`inv_pres`, 189 `s1_restore`, 181 `s0_restore`, and
**200 of 201 carry `stack_or_arena`** — the clause the footprint composition
needs.

**`StoreRepr`/`Arena.contains` is encoded.** It is the entry hypothesis every
residual carries (`EvalEntry.store`), so assuming it is faithful to the statement
being checked rather than a shortcut around it; what the check still has to
establish is that the offset from such a base stays inside the object, which the
machine text does decide. `heap_hyp` instantiates it at each of the 481
pointer-based store sites out of 10054, and any verdict resting on it is tagged
`VALID[StoreRepr@n]` with the site count. Two things had to be right for it to
land: the containment bound is `base ≤ A_hi − 32`, since `base + 32 ≤ A_hi` is
satisfiable by wraparound and the solver takes it; and `INV` has to bound the
frame ABOVE `sp` as well as below, or ordinary `sd rX, 0x418(sp)` spills escape
the stack window. That took the clause from 128 summaries to 195, and the two
register-indirect calls (the `Value.native` dispatches for `print`/`println`/
`assert`, `NativePrintSpec` in the proof) took it to 200 once classified as the
callee contracts they are rather than left as empty clause sets.

**No footprint refutations.** An earlier configuration reported ten; every one
was an artifact of starting the span at the ARM rather than the function entry,
which leaves what the prologue established unconstrained — `s1 = sret` above all,
since every arm stores the boxed result through it, so the solver put that store
inside the code image. Starting at the function entry with the AST kind pinned
derives those facts instead, the same move `blockA_k` makes in the proof, and
they vanish. The two REFUTED that survive are the posts being wrong for those
spans, not the spans: `hEpilogueSpill` is a frame fragment, so `sp` moves across
it and it boxes nothing; `hInitStore` is the main-init image, not an arm.

**One induction-variable invariant is left, and it is 33 of the 52.**
`loop_0x800031dc`, the argument-marshalling loop in the EX_CALL arm, is the sole
summary without `stack_or_arena` and the sole `summary-clause` blocker for 33
queries. Its seventh store lands at `sp + 240 + 24n`, slot `n` of the
outgoing-argument array, and the 1088-byte frame needs `n < 35`.

The bound is in the source, and encoding it was not enough. `MAX_ARGS` is 32 and
`c/src/interp.c:251` checks `argc > MAX_ARGS` before the loop; it is encoded as a
named precondition with its provenance, and every residual query discharges it
for real, since those spans start at `eval_expr`'s entry. It still does not
close the gap, because it bounds the COUNT while the store address is built from
the COUNTER. What closes it is `a6 <= a5` at the header, established as `a6 = 0`
on entry and preserved across the `bne` back-edge. The clause bank cannot express
that: every candidate there relates a summary's entry state to its exit state,
and this is a bound on a variable carried around the back-edge. An
induction-variable clause family, parameterised over (register, bound
expression) and mined the same assume-guarantee way, is the concrete next
extension. The witness and the disassembled block are in `bmc/OBSTRUCTION.md`.

A further 17 verdicts are `UNKNOWN(footprint)`, which is the solver timing out on
the function-entry spans rather than a missing fact. Those want a budget.

## The pipeline, per residual

1. Read the span from the ground table; the region is its enclosing function.
2. `reflectBmc` it, and record whether the frontier emptied.
3. Encode `Pre` (`bmc/pre.smt2`): the jump-table rodata pins, the stack/arena
   layout facts `EvalEntry` carries, code disjointness, and the no-wrap bounds.
   Every one of those was added because the solver produced a countermodel that
   turned on its absence, not to make a query pass.
4. Mine the summary clause sets: Houdini over a guarded candidate set, each
   clause established by ONE-STEP unfolding of the summary's body under the
   assume-guarantee hypothesis that every summary — itself included, renamed
   `<sym>_ih` — already satisfies the set.
5. Z3 on `Pre ∧ clauses ∧ ¬Post`, footprint route for the memory family. UNSAT is
   valid; asserting clauses is weaker than asserting definitions, so an UNSAT
   here is an UNSAT under the definitions.
6. Any refutation feeds back a spec amendment and a re-census.
