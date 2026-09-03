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

`bmc/verdicts.tsv`. Of the summaries, 192/201 carry `sp_restore`/`ra_restore`/
`inv_pres`, 189 `s1_restore`, 181 `s0_restore`, 133 `above_sp`, and **200 of 201
carry `stack_or_arena`** — the clause the footprint composition needs.

Three entry facts got it there, and `bmc/OBSTRUCTION.md` has the detail.
`StoreRepr`/`Arena.contains` is the hypothesis every residual already carries
(`EvalEntry.store`), so encoding it is faithful rather than a shortcut; it is
instantiated at each of the 481 pointer-based store sites out of 10054, and any
verdict resting on it is tagged with the count. The two `Value.native`
dispatches are the `NativePrintSpec` callee contracts. `above_sp` is the ABI fact
that a callee writes below its entry `sp`, mined rather than assumed. Two of the
three needed a countermodel to state correctly: containment is `base <= A_hi -
32`, never `base + 32 <= A_hi`, which wraparound satisfies; and `INV` has to
bound the frame ABOVE `sp` too, or plain `sd rX, 0x418(sp)` spills escape.

**No footprint refutations, on any span.** An earlier configuration reported ten;
every one was an artifact of starting the span at the ARM rather than the
function entry, which leaves what the prologue established unconstrained —
`s1 = sret` above all, since every arm stores the boxed result through it.
Starting at the function entry with the AST kind pinned derives those facts, the
same move `blockA_k` makes in the proof, and they vanish. The two REFUTED that
survive are the posts being wrong for those spans, not the spans:
`hEpilogueSpill` is a frame fragment, so `sp` moves across it and it boxes
nothing; `hInitStore` is the main-init image, not an arm.

**Nothing in the campaign says a residual is false.** 2 are VALID, 33
`UNKNOWN(iv-undischarged)`, 17 `UNKNOWN(footprint)`.

The 33 are no longer a budget wall. Slicing the discharge query to the state its
invariant is about takes it from 547 KB and 150 summaries to 40 KB and 1, and a
check that did not return at 400 s now returns in 1-16 s. The answer is `sat`,
so the invariant does not discharge as posed, and the countermodel says why: the
arrival is reached under a guard the solver has not resolved from the pinned AST
kind, so an arm the pin excludes still looks reachable. Resolving the dispatch
inside a sliced query is the next step, and applying the same slice to the post
queries is what clears the 17 footprint timeouts.

**One summary and one mechanism are left.** `loop_0x800031dc`, the
argument-marshalling loop, writes `sp + 240 + 24n` and needs `n < 35`. The
invariant that bounds it is `a6 < a5 <= 32` — the `bne` back-edge with `a6 = 0`
on entry, and `MAX_ARGS` from `c/src/interp.c:251`. It is stated as an
`IV_INVARIANT`, which the driver holds to both obligations at once: proved
inductive at the summary's recursive occurrence, and discharged at every
application site. Three refinements got the discharge from a
400 s timeout to a definite answer in seconds, and all three stay: it runs under
the arrival's OWN guard rather than unconditionally; an arrival whose guard is
UNSAT is skipped, since a span that cannot reach a loop has no invariant of it to
establish; and the invariant is stated with SIGNED comparisons, because every
comparison the machine makes here is signed (`blt a4,a5` at 0x800031c8 IS the
`MAX_ARGS` check, `bge zero,a5` at 0x800031d8 skips an empty loop, `bne a6,a5` at
0x80003250 closes it), and an unsigned reading lets `a5` be `0x8000000000000000`,
which passes the signed check and blows the bound.

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
