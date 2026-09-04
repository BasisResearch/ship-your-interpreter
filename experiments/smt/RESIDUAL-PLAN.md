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

**Retracted and restated.** This section previously reported 46/46 VALID on the
footprint posts and "not one REFUTED". Both were artefacts. 26 of the 52 queries
had contradictory assumptions and proved every post they were asked, and the
loop clause sets they leaned on were mined against loop bodies that never run.
The numbers below are what the encoder says once neither is true.

Last measured on the `bmcE` encoder (52 spans, 47 summaries, `-j10 --timeout
120`, z3 4.15.4):

| post | VALID | N/A | REFUTED | UNKNOWN |
|---|---|---|---|---|
| `sp` | 18 (2 frame-shifted) | — | — | 34 |
| `storerepr` | 1 | 4 | 1 | 46 |
| `valuerepr_tag` | 1 | 17 | — | 34 |
| `outside_stack_arena` | — | — | — | 52 |
| `code` | — | — | — | 52 |

**No query is vacuous.** That is the load-bearing line: it is what makes any
VALID above mean something, and it was not true of any campaign before this one.

The one refutation is `hInitStore.storerepr`. The 104 blocked footprint verdicts
have exactly two causes, both named:

* **68 — the args-loop invariant at its recursive occurrence.**
  `loop_0x800031dc` needs `0 <= a6 < a5 <= 32` discharged where the loop applies
  itself. Genuinely open; the cut-and-retry fallback does not close it either.
* **36 — a false refusal, since fixed.** `footprint_check` tested
  `"unmodelled_step" in base`, a bare substring, and `smtPreamble` declares that
  symbol unconditionally, so every query matched through its own
  `(declare-fun ...)` line. There are ZERO applications of it in all 52 queries.
  The guard now tests for an application. Not yet re-measured.

`stack_or_arena` survives on 28 of 47 summaries, down from 52 of 53. That drop is
the loop-obligation fix landing: a loop body that actually runs does not preserve
the clause, and the earlier survival rate was measuring a body that never
executed.

### On regenerating this table

The encoder is under active repair and these artefacts are per-encoder. Five
campaigns were run in one night and four were superseded mid-flight by a fix to
`ReflectSpan.lean`. The driver's provenance guard (a `src/` copy in the campaign
directory, compared against the tree) is what catches that, and it should be
believed: a verdict against a different encoder is a verdict about another
program. Regenerate once the encoder settles, not while it is being fixed.

## The evidence the verdicts rest on

The campaign cannot validate itself. Every clause it mines is proved against the
encoder's own model of a callee, so an encoder defect is invisible to it, and the
assumed clause sets are checked by nobody. Ten defects were found by reading the
encoder, nine of which never showed up in a verdict.

`DIFFTEST-PLAN.md` and `DIFFTEST-FINDINGS.md` are the answer to that, and they
are now the primary assurance layer: 104 programs traced through the proof model,
43,723 real `(pre, post)` clause pairs, 323,598 state checks over 6,170 distinct
PCs. It found eight further defects, including loop obligations that were vacuous
past the first iteration and `ra_restore` assumed for `__moddi3`/`__divdi3`,
which return through `t0` and were refuted on 112 of 112 real applications.

`scripts/difftest.sh` is the gate, and `VSA_DIFFTEST=1 scripts/check_all.sh` runs
it as stage d. **Run it after any change to `ReflectSpan.lean` or
`ReflectResiduals.lean`, before believing a campaign's verdicts.**

## What was wrong with the encoder, and how it was found

Every one of the nine footprint refutations this document previously reported was
an artefact. Each was found by reading a countermodel, never by trusting a
verdict, and each is recorded in `experiments/observations.md`.

* **A callee that never returns was summarised as a returning map.** `jal ra,
  exit` became `callee_exit` applied at a return address that is never reached.
  `sp_restore` is correctly refuted for `exit` — it has no epilogue — so every
  `sp`-relative store the encoder then reflected had a free `sp`. On the `.fn`
  arm that address is `0x80003e54`, mid-spill of a different arm: the `hFn` code
  refutation. `neverReturns` walks the CFG with interprocedural call and tail
  edges, every unknown resolving to "may return", and finds four of 167 targets.
* **The entry headroom pin used `INV`'s own constant.** Every clause is guarded
  by `INV` and instantiated after the prologue lowered `sp`, where `INV` then
  failed by exactly the frame — so every clause was vacuous. That is the nine
  `hS*` failures. Pinned at 7408, what `ExecEntry.stackBudget` carries; the step
  needs `d < maxCallDepth`, which `ExecEntry` has no field for, so it is recorded
  in `assumed.tsv` rather than passed off as derived.
* **`ret` counted as an exit arrival anywhere.** "Exit" meant "left the span",
  which coincides with "reached the stop" only when the stop is the return.
  `hInitStore` stops at `interp_run`'s loop head, and two of its three arrivals
  were returns whose epilogue had already restored `sp`.
* **A span with no exit arrival answered the post about its ENTRY state**, and
  the `ite` merge fell through to the last arrival for inputs no guard covered.
  Both are silent sources of wrong verdicts; the first is a false VALID.
* **`storerepr` never excluded the arena**, which `INV` permits below the stack,
  so a heap write refuted the field whose job is to initialise the store.
* **The state chain was emitted as array-equality atoms.** `defunise` makes them
  macros: 138s to 10s. Not only speed — the miner drops any clause it cannot
  close in `--timeout`, which is why the args loop appeared to lack
  `stack_or_arena` when the clause was true all along.

A `funcStarts` prologue filter added earlier was **reverted**: `0x80004790` is
newlib's `malloc` tail-calling `_malloc_r(_impure_ptr, n)`, a real frameless
entry, so `exit`'s region was right and the filter dropped 103 of 167 real
entries — `eval_expr` among them — to fix a problem that did not exist.

## What these verdicts do and do not say

All five posts are frame properties or close to it. `code`,
`outside_stack_arena` and `sp` say nothing was clobbered; `storerepr` is
preservation. Only `valuerepr_tag` has functional content, and it is the weakest
form: the kind word is *a* valid `ValueKind`, not the right one.

That ceiling is structural. The summaries are uninterpreted `MState → MState`
characterised by frame clauses, so `callee_eval_expr` has no clause saying what
it COMPUTES, and frame properties are exactly the ones that survive
summarisation. Getting "the `.add` arm leaves `Value.int (a+b)` at the sret
buffer" needs a value clause tying an IH summary's result to the spec's `eval` —
which the Lean recursor IH supplies and this layer can only assume and compose.
The leaf arithmetic arms are where that pays first, since the arm does the
arithmetic in registers and needs the callees only for operands. Frame is a
prerequisite rather than a detour: a value post is stated AT an address, so
without the frame it is refutable for reasons that have nothing to do with the
arithmetic.

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
