# What is left

## The clause set

Seven clauses, mined by assume-guarantee over 201 summaries to a fixpoint in
~55 s. Surviving: `inv_pres` 192, `sp_restore` 192, `ra_restore` 192,
`s1_restore` 189, `s0_restore` 181, `above_sp` 133, and **`stack_or_arena` 200 of
201** — the clause the footprint family composes through.

Three entry facts got `stack_or_arena` from 128 to 200. `StoreRepr`/
`Arena.contains` is the hypothesis every residual already carries
(`EvalEntry.store`), instantiated at each of the 481 pointer-based store sites out
of 10054; verdicts resting on it are tagged `VALID[StoreRepr@n]`. The two
`Value.native` dispatches are the `NativePrintSpec` callee contracts. `above_sp`
is the ABI fact that a callee writes below its entry `sp`, mined rather than
assumed — true of 133 summaries, correctly false of a loop inside a frame.

## Where the 52 stand

`outside_stack_arena`: **9 VALID, 9 REFUTED, 34 UNKNOWN**. `code`: 9 VALID, 10
REFUTED, 33 UNKNOWN.

VALID: `hArgsNil`, `hEpilogueSpill`, `hInitStore`, `hSExpr`, `hSRet`,
`hSRetNull`, `hSeqNil`, `hSeqConsNormal`, `hSeqConsAbrupt`.

**Every refutation traces to a missing clause, not to a fault in the arm.** The
nine are `hSBlock`, `hSForStart`, the three `hSIf*`, `hSVarInit`, `hSVarNull` and
the two `hSWhile*`. Their escaping store is `sd _, 8(sp)` — `sp`-relative, and
safe as long as everything applied before it preserves `sp`. Nine of the 201
summaries do not carry `sp_restore`, each refuted with its own countermodel, and
five of those nine are on `hSBlock`'s path (`loop_0x80004098` and its neighbours,
the `exec_stmt` arm loops). With `sp` free after such a summary, the model puts
it above `SL_hi` and the store lands outside. Establishing `sp_restore` for those
loops is what closes this class.

## Three refutations that were NOT real

Worth recording, because the same shape produced all three and each looked like a
finding until the countermodel was read.

* `base + 32 <= A_hi` for `Arena.contains` — satisfiable by wraparound, with
  `base = 0xff..e1` and `base + 32 = 1`. Must be `base <= A_hi - 32`.
* `sp + frame <= SL_hi` for the stack bound — same wraparound, with the stack put
  at the top of the address space and a spill wrapped into the code image.
* The residual queries never asserted the layout invariant, only the summary
  obligations did. The solver picked a seventeen-byte arena (`A_lo = 1`,
  `A_hi = 0x12`), `A_hi - 32` underflowed, and every `Arena.contains` hypothesis
  went vacuous. That alone accounted for **fifteen** spurious refutations;
  `(assert (INV s0))` in the entry pins removes them.

The general rule: in a bitvector encoding, never state a region bound with an
addition on the side the solver controls. Every one of these was found by reading
a countermodel rather than by trusting a verdict.

## The 34 UNKNOWN

`UNKNOWN(iv-undischarged)` on the args loop, and they are now correct for the
right reason on most spans. `loop_0x800031dc` writes `sp + 240 + 24n` and needs
`n < 35`; the invariant is `0 <= a6 < a5 <= 32` (the `bne` at 0x80003250, and
`MAX_ARGS` at `c/src/interp.c:251`), stated SIGNED because every comparison the
machine makes there is signed. The driver holds it to being proved inductive at
the summary's recursive occurrence AND discharged at every application site.

Resolving the AST-kind dispatch closed most of it: with the encoder stating which
guard the pinned kind makes true, `hVar`, `hIAdd` and `hNeg` discharge instantly,
because the args loop sits on an arm their kind excludes. What remains is the
call class itself (`hCall` and its six siblings), where the loop is genuinely
reachable and the invariant has to be proved rather than sidestepped.

## Next

1. `sp_restore` for the nine summaries lacking it — closes the 9 refutations.
2. The args-loop invariant on the call class — closes the 34 UNKNOWN.
