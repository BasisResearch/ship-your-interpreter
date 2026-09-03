# What is left, machine-checked

`stack_or_arena` — "every store this summary makes lands in the stack window or
the heap arena" — is the clause the whole footprint family composes through. It
now survives for **200 of 201 summaries**.

## The one summary that fails

`loop_0x800031dc`, the argument-marshalling loop inside `eval_expr`'s EX_CALL
arm. Seven stores, three of them pointer-based. Six are fine; the seventh is not:

    (bvadd (select (rr i23) #x000000000000000e) #xfffffffffffffd00)     ; sd _, -768(a4)

Read the block and that address is `sp + 32 + 976 - 768 + 24*n`, i.e. slot `n` of
the outgoing-argument array in the frame:

    ld   a2,16(s0)          ; the args list
    addiw a1,a6,0           ; n, the argument index
    slli a4,a6,3
    ...
    slli a4,a4,3            ; 24*n
    addi a5,a4,976
    addi a4,sp,32
    add  a4,a5,a4           ; sp + 1008 + 24*n
    sd   a4,0(sp)           ; ... stored at -768(a4) further down

Nothing in the encoding bounds `n`, so the solver takes it large and walks the
address out of the frame. The countermodel:

    address  #x000000000ffffffc   QA #x0000000010000000
    SL_lo    #x0000000022036eef   SL_hi #x00000000900000a1
    A_lo     #x000000001000024e   A_hi  #x000000002000004f

## What that fact is

It is not the heap-well-formedness fact any more. `StoreRepr`/`Arena.contains` is
encoded (`heap_hyp` in `scripts/houdini_summary.py`, instantiated at each of the
481 pointer-based store sites out of 10054), and it is what took this clause from
128 summaries to 200.

What remains is the **argument-index bound**: the args loop runs at most as many
times as the callee has parameters, and the frame reserves a slot per parameter.
In the Lean development that comes from the call arm's arity geometry together
with `TermGuards.argsMeasure`, the back-edge measure for `EvalArgs.cons`. It is a
loop bound, not a memory invariant, so it does not fit the clause bank as it
stands: the candidates are all relations between the entry and exit state, and
this one is a bound on an induction variable.

## What it costs

That single summary is the sole `summary-clause` blocker for **33 of the 52**
residual queries (`verdicts.tsv`). A further 17 are `UNKNOWN(footprint)`, which
is the solver timing out on the function-entry spans rather than a missing fact;
those want a budget, not an idea.

So the ledger for the footprint family is: encoding exact and complete (52/52
spans), `StoreRepr` encoded, 200/201 summaries carrying the clause, and one loop
bound between here and a verdict on the class.
