# What is left, machine-checked

`stack_or_arena` — "every store this summary makes lands in the stack window or
the heap arena" — is the clause the whole footprint family composes through. It
survives for **200 of 201 summaries**.

## The one summary that fails, and why

`loop_0x800031dc` is the argument-marshalling loop of `eval_expr`'s EX_CALL arm.
Seven stores; six are fine. The seventh:

    (bvadd (select (rr i23) #x000000000000000e) #xfffffffffffffd00)     ; sd _, -768(a4)

Read the block and that is `sp + 240 + 24n`, slot `n` of the outgoing-argument
array. The frame is 1088 bytes, so it needs `n < 35`:

    800031dc  ld    a2,16(s0)        ; the args list        <- loop header
    800031e0  addiw a1,a6,0          ; n, the counter
    800031e4  slli  a4,a6,3
    800031ec  slli  a4,a1,1
    800031f0  add   a4,a4,a1         ; 3n
    800031f8  slli  a4,a4,3          ; 24n
    80003200  addi  a5,a4,976
    80003204  addi  a4,sp,32
    80003208  add   a4,a5,a4         ; sp + 1008 + 24n
    ...
    80003234  sd    a2,-768(a4)      ; sp + 240 + 24n       <- the escaping store
    8000323c  addi  a6,a6,1          ; n++
    80003250  bne   a6,a5,0x800031dc ; a5 = the argument count

## The bound exists in the source, and it is still not enough

    c/src/interp.c:8    #define MAX_ARGS 32
    c/src/interp.c:251  if (argc > MAX_ARGS) runtime_error(in, e->line, "too many arguments (max 32)", 0, 0);
    c/src/interp.c:253  Value args[MAX_ARGS];

That check is emitted BEFORE the loop header, so the loop's own obligation cannot
see it (every residual query can, since those start at `eval_expr`'s entry). It
is encoded as a named precondition in `scripts/houdini_summary.py`
(`PRECONDITIONS`), and it does not close the gap on its own: it bounds the COUNT
`a5`, while the store address is built from the COUNTER `a6`.

What closes it is the induction-variable invariant `a6 <= a5` at the header,
established as `a6 = 0` on entry and preserved by `a6 <= a5` plus the `bne`
back-edge. The clause bank cannot express it: every candidate there is a relation
between a summary's entry and exit state, and this is a bound on a variable
carried around the back-edge. Adding an induction-variable clause family,
parameterised over (register, bound expression) and mined the same
assume-guarantee way, is the concrete next extension.

## What it costs

That single summary is the sole `summary-clause` blocker for **33 of the 52**
residual queries (`verdicts.tsv`). A further 17 are `UNKNOWN(footprint)`, the
solver timing out on the function-entry spans rather than a missing fact; those
want a budget.

The ledger for the footprint family: encoding exact and complete (52/52 spans),
`StoreRepr`/`Arena.contains` encoded and instantiated at all 481 pointer-based
store sites, 200/201 summaries carrying the clause, and one induction-variable
invariant between here and a verdict on the class.
