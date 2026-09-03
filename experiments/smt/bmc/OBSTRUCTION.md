# The one remaining obstruction, machine-checked

`stack_or_arena` — "every store this summary makes lands in the stack window or
the heap arena" — is the clause the whole footprint family composes through. It
survives for 139 of 201 summaries. For the other **60 it is REFUTED, with a
countermodel** (`drop-reasons.json`: 60 `sat`, and only ONE clause anywhere in
the campaign dropped for solver timeout instead of a countermodel).

Representative witness, the smallest such summary:

    summary   : loop_2147496860  (loop header 0x8000339c)
    store     : #0 of 3, width 8, guard g0
    address   : (bvadd (select (rr i6) #x0000000000000009) #x0000000000000000)
    witness   : (((bvadd (select (rr i6) #x0000000000000009) #x0000000000000000) #xfffffffffffffdf9) (QA #xfffffffffffffe00) (SL_lo #x7f80000fffffaef3) (SL_hi #x7ffffffffffffe01) (A_lo #x7fffffffffffffe3) (A_hi #x81fffffffffffff1))

The store's base register is a *pointer read out of memory*. Nothing in the
machine text constrains where it points, so the solver is free to put it outside
both regions — and does. This is not a solver limit and not a loop invariant
waiting to be mined: it is the heap-well-formedness fact, which the Lean arms
carry as `StoreRepr` / `Arena.contains` — a pointer reachable from a represented
store points into the arena.

It accounts for all 48 remaining `UNKNOWN(summary-clause)` verdicts in
`verdicts.tsv`. Encoding it (as an entry fact beside `entryPinsSmt`, together
with its preservation across the arm's own writes) is the single next step for
this campaign; nothing else in the pipeline is blocked.
