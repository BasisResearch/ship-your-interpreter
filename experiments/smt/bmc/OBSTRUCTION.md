# What is left

## The clause set

`stack_or_arena` — "every store this summary makes lands in the stack window or
the heap arena" — is the clause the footprint family composes through. It
survives for **200 of 201 summaries**, after three things were encoded:

* **`StoreRepr` / `Arena.contains`**, the entry hypothesis every residual carries
  (`EvalEntry.store`), instantiated at each of the 481 pointer-based store sites
  out of 10054 (`heap_hyp`). Verdicts resting on it are tagged
  `VALID[StoreRepr@n]` with the site count. 128 → 195.
* **The `Value.native` dispatches** (`print`/`println`/`assert`) as the callee
  contracts they are — `NativePrintSpec` in the proof — rather than empty clause
  sets poisoning every query that reaches them. 195 → 200.
* **`above_sp`**, the ABI fact that a callee writes below its entry `sp`, so the
  caller's spill slots survive a call. Mined, not assumed: true of 133
  summaries, correctly false of a loop inside a frame whose stores are at
  `sp + k`.

Two of those needed a countermodel to get right. Containment must be
`base <= A_hi - 32`, since `base + 32 <= A_hi` is satisfiable by wraparound and
the solver takes it. And `INV` must bound the frame ABOVE `sp` as well as below,
or an ordinary `sd rX, 0x418(sp)` spill escapes the stack window.

## The one summary that fails

`loop_0x800031dc`, the argument-marshalling loop of the EX_CALL arm. It writes
slot `n` of the outgoing-argument array at `sp + 240 + 24n`, and the 1088-byte
frame needs `n < 35`:

    800031dc  ld    a2,16(s0)        ; the args list        <- loop header
    800031e0  addiw a1,a6,0          ; n, the counter
    800031f8  slli  a4,a4,3          ; 24n
    80003200  addi  a5,a4,976
    80003204  addi  a4,sp,32
    80003208  add   a4,a5,a4         ; sp + 1008 + 24n
    80003214  sd    a6,16(sp)        ; spill the counter
    80003220  jal   ra,0x80003164    ; eval_expr (recursive)
    8000322c  ld    a6,16(sp)        ; reload it
    80003234  sd    a2,-768(a4)      ; sp + 240 + 24n       <- the escaping store
    8000323c  addi  a6,a6,1
    80003250  bne   a6,a5,0x800031dc

The invariant that bounds it is `a6 < a5 <= 32`, and both halves are real:
`a6 < a5` from the `bne` back-edge with `a6 = 0` on entry, and `a5 <= 32` from
`MAX_ARGS` (`c/src/interp.c:8`, checked at line 251, sized at line 253). It is
stated as an `IV_INVARIANT`, which the driver holds to both obligations at once:
PROVED INDUCTIVE at the summary's own recursive occurrence, and DISCHARGED at
every application site in a residual query.

It fails the inductive step, and the reason is exact. The counter is spilled to
`16(sp)`, the recursive `eval_expr` runs, and the counter is reloaded — but the
reload reads a post-call MERGE state. The frame clause is ground-instantiated at
the callee application, not propagated through the merge, so the solver is free
to say the reload returned something else. Instantiating the memory clauses at
every store address (`dedup_addrs`) was not enough; the merge is the gap.

## What the verdicts are limited by

Of the 52: 2 VALID, 33 `UNKNOWN(iv-undischarged)`, 17 `UNKNOWN(footprint)`. No
residual is refuted, and the footprint family has zero refutations on any span.

The 33 are no longer a budget wall. Slicing the discharge query to the state the
invariant is about (`slice_to`) takes it from 547 KB and 150 summaries to 40 KB
and 1, and a check that did not return in 400 s now returns in 1-16 s. The answer
it returns is `sat`, so the invariant genuinely does not discharge as posed, and
the countermodel says why: the arrival is reached under a guard the solver has not
resolved from the pinned AST kind, so an arm the pin excludes still looks
reachable. Three refinements were needed to get an answer this sharp, and all
three stay:

* the discharge runs under the arrival's OWN guard (`guard_of`), not
  unconditionally — the emitter binds the guard immediately before the
  application it guards;
* an arrival whose guard is UNSAT is skipped, since a span that cannot reach a
  loop has no invariant of it to establish;
* the invariant is stated with SIGNED comparisons, because every comparison the
  machine makes here is signed (`blt a4,a5` at 0x800031c8, `bge zero,a5` at
  0x800031d8, `bne a6,a5` at 0x80003250). An unsigned reading lets `a5` be
  `0x8000000000000000`, which passes the signed check and blows the bound.

The 17 `UNKNOWN(footprint)` remain solver budget on the function-entry spans.

## The next step

Resolve the AST-kind dispatch inside a sliced query. The kind pin and the
jump-table rodata pins are both present, but in the slice the solver does not
carry them through to the dispatch guard, so a query pinned to one arm still has
to discharge invariants belonging to the others. Slicing on the guard's own
dependency chain, or asserting the resolved arm target directly at the dispatch,
is what closes it. The footprint timeouts want the same slice applied to the
post queries, which is mechanical once this lands.
