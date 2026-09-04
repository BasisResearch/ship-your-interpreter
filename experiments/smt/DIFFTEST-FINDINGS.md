# Differential testing the BMC encoder — what it found

`DIFFTEST-PLAN.md` is the design; this is the result of the first run of it.
The plan predicted it "would have found nine of ten" of the defects that had been
found by reading. It found **eight new ones**, five of which were invisible in
the verdicts, one of which made every loop clause in the campaign vacuous, and
one of which made five of the 52 queries prove every post they were asked.

Reproduce with `scripts/difftest.sh`. Corpus: `c/tests/*.wl` (the ones that fit)
+ `c/difftests/*.wl` + whatever `scripts/wl_fuzz.py` generates.

## The measurements

104 programs: `c/tests` + `c/difftests` (hand-written, one per arm the first pass
showed uncovered) + 90 from `scripts/wl_fuzz.py`.

| phase | scale | result |
|---|---|---|
| 1 span existence | 104 traces, 52 spans | 52/52 entered, 52/52 reach an encoder-recognised exit **from their own arm** |
| 1 dispatch | 3 ground jump tables, 33 arms | every observed computed goto lands on a declared arm; 31/33 arms taken (the 2 are structurally unreachable, below) |
| 2 clause witness | 38 summaries, **43723** real `(pre, post)` pairs | 0 refutations after the fixes below; 5 clause families before |
| 3 step semantics | 6170 distinct PCs, **323598** state checks over 104 programs | 0 disagreements after the fixes below; 2 before |

Phase 3's checks are the whole executed image: every `alu` form's effect on all
31 registers, every store's landing place and the words on either side of it, and
every branch condition, evaluated against the proof model on real operands. The
comparison is a REWRITE, not a solver query — the trace supplies the operand
bytes, so the encoder's term is ground and `(simplify ok)` decides it. The same
check phrased as satisfiability over a byte array ran twelve minutes on one chunk
at 400 MB and answered nothing.

## Defects found

### 1. Every loop obligation was vacuous past the first iteration (unsound)

`loopExits` collected a loop's exit edges with `blockSuccs`, which treats a
`stops` PC as unreachable. A loop obligation is generated with
`stops = loopExits …` — *the loop's own exits* — so the exits came back EMPTY for
all 23 loop summaries. `bmcRound`'s re-arrival branch then contributed no
successor and no exit, and `fbody` was the zero-iteration path alone: every loop
clause was mined against a body that never runs.

Phase 2 refuted `s0_restore` for `loop_0x80003314` on a real pair
(`x8: 0x87fff428 -> 0x87fff440`); the loop body is `addi s0, s0, 24`.

Fix: `blockSuccsE` (successors *including* the ones a stop cuts off) for the exit
computation, and an exit edge that lands on a stop becomes an EXIT ARRIVAL rather
than a frontier arrival. `fbody` for that loop went from `b0` to
`(ite g4x b0 m22)`. Re-mining then dropped `s0_restore` (and `ra_restore` from
eight loops, and `above_sp` from three) on its own.

### 2. `ra_restore` assumed for functions that do not restore `ra` (unsound)

`__moddi3` (`0x80004728`) is `mv t0, ra ; jal __hidden___udivdi3 ; mv a0, a1 ;
jr t0` — it saves the return address in `t0`, clobbers `ra` with the inner call's,
and returns through `t0`. `ra_restore` was ASSUMED for it and for `__divdi3`,
and refuted on 112 of 112 real applications (`x1: 0x800037c8 -> 0x80004738`).

Fix: `ReflectSpan.retsViaSaved` — a reachability walk from the function's entry
looking for an unresolved `jalr x0, rN` (rN ≠ ra, or ra with a non-zero offset).
`#emit_bmc` writes the verdict to `clause-drop.tsv` and the driver removes the
clause, the way it already removes `above_sp` for the assumed set. A range scan
is not enough: `__divdi3` falls through into the division family's shared tail
and `funcStarts` puts a boundary in between.

### 3. `stack_or_arena` false of the whole C runtime (unsound)

The clause says an address outside the stack window and outside the arena is
unchanged. Both windows are free constants, so it is asserted for windows that do
not cover the writable statics — and `malloc` writes its free-list head, `fputc`
the stream buffer, and anything that can fail writes `errno`. Refuted on every
application of `malloc`/`free`/`fputc`/`env_new`/`env_define`/`value_print`/
`stringify`, and through them on the MINED `callee_eval_expr` (97/2611) and
`callee_exec_stmt` (337/783).

Fix: `ReflectSpan.writableRegion` reads the ELF's `SHF_WRITE` sections
(`0x8001ad00..0x8001c168` here); `#emit_bmc` emits them as ground `G_lo`/`G_hi`
and the clause exempts that region. `.text` and `.rodata` sit BELOW it, so code
and jump-table preservation — what the clause is actually used for — is
unaffected.

### 4. A loop with no exit edges dropped its path silently (unsound)

`bmcRound`'s re-arrival branch pushed one frontier arrival per loop exit and one
exit per `leaves`. With neither, the path simply vanished: no successor, no exit,
no `halts` entry — the same shape as defect 2 in the plan's table. Twelve of the
23 loop summaries were in exactly that state, because `neverReturns` cannot see
that `runtime_error` longjmps, so the fallthrough after `jal ra, runtime_error`
is modelled as live and closes a cycle with the next error site's argument setup.

Fix: record it as a halt. `hVar`'s halt count went 22 → 57.

### 5. `retExit` decided by a word in another function (latent)

Twelve `exec_stmt` arm spans declare the stop `0x800043ec` (`interp_run`'s entry),
which is outside `exec_stmt`'s own region `[0x80003fe0, 0x80004308)`. A stop
outside the region can never be an arrival, so those spans exit by the function's
`ret` — and `retExit` was read as `isRet(0x800043e8)`, which is `interp_init`'s
`ret`. It came out `true` by luck. Had that word not been a return, all twelve
spans would have had zero exit arrivals.

Fix: `retExit = if stop ∈ region then isRet(stop-4) else true`, and the
mis-declared stops are recorded in `stop-outside.tsv` instead of staying latent.

### 6. `decodeTerm` dropped the `jalr` immediate (latent)

`jr 12(a3)` at `0x80006b38` (memset's duff device) exists in this image.
`Term.jalr` carried only `(rd, rs1)`, so the encoder's target expression was `a3`
where the machine goes to `a3 + 12`. Phase 3 flagged it on 24 sampled executions
across 14 programs.

Fix: `Term.jalr` carries the immediate; the dispatch target expression is
`(bvand (bvadd rs1 imm) ~1)`; `isRet`/`neverReturns`/`blockSuccs` require
`imm = 0` for a return.

### 7. Five queries proved every post they were asked (unsound)

`hAssign`, `hAndTrue`, `hAndFalse`, `hOrTrue`, `hOrFalse` declared stops their
own arm cannot reach. The logical arm ends at `0x800035dc` with
`j 0x800033ec`; the declared stop `0x800035e0` is the UNARY arm's first
instruction. `hVar` and `hAssign` declared `0x80003480` and `0x80003560`, the
second instruction of the next arm and of the logical arm — both arms actually
end at eval_expr's SECOND epilogue, `0x80003448`.

This is the defect the table already documents for `hNeg`/`hNot` ("the unary arm
ENDS at 0x80003624 … 0x80003628 is the next arm's code and is never reached from
here"), never applied to the other five. The consequence is worse than a wrong
answer: the query's dispatch pin says the logical arm is taken and its exit guard
demands a path to the unary arm's code, so the assumptions are contradictory and
every post is proved. Before the campaign's vacuity gate existed they read as
five VALID fields.

Measured both ways, independently: phase 1 says the arm runs 13 times over the
corpus and arrives 0 times; `(check-sat)` on the query's own binding chain plus
its exit guard and dispatch pin says `unsat` in 0.2 s. Fixed — `hAndTrue`/
`hAndFalse`/`hOrTrue`/`hOrFalse` → `0x800033ec`, `hVar`/`hAssign` → `0x80003448`
— after which all five are `UNKNOWN` (a real verdict) rather than vacuous.

### 8. Phase 1 could not see defect 7 (a hole in this test, found by this test)

The first phase-1 walked from the span's ENTRY, which for an arm residual is the
function entry, so *any* arm's path to the declared stop made the span look
reachable — `hAssign`'s stop is reachable, just not from `hAssign`'s arm. The
verdict is only ever about the arm the query pins, so the walk is now conditioned
on it: outcomes are counted over the instances that pass through the residual's
own arm. That is what turned defect 7 from an SMT-visible curiosity into a
one-line finding with no solver at all.

The same change surfaced a scope fact nothing else states, reported as a note
rather than a failure: the 21 binary-operator residuals declare the stop
`0x800037c0`, which is INSIDE the `%` sub-arm (`mv a0,s3` just before
`jal __moddi3`), so 113 of 707 real executions of that arm reach it; the six
`EX_CALL` residuals declare `0x80003360`, inside the argument loop, reached by 14
of 79. Those verdicts are about the arriving executions only. The Lean statement
(`BinIntCell` → `BinIntCellResid`, which is about `TwoSubReturn`) suggests the
operator dispatch at `0x80003558` is the intended end, but that is a
statement-level decision and is left declared as it is, now with the number
attached.

### 9. A driver bug the loop fix exposed (would have read as a failed check)

With loop obligations no longer vacuous, `fbody` became a guarded merge, and
`slice_to` dropped bindings that the surviving `(define-fun fbody …)` still
named — Z3 answered `unknown constant g33x`, which the driver would have read as
"clause does not survive". `slice_to` now drops any `define-fun` whose
dependencies the slice removed, the way it already dropped `state_exit`/`mem_exit`.

## Accepted divergences

* **HTIF mailbox.** The proof model consumes a store to `.tohost`
  (`0x8001ad00..0x8001ad10`) as a device command; the encoder's memory is a plain
  byte array and keeps the value. 664 such stores in the corpus. Excluded from
  the phase-3 comparison by `difftest.py:mmio_region`, and named there: the only
  stores to it are in `_write` and `exit`, both ASSUMED contracts whose bodies no
  span reflects.
* **Two unreachable dispatch arms.** `0x80003928` is the binary-operator table's
  entry for tokens `T_BANG` (16) and `T_EQ` (18), neither of which is a binary
  operator, so no well-formed AST reaches them. A finding about the corpus only
  in the sense the plan means: "spans that no program can reach are a finding in
  themselves".

### 10. `state_exit` is the wrong arrival's state when the exit guards overlap

The plan's phase 3 proper — drive the encoder's own binding chain with a real
entry state, pin every summary from its observed `(pre, post)` pair, and compare
`state_exit` against the machine — agrees on **259 of 309 span executions**, on
all 31 registers and on the entire store footprint. Every one of the other 50 is
the same defect.

`reflectBmc` folds the exit arrivals into `ite g1 s1 (ite g2 s2 … sN)`. That is
only the exit state if the guards are pairwise disjoint, and they are not: an
arrival at the exit PC is produced in every BMC round some block reaches it, and
the guards are the arrival guards, which under ABSTRACTED summaries are
simultaneously satisfiable. Measured on `hSBlock` at `dt_block@71886`:

* seven exit guards are true at once;
* six of the seven select a state **the machine is never in** at any point of
  that execution;
* the seventh, `b604`, matches the machine exactly on all 31 registers;
* the `ite` takes the first, `b425`, so `state_exit` disagrees with the machine
  on eleven registers (`x5` = `0x7f7f7f7f7f7f7fff`, which is `strlen`'s
  has-zero-byte constant, so the selected state is from a path through the
  string code the machine never entered).

Same shape on `hSIfTrue/False/None` (7 arms), `hSWhileBreak/False`, `hSForStart`
(2), and `hSeqNil/ConsNormal/ConsAbrupt` (3). A post proved about `state_exit`
on these spans is a post about whichever arrival the emitter listed first.

NOT FIXED, and deliberately so — the three candidate cures are a design decision:
make the guards disjoint by construction (which needs path information the merge
exists to discard); emit disjointness as its own obligation and qualify the
verdict when it fails; or replace the `ite` with `(=> g_i (= state_exit s_i))`
per arrival, which turns a silent wrong answer into a VACUOUS one the existing
gate already catches. The third is the smallest honest change and would take the
affected spans' verdicts to vacuous rather than to VALID.

### 11-14. Four gaps in the checking layer

Found by an independent audit of the driver, all fixed:

* **`complete` was gated for queries and never for obligations.** The emitter
  writes `; complete=false` into an obligation whose frontier did not empty and
  `mine()` never read it, so a clause could be mined from a body missing paths
  and then ASSUMED in every query that applies the summary. All 25 are complete
  today; `--rounds` and the emit bound are arguments and nothing caught that.
  Now a refusal.
* **`unmodelled_step` was invisible to the footprint route.** That route composes
  "no direct store hits `QA`" with "every applied summary carries
  `stack_or_arena`", and `applied_of` only matches
  `callee_`/`loop_`/`icall_`/`idisp_`. An opaque step is an unconstrained memory
  transformer neither leg covers, so a span containing one would report VALID
  over a step that can write anywhere. Zero occurrences in this image, which is
  why it had to become a refusal rather than stay a silence.
* **`heap_hyp` collapsed a disjunctive entry pin to one side.** For every store
  whose base is not `sp` it asserted `A_lo <= base <= A_hi - 32`. Measured over
  the campaign's write sets, 1722 of 26825 stores are pointer-based, and the
  bases are `s2` (the env, 830), `s1` (the caller's SRET BUFFER, 711), `a4`
  (108), `a0` (72). `entryPinsSmt` states the sret fact honestly as a disjunction
  (`a0 + 24 <= SL_lo` or `sp <= a0`) and `heap_hyp` silently took the arena
  branch, so an `outside_stack_arena` verdict on an eval arm held only on that
  branch. The vacuity gate cannot see it, because the arena branch is satisfiable
  on its own. Now stated as the disjunction "in the arena or in the stack
  window", which is strictly weaker and keeps the footprint check working.
* **`hits_QA` had the wraparound hole its neighbour's comment warns about.**
  `(bvule a QA) /\ (bvult QA (bvadd a w))` is false when `a + w` wraps, so the
  aggregate returns unsat and the post reads VALID. Constrained bases cannot
  wrap today, and `heap_hyp` had been given exactly this treatment three lines
  earlier while this one had not. Now `QA - a <u w`, which has no escape.

## The gate

`scripts/difftest.sh` runs the whole thing — emit the encoder's answers, build
and trace the corpus, phases 1-3 — and exits non-zero on any disagreement.
`VSA_DIFFTEST=1 scripts/check_all.sh` runs it as stage d. It is the gate to run
after ANY change to `experiments/smt/ReflectSpan.lean` or `ReflectResiduals.lean`.

FINDINGS fail the gate; NOTES do not. A finding is something wrong under any
reading (a span with no reachable exit, a dispatch the encoder mis-resolved, a
step that disagrees with the machine, a clause refuted on a real pair). A note is
a scope fact the campaign cannot state for itself: how much of an arm's real
behaviour a verdict covers, which arms no program reaches, which computed gotos
are left opaque, which stops are declared outside their own region.

## What this still does not do

It tests the ENCODER against the model, not the model against the hardware, and
not the residuals against the spec — the plan says so and it is still true. It is
also finite: a callee pinned by observed pairs is unconstrained on every other
input, and phase 2's verdicts are about the pairs the corpus produced. What
changed is that the encoder now has positive evidence at all, and a gate that
re-checks it (`scripts/difftest.sh`) before the next campaign's verdicts are
believed.
