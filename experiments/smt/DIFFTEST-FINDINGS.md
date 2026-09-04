# Differential testing the BMC encoder — what it found

`DIFFTEST-PLAN.md` is the design; this is the result of the first run of it.
The plan predicted it "would have found nine of ten" of the defects that had been
found by reading. It found **six new ones** on its first pass, four of which
were invisible in the verdicts, and one of which made every loop clause in the
campaign vacuous.

Reproduce with `scripts/difftest.sh`. Corpus: `c/tests/*.wl` (the ones that fit)
+ `c/difftests/*.wl` + whatever `scripts/wl_fuzz.py` generates.

## The measurements

| phase | scale | result |
|---|---|---|
| 1 span existence | 14 traces, 52 spans, 2611 eval / 783 exec / 106 seq instances | 52/52 entered, 52/52 reach an encoder-recognised exit |
| 1 dispatch | 3 ground jump tables, 33 arms | every observed computed goto lands on a declared arm; 31/33 arms taken |
| 2 clause witness | 37 summaries, 20223 real `(pre, post)` pairs | 0 refutations after the fixes below; 5 before |
| 3 step semantics | 6170 distinct PCs, 101146 sampled executions, 90264 state checks | 0 disagreements after the fixes below; 2 before |

Phase 3's 90264 checks are the whole executed image: every `alu` form's effect on
all 31 registers, every store's landing place and its neighbours, and every
branch condition, evaluated against the proof model on real operands.

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

### 7. A driver bug the loop fix exposed (would have read as a failed check)

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

## What this still does not do

It tests the ENCODER against the model, not the model against the hardware, and
not the residuals against the spec — the plan says so and it is still true. It is
also finite: a callee pinned by observed pairs is unconstrained on every other
input, and phase 2's verdicts are about the pairs the corpus produced. What
changed is that the encoder now has positive evidence at all, and a gate that
re-checks it (`scripts/difftest.sh`) before the next campaign's verdicts are
believed.
