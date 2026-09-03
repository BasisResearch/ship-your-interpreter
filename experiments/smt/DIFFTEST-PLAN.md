# Differential testing the BMC encoder

## Why

The encoder has never been positively validated. Every defect in it has been
found by someone reading it, and in one session that was ten:

| # | defect | how it presented |
|---|---|---|
| 1 | `jal ra, exit` summarised as a returning map | one span's `code` post refuted |
| 2 | span with no exit arrival answered its ENTRY state | silent false VALID |
| 3 | entry headroom pin equal to `INV`'s own constant | 9 footprint posts unprovable |
| 4 | `funcStarts` prologue filter dropped 103 real entries | wrong function regions |
| 5 | state chain as array-equality atoms | 10x slow, clauses dropped on timeout |
| 6 | `ret` counted as an exit arrival anywhere | 3 false refutations |
| 7 | `storerepr` never excluded the arena | 1 false refutation |
| 8 | callee summary applied before `ra := pc+4` | wrong `ra` after every call |
| 9 | `sltiu` silently `mkLine`d to a NOP | 2 sites mis-executed |
| 10 | dispatch pin negated a NESTED dispatch's arms | **26 of 52 queries vacuous** |

Nine were invisible in the verdicts. Two campaigns reported "zero refutations"
while (8) and (10) were live. Absence of known bugs is not evidence, and the
next inspection pass has no reason to do better than the last one.

The machine can check this instead. `riscv-lean/lean_emulator` runs the proof
ELF in the EXACT proof model. Run a real program, watch what the machine does
across a span, and compare it to what the encoder says the machine does.

## The comparison

Not memory arrays. The encoder models a span as a **register file** plus a
first-order **write log**, so that is what to compare, and both are small.

A store's address and value are derivable from the register file at that step
(`addr = regs[rs1] + imm`, `value = regs[rs2]`), so the trace needs only
`(step, pc, regs)`. No hook into the model's memory is required. If two runs
agree on the register file at the exit and on the write log across the span,
they agree on the memory state, because the encoder's memory IS the write log
applied to the entry memory.

## What makes a span with calls testable

A span's reflected term is not a function of `s0` alone: `callee_X` is
uninterpreted. The trace closes that. For each application `(callee_X mK)` the
trace holds the concrete state at the call and at its return, so the instance
is pinned with

```smt2
(assert (= (callee_X <concrete-pre>) <concrete-post>))
```

and the whole term evaluates. This is also why the same trace validates the
CLAUSE SETS: a clause is a claim about `(pre, post)` pairs, and the trace has
real ones. A clause that fails on a real pair is refuted concretely, with no
solver search at all.

## Phases

Ordered by what they catch per unit of work. Each stands alone; stop at any
point and the earlier ones still gate.

### Phase 0 — the trace (the only new machinery)

`traceLoop` in `riscv-lean/lean_emulator/LeanRiscv.lean`, beside `my_main`.
Replicates `loop ()` but reads `PC` and the register file between `try_step`
calls. Nothing in the generated Sail code changes.

Anchors, all checked:

| need | symbol |
|---|---|
| step one instruction | `try_step (step_no : Nat) (exit_wait : Bool) : SailM Bool` — `LeanRV64DExecutable/Step.lean:398` |
| the loop to copy | `loop (_ : Unit) : SailM Nat` — same file, `:472` |
| read a GPR | `rX (app_0 : regno) : SailM (BitVec 64)` — `LeanRV64DExecutable/Regs.lean:615` |
| emit a row | `print_effect (str : String)` — `Sail/ConcurrencyInterfaceV1.lean:292` |
| where it lands | `sailOutput : Array String` — same file, `:107` |

**`SailM` is a pure state monad — no `IO` inside.** `runElf64` only gets the
state back at the end (`main.run initialState`), so the trace cannot be written
to a file as it goes. It rides the model's own output channel instead: emit each
row via `print_effect` with a `#T\t` prefix, then in `runElf64` partition
`s.sailOutput` on that prefix — rows to the trace file, everything else to
stdout as the program's real output. No new state, no change to the model.

That accumulates in memory, which is the reason for the PC filter rather than a
nicety: `--trace-pcs <file>` records only steps whose PC is in a given set (the
span entry/exit PCs, the call sites, the store sites — all the checks below
read). A full trace of every retired instruction would not fit.

Output: `<prog>.trace.tsv`, columns `step pc x0..x31`.

Standing rule: build test ELFs in a **/tmp copy of `c/`**, never in `c/`. The
proof ELF is the object under study; its sha256 begins `b146c6ed…` and is
re-checked after any session that touches the tree.

### Phase 1 — do the declared spans exist? (catches 2, 6, 10)

For each of the 52 spans, does any trace enter at its entry PC and reach its
declared stop?

* never reaches the stop → the span is mis-declared. This is `hNeg`/`hNot`,
  whose stop `0x80003628` is unreachable past a `jal x0`.
* reaches it only via a `ret` → the encoder's `retExit` classification is
  checkable against reality rather than against `isRet(stop-4)`.
* entered but the exit arrival count disagrees with the encoder's → a merge bug.

No SMT at all. A dictionary over the trace. This is the cheapest check in the
plan and it catches the most expensive class of bug.

### Phase 2 — do the clauses hold on real call pairs? (catches 8, and the `above_sp` question)

For every `(callee_X, pre, post)` in the trace, evaluate each of the seven
clauses concretely. `ra_restore` on a loop body that calls, `above_sp` on
`memcpy`/`strcpy`/`snprintf`/`value_int` — anything that writes through a
caller-passed pointer — resolves in one pass, with a witness.

This is the check the campaign structurally cannot make: mined clauses are
proved against the encoder's own model of the callee, so an encoder bug is
invisible to them, and ASSUMED clauses are checked by nobody. A concrete
counterexample from a real trace is immune to both.

Report as `experiments/smt/bmc/clause-witness.tsv`:
`summary clause verdict pre_step post_step`.

### Phase 3 — does the reflected term agree with the machine? (catches 1, 3, 4, 7, 9)

The main event. Per span, per trace segment:

1. take the entry state from the trace, assert it as `s0`;
2. pin every summary application from its observed `(pre, post)` pair;
3. `(get-value ...)` the exit register file from `state_exit`;
4. compare against the trace's registers at the stop.

A mismatch names the register and the step. Bisecting the binding chain by
step localises it to one instruction, which is how (9) would surface in
seconds rather than by reading a decoder.

Also compare the derived write log against `writes/<field>.tsv`: an address the
encoder records and the machine never writes (or the reverse) is a footprint
bug, and the footprint posts are where most of the VALIDs live.

### Phase 4 — make it a gate

`scripts/difftest.sh <prog.wl>`: build in /tmp, run traced, phases 1-3, exit
nonzero on any mismatch. Add to `check_all.sh` as a new stage after the axiom
audit. Then every encoder change is checked against the machine before its
verdicts are believed.

## Corpus

`c/tests/*.wl` is 10 programs. That exercises the common arms and nothing else.

Coverage is measurable rather than guessed: Phase 1 already reports which of the
52 spans a corpus enters, so the gap is a list, not an estimate. Fill it by
writing one `.wl` per unreached span — the AST kind that selects the arm is
known, since it is the kind the encoder pins. The error-site arms need programs
that fault; `c/tests/err_*.wl` is the existing shape.

Target: every span entered by at least one trace. Spans that no program can
reach are a finding in themselves and belong in `no-exit.tsv`'s company.

## What this does not do

It tests the ENCODER against the model, not the model against the hardware, and
not the residuals against the spec. A span whose Lean statement asks the wrong
question still asks it. Phase 1 catches a mis-declared span endpoint but not a
mis-stated post — `valuerepr_tag` fired at `exec_stmt`, where `a0` is not a
result buffer, is a category error no trace reveals.

It is also finite. Agreement on a corpus is not agreement on all inputs, and
the summaries make that gap real: a callee pinned by two observed pairs is
unconstrained on every other input. This is a bug FINDER, and on the evidence
of the table at the top it would have found nine of ten.

## Order of work

Phase 0 is the only piece with real unknowns (~a day). Phases 1 and 2 are each
a script over the trace and pay for themselves immediately. Phase 3 is the
largest and depends on 0. Phase 4 is an afternoon once 1-3 pass.

Do 0, 1, 2 first and report. If Phase 1 says the spans are sound and Phase 2
says the clauses hold on real traces, that is already more assurance than the
encoder has ever had.
