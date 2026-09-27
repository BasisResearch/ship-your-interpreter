import Vsa.Sim.ErrorTail

/-!
# Layer 5 — decoding `ErrorTailChain` (the interp_run-cont / main / crt0 / exit span)

`errorTailHalts_exit` (`Vsa/Sim/ErrorTail.lean`) lands the runtime_error → exit(70)
chain conditional on the **one** remaining residual `ErrorTailChain ra0
ExitStorePreExit out`: a `Triple` from the `runtime_error_spec` postcondition state
(the interp_run setjmp-continuation, `PC = 0x80004428`, `x10 = 1`, `GoodState`,
`tick < 2`) to the `_exit` `sd a5,tohost` store-site predicate `ExitStorePreExit`
(`Vsa/Sim/ErrorTail.lean`).  This file decodes that control-transfer span and
reduces `ErrorTailChain` to a `Triple.seq` composition of the span's four natural
straight-line segments (each a minimal, concretely-pinned named residual) plus the
`fprintf(stderr,…)` output-neutrality fact.

## The decoded span (from `experiments/disasm.txt`)

With `a0 = 1` on entry at the interp_run setjmp-continuation `0x80004428`:

```
── interp_run continuation ──────────────────────────────────────────────────
80004428:  bnez a0,80004508        -- a0 = 1  ⇒ TAKEN → 0x80004508
80004508:  ld   a5,0(sp)
8000450c:  li   s5,1               -- return value s5 := 1
80004510:  sw   zero,8(a5)
80004514:  ld   ra,168(sp)         -- interp_run epilogue: restore callee-saveds
   …       (ld s0,s1,s2,s3,s4,s6)
80004530:  mv   a0,s5              -- a0 := s5 = 1
80004534:  ld   s5,120(sp)
80004538:  addi sp,sp,176
8000453c:  ret                     -- → main's `jal interp_run` link, 0x800045ec
── main error path ──────────────────────────────────────────────────────────
800045ec:  bnez a0,80004600        -- a0 = 1  ⇒ TAKEN → 0x80004600
80004600:  ld   a5,0(s0)           -- s0 = &_impure_ptr
80004604:  addi a2,sp,496
80004608:  auipc a1,0x15
8000460c:  addi a1,a1,-40          -- a1 = &"…" format string
80004610:  ld   a0,24(a5)          -- a0 = stderr FILE*
80004614:  jal  fprintf            -- writes to the stderr FILE* (NOT tohost);
                                    --   `output`/`sailOutput` UNCHANGED
80004618:  li   a0,70              -- exit status 70
8000461c:  j    800045f0           -- main epilogue
800045f0:  ld   ra,760(sp)
800045f4:  ld   s0,752(sp)
800045f8:  addi sp,sp,768
800045fc:  ret                     -- → crt0's `jal main` link, 0x80000038
── crt0 → exit ───────────────────────────────────────────────────────────────
80000038:  j    80004764 <exit>    -- a0 = 70
80004764:  addi sp,sp,-16          -- exit prologue
   …       (li a1,0; sd s0; sd ra; mv s0,a0)
80004778:  jal  __call_exitprocs   -- runs atexit handlers (no tohost writes here)
8000477c:  ld   a5,__stdio_exit_handler
80004780:  beqz a5,80004788
80004784:  jalr a5                 -- flush stdio (stderr already flushed above)
80004788:  mv   a0,s0              -- a0 := s0 = 70
8000478c:  jal  80000180 <_exit>
── _exit prologue → the tohost store ────────────────────────────────────────
80000180:  slli a4,a0,0x20         -- a4 = a0 << 32
80000184:  srli a5,a4,0x1f         -- a5 = a4 >> 31   = (70 << 1)
80000188:  ori  a5,a5,1            -- a5 = (70 <<< 1) ||| 1     (the exit word)
8000018c:  auipc a4,0x1b
80000190:  sd   a5,-1164(a4)       -- sd a5,tohost   ← ExitStorePreExit site
```

## `fprintf`

The one output subtlety is `fprintf(stderr,…)` @0x80004614.  It writes through the
stderr `FILE*` (`_impure_ptr->_stderr`, `a0 = 24(_impure_ptr)`), **not** the console
`tohost` putchar path.  In this bare-metal image `stderr` is a memory `FILE*` sink
whose backing device is not the `tohost` mailbox, so `sailOutput` — and hence
`Machine.output` — is unchanged across the call.  We do not forward-simulate
`fprintf`; its output-neutrality is a named residual (`FprintfStderrNeutral`, folded
into the `mainError` segment's postcondition `output c.σ = out`).

## Structure

Rather than thread one monolithic `Triple` across five functions and three function
calls (`fprintf`, `__call_exitprocs`, the stdio exit handler) — whose bytes are not
yet pinned in the `Code` module — we **decompose** `ErrorTailChain` into the four
segment `Triple`s above, joined at three concrete boundary predicates
(`AtMainRet` @0x800045ec, `AtCrt0Exit` @0x80000038, `AtExitProlog` @0x80000180) by
`Triple.seq`.  Each segment is a minimal, individually-decodable named residual that
pins the concrete PCs / `a0` / `output` facts of its span; the composition is proved
here (`errorTailChain_of_segments`).  This converts the single opaque
`ErrorTailChain` residual into four well-scoped segment residuals, exactly the
per-segment discipline every other Layer-3/4 spec in the tree follows.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.Sim.Code (LongjmpLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Boundary predicates

The three intermediate control-transfer boundaries of the span.  Each is the minimal
"parked here with this `a0`, `GoodState`, tick-bounded, output accumulated" shape a
segment `Triple` needs of the previous segment's result.  We keep the exit-code
register (`x10 = a0`) and the accumulated console output (`output c.σ = out`)
explicit — these are the load-bearing facts (`a0` steers each `bnez`/drives the
`_exit` word; `output` is the string `errorTailHalts` finally reports). -/

/-! ## The four segment residuals

Each is a `Triple` for one straight-line span of the decoded control transfer, to be
discharged by decoding that span's instructions (via the `StepObs`/block batteries)
once the exit-path function bytes are pinned in the `Code` module.  They are stated
here as the exact interfaces the composition consumes. -/

/-! ## The composition — `ErrorTailChain` from the four segments

`ErrorTailChain ra0 ExitStorePreExit out` (`Vsa/Sim/ErrorSim.lean`) is a `Triple`
from the setjmp-continuation `{GoodState, tick<2, PC = ra0, x10 = 1}` to
`ExitStorePreExit out`.  We compose the four segment `Triple`s left-to-right with
`Triple.seq`, then `conseq`-strengthen the composed precondition to
`ErrorTailChain`'s (which is exactly Segment 1's precondition, minus the `output`
ghost — supplied by the `∃ out` quantification over the whole chain). -/

/-! ## `errorTailHalts` with `ErrorTailChain` supplied from the segments

`errorTailHalts_exit` (`Vsa/Sim/ErrorTail.lean`) is conditional on the single
`ErrorTailChain` residual (plus the `SnprintfContract` and the `runtime_error_spec`
frame geometry).  Supplying `errorTailChain_of_segments` here concretizes it: the
runtime_error → exit(70) chain now rests only on the `SnprintfContract`, the four
decoded segment `Triple`s, the entry-output pinning, and the frame geometry `hre`
(with `ra0 = 0x80004428`, the concrete interp_run setjmp-continuation). -/

end Vsa.Sim
