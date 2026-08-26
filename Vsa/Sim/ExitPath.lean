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
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)

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

/-- **B1** — parked at main's `jal interp_run` link (`0x800045ec`) with the
interp_run return value `a0 = 1` (the error return), `GoodState`, tick-bounded, and
the console output accumulated so far equal to `out`. -/
def AtMainRet (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800045ec#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
  output c.σ = out

/-- **B2** — parked at crt0's `jal main` link (`0x80000038`, the `j exit`) with the
exit status `a0 = 70` (main's error return), `GoodState`, tick-bounded, and the
console output still equal to `out` (`fprintf(stderr,…)` did not touch `tohost`). -/
def AtCrt0Exit (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80000038#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some (70#64 : BitVec 64) ∧
  output c.σ = out

/-- **B3** — parked at the `_exit` entry (`0x80000180`) with the exit status
`a0 = 70`, `GoodState`, tick-bounded, and the console output still `out`.  From here
the `slli/srli/ori` form the syscall-exit word `(70<<<1)|1` in `a5` and the
`sd a5,tohost` @0x80000190 is the `ExitStorePreExit` site. -/
def AtExitProlog (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80000180#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some (70#64 : BitVec 64) ∧
  output c.σ = out

/-! ## The four segment residuals

Each is a `Triple` for one straight-line span of the decoded control transfer, to be
discharged by decoding that span's instructions (via the `StepObs`/block batteries)
once the exit-path function bytes are pinned in the `Code` module.  They are stated
here as the exact interfaces the composition consumes. -/

/-- **Segment 1 — the interp_run continuation** (`0x80004428 → 0x800045ec`).  From
the setjmp-continuation with `a0 = 1`, the taken `bnez a0` reaches `0x80004508`
(`li s5,1`), the interp_run epilogue restores the callee-saveds and sets `a0 := s5 =
1`, and `ret` returns to main's `jal interp_run` link `0x800045ec`.  `output` is
unchanged (no `tohost` store on this path). -/
def InterpContSeg (out : String) : Prop :=
  Triple
    (fun c => GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) ∧
      c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      output c.σ = out)
    (AtMainRet out)

/-- **Segment 2 — main's error path** (`0x800045ec → 0x80000038`), including the
`fprintf(stderr,…)` call.  The taken `bnez a0` reaches `0x80004600`; the
`fprintf(stderr,…)` writes to the stderr `FILE*` (NOT `tohost`, so `output`/
`sailOutput` are unchanged — this is the `FprintfStderrNeutral` fact, carried in the
postcondition's `output c.σ = out`); `li a0,70` sets the exit status; the main
epilogue `ret`s to crt0's `jal main` link `0x80000038`. -/
def MainErrorSeg (out : String) : Prop :=
  Triple (AtMainRet out) (AtCrt0Exit out)

/-- **Segment 3 — crt0 → exit → _exit entry** (`0x80000038 → 0x80000180`).  The crt0
`j exit` enters `exit`, which runs `__call_exitprocs` and the optional stdio exit
handler (neither writes `tohost`, so `output` is unchanged), then `mv a0,s0` (= 70)
and `jal _exit` reaches the `_exit` entry `0x80000180`. -/
def Crt0ExitSeg (out : String) : Prop :=
  Triple (AtCrt0Exit out) (AtExitProlog out)

/-- **Segment 4 — the `_exit` prologue** (`0x80000180 → the sd a5,tohost` site).  The
`slli/srli/ori` form the syscall-exit word `(70<<<1)|1` in `a5`, `auipc a4` forms the
`tohost` base, and control parks at the `sd a5,tohost` @0x80000190 — the
`ExitStorePreExit` store site with `a5 = (70<<<1)|1`. -/
def ExitPrologSeg (out : String) : Prop :=
  Triple (AtExitProlog out) (ExitStorePreExit out)

/-! ## The composition — `ErrorTailChain` from the four segments

`ErrorTailChain ra0 ExitStorePreExit out` (`Vsa/Sim/ErrorSim.lean`) is a `Triple`
from the setjmp-continuation `{GoodState, tick<2, PC = ra0, x10 = 1}` to
`ExitStorePreExit out`.  We compose the four segment `Triple`s left-to-right with
`Triple.seq`, then `conseq`-strengthen the composed precondition to
`ErrorTailChain`'s (which is exactly Segment 1's precondition, minus the `output`
ghost — supplied by the `∃ out` quantification over the whole chain). -/

/-- The `ErrorTailChain` precondition (the interp_run setjmp-continuation), named so
the entry-output residual and the composition share one shape. -/
def ChainPre (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64)

/-- **`ErrorTailChain` reduced to its four segment residuals.**  Given the four
decoded straight-line segment `Triple`s of the interp_run-cont / main / crt0 / exit
span (`InterpContSeg`, `MainErrorSeg`, `Crt0ExitSeg`, `ExitPrologSeg`) and the
entry-output pinning `hEntryOut` (the accumulated console output at the
setjmp-continuation is `out` — the string the whole `errorTailHalts` reports; it is
NOT named by `ErrorTailChain`'s precondition, which is why it is an explicit
residual, and it is exactly `output c.σ` at the `runtime_error_spec` landing config),
their `Triple.seq` composition is the `ErrorTailChain ra0 ExitStorePreExit out`
residual of `errorTailHalts_exit`, for `ra0 = 0x80004428` (the interp_run
setjmp-continuation the `runtime_error_spec` postcondition lands at).  This
concretizes the span's control structure and the `fprintf` output-neutrality
handling, leaving only the four per-segment machine decodes. -/
theorem errorTailChain_of_segments (out : String)
    (hEntryOut : ∀ c, ChainPre c → output c.σ = out)
    (h1 : InterpContSeg out) (h2 : MainErrorSeg out)
    (h3 : Crt0ExitSeg out) (h4 : ExitPrologSeg out) :
    ErrorTailChain (0x80004428#64 : BitVec 64) ExitStorePreExit out := by
  refine ⟨?_⟩
  -- compose the four segments into one Triple from S1's precondition to ExitStorePreExit.
  have hchain :
      Triple
        (fun c => GoodState c.σ ∧ c.tick < 2 ∧
          c.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) ∧
          c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
          output c.σ = out)
        (ExitStorePreExit out) :=
    Triple.seq h1 (Triple.seq h2 (Triple.seq h3 h4))
  -- strengthen: ErrorTailChain's precondition (no `output` ghost) implies S1's, the
  -- missing `output c.σ = out` supplied by `hEntryOut`.
  exact Triple.conseq hchain
    (fun c hc => ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hEntryOut c hc⟩)
    (fun _ hq => hq)

/-! ## `errorTailHalts` with `ErrorTailChain` supplied from the segments

`errorTailHalts_exit` (`Vsa/Sim/ErrorTail.lean`) is conditional on the single
`ErrorTailChain` residual (plus the `SnprintfContract` and the `runtime_error_spec`
frame geometry).  Supplying `errorTailChain_of_segments` here concretizes it: the
runtime_error → exit(70) chain now rests only on the `SnprintfContract`, the four
decoded segment `Triple`s, the entry-output pinning, and the frame geometry `hre`
(with `ra0 = 0x80004428`, the concrete interp_run setjmp-continuation). -/

/-- **`errorTailHalts` with the exit-path span decomposed.**  The runtime_error →
exit(70) chain, conditional on the `SnprintfContract` `SC`, the four segment
`Triple`s of the interp_run-cont / main / crt0 / exit span (`h1`..`h4`), the
entry-output pinning `hEntryOut`, and the `runtime_error_spec` frame geometry `hre`
at the concrete continuation `ra0 = 0x80004428`.  The `ErrorTailChain` residual is now
supplied concretely by `errorTailChain_of_segments`. -/
theorem errorTailHalts_segments
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp (0x80004428#64 : BitVec 64)
      s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String)
    (hEntryOut : ∀ c, ChainPre c → output c.σ = out)
    (h1 : InterpContSeg out) (h2 : MainErrorSeg out)
    (h3 : Crt0ExitSeg out) (h4 : ExitPrologSeg out)
    (c : Config)
    (hre : GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
      c.σ.mem = m0 ∧
      c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
      c.σ.regs.get? Register.x10 = some inp ∧
      WinRAM (inp + 16#64) ∧
      (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
      (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)) :
    Halts c out 70 :=
  errorTailHalts_exit g inp (0x80004428#64 : BitVec 64)
    s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0 SC out
    (errorTailChain_of_segments out hEntryOut h1 h2 h3 h4) c hre

end Vsa.Sim
