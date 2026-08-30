import Vsa.Sim.ExitPath
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics
import Vsa.Sim.Code.Interp_run

/-!
# Layer 5/6 — the interp_run-continuation segment of `ErrorTailChain`

`Vsa/Sim/ExitPath.lean` reduced the opaque `ErrorTailChain` residual to four
straight-line segment `Triple`s (`InterpContSeg`, `MainErrorSeg`, `Crt0ExitSeg`,
`ExitPrologSeg`).  `Vsa/Sim/ExitPathSeg.lean` already discharged `ExitPrologSeg`.
This file discharges **`InterpContSeg`** — the one segment that is pure
straight-line machine code (register restores + one stack store) terminated by a
`ret`, with NO external function calls.  It is the segment the task brief flags as
the payoff of the `seg_eval`/block-reflection layer: the ≈16-instruction restore
span that a hand-threaded `StepObs` chain would blow up to ≈900 lines collapses
to ONE `bblocks_sound_bt` application over a 2-block chain.

## The decoded span (`0x80004428 → 0x800045ec`, from `experiments/disasm.txt`)

```
── interp_run continuation ──────────────────────────────────────────────────
80004428:  bnez a0,80004508        -- a0 = 1 ⇒ TAKEN → 0x80004508   (block 0)
80004508:  ld   a5,0(sp)                                             (block 1)
8000450c:  li   s5,1               -- return value s5 := 1
80004510:  sw   zero,8(a5)         -- clears the setjmp `active` flag
80004514:  ld   ra,168(sp)         -- epilogue restores: ra ← 168(sp) = 0x800045ec
80004518:  ld   s0,160(sp)
8000451c:  ld   s1,152(sp)
80004520:  ld   s2,144(sp)
80004524:  ld   s3,136(sp)
80004528:  ld   s4,128(sp)
8000452c:  ld   s6,112(sp)
80004530:  mv   a0,s5              -- a0 := s5 = 1  (the interp_run error return)
80004534:  ld   s5,120(sp)
80004538:  addi sp,sp,176
8000453c:  ret                     -- jr ra → 0x800045ec (main's jal interp_run link)
```

## Structure

Two basic blocks:

* **B0**: empty body, terminator `bnez a0,0x80004508` — TAKEN because `a0 = 1`
  (the error return; `guardB BNE 1 0 = true`).
* **B1**: the 13-instruction restore body (`ld`/`li`/`sw`/`ld…`/`mv`/`ld`/`addi`)
  terminated by `ret` (`jr ra`).

The nine `ld`s read the interp_run spill frame; the single `sw zero,8(a5)`
clears the setjmp buffer's `active` flag.  All of these read/write concrete
stack addresses whose *values* (the spilled register contents, in particular the
saved `ra = 0x800045ec`) and *geometry* (the store lands above the HTIF window;
the loads are 8-aligned in RAM; the restored `ra` is 4-aligned) are frame facts
the `interp_run` prologue established but that `InterpContSeg`'s precondition does
not itself name.  They are bundled into the single named residual
`InterpContFrame` — the exit-70 analogue of `ExitPathSeg`'s `ExitPrologGeom`
(the `_exit`-code/HTIF residual) and of the `runtime_error_spec` frame geometry
that `errorTailHalts_segments` already carries as `hre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The 2-block chain -/

/-- Block 0: empty body, `bnez a0,0x80004508` (`bne a0,x0`) — TAKEN (`a0 = 1`).
Word `0e051063`, bytes `63 10 05 0e`, imm13 `0x0e0` (= `0x80004508 - 0x80004428`). -/
def icB0 : BBlock :=
  { body := [],
    term := some ⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8,
      .br bop.BNE true, 10, 0, 0x00e0#13, 0#21, 0#12⟩ }

/-- Block 1: the interp_run epilogue restore body, terminated by `ret` (`jr ra`).

Body (13 instructions, program order):
`ld a5,0(sp)`; `li s5,1`; `sw zero,8(a5)`; `ld ra,168(sp)`; `ld s0,160(sp)`;
`ld s1,152(sp)`; `ld s2,144(sp)`; `ld s3,136(sp)`; `ld s4,128(sp)`;
`ld s6,112(sp)`; `mv a0,s5`; `ld s5,120(sp)`; `addi sp,sp,176`.
Terminator: `ret` (`jr ra`), word `00008067`, bytes `67 80 00 00`. -/
def icB1 : BBlock :=
  { body :=
      [ -- ld a5,0(sp)     word 00013783  bytes 83 37 01 00  rd=15 rs1=2 off=0x000
        ⟨0x80004508#64, 0x00013783#32, 0x83#8, 0x37#8, 0x01#8, 0x00#8, .ld, 15, 2, 0, 0x000#12⟩,
        -- li s5,1         word 00100a93  bytes 93 0a 10 00  addi s5,x0,1
        ⟨0x8000450c#64, 0x00100a93#32, 0x93#8, 0x0a#8, 0x10#8, 0x00#8, .addi, 21, 0, 0, 0x001#12⟩,
        -- sw zero,8(a5)   word 0007a423  bytes 23 a4 07 00  rs2=0 rs1=15 off=0x008 w4
        ⟨0x80004510#64, 0x0007a423#32, 0x23#8, 0xa4#8, 0x07#8, 0x00#8, .sw, 0, 15, 0, 0x008#12⟩,
        -- ld ra,168(sp)   word 0a813083  bytes 83 30 81 0a  rd=1 rs1=2 off=0x0a8
        ⟨0x80004514#64, 0x0a813083#32, 0x83#8, 0x30#8, 0x81#8, 0x0a#8, .ld, 1, 2, 0, 0x0a8#12⟩,
        -- ld s0,160(sp)   word 0a013403  bytes 03 34 01 0a  rd=8 rs1=2 off=0x0a0
        ⟨0x80004518#64, 0x0a013403#32, 0x03#8, 0x34#8, 0x01#8, 0x0a#8, .ld, 8, 2, 0, 0x0a0#12⟩,
        -- ld s1,152(sp)   word 09813483  bytes 83 34 81 09  rd=9 rs1=2 off=0x098
        ⟨0x8000451c#64, 0x09813483#32, 0x83#8, 0x34#8, 0x81#8, 0x09#8, .ld, 9, 2, 0, 0x098#12⟩,
        -- ld s2,144(sp)   word 09013903  bytes 03 39 01 09  rd=18 rs1=2 off=0x090
        ⟨0x80004520#64, 0x09013903#32, 0x03#8, 0x39#8, 0x01#8, 0x09#8, .ld, 18, 2, 0, 0x090#12⟩,
        -- ld s3,136(sp)   word 08813983  bytes 83 39 81 08  rd=19 rs1=2 off=0x088
        ⟨0x80004524#64, 0x08813983#32, 0x83#8, 0x39#8, 0x81#8, 0x08#8, .ld, 19, 2, 0, 0x088#12⟩,
        -- ld s4,128(sp)   word 08013a03  bytes 03 3a 01 08  rd=20 rs1=2 off=0x080
        ⟨0x80004528#64, 0x08013a03#32, 0x03#8, 0x3a#8, 0x01#8, 0x08#8, .ld, 20, 2, 0, 0x080#12⟩,
        -- ld s6,112(sp)   word 07013b03  bytes 03 3b 01 07  rd=22 rs1=2 off=0x070
        ⟨0x8000452c#64, 0x07013b03#32, 0x03#8, 0x3b#8, 0x01#8, 0x07#8, .ld, 22, 2, 0, 0x070#12⟩,
        -- mv a0,s5        word 000a8513  bytes 13 85 0a 00  addi a0,s5,0
        ⟨0x80004530#64, 0x000a8513#32, 0x13#8, 0x85#8, 0x0a#8, 0x00#8, .addi, 10, 21, 0, 0x000#12⟩,
        -- ld s5,120(sp)   word 07813a83  bytes 83 3a 81 07  rd=21 rs1=2 off=0x078
        ⟨0x80004534#64, 0x07813a83#32, 0x83#8, 0x3a#8, 0x81#8, 0x07#8, .ld, 21, 2, 0, 0x078#12⟩,
        -- addi sp,sp,176  word 0b010113  bytes 13 01 01 0b  rd=2 rs1=2 off=0x0b0
        ⟨0x80004538#64, 0x0b010113#32, 0x13#8, 0x01#8, 0x01#8, 0x0b#8, .addi, 2, 2, 0, 0x0b0#12⟩ ],
    term := some ⟨0x8000453c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩ }

/-- The interp_run-continuation chain. -/
def interpContChain : List BBlock := [icB0, icB1]

/-! ## The frame residual

`InterpContSeg`'s precondition names only `{GoodState, tick<2, PC = 0x80004428,
a0 = 1, output = out}`.  The restore span additionally needs, of the interp_run
spill frame `sp = spv` on entry:

* the nine `ld` byte pins (the spilled register images) and, for the `ld ra`,
  that the spilled `ra` reads back as `0x800045ec` (main's `jal interp_run`
  link) — supplied as the load byte-lists `ldsIC` with the `ra` slot pinned;
* the load geometry (each `sp + off` is in RAM, 8-aligned, disjoint from the
  HTIF window);
* the store geometry for `sw zero,8(a5)` (`a5 + 8` in RAM above the HTIF
  window), where `a5` is the value read at `0(sp)`.

We package exactly the `ChainFacts` obligation the block lemma consumes, plus the
pin `sp = spv`.  This is the exit-70 analogue of `ExitPathSeg.ExitPrologGeom`. -/

/-- The load byte-lists for `icB1`'s nine `ld`s, in program order
(`a5, ra, s0, s1, s2, s3, s4, s6, s5`), with the `ra` slot pinned to the LE
bytes of `0x800045ec`.  The other eight are arbitrary (the restored callee-saveds
are not observed downstream). -/
def ldsIC (a5b s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8)) :
    List (List (BitVec 8)) :=
  [ a5b,
    [0xec#8, 0x45#8, 0x00#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8],  -- ra = 0x800045ec
    s0b, s1b, s2b, s3b, s4b, s6b, s5b ]

/-- The frame residual: the block lemma's `ChainFacts` for `interpContChain`
from the entry config, over the concrete `sp = spv`, `a0 = 1` pin lists, plus the
`Interp_run` code being loaded.  Existentially binds the eight unobserved
spill images. -/
def InterpContFrame (out : String) : Prop :=
  ∀ c : Config, (GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
        output c.σ = out) →
    Interp_runLoaded c.σ.mem ∧
    ∃ (spv : BitVec 64) (a5b s0b s1b s2b s3b s4b s6b s5b : List (BitVec 8)),
      c.σ.regs.get? Register.x2 = some spv ∧
      ChainFacts c.σ.mem c.σ.mem [(10, (1#64 : BitVec 64)), (2, spv)]
        (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b) interpContChain

/-! ## `InterpContSeg` discharged (conditional on `InterpContFrame`) -/

/-- **`InterpContSeg` discharged.**  From the interp_run setjmp-continuation with
`a0 = 1`, the taken `bnez` + the epilogue-restore chain + `ret` land at main's
`jal interp_run` link `0x800045ec` with `a0 = 1` (the interp_run error return),
`GoodState`, tick-bounded, and `output` unchanged (no `tohost` store on the
path — the `sw zero,8(a5)` writes the setjmp buffer, above RAM's HTIF window),
i.e. `AtMainRet out`.  ONE `bblocks_sound_bt` over the 2-block chain, conditional
only on the `InterpContFrame` spill-frame geometry. -/
theorem interpContSeg_of (out : String) (hframe : InterpContFrame out) :
    Triple
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (0x80004428#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
        output c.σ = out)
      (AtMainRet out) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hx10, hout⟩ := hpre
  obtain ⟨hmem, spv, a5b, s0b, s1b, s2b, s3b, s4b, s6b, s5b, hsp, hcf⟩ :=
    hframe c ⟨hG, htick, hpc, hx10, hout⟩
  obtain ⟨vm, hmi⟩ := hG.minstret
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, _hframe⟩ :=
    bblocks_sound_bt interpContChain c.σ c.tick c.steps (0x80004428#64) vm
      [(10, (1#64 : BitVec 64)), (2, spv)] (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b)
      hG hpc hmi ⟨hx10, hsp, trivial⟩
      (show KeysOK [10, 2] by decide)
      hcf
      (show ChainOK (0x80004428#64) [10, 2] interpContChain by decide)
      htick
  -- read out the final PC = the restored ra target = 0x800045ec.
  refine ⟨⟨σ', i', c.steps + chainLen interpContChain⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · exact hG'
  · exact hi'
  · -- PC = chainEndPC … = tgtPCT ret (runChain …) = 0x800045ec
    -- The chain ends in `jr ra`; `ra` (key 1) is written by the `ld ra` in `icB1`,
    -- pinned to `0x800045ec` via `ldsIC`, INDEPENDENT of the load base `spv`
    -- (key 2).  So the end PC reduces by `rfl` past the abstract `spv`.
    -- `jr ra`: the terminator target is `srcVal 1` of the run state, i.e. key 1
    -- (`ra`) written by the `ld ra` in `icB1.body` to the pinned `ra` bytes.
    -- Loads write only from their byte-list (`wvalM` for a load ignores the base
    -- register value), so `spv` (key 2) stays an inert association and the key-1
    -- lookup finds the `ld ra` write first, never reaching it.  We first pin the
    -- `srcVal 1` of the run state (`runChain`, exactly the `hlk` shape below that
    -- reduces by `rfl`), then discharge the `tgtPCT`/`update` wrapper.
    -- Pin the key-1 (`ra`) value of the run state — the `runGM` nesting that
    -- `chainEndPC` unfolds to (`icB0.body = []` ⇒ inner `runGM` is `id`).  `simp`
    -- reduces the assoc-list scan (which `rfl` alone gives up on for the 13-deep
    -- fold); the key-1 lookup finds the `ld ra` write, independent of `spv`.
    have hra : srcVal 1 (runGM icB1.body (runGM icB0.body
        [(10, (1#64 : BitVec 64)), (2, spv)] (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b))
        (ldsRunM icB0.body (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b)))
        = (0x800045ec#64 : BitVec 64) := by
      simp only [icB0, icB1, ldsIC, runGM, stepGM, stepLdsM, wvalM, eraseG, srcVal,
        lookupG, List.headD, List.tail, ldsRunM]
      rfl
    have : chainEndPC (0x80004428#64) [(10, (1#64 : BitVec 64)), (2, spv)]
        (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b) interpContChain = (0x800045ec#64 : BitVec 64) := by
      -- `chainEndPC … = tgtPCT (jr ra) (runGM …) = update (srcVal 1 (runGM …) + 0) 0`.
      show BitVec.update (srcVal 1 (runGM icB1.body (runGM icB0.body
        [(10, (1#64 : BitVec 64)), (2, spv)] (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b))
        (ldsRunM icB0.body (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b)))
        + sign_extend (m := 64) (0#12)) 0 0#1 = _
      rw [hra]
      apply BitVec.eq_of_toNat_eq
      rfl
    rw [this] at hpc'
    exact hpc'
  · -- a0 = 1: the `mv a0,s5` copied s5 = 1 (li s5,1); read from runChain via lookupG.
    have hlk : lookupG 10 (runChain interpContChain [(10, (1#64 : BitVec 64)), (2, spv)]
        (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b)) = some (1#64 : BitVec 64) := by
      rfl
    have := gholds_lookup (runChain interpContChain [(10, (1#64 : BitVec 64)), (2, spv)]
      (ldsIC a5b s0b s1b s2b s3b s4b s6b s5b)) hGH hlk
    exact this
  · -- output unchanged.
    unfold output; rw [hout']; unfold output at hout; exact hout

#print axioms interpContSeg_of

end Vsa.Sim
