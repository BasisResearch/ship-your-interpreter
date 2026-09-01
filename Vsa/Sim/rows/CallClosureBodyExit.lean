import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureBodyExit` — the body-exit `beqz` split + the loop-exit check (wave 40)

Wave-40 residual span (found in the ret-route audit): the machine between the
body IH's exit (`SegExit@callBodyRetPC = 0x80003378` — the config is parked AT
the `beqz`) and the two return arms.  The `beqz a0` decides on the body's
status word (`BodyStatusABI`):

```
80003378  ▷ beqz a0 → 0x80003340        TAKEN (a0=0, status .normal): loop-exit check
-- .normal continuation (the loop-exit re-check after the LAST statement):
80003340  ld a6,0(sp)       0x00013803   -- reload the body block node
80003344  addi s0,s0,1      0x00140413   -- stmt counter += 1  (callee-saved write)
80003348  sext.w a5,s0      0x0004079b
8000334c  lw a4,16(a6)      0x01082703   -- body stmt count
80003350  ▷ bge a5,a4 → 0x80003954      TAKEN (counter = count, all statements done):
                                          the .normal return path (callClosureNormalDepthSeg)
-- .ret v: beqz NOT taken (a0=3) → 0x8000337c (callClosureRetClassSeg)
```

The `.normal` polarity models the LAST loop-exit re-check (`s0 = count - 1` at
the IH exit, so the bumped counter equals the count and the `bge` is TAKEN —
the guard sits in `ChainFacts`, off the loop invariant the `mExecSeq`-side seq
rows carry).  Mid-loop back-edges (`bge` NOT taken → `0x80003354`) are INSIDE
the body IH's span and are the seq rows' concern, not this row's.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- `.ret v` polarity: `beqz` NOT taken (a0 = 3) → the classification span
`0x8000337c` (`callClosureRetClassSeg`). -/
#derive_case callClosureBodyExitRetSeg chain
  []
    terminator ⟨0x80003378#64, 0xfc0504e3#32, 0xe3#8, 0x04#8, 0x05#8, 0xfc#8,
      .br bop.BEQ false, 10, 0, 0x1FC8#13, 0#21, 0#12⟩

#print axioms callClosureBodyExitRetSeg_seg

/- `.normal` polarity: `beqz` TAKEN (a0 = 0) → the loop-exit re-check, `bge`
TAKEN (all statements done) → the `.normal` return path `0x80003954`
(`callClosureNormalDepthSeg`). -/
#derive_case callClosureBodyExitNormalSeg chain
  []
    terminator ⟨0x80003378#64, 0xfc0504e3#32, 0xe3#8, 0x04#8, 0x05#8, 0xfc#8,
      .br bop.BEQ true, 10, 0, 0x1FC8#13, 0#21, 0#12⟩ ;;
  [(0x80003340#64, 0x00013803#32),  -- ld a6,0(sp)
   (0x80003344#64, 0x00140413#32),  -- addi s0,s0,1
   (0x80003348#64, 0x0004079b#32),  -- sext.w a5,s0
   (0x8000334c#64, 0x01082703#32)]  -- lw a4,16(a6)
    terminator ⟨0x80003350#64, 0x60e7d263#32, 0x63#8, 0xd2#8, 0xe7#8, 0x60#8,
      .br bop.BGE true, 15, 14, 0x0604#13, 0#21, 0#12⟩

#print axioms callClosureBodyExitNormalSeg_seg

/-- The shared entry pin list: `x10` (a0, the body's status word — the `beqz`
source), `x2` (sp — the `.normal` route's `0(sp)` reload), `x8` (s0, the stmt
counter the `.normal` route bumps). -/
def callClosureBodyExitL (a0v sp s0v : BitVec 64) : GRegs :=
  [(10, a0v), (2, sp), (8, s0v)]

/-- The `.ret` post: parked at the classification entry `0x8000337c`, memory
unchanged. -/
def CallClosureBodyExitRetPost (a0v sp s0v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureBodyExitRetSeg
    (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000337c#64 ∧
  GHolds c.σ (evalBlocks callClosureBodyExitRetSeg
    (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)).regs

/-- The `.normal` post: parked at the `.normal` return path `0x80003954`,
memory unchanged, the bumped counter exposed. -/
def CallClosureBodyExitNormalPost (a0v sp s0v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureBodyExitNormalSeg
    (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80003954#64 ∧
  GHolds c.σ (evalBlocks callClosureBodyExitNormalSeg
    (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)).regs

/-- **`callClosureBodyExitRetRow`** — the `.ret v` `beqz` fall-through as a
`Triple` (`segToTriple`). -/
theorem callClosureBodyExitRetRow (a0v sp s0v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureBodyExitRetSeg (callClosureBodyExitL a0v sp s0v)
        lds 0x80003378#64 m0)
      (CallClosureBodyExitRetPost a0v sp s0v lds m0) := by
  apply segToTriple callClosureBodyExitRetSeg (callClosureBodyExitL a0v sp s0v)
    lds 0x80003378#64 m0 (CallClosureBodyExitRetPost a0v sp s0v lds m0)
    (by have h : keysG (callClosureBodyExitL a0v sp s0v) = [10, 2, 8] := rfl
        rw [h]
        show ChainOK 0x80003378#64 [10, 2, 8] callClosureBodyExitRetSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003378#64
      (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)
      callClosureBodyExitRetSeg)
    = some 0x8000337c#64
  rfl

#print axioms callClosureBodyExitRetRow

/-- **`callClosureBodyExitNormalRow`** — the `.normal` loop-exit route as a
`Triple` (`segToTriple`), landing at the `.normal` return path. -/
theorem callClosureBodyExitNormalRow (a0v sp s0v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureBodyExitNormalSeg (callClosureBodyExitL a0v sp s0v)
        lds 0x80003378#64 m0)
      (CallClosureBodyExitNormalPost a0v sp s0v lds m0) := by
  apply segToTriple callClosureBodyExitNormalSeg (callClosureBodyExitL a0v sp s0v)
    lds 0x80003378#64 m0 (CallClosureBodyExitNormalPost a0v sp s0v lds m0)
    (by have h : keysG (callClosureBodyExitL a0v sp s0v) = [10, 2, 8] := rfl
        rw [h]
        show ChainOK 0x80003378#64 [10, 2, 8] callClosureBodyExitNormalSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003378#64
      (SegEvalState.init (callClosureBodyExitL a0v sp s0v) lds)
      callClosureBodyExitNormalSeg)
    = some 0x80003954#64
  rfl

#print axioms callClosureBodyExitNormalRow

end Vsa.Sim
