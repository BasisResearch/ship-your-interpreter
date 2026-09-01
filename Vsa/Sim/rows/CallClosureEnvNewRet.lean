import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureEnvNewRet` — the env_new return staging, both blez polarities (wave 38)

Task Wave-38, residual span (d), first handoff: the `0x800032c0..0x800032d8`
env_new-return staging — the machine body of the `hEnvNewToFold` /
`hNoParams` bridges (`callClosureEntrySplice`, `rows/CallClosureSplice.lean`).
The `blez a5 @0x800032c8` splits the two routes, so this is a TWO-POLARITY seg
family (the `StrCmpSignTail` pattern):

```
800032c0  ld a5,0(sp)       0x00013783   -- reload argc (spilled by the dispatch stage)
800032c4  mv s3,a0          0x00050993   -- RESEAT s3 := the fresh frame ptr  (callee-saved!)
800032c8  ▷ blez a5 (= bge x0,a5) → 0x80003324   TAKEN: zero-param bypass (hNoParams)
-- fall-through (params exist, hEnvNewToFold):
800032cc  sd s6,1024(sp)    0x41613023   -- SPILL caller s6
800032d0  addi s0,sp,240    0x0f010413   -- cursor := arg vector base  (callee-saved write!)
800032d4  slli s6,a5,0x3    0x00379b13   -- s6 := 8·argc  (the fold bound; callee-saved write!)
800032d8  li a5,0           0x00000793   -- byte index := 0
                             → 0x800032dc (callParamFoldPC, the fold head)
```

Both segs write callee-saved registers (`s3`; the fold route also `s0`/`s6`) —
fine for `segToTriple` rows (no ABI claim is made; the reseated values are in
the exposed post bundle, and the seam frame is the consumer's `CallFrameMeta`
concern).  The `blez` guard obligations sit in `ChainFacts` (dischargeable
from `argc = 0` resp. `argc > 0` — the `(cd.params.zip vs).length` split the
entry splice already cases on).

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

/- Zero-param bypass polarity: `blez` TAKEN → `0x80003324` (the value_null
staging, the `hNoParams` route). -/
#derive_case callClosureEnvNewRetBypassSeg chain
  [(0x800032c0#64, 0x00013783#32),  -- ld a5,0(sp)
   (0x800032c4#64, 0x00050993#32)]  -- mv s3,a0  (addi x19,x10,0)
    terminator ⟨0x800032c8#64, 0x04f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x04#8,
      .br bop.BGE true, 0, 15, 0x005C#13, 0#21, 0#12⟩

#print axioms callClosureEnvNewRetBypassSeg_seg

/- Fold polarity: `blez` NOT taken, fall through the fold init to the fold
head `0x800032dc = callParamFoldPC` (the `hEnvNewToFold` route). -/
#derive_case callClosureEnvNewRetFoldSeg chain
  [(0x800032c0#64, 0x00013783#32),  -- ld a5,0(sp)
   (0x800032c4#64, 0x00050993#32)]  -- mv s3,a0
    terminator ⟨0x800032c8#64, 0x04f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x04#8,
      .br bop.BGE false, 0, 15, 0x005C#13, 0#21, 0#12⟩ ;;
  [(0x800032cc#64, 0x41613023#32),  -- sd s6,1024(sp)
   (0x800032d0#64, 0x0f010413#32),  -- addi s0,sp,240
   (0x800032d4#64, 0x00379b13#32),  -- slli s6,a5,0x3
   (0x800032d8#64, 0x00000793#32)]  -- li a5,0

#print axioms callClosureEnvNewRetFoldSeg_seg

/-- The shared entry pin list: `x2` (sp), `x10` (a0 = the fresh frame ptr from
`env_new_post`), and — for the fold route's `sd s6,1024(sp)` spill — `x22`
(s6, the CALLER's value; its bytes are the `1024(sp)` slot content). -/
def callClosureEnvNewRetL (sp a0v s6v : BitVec 64) : GRegs :=
  [(2, sp), (10, a0v), (22, s6v)]

/-- The bypass-route post: parked at `0x80003324` (the value_null staging),
memory = entry + the write-log (none — this route stores nothing). -/
def CallClosureEnvNewRetBypassPost (sp a0v s6v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureEnvNewRetBypassSeg
    (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80003324#64 ∧
  GHolds c.σ (evalBlocks callClosureEnvNewRetBypassSeg
    (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)).regs

/-- The fold-route post: parked at the fold head `0x800032dc`
(`callParamFoldPC`), memory = entry + the `s6` spill at `1024(sp)`, the
computed pins (incl. `s3 = a0v`, `s0 = sp+240`, `s6 = 8·argc`, `a5 = 0`)
exposed. -/
def CallClosureEnvNewRetFoldPost (sp a0v s6v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureEnvNewRetFoldSeg
    (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800032dc#64 ∧
  GHolds c.σ (evalBlocks callClosureEnvNewRetFoldSeg
    (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)).regs

/-- **`callClosureEnvNewRetBypassRow`** — the zero-param route as a `Triple`
(`segToTriple`). -/
theorem callClosureEnvNewRetBypassRow (sp a0v s6v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureEnvNewRetBypassSeg (callClosureEnvNewRetL sp a0v s6v)
        lds 0x800032c0#64 m0)
      (CallClosureEnvNewRetBypassPost sp a0v s6v lds m0) := by
  apply segToTriple callClosureEnvNewRetBypassSeg (callClosureEnvNewRetL sp a0v s6v)
    lds 0x800032c0#64 m0 (CallClosureEnvNewRetBypassPost sp a0v s6v lds m0)
    (by have h : keysG (callClosureEnvNewRetL sp a0v s6v) = [2, 10, 22] := rfl
        rw [h]
        show ChainOK 0x800032c0#64 [2, 10, 22] callClosureEnvNewRetBypassSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x800032c0#64
      (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)
      callClosureEnvNewRetBypassSeg)
    = some 0x80003324#64
  rfl

#print axioms callClosureEnvNewRetBypassRow

/-- **`callClosureEnvNewRetFoldRow`** — the fold-init route as a `Triple`
(`segToTriple`), landing at `callParamFoldPC`. -/
theorem callClosureEnvNewRetFoldRow (sp a0v s6v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureEnvNewRetFoldSeg (callClosureEnvNewRetL sp a0v s6v)
        lds 0x800032c0#64 m0)
      (CallClosureEnvNewRetFoldPost sp a0v s6v lds m0) := by
  apply segToTriple callClosureEnvNewRetFoldSeg (callClosureEnvNewRetL sp a0v s6v)
    lds 0x800032c0#64 m0 (CallClosureEnvNewRetFoldPost sp a0v s6v lds m0)
    (by have h : keysG (callClosureEnvNewRetL sp a0v s6v) = [2, 10, 22] := rfl
        rw [h]
        show ChainOK 0x800032c0#64 [2, 10, 22] callClosureEnvNewRetFoldSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x800032c0#64
      (SegEvalState.init (callClosureEnvNewRetL sp a0v s6v) lds)
      callClosureEnvNewRetFoldSeg)
    = some 0x800032dc#64
  rfl

#print axioms callClosureEnvNewRetFoldRow

end Vsa.Sim
