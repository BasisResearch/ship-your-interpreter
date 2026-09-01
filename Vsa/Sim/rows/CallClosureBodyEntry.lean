import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureBodyEntry` — the body-entry staging, both bgtz polarities (wave 38)

Task Wave-38, residual span (d), second handoff: the `0x8000332c..0x8000333c`
body-entry staging after `value_null` returns — the machine tail of the
`hFoldToHandoff` bridge (bgtz TAKEN, `cd.body ≠ []` → the body-loop head
`callBodyLoopPC`) and the head of the `emptyBypass` route (bgtz NOT taken ▷
`j 0x80003954`, the `.normal` return path):

```
8000332c  ld a6,32(s5)      0x020ab803   -- a6 := cd->body (block node)
80003330  li s0,0           0x00000413   -- stmt counter := 0  (callee-saved write)
80003334  lw a5,16(a6)      0x01082783   -- a5 := body stmt count
80003338  ▷ bgtz a5 (= blt x0,a5) → 0x80003354 (callBodyLoopPC)   TAKEN: body runs
8000333c  ▷ j 0x80003954                 NOT taken: EMPTY-BODY BYPASS (.normal path)
```

The `bgtz` guard sits in `ChainFacts` (dischargeable from `cd.body ≠ []` resp.
`= []` via the body count the store representation pins).  `li s0,0` writes a
callee-saved — fine for `segToTriple` rows (no ABI claim; the seam frame is the
consumer's concern).

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

/- Body route: `bgtz` TAKEN → the body-loop head `0x80003354`
(`callBodyLoopPC`, the `mExecSeq` entry). -/
#derive_case callClosureBodyEntrySeg chain
  [(0x8000332c#64, 0x020ab803#32),  -- ld a6,32(s5)
   (0x80003330#64, 0x00000413#32),  -- li s0,0
   (0x80003334#64, 0x01082783#32)]  -- lw a5,16(a6)
    terminator ⟨0x80003338#64, 0x00f04e63#32, 0x63#8, 0x4e#8, 0xf0#8, 0x00#8,
      .br bop.BLT true, 0, 15, 0x001C#13, 0#21, 0#12⟩

#print axioms callClosureBodyEntrySeg_seg

/- Empty-body route: `bgtz` NOT taken ▷ `j 0x80003954` (the `.normal` return
path, the `emptyBypass` field's machine head). -/
#derive_case callClosureBodyBypassSeg chain
  [(0x8000332c#64, 0x020ab803#32),  -- ld a6,32(s5)
   (0x80003330#64, 0x00000413#32),  -- li s0,0
   (0x80003334#64, 0x01082783#32)]  -- lw a5,16(a6)
    terminator ⟨0x80003338#64, 0x00f04e63#32, 0x63#8, 0x4e#8, 0xf0#8, 0x00#8,
      .br bop.BLT false, 0, 15, 0x001C#13, 0#21, 0#12⟩ ;;
  []
    terminator ⟨0x8000333c#64, 0x6180006f#32, 0x6f#8, 0x00#8, 0x80#8, 0x61#8,
      .j, 0, 0, 0#13, 0x00618#21, 0#12⟩

#print axioms callClosureBodyBypassSeg_seg

/-- The shared entry pin list: `x21` (s5 = the closure record; `cd->body` at
`32(s5)`). -/
def callClosureBodyEntryL (s5v : BitVec 64) : GRegs := [(21, s5v)]

/-- The body-route post: parked at `callBodyLoopPC = 0x80003354` (the
`mExecSeq`/`BodyHandoff` entry), memory unchanged (this span stores nothing),
the computed pins (`s0 = 0`, `a6` = the body node, `a5` = the count)
exposed. -/
def CallClosureBodyEntryPost (s5v : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureBodyEntrySeg
    (SegEvalState.init (callClosureBodyEntryL s5v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80003354#64 ∧
  GHolds c.σ (evalBlocks callClosureBodyEntrySeg
    (SegEvalState.init (callClosureBodyEntryL s5v) lds)).regs

/-- The bypass-route post: parked at `0x80003954` (the `.normal` return
path). -/
def CallClosureBodyBypassPost (s5v : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureBodyBypassSeg
    (SegEvalState.init (callClosureBodyEntryL s5v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80003954#64 ∧
  GHolds c.σ (evalBlocks callClosureBodyBypassSeg
    (SegEvalState.init (callClosureBodyEntryL s5v) lds)).regs

/-- **`callClosureBodyEntryRow`** — the body route as a `Triple`
(`segToTriple`), landing at `callBodyLoopPC`. -/
theorem callClosureBodyEntryRow (s5v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureBodyEntrySeg (callClosureBodyEntryL s5v) lds 0x8000332c#64 m0)
      (CallClosureBodyEntryPost s5v lds m0) := by
  apply segToTriple callClosureBodyEntrySeg (callClosureBodyEntryL s5v)
    lds 0x8000332c#64 m0 (CallClosureBodyEntryPost s5v lds m0)
    (by have h : keysG (callClosureBodyEntryL s5v) = [21] := rfl
        rw [h]
        show ChainOK 0x8000332c#64 [21] callClosureBodyEntrySeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x8000332c#64
      (SegEvalState.init (callClosureBodyEntryL s5v) lds) callClosureBodyEntrySeg)
    = some 0x80003354#64
  rfl

#print axioms callClosureBodyEntryRow

/-- **`callClosureBodyBypassRow`** — the empty-body route as a `Triple`
(`segToTriple`), landing at the `.normal` path `0x80003954`. -/
theorem callClosureBodyBypassRow (s5v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureBodyBypassSeg (callClosureBodyEntryL s5v) lds 0x8000332c#64 m0)
      (CallClosureBodyBypassPost s5v lds m0) := by
  apply segToTriple callClosureBodyBypassSeg (callClosureBodyEntryL s5v)
    lds 0x8000332c#64 m0 (CallClosureBodyBypassPost s5v lds m0)
    (by have h : keysG (callClosureBodyEntryL s5v) = [21] := rfl
        rw [h]
        show ChainOK 0x8000332c#64 [21] callClosureBodyBypassSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x8000332c#64
      (SegEvalState.init (callClosureBodyEntryL s5v) lds) callClosureBodyBypassSeg)
    = some 0x80003954#64
  rfl

#print axioms callClosureBodyBypassRow

end Vsa.Sim
