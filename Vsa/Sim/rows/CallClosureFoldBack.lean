import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureFoldBack` — the params-fold back-edge, both bne polarities (wave 40)

Wave-40 residual span: the `0x80003314..0x8000331c` fold back-edge after
`env_define` returns — the machine tail of ONE `callParamFoldSeam_of` iteration
(`rows/CallClosureSplice.lean` §2, its `hBack` piece).  The
`bne s6,a5 @0x8000331c` splits the two routes, so this is a TWO-POLARITY seg
family (the `CallClosureEnvNewRet` pattern):

```
80003314  ld a5,0(sp)       0x00013783   -- reload the byte index (spilled at 0x80003300)
80003318  addi a5,a5,8      0x00878793   -- index += 8 (one param = one name slot)
8000331c  ▷ bne s6,a5 → 0x800032dc (callParamFoldPC)   TAKEN: k+1 < n, next iteration
-- fall-through (k+1 = n, the fold is done):
80003320  ld s6,1024(sp)    0x40013b03   -- RESTORE caller s6 (spilled at 0x800032cc)
                             → 0x80003324 (the value_null staging, callClosureValueNullCallSeg)
```

The `bne` guard obligations sit in `ChainFacts` (dischargeable from the
carrier's `idx`/`bound` pins: `s6 = 8·n`, reloaded `a5+8 = 8·(k+1)` —
`k+1 < n` resp. `k+1 = n`, the split `callClosureEntrySplice`'s
`storeChainList` fold already cases on).  The exit route's `ld s6,1024(sp)`
readback is the `CallClosureEnvNewRetFoldRow` spill (`sd s6,1024(sp)` at
`0x800032cc`) — in-span, carried by the fold carrier's memory, NOT an
entry-side table slot.

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

/- Loop polarity: `bne` TAKEN → the fold head `0x800032dc` (`callParamFoldPC`,
the next `CallParamFoldInv` carrier index). -/
#derive_case callClosureFoldBackLoopSeg chain
  [(0x80003314#64, 0x00013783#32),  -- ld a5,0(sp)
   (0x80003318#64, 0x00878793#32)]  -- addi a5,a5,8
    terminator ⟨0x8000331c#64, 0xfcfb10e3#32, 0xe3#8, 0x10#8, 0xfb#8, 0xfc#8,
      .br bop.BNE true, 22, 15, 0x1FC0#13, 0#21, 0#12⟩

#print axioms callClosureFoldBackLoopSeg_seg

/- Exit polarity: `bne` NOT taken (k+1 = n), fall through the `s6` restore to
the value_null staging `0x80003324` (`callClosureValueNullCallSeg`'s entry). -/
#derive_case callClosureFoldBackExitSeg chain
  [(0x80003314#64, 0x00013783#32),  -- ld a5,0(sp)
   (0x80003318#64, 0x00878793#32)]  -- addi a5,a5,8
    terminator ⟨0x8000331c#64, 0xfcfb10e3#32, 0xe3#8, 0x10#8, 0xfb#8, 0xfc#8,
      .br bop.BNE false, 22, 15, 0x1FC0#13, 0#21, 0#12⟩ ;;
  [(0x80003320#64, 0x40013b03#32)]  -- ld s6,1024(sp)

#print axioms callClosureFoldBackExitSeg_seg

/-- The shared entry pin list: `x2` (sp — the index reload at `0(sp)` and the
exit route's `1024(sp)` restore) and `x22` (s6, the fold bound `8·n` the `bne`
reads). -/
def callClosureFoldBackL (sp s6v : BitVec 64) : GRegs := [(2, sp), (22, s6v)]

/-- The loop-route post: parked back at `callParamFoldPC = 0x800032dc`, memory
unchanged (this span stores nothing), the bumped index (`a5 = lds₀ + 8`)
exposed. -/
def CallClosureFoldBackLoopPost (sp s6v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureFoldBackLoopSeg
    (SegEvalState.init (callClosureFoldBackL sp s6v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800032dc#64 ∧
  GHolds c.σ (evalBlocks callClosureFoldBackLoopSeg
    (SegEvalState.init (callClosureFoldBackL sp s6v) lds)).regs

/-- The exit-route post: parked at `0x80003324` (the value_null staging),
memory unchanged, the restored `s6` (= the `1024(sp)` readback, `lds₁`)
exposed. -/
def CallClosureFoldBackExitPost (sp s6v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureFoldBackExitSeg
    (SegEvalState.init (callClosureFoldBackL sp s6v) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80003324#64 ∧
  GHolds c.σ (evalBlocks callClosureFoldBackExitSeg
    (SegEvalState.init (callClosureFoldBackL sp s6v) lds)).regs

/-- **`callClosureFoldBackLoopRow`** — the back-edge (next iteration) route as
a `Triple` (`segToTriple`). -/
theorem callClosureFoldBackLoopRow (sp s6v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureFoldBackLoopSeg (callClosureFoldBackL sp s6v)
        lds 0x80003314#64 m0)
      (CallClosureFoldBackLoopPost sp s6v lds m0) := by
  apply segToTriple callClosureFoldBackLoopSeg (callClosureFoldBackL sp s6v)
    lds 0x80003314#64 m0 (CallClosureFoldBackLoopPost sp s6v lds m0)
    (by have h : keysG (callClosureFoldBackL sp s6v) = [2, 22] := rfl
        rw [h]
        show ChainOK 0x80003314#64 [2, 22] callClosureFoldBackLoopSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003314#64
      (SegEvalState.init (callClosureFoldBackL sp s6v) lds)
      callClosureFoldBackLoopSeg)
    = some 0x800032dc#64
  rfl

#print axioms callClosureFoldBackLoopRow

/-- **`callClosureFoldBackExitRow`** — the fold-exit route as a `Triple`
(`segToTriple`), landing at the value_null staging `0x80003324`. -/
theorem callClosureFoldBackExitRow (sp s6v : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureFoldBackExitSeg (callClosureFoldBackL sp s6v)
        lds 0x80003314#64 m0)
      (CallClosureFoldBackExitPost sp s6v lds m0) := by
  apply segToTriple callClosureFoldBackExitSeg (callClosureFoldBackL sp s6v)
    lds 0x80003314#64 m0 (CallClosureFoldBackExitPost sp s6v lds m0)
    (by have h : keysG (callClosureFoldBackL sp s6v) = [2, 22] := rfl
        rw [h]
        show ChainOK 0x80003314#64 [2, 22] callClosureFoldBackExitSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003314#64
      (SegEvalState.init (callClosureFoldBackL sp s6v) lds)
      callClosureFoldBackExitSeg)
    = some 0x80003324#64
  rfl

#print axioms callClosureFoldBackExitRow

end Vsa.Sim
