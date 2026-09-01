import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `strdupMemcpyArg` — the stringify strdup-tail memcpy prefix as a `#derive_case` seg

The shared strdup tail (`0x80003044`, `Vsa/Sim/rows/StringifyStrdupTail.lean`) stages
the memcpy arguments across the malloc OOM guard:

```
8000305c  ld   a2,8(sp)     -- x12 := len+1        (reload the spilled size)
80003060  mv   s0,a0        -- x8  := new          (save the malloc result)
80003064  beqz a0,80003140  -- OOM guard; NOT taken on the arena's no-OOM path (a0 ≠ 0)
80003068  mv   a1,s1        -- x11 := buf          (marshal the source pointer)
8000306c  jal  memcpy@80006bc8                       -- SEAM (callSeg)
```

This is the EXACT `EnvDefBridges4.appendHeadSeg` idiom (`ld;sd ▷ beqz(false)` then a
fall-through block): two basic blocks, the first ending in a NOT-taken `beqz` carried
in-model (`BlockTerm`'s `TKind.br`; `beqz` writes no GPR), the second the straight-line
`mv a1,s1` parked at the `jal memcpy` seam.  The whole `Steps` chain / computed end-PC /
write-log is auto-threaded by `#derive_case`; the row's ONLY kernel obligation is the
single `ChainOK` `decide`.

NOT-taken polarity is the arena's no-OOM path: the strdup-tail contract
(`stringifyStrdupTailContract`) threads the malloc-post's non-null branch (the arena
never returns NULL for a bounded request), so `a0 ≠ 0` and the `beqz` falls through.
The seg fixes `taken = false`; the CALLER (the frame-carrying `bridgeMemcpyPre`
repackaging) supplies the `a0 ≠ 0` semantic fact that justifies that polarity.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- The memcpy-prefix span `0x8000305c → 0x8000306c` (two blocks, the first ending in a
not-taken `beqz`, the second falling through to the `jal memcpy` seam), decoded from
`experiments/disasm.txt`.  Block 1: `ld a2,8(sp) ; mv s0,a0 ▷ beqz a0 (false)`.
Block 2: `mv a1,s1` (fall-through). -/
#derive_case strdupMemcpyArgSeg chain
  [(0x8000305c#64, 0x00813603#32),   -- ld a2,8(sp)  (x12 := len+1)
   (0x80003060#64, 0x00050413#32)]   -- mv s0,a0     (x8  := new)
    terminator ⟨0x80003064#64, 0x0c050e63#32, 0x63#8, 0x0e#8, 0x05#8, 0x0c#8,
      .br bop.BEQ false, 10, 0, 0x00dc#13, 0#21, 0#12⟩ ;;
  [(0x80003068#64, 0x00048593#32)]   -- mv a1,s1     (x11 := buf, memcpy source)

/-- The memcpy-prefix entry pins: `x2 = sp` (base for the spill reload), `x10 = a0 =
malloc result` (saved into `s0`, and the `beqz` guard), `x9 = s1 = buf` (the source
pointer, marshalled into `a1`). -/
def strdupMemcpyArgL (sp a0 s1 : BitVec 64) : GRegs := [(2, sp), (10, a0), (9, s1)]

/-- The memcpy-prefix post: parked at the computed end PC `0x8000306c` (the `jal memcpy`
seam, ready for the `callSeg`), memory = the entry memory with the seg's write-log applied
(no stores in this span → memory unchanged), computed off `#derive_case`. -/
def StrdupMemcpyArgPost (sp a0 s1 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks strdupMemcpyArgSeg
    (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000306c#64

/-- **`strdupMemcpyArgRow`** — the memcpy-prefix span as a `Triple`, via `segToTriple`
over the (not-taken)-branch-terminated `strdupMemcpyArgSeg`.  `hwf` is the row's one
kernel `decide` (`ChainOK`); `hpost` projects the computed end PC (`0x8000306c`, the `jal
memcpy` seam) and the write-log memory off the `#derive_case` outcome.  Replaces the hand
`site_*` `stepObs` battery for this span. -/
theorem strdupMemcpyArgRow (sp a0 s1 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strdupMemcpyArgSeg (strdupMemcpyArgL sp a0 s1) lds 0x8000305c#64 m0)
      (StrdupMemcpyArgPost sp a0 s1 lds m0) := by
  apply segToTriple strdupMemcpyArgSeg (strdupMemcpyArgL sp a0 s1) lds 0x8000305c#64 m0
    (StrdupMemcpyArgPost sp a0 s1 lds m0)
    (by have h : keysG (strdupMemcpyArgL sp a0 s1) = [2, 10, 9] := rfl
        rw [h]; show ChainOK 0x8000305c#64 [2, 10, 9] strdupMemcpyArgSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x8000305c#64 (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)
    strdupMemcpyArgSeg) = some 0x8000306c#64
  rfl

#print axioms strdupMemcpyArgRow

end Vsa.Sim
