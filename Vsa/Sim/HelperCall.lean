import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.BridgeSeg
import Vsa.MemReprReadFields
import Vsa.MemReprWithin
import Vsa.Sim.MemRegion
import Vsa.Sim.PinW
import Vsa.Sim.Code.Strcmp
import Vsa.Sim.StepCount
import Vsa.Sim.TermEntry
import Vsa.Sim.LayoutInstance
import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.ExecRetEpilogue

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

theorem sext32_of_lt (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 2 ^ 31)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hw : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    simp only [BitVec.append_eq, BitVec.toNat_append]
    have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [Nat.shiftLeft_eq, Nat.reducePow]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  have hmsb : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hw, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

end Vsa.Sim
