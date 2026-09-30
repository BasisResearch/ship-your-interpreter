import Vsa.Sim.MemcpySites4
import Vsa.Sim.DivSpec
import Vsa.Sim.MemcpySpec2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem and7_toNat (v : BitVec 64) : (v &&& sign_extend (m := 64) (0x007#12)).toNat = v.toNat % 8 := by
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2:Nat)^3 = 8 from rfl]

theorem sltiu8_val (v : BitVec 64) :
    zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true ↔ v.toNat < 8 := by
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 from by decide, decide_eq_true_iff]
  constructor
  · intro h; have := Int.ofNat_lt.mp h; omega
  · intro h; exact Int.ofNat_lt.mpr h

theorem sltiu8_ne_zero_iff (v : BitVec 64) :
    ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x008#12))))) != (0#64)) = true
      ↔ v.toNat < 8 := by
  rw [bne_iff_ne, ne_eq]
  by_cases hlt : v.toNat < 8
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true := (sltiu8_val v).mpr hlt
    rw [hv]
    simp only [hlt, iff_true]
    intro h; exact absurd (congrArg BitVec.toNat h) (by decide)
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = false := by
      cases h : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) with
      | false => rfl
      | true => exact absurd ((sltiu8_val v).mp h) hlt
    rw [hv, show (zero_extend (m := 64) (bool_to_bit false) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide]
    simp only [hlt, iff_false, Classical.not_not]

end Vsa.Sim
