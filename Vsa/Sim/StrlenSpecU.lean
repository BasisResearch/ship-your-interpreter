import Vsa.Sim.StrlenSpec
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem andi7_unaligned (p : BitVec 64) (halign : p.toNat % 8 ≠ 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) ≠ 0#64 := by
  intro h
  apply halign
  have : (p &&& sign_extend (m := 64) (0x007#12)).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl] at this
  exact this

theorem a4_incrG (base : BitVec 64) (off0 j : Nat) :
    (base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x008#12)
      = base + BitVec.ofNat 64 (off0+8*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

theorem snez_finalG (off0 j len : Nat) (b6 : BitVec 8)
    (hlo : off0 + 8*j + 5 < len) (hhi : len < off0 + 8*(j+1)) (hnw : off0 + 8*(j+1) + 8 < 2^64)
    (hb6 : b6 = 0 ↔ off0 + 8*j + 6 = len) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))
      + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len := by
  have hsext : (sign_extend (m := 64) (0xffe#12) : BitVec 64) = -(BitVec.ofNat 64 2) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat
      = (if b6 = 0 then 0 else 1) := snez_toNat b6

  have hsvlt : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat < 2 := by
    rw [hsnez]; by_cases h : b6 = 0
    · simp only [if_pos h]; decide
    · simp only [if_neg h]; decide
  have hval : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) - 2 = len := by
    rw [hsnez]
    by_cases h : b6 = 0
    · have := hb6.mp h; simp only [if_pos h]; omega
    · have hne : ¬ (off0 + 8*j + 6 = len) := fun hc => h (hb6.mpr hc); simp only [if_neg h]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, hsext, BitVec.toNat_neg]
  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
  rw [h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2^64 from by omega),
    Nat.mod_eq_of_lt (show off0+8*(j+1) < 2^64 from by omega),
    Nat.mod_eq_of_lt (show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) < 2^64 from by omega)]
  have hm2 : (2^64 - 2) % 2^64 = 2^64 - 2 := Nat.mod_eq_of_lt (by omega)
  rw [hm2]
  rw [show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) + (2^64 - 2) = len + 2^64 from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (show len < 2^64 from by omega)]

end Vsa.Sim
