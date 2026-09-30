import Vsa.Sim.StrcmpSpecW
import Vsa.Sim.ObsAvoid

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem shl_48 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v <<< (48:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

theorem shl_32 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x20#6) 5 0) = v <<< (32:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x20#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x20#6) 5 0 : BitVec 6) = (32#6 : BitVec 6) from rfl]
  rfl

theorem shl_16 (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x10#6) 5 0) = v <<< (16:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x10#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x10#6) 5 0 : BitVec 6) = (16#6 : BitVec 6) from rfl]
  rfl

theorem shr_48 (v : BitVec 64) :
    shift_bits_right v (Sail.BitVec.extractLsb (0x30#6) 5 0) = v >>> (48:Nat) := by
  show v >>> (Sail.BitVec.extractLsb (0x30#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x30#6) 5 0 : BitVec 6) = (48#6 : BitVec 6) from rfl]
  rfl

theorem word_off8 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x008#12)
      = p + BitVec.ofNat 64 (24*j + 8) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem word_off16 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x010#12)
      = p + BitVec.ofNat 64 (24*j + 16) := by
  rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem word_off24 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (24*j)) + sign_extend (m := 64) (0x018#12)
      = p + BitVec.ofNat 64 (24*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 24*j + 24 = 24*(j+1) from by omega]

theorem shiftLeft_eq_iff (w w' : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (w <<< k = w' <<< k) ↔ (∀ i, i < 64 - k → w.getLsbD i = w'.getLsbD i) := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.getLsbD (i + k)) h
    simp only [BitVec.getLsbD_shiftLeft, show ¬ (i + k < k) from by omega,
      show i + k - k = i from by omega, decide_false, Bool.not_false, Bool.and_true] at this
    have hb : i + k < 64 := by omega
    simpa [hb] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft]
    by_cases hlt : i < k
    · simp [hlt]
    · have hik : i - k < 64 - k := by omega
      simp only [show (decide (i < k)) = false from by simp [hlt], Bool.not_false,
        Bool.and_true, h (i-k) hik]

theorem shiftLeft_bytes_agree (w w' : BitVec 64) (s : Nat)
    (h : ∀ i, i < 8*(8-s) → w.getLsbD i = w'.getLsbD i) (m : Nat) (hm : m < 8 - s) :
    w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i < 8 from hi), Bool.true_and]
  exact h (8*m + i) (by omega)

theorem slli48_eq_iff (w w' : BitVec 64) :
    (w <<< (48:Nat) = w' <<< (48:Nat)) ↔
      (∀ m, m < 2 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 48 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 6 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 2 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

end Vsa.Sim
