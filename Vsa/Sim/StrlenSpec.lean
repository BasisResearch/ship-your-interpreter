import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Muldi3Spec
import Vsa.MemRepr
import Vsa.Triple
import Vsa.Sim.ObsAvoid
import Vsa.Alloc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem sext64_self (x : BitVec 64) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

theorem ldBytesT_byte (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (k : Nat) (hk : k < 8) :
    (ldBytesT σ a).extractLsb' (8*k) 8 = (σ.mem[a.toNat + k]?).getD 0 := by
  have hshow : ldBytesT σ a =
    ((((((((σ.mem[a.toNat + 7]?).getD 0) +++ ((σ.mem[a.toNat + 6]?).getD 0)) +++
     ((σ.mem[a.toNat + 5]?).getD 0)) +++ ((σ.mem[a.toNat + 4]?).getD 0)) +++
     ((σ.mem[a.toNat + 3]?).getD 0)) +++ ((σ.mem[a.toNat + 2]?).getD 0)) +++
     ((σ.mem[a.toNat + 1]?).getD 0)) +++ ((σ.mem[a.toNat]?).getD 0) := rfl
  rw [hshow]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

theorem ptrN (base : BitVec 64) (k : Nat) (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 from by omega),
    Nat.mod_eq_of_lt h]

theorem sext0_add (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

theorem strlenWordVal_eq (w : BitVec 64) :
    ((w &&& magic7f) + magic7f ||| w) ||| magic7f = strlenWordVal w := rfl

def strlenWordAt (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  ((((((((m0[a + 7]?).getD 0).append ((m0[a + 6]?).getD 0)).append
    ((m0[a + 5]?).getD 0)).append ((m0[a + 4]?).getD 0)).append
    ((m0[a + 3]?).getD 0)).append ((m0[a + 2]?).getD 0)).append
    ((m0[a + 1]?).getD 0)).append ((m0[a]?).getD 0)

theorem ldBytesT_wordAt (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    ldBytesT σ a = strlenWordAt σ.mem a.toNat := rfl

theorem andi7_aligned (p : BitVec 64) (halign : p.toNat % 8 = 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl, halign]
  rfl

theorem magic_build :
    (shift_bits_left (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      (Sail.BitVec.extractLsb (0x20#6) 5 0)
      + (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12)))
      = magic7f := by
  apply BitVec.eq_of_toNat_eq; decide

theorem allOnes_build : ((0#64) + sign_extend (m := 64) (0xfff#12)) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem ofNat_sub (a b : Nat) (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have : (BitVec.ofNat 64 (a-b)) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [← this, BitVec.add_sub_cancel]

theorem sub_a4_a0_val (p : BitVec 64) (m : Nat) :
    (p + BitVec.ofNat 64 m) - p = BitVec.ofNat 64 m := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem zext_beqz (b : BitVec 8) : ((zero_extend (m := 64) b) == (0#64)) = (b == 0#8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have : (zero_extend (m := 64) b).toNat = 0 := by rw [h]; rfl
    apply BitVec.eq_of_toNat_eq
    simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using this
  · intro h; rw [h]; rfl

theorem snez_toNat (b : BitVec 8) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b)))).toNat
      = (if b = 0 then 0 else 1) := by
  rcases (Decidable.em (b = 0)) with h | h
  · subst h; decide
  · simp only [if_neg h]
    have hpos : 0 < (zero_extend (m := 64) b).toNat := by
      rcases Nat.eq_zero_or_pos (zero_extend (m := 64) b).toNat with hz | hp
      · exfalso; apply h; apply BitVec.eq_of_toNat_eq
        simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using hz
      · exact hp
    have : zopz0zI_u (0#64) (zero_extend (m := 64) b) = true := by
      unfold zopz0zI_u Sail.BitVec.toNatInt
      simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; exact_mod_cast hpos
    rw [this]; rfl
