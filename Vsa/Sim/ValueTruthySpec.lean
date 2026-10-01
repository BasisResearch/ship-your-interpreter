import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprSurvival

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem word_toNat_recon (b0 b1 b2 b3 : BitVec 8) :
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  have h3 := b3.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem read64_bytes (m : Mem) (a p : Nat) (h : read64 m a = some p) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      m[a + 4]? = some b4 ∧ m[a + 5]? = some b5 ∧ m[a + 6]? = some b6 ∧ m[a + 7]? = some b7 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p := by
  simp only [read64, readLE, bind, Option.bind] at h
  match hb0 : m[a]?, hb1 : m[a + 1]?, hb2 : m[a + 2]?, hb3 : m[a + 3]?,
        hb4 : m[a + 4]?, hb5 : m[a + 5]?, hb6 : m[a + 6]?, hb7 : m[a + 7]? with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h
      have hk := Option.some.inj h
      omega
  | none, _, _, _, _, _, _, _ => rw [hb0] at h; exact absurd h (by simp)
  | some _, none, _, _, _, _, _, _ => rw [hb0, hb1] at h; exact absurd h (by simp)
  | some _, some _, none, _, _, _, _, _ => rw [hb0, hb1, hb2] at h; exact absurd h (by simp)
  | some _, some _, some _, none, _, _, _, _ => rw [hb0, hb1, hb2, hb3] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, none, _, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, none, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, none, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, some _, none =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h; exact absurd h (by simp)

theorem word8_toNat_recon (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem sext_full (w : BitVec (8 * 8)) : (sign_extend (m := 64) w : BitVec 64) = w := by
  show Sail.BitVec.signExtend w 64 = w
  simp only [Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq w

theorem snez_reg (v : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v)) : BitVec 64)
      = cond (v != 0#64) (1#64) (0#64) := by
  by_cases h : v = 0#64
  · subst h
    have hz : zopz0zI_u (0#64) (0#64) = false := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]; decide
    rw [hz]
    simp only [bne_self_eq_false, cond_false]
    apply BitVec.eq_of_toNat_eq; decide
  · have htrue : zopz0zI_u (0#64) v = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
      have hp : 0 < v.toNat := by
        rcases Nat.eq_zero_or_pos v.toNat with h0 | hp
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
        · exact hp
      exact Int.ofNat_lt.mpr hp
    rw [htrue, show (v != 0#64) = true from by simp only [bne_iff_ne, ne_eq]; exact h, cond_true]
    apply BitVec.eq_of_toNat_eq; decide

theorem obs_branch_nottaken_other {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    {w : RegisterType R} (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_branch_nottaken σ pc vm R h1 h2 h4 h5).trans hσ)

end Vsa.Sim
