import Vsa.Sim.MemcpySites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem sbData_zext (b : BitVec 8) :
    sbData (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.shiftRight_zero]
  have hlt : (b : BitVec 8).toNat < 2^8 := b.isLt
  have key : ∀ W : Nat, (2:Nat)^W = 2^8 → (BitVec.ofNat W (b.toNat % 2^64)).toNat = b.toNat := by
    intro W hW
    rw [BitVec.toNat_ofNat, hW]
    have h2 : (b : BitVec 8).toNat % 2^64 = (b : BitVec 8).toNat := Nat.mod_eq_of_lt (by omega)
    rw [h2, Nat.mod_eq_of_lt hlt]
  exact key _ (by decide)

abbrev NotWrittenB (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenB.x11 {R : Register} (h : NotWrittenB R) : (Register.x11 == R) = false := h.1

theorem post_store_pc (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_store_pc {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_store_pc σ pc vm m')

theorem obs_store_other {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5).trans hσ)

theorem obs_store_minstret {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

def memcpy_bytepath_post (g : (R : Register) → Option (RegisterType R)) (r dst : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k < n → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R)

end Vsa.Sim
