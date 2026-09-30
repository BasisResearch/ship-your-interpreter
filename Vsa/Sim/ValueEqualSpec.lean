import Vsa.Sim.ChainFrameOut
import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch11Part24
import Vsa.Sim.DecodeTable.Batch12Part27

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

theorem equal_false_of_kind_ne (va vb : Value) (h : kindTag va ≠ kindTag vb) :
    Value.equal va vb = false := by
  cases va <;> cases vb <;> simp_all [kindTag, Value.equal]

theorem seqz_val (v : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) : BitVec 64)
      = cond (v == 0#64) (1#64) (0#64) := by
  by_cases h : v = 0#64
  · subst h
    have : zopz0zI_u (0#64) (sign_extend (m := 64) (0x001#12)) = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt]; decide
    rw [this]; simp only [beq_self_eq_true, cond_true]
    apply BitVec.eq_of_toNat_eq; decide
  · have hpos : 0 < v.toNat := by
      rcases Nat.eq_zero_or_pos v.toNat with h0 | hp
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
      · exact hp
    have hfalse : zopz0zI_u v (sign_extend (m := 64) (0x001#12)) = false := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt,
        show (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 from by decide,
        decide_eq_false_iff_not]
      intro hlt
      have := Int.ofNat_lt.mp hlt
      omega
    rw [hfalse, show (v == 0#64) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; exact h,
      cond_false]
    apply BitVec.eq_of_toNat_eq; decide

end Vsa.Sim
