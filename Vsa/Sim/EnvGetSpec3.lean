import Vsa.Sim.StrcmpSpecW3
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Env_get
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem sext64_id_eg4 (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

theorem word8_recon_eg4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
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

theorem read64_bytes_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem[a]? = some b0 ∧ mem[a+1]? = some b1 ∧ mem[a+2]? = some b2 ∧
      mem[a+3]? = some b3 ∧ mem[a+4]? = some b4 ∧ mem[a+5]? = some b5 ∧
      mem[a+6]? = some b6 ∧ mem[a+7]? = some b7 ∧
      q = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [read64, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, hb0, r1, ⟨b1, hb1, r2, ⟨b2, hb2, r3, ⟨b3, hb3, r4, ⟨b4, hb4, r5,
    ⟨b5, hb5, r6, ⟨b6, hb6, r7, ⟨b7, hb7, r8, hr8, hq7⟩, hq6⟩, hq5⟩, hq4⟩, hq3⟩,
    hq2⟩, hq1⟩, hq0⟩ := h
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hb1
  · simpa using hb2
  · simpa using hb3
  · simpa using hb4
  · simpa using hb5
  · simpa using hb6
  · simpa using hb7
  · subst hr8; simp only [Nat.add_zero, Nat.mul_zero] at *
    omega

theorem read64_lt_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) : q < 2^64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hq⟩ := read64_bytes_eg4 mem a q h
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  omega

theorem ld_value_eq_read64 (mem : Mem) (a q : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : read64 mem a = some q)
    (e0 : mem[a]? = some b0) (e1 : mem[a+1]? = some b1) (e2 : mem[a+2]? = some b2)
    (e3 : mem[a+3]? = some b3) (e4 : mem[a+4]? = some b4) (e5 : mem[a+5]? = some b5)
    (e6 : mem[a+6]? = some b6) (e7 : mem[a+7]? = some b7) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hq⟩ :=
    read64_bytes_eg4 mem a q h
  have hb0 : b0 = c0 := by rw [e0] at f0; injection f0
  have hb1 : b1 = c1 := by rw [e1] at f1; injection f1
  have hb2 : b2 = c2 := by rw [e2] at f2; injection f2
  have hb3 : b3 = c3 := by rw [e3] at f3; injection f3
  have hb4 : b4 = c4 := by rw [e4] at f4; injection f4
  have hb5 : b5 = c5 := by rw [e5] at f5; injection f5
  have hb6 : b6 = c6 := by rw [e6] at f6; injection f6
  have hb7 : b7 = c7 := by rw [e7] at f7; injection f7
  subst hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [sext64_id_eg4]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_eg4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mem a q h), ← hq]

end Vsa.Sim
