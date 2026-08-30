import Vsa.Sim.ValueEqualSpec
import Vsa.Sim.ValueEqualSites2
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — total-correctness spec for `value_equal`, part 2 (payload variants + merge)

This finishes `value_equal` (@0x8000285c): the four payload-comparing handlers
(bool/int/closure/native) end-to-end, and the unified `value_equal_spec` that merges
them with the previously-proven null/mismatch theorem.

Each payload handler runs, after `ve_dispatch` lands on the handler PC:

* **bool** (0x800028b0): `lw a0,8(a0); lw a5,8(a1); sub; seqz; ret`
* **int / closure** (0x80002894): `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`
* **native** (0x800028e8): `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

The `sub; seqz; ret` tail is shared (`ve_sub_seqz_ret`); the per-kind bridges
(`bool_eq_bridge`/`int_eq_bridge`/`ptr_eq_bridge`) rewrite the `sub == 0` register test
to the matching `Value.equal` clause.
-/

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

/-! ## Shared `sub a0,a0,a5; seqz a0,a0; ret` tail

From a state at the `sub` site with `x10 = payA`, `x15 = payB`, runs the three
instructions, ending at the return target with `x10 = cond (payA - payB == 0) 1 0`,
preserving `x1`, memory, and the ghost frame. Parameterised by the three site lemmas so
it serves all three payload handlers. -/
theorem ve_sub_seqz_ret (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (payA payB : BitVec 64) (subaddr seqzaddr retaddr : BitVec 64)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hout : σ.sailOutput = o) (hloaded : Value_equalLoaded m0)
    (hpc : σ.regs.get? Register.PC = some subaddr)
    (ha0 : σ.regs.get? Register.x10 = some payA) (ha5 : σ.regs.get? Register.x15 = some payB)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    -- the `sub` step: x10 := payA - payB
    (hsub : ∀ (σ0 : MState) (i0 u0 : Nat) (v10 v15 : BitVec 64),
      GoodState σ0 → σ0.regs.get? Register.PC = some subaddr →
      σ0.regs.get? Register.minstret = some vmi →
      σ0.regs.get? Register.x10 = some v10 → σ0.regs.get? Register.x15 = some v15 →
      Value_equalLoaded σ0.mem → i0 < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Vsa.Machine.Step ⟨σ0, i0, u0⟩ ⟨σ', i', u0 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ0.mem ∧
        ReadsLikePost σ' (sigmaPost_alu σ0 subaddr vmi Register.x10 (v10 - v15)))
    (hsubpc : BitVec.addInt subaddr 4 = seqzaddr)
    -- the `seqz` step: x10 := cond (x10 = 0) 1 0
    (hseqz : ∀ (σ0 : MState) (i0 u0 : Nat) (vmi0 v10 : BitVec 64),
      GoodState σ0 → σ0.regs.get? Register.PC = some seqzaddr →
      σ0.regs.get? Register.minstret = some vmi0 →
      σ0.regs.get? Register.x10 = some v10 →
      Value_equalLoaded σ0.mem → i0 < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Vsa.Machine.Step ⟨σ0, i0, u0⟩ ⟨σ', i', u0 + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ0.mem ∧
        ReadsLikePost σ' (sigmaPost_alu σ0 seqzaddr vmi0 Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))))
    (hseqzpc : BitVec.addInt seqzaddr 4 = retaddr)
    -- the ret byte facts
    (hbb0 : m0[retaddr.toNat]? = some (0x67#8)) (hbb1 : m0[retaddr.toNat + 1]? = some (0x80#8))
    (hbb2 : m0[retaddr.toNat + 2]? = some (0x00#8)) (hbb3 : m0[retaddr.toNat + 3]? = some (0x00#8))
    (hretlo : 0x80000000 ≤ retaddr.toNat) (hrethi : retaddr.toNat + 4 ≤ tohostAddr)
    (hretalign : retaddr.toNat % 4 = 0) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      σ2.regs.get? Register.x10 = some (cond ((payA - payB) == 0#64) (1#64) (0#64)) ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧ σ2.mem = m0 ∧ σ2.sailOutput = o ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  -- sub
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    hsub σ i steps0 payA payB hG hpc hmi ha0 ha5 (hmem ▸ hloaded) hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some seqzaddr := by
    have := obs_alu_pc hobs1; rwa [hsubpc] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (payA - payB) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.1).trans (hframe R hR)
  -- seqz
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    hseqz σ1 i1 (steps0 + 1) vmi1 (payA - payB) hG1 hpc1 hmi1 ha0_1 (hmem1eq ▸ hloaded) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some retaddr := by
    have := obs_alu_pc hobs2; rwa [hseqzpc] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (cond ((payA - payB) == 0#64) (1#64) (0#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, seqz_val]
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.1).trans (hframe1 R hR)
  -- ret
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_ret_gen σ2 i2 (steps0 + 1 + 1) retaddr vmi2 r (0x67#8) (0x80#8) (0x00#8) (0x00#8)
      hG2 hpc2 hmi2 hra_2 (hmem2eq ▸ hbb0) (hmem2eq ▸ hbb1) (hmem2eq ▸ hbb2) (hmem2eq ▸ hbb3)
      rfl hretlo hrethi hretalign hrettgt hi2
  have hout3 : σ3.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3] : σ3.sailOutput = σ.sailOutput).trans hout
  refine ⟨σ3, i3, ((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2)).trans (Steps.single hs3),
    hi3, hG3, obs_jr_pc hobs3, ?_,
    obs_jr_other' hobs3 Register.x1 (by decide) hra_2,
    obs_jr_minstret hobs3, by rw [hmem3, hmem2eq], hout3,
    fun R hR => (frame_jr_ve hobs3 R hR).trans (hframe2 R hR)⟩
  exact obs_jr_other' hobs3 Register.x10 (by decide) ha0_2

/-! ## Region / payload-address helpers for the 8-byte loads

`ve_pay8_addr`/`ve_pay16_addr` give the load address; these bundle the RAM/HTIF/align
side facts the `ld`/`lw` sites need at `+8` (8-byte) and `+16` (8-byte). -/

theorem ve_pay8_bounds (buf : BitVec 64) (hr : VERegion buf) :
    0x80000000 ≤ (buf + sign_extend (m := 64) (0x008#12)).toNat ∧
    (buf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
    ((buf + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (buf + sign_extend (m := 64) (0x008#12)).toNat) ∧
    (buf + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0 := by
  rw [ve_pay8_addr buf hr]
  refine ⟨by have := hr.lo; omega, by have := hr.hi; omega, ?_, by have := hr.align; omega⟩
  right; rw [show tohostAddr = 0x8001ad00 from rfl]; have := hr.win
  rw [show tohostAddr = 0x8001ad00 from rfl] at this; omega

/-- Fold an 8-byte little-endian load result `sext (b7++…++b0)` to `ofNat p`, given the
byte reconstruction `… = p` and the top byte fact `b7.toNat < 256` (⇒ `p < 2^64`). -/
theorem ld_sext_ofNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (p : Nat)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
      (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8))) = BitVec.ofNat 64 p := by
  rw [sext_full]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · omega
  · have := b7.isLt; omega

/-- `p < 2^64` from an 8-byte reconstruction. -/
theorem ld_recon_lt (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (p : Nat)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
      (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p) :
    p < 2 ^ 64 := by have := b7.isLt; omega

/-- Any `read64` result is a 64-bit-representable natural. -/
theorem read64_lt (m0 : Mem) (a p : Nat) (h : read64 m0 a = some p) : p < 2 ^ 64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hrec⟩ := read64_bytes m0 a p h
  exact ld_recon_lt b0 b1 b2 b3 b4 b5 b6 b7 p hrec

theorem ve_pay16_bounds (buf : BitVec 64) (hr : VERegion buf) :
    0x80000000 ≤ (buf + sign_extend (m := 64) (0x010#12)).toNat ∧
    (buf + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
    ((buf + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (buf + sign_extend (m := 64) (0x010#12)).toNat) ∧
    (buf + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0 := by
  rw [ve_pay16_addr buf hr]
  refine ⟨by have := hr.lo; omega, by have := hr.hi; omega, ?_, by have := hr.align; omega⟩
  right; rw [show tohostAddr = 0x8001ad00 from rfl]; have := hr.win
  rw [show tohostAddr = 0x8001ad00 from rfl] at this; omega

/-! ## int / closure handler (0x80002894): `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`

Loads both 8-byte payloads at `+8`, subtracts, `seqz`, returns. The `sub == 0` bridge is
`int_eq_bridge` (int) / `ptr_eq_bridge` (closure). This lemma runs the shared 8-byte load
sequence + tail, leaving the caller to supply the two payloads `q1 q2` and the bridge. -/
theorem ve_int_handler (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (q1 q2 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hout : σ.sailOutput = o) (hloaded : Value_equalLoaded m0)
    (hpc : σ.regs.get? Register.PC = some (0x80002894#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    (hp1 : read64 m0 (bufa.toNat + 8) = some q1) (hp2 : read64 m0 (bufb.toNat + 8) = some q2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      σ2.regs.get? Register.x10 =
        some (cond ((BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) == 0#64) (1#64) (0#64)) ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧ σ2.mem = m0 ∧ σ2.sailOutput = o ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hab0, hab1, hab2, hab3, hab4, hab5, hab6, hab7, harec⟩ :=
    read64_bytes m0 (bufa.toNat + 8) _ hp1
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hdb0, hdb1, hdb2, hdb3, hdb4, hdb5, hdb6, hdb7, hdrec⟩ :=
    read64_bytes m0 (bufb.toNat + 8) _ hp2
  obtain ⟨hlo_a, hhi_a, hhtif_a, halign_a⟩ := ve_pay8_bounds bufa hrega
  obtain ⟨hlo_b, hhi_b, hhtif_b, halign_b⟩ := ve_pay8_bounds bufb hregb
  -- 0x80002894: ld a0,8(a0)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002894 σ i steps0 (0x80002894#64) vmi bufa a0 a1 a2 a3 a4 a5 a6 a7
      hG hpc hmi ha0 (hmem ▸ hloaded) rfl hlo_a hhi_a hhtif_a halign_a
      (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab0) (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab1)
      (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab2) (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab3)
      (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab4) (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab5)
      (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab6) (by rw [ve_pay8_addr bufa hrega, hmem]; exact hab7) hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002898#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002894#64) 4 = (0x80002898#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (BitVec.ofNat 64 q1) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat a0 a1 a2 a3 a4 a5 a6 a7 q1 harec]
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.1).trans (hframe R hR)
  -- 0x80002898: ld a5,8(a1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002898 σ1 i1 (steps0 + 1) (0x80002898#64) vmi1 bufb d0 d1 d2 d3 d4 d5 d6 d7
      hG1 hpc1 hmi1 ha1_1 (hmem1eq ▸ hloaded) rfl hlo_b hhi_b hhtif_b halign_b
      (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb0) (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb1)
      (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb2) (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb3)
      (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb4) (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb5)
      (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb6) (by rw [ve_pay8_addr bufb hregb, hmem1eq]; exact hdb7) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000289c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80002898#64) 4 = (0x8000289c#64 : BitVec 64) from by decide] at this
  have ha5_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 q2) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat d0 d1 d2 d3 d4 d5 d6 d7 q2 hdrec]
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.2.2.1).trans (hframe1 R hR)
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := value_equal_at_800028a4 hloaded
  -- shared sub; seqz; ret tail
  have hout2 : σ2.sailOutput = o :=
    (by chain_out [hobs1, hobs2] : σ2.sailOutput = σ.sailOutput).trans hout
  have htail := ve_sub_seqz_ret g r m0 o c σ2 i2 (steps0 + 1 + 1)
    (BitVec.ofNat 64 q1) (BitVec.ofNat 64 q2) (0x8000289c#64) (0x800028a0#64) (0x800028a4#64)
    (((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2))) hi2 hG2 hmem2eq hout2 hloaded
    hpc2 ha0_2 ha5_2 hra_2 vmi2 hmi2 hrettgt hframe2
    (fun σ0 i0 u0 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 hi0 =>
      site_8000289c σ0 i0 u0 (0x8000289c#64) vmi2 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 rfl hi0)
    (by decide)
    (fun σ0 i0 u0 vmi0 v10 hG0 hpc0 hmi0 h10 hl0 hi0 =>
      site_800028a0 σ0 i0 u0 (0x800028a0#64) vmi0 v10 hG0 hpc0 hmi0 h10 hl0 rfl hi0)
    (by decide)
    (by show m0[(2147494052 : Nat)]? = _; exact hbb0)
    (by show m0[(2147494052 + 1 : Nat)]? = _; exact hbb1)
    (by show m0[(2147494052 + 2 : Nat)]? = _; exact hbb2)
    (by show m0[(2147494052 + 3 : Nat)]? = _; exact hbb3)
    (by decide) (by rw [show tohostAddr = 0x8001ad00 from rfl]; decide) (by decide)
  exact htail

/-! ## bool handler (0x800028b0): `lw a0,8(a0); lw a5,8(a1); sub; seqz; ret`

Loads both 4-byte `{0,1}` bool payloads at `+8`. `sext_word_small` folds each to
`cond b (1#64) (0#64)`; `bool_eq_bridge` bridges the `sub == 0` test. -/
theorem ve_bool_handler (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (b1 b2 : Bool)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hout : σ.sailOutput = o) (hloaded : Value_equalLoaded m0)
    (hpc : σ.regs.get? Register.PC = some (0x800028b0#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    (hp1 : read32 m0 (bufa.toNat + 8) = some (cond b1 1 0))
    (hp2 : read32 m0 (bufb.toNat + 8) = some (cond b2 1 0)) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      σ2.regs.get? Register.x10 = some (cond (b1 == b2) (1#64) (0#64)) ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧ σ2.mem = m0 ∧ σ2.sailOutput = o ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  obtain ⟨a0, a1, a2, a3, hab0, hab1, hab2, hab3, harec⟩ := read32_bytes m0 (bufa.toNat + 8) _ hp1
  obtain ⟨d0, d1, d2, d3, hdb0, hdb1, hdb2, hdb3, hdrec⟩ := read32_bytes m0 (bufb.toNat + 8) _ hp2
  have hlt1 : (cond b1 1 0 : Nat) < 128 := by cases b1 <;> decide
  have hlt2 : (cond b2 1 0 : Nat) < 128 := by cases b2 <;> decide
  -- reuse the +8 bounds but with 4-byte width facts
  have hpay8 := ve_pay8_addr bufa hrega
  have hpay8b := ve_pay8_addr bufb hregb
  have hlo_a : 0x80000000 ≤ (bufa + sign_extend (m := 64) (0x008#12)).toNat := by rw [hpay8]; have := hrega.lo; omega
  have hhi_a : (bufa + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000 := by rw [hpay8]; have := hrega.hi; omega
  have hhtif_a : (bufa + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (bufa + sign_extend (m := 64) (0x008#12)).toNat := by
    rw [hpay8]; right; rw [show tohostAddr = 0x8001ad00 from rfl]; have := hrega.win
    rw [show tohostAddr = 0x8001ad00 from rfl] at this; omega
  have halign_a : (bufa + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0 := by rw [hpay8]; have := hrega.align; omega
  have hlo_b : 0x80000000 ≤ (bufb + sign_extend (m := 64) (0x008#12)).toNat := by rw [hpay8b]; have := hregb.lo; omega
  have hhi_b : (bufb + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000 := by rw [hpay8b]; have := hregb.hi; omega
  have hhtif_b : (bufb + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (bufb + sign_extend (m := 64) (0x008#12)).toNat := by
    rw [hpay8b]; right; rw [show tohostAddr = 0x8001ad00 from rfl]; have := hregb.win
    rw [show tohostAddr = 0x8001ad00 from rfl] at this; omega
  have halign_b : (bufb + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0 := by rw [hpay8b]; have := hregb.align; omega
  -- 0x800028b0: lw a0,8(a0)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800028b0 σ i steps0 (0x800028b0#64) vmi bufa a0 a1 a2 a3
      hG hpc hmi ha0 (hmem ▸ hloaded) rfl hlo_a hhi_a hhtif_a halign_a
      (by rw [hpay8, hmem]; exact hab0) (by rw [hpay8, hmem]; exact hab1)
      (by rw [hpay8, hmem]; exact hab2) (by rw [hpay8, hmem]; exact hab3) hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800028b4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800028b0#64) 4 = (0x800028b4#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (cond b1 (1#64) (0#64)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, sext_word_small _ (cond b1 1 0) hlt1 (by rw [word_toNat_recon]; omega)]
    cases b1 <;> rfl
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.1).trans (hframe R hR)
  -- 0x800028b4: lw a5,8(a1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800028b4 σ1 i1 (steps0 + 1) (0x800028b4#64) vmi1 bufb d0 d1 d2 d3
      hG1 hpc1 hmi1 ha1_1 (hmem1eq ▸ hloaded) rfl hlo_b hhi_b hhtif_b halign_b
      (by rw [hpay8b, hmem1eq]; exact hdb0) (by rw [hpay8b, hmem1eq]; exact hdb1)
      (by rw [hpay8b, hmem1eq]; exact hdb2) (by rw [hpay8b, hmem1eq]; exact hdb3) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x800028b8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800028b4#64) 4 = (0x800028b8#64 : BitVec 64) from by decide] at this
  have ha5_2 : σ2.regs.get? Register.x15 = some (cond b2 (1#64) (0#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, sext_word_small _ (cond b2 1 0) hlt2 (by rw [word_toNat_recon]; omega)]
    cases b2 <;> rfl
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.2.2.1).trans (hframe1 R hR)
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := value_equal_at_800028c0 hloaded
  have hout2 : σ2.sailOutput = o :=
    (by chain_out [hobs1, hobs2] : σ2.sailOutput = σ.sailOutput).trans hout
  have htail := ve_sub_seqz_ret g r m0 o c σ2 i2 (steps0 + 1 + 1)
    (cond b1 (1#64) (0#64)) (cond b2 (1#64) (0#64)) (0x800028b8#64) (0x800028bc#64) (0x800028c0#64)
    (((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2))) hi2 hG2 hmem2eq hout2 hloaded
    hpc2 ha0_2 ha5_2 hra_2 vmi2 hmi2 hrettgt hframe2
    (fun σ0 i0 u0 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 hi0 =>
      site_800028b8 σ0 i0 u0 (0x800028b8#64) vmi2 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 rfl hi0)
    (by decide)
    (fun σ0 i0 u0 vmi0 v10 hG0 hpc0 hmi0 h10 hl0 hi0 =>
      site_800028bc σ0 i0 u0 (0x800028bc#64) vmi0 v10 hG0 hpc0 hmi0 h10 hl0 rfl hi0)
    (by decide)
    (by show m0[(2147494080 : Nat)]? = _; exact hbb0)
    (by show m0[(2147494080 + 1 : Nat)]? = _; exact hbb1)
    (by show m0[(2147494080 + 2 : Nat)]? = _; exact hbb2)
    (by show m0[(2147494080 + 3 : Nat)]? = _; exact hbb3)
    (by decide) (by rw [show tohostAddr = 0x8001ad00 from rfl]; decide) (by decide)
  obtain ⟨σ3, i3, hs3, hi3, hG3, hpc3, ha0_3, hra_3, hmi3, hmem3, hframe3⟩ := htail
  exact ⟨σ3, i3, hs3, hi3, hG3, hpc3, by rw [ha0_3, bool_eq_bridge b1 b2], hra_3, hmi3, hmem3, hframe3⟩

/-! ## native handler (0x800028e8): `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

Loads both fn pointers at `+16`, subtracts, `seqz`, returns. Same shape as the int
handler but at offset `+16` and using the `f0/f4/f8` tail sites. -/
theorem ve_native_handler (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (q1 q2 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hout : σ.sailOutput = o) (hloaded : Value_equalLoaded m0)
    (hpc : σ.regs.get? Register.PC = some (0x800028e8#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    (hp1 : read64 m0 (bufa.toNat + 16) = some q1) (hp2 : read64 m0 (bufb.toNat + 16) = some q2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps c ⟨σ2, i2, steps0 + 1 + 1 + 1 + 1 + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
      σ2.regs.get? Register.x10 =
        some (cond ((BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) == 0#64) (1#64) (0#64)) ∧
      σ2.regs.get? Register.x1 = some r ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧ σ2.mem = m0 ∧ σ2.sailOutput = o ∧
      (∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hab0, hab1, hab2, hab3, hab4, hab5, hab6, hab7, harec⟩ :=
    read64_bytes m0 (bufa.toNat + 16) _ hp1
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hdb0, hdb1, hdb2, hdb3, hdb4, hdb5, hdb6, hdb7, hdrec⟩ :=
    read64_bytes m0 (bufb.toNat + 16) _ hp2
  obtain ⟨hlo_a, hhi_a, hhtif_a, halign_a⟩ := ve_pay16_bounds bufa hrega
  obtain ⟨hlo_b, hhi_b, hhtif_b, halign_b⟩ := ve_pay16_bounds bufb hregb
  -- 0x800028e8: ld a0,16(a0)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800028e8 σ i steps0 (0x800028e8#64) vmi bufa a0 a1 a2 a3 a4 a5 a6 a7
      hG hpc hmi ha0 (hmem ▸ hloaded) rfl hlo_a hhi_a hhtif_a halign_a
      (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab0) (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab1)
      (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab2) (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab3)
      (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab4) (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab5)
      (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab6) (by rw [ve_pay16_addr bufa hrega, hmem]; exact hab7) hi
  have hmem1eq : σ1.mem = m0 := by rw [hmem1, hmem]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800028ec#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800028e8#64) 4 = (0x800028ec#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (BitVec.ofNat 64 q1) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat a0 a1 a2 a3 a4 a5 a6 a7 q1 harec]
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hframe1 : ∀ R : Register, NotWrittenVE R → σ1.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs1 R hR hR.1).trans (hframe R hR)
  -- 0x800028ec: ld a5,16(a1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800028ec σ1 i1 (steps0 + 1) (0x800028ec#64) vmi1 bufb d0 d1 d2 d3 d4 d5 d6 d7
      hG1 hpc1 hmi1 ha1_1 (hmem1eq ▸ hloaded) rfl hlo_b hhi_b hhtif_b halign_b
      (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb0) (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb1)
      (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb2) (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb3)
      (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb4) (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb5)
      (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb6) (by rw [ve_pay16_addr bufb hregb, hmem1eq]; exact hdb7) hi1
  have hmem2eq : σ2.mem = m0 := by rw [hmem2, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x800028f0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800028ec#64) 4 = (0x800028f0#64 : BitVec 64) from by decide] at this
  have ha5_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 q2) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, ld_sext_ofNat d0 d1 d2 d3 d4 d5 d6 d7 q2 hdrec]
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hframe2 : ∀ R : Register, NotWrittenVE R → σ2.regs.get? R = g R := fun R hR =>
    (frame_alu_ve hobs2 R hR hR.2.2.1).trans (hframe1 R hR)
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := value_equal_at_800028f8 hloaded
  have hout2 : σ2.sailOutput = o :=
    (by chain_out [hobs1, hobs2] : σ2.sailOutput = σ.sailOutput).trans hout
  have htail := ve_sub_seqz_ret g r m0 o c σ2 i2 (steps0 + 1 + 1)
    (BitVec.ofNat 64 q1) (BitVec.ofNat 64 q2) (0x800028f0#64) (0x800028f4#64) (0x800028f8#64)
    (((hsteps0.trans (Steps.single hs1)).trans (Steps.single hs2))) hi2 hG2 hmem2eq hout2 hloaded
    hpc2 ha0_2 ha5_2 hra_2 vmi2 hmi2 hrettgt hframe2
    (fun σ0 i0 u0 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 hi0 =>
      site_800028f0 σ0 i0 u0 (0x800028f0#64) vmi2 v10 v15 hG0 hpc0 hmi0 h10 h15 hl0 rfl hi0)
    (by decide)
    (fun σ0 i0 u0 vmi0 v10 hG0 hpc0 hmi0 h10 hl0 hi0 =>
      site_800028f4 σ0 i0 u0 (0x800028f4#64) vmi0 v10 hG0 hpc0 hmi0 h10 hl0 rfl hi0)
    (by decide)
    (by show m0[(2147494136 : Nat)]? = _; exact hbb0)
    (by show m0[(2147494136 + 1 : Nat)]? = _; exact hbb1)
    (by show m0[(2147494136 + 2 : Nat)]? = _; exact hbb2)
    (by show m0[(2147494136 + 3 : Nat)]? = _; exact hbb3)
    (by decide) (by rw [show tohostAddr = 0x8001ad00 from rfl]; decide) (by decide)
  exact htail

/-! ## Merged `value_equal_spec` (all non-`str` variants)

Cases on `(va, vb)`. Mismatched kinds and both-`null` reuse
`value_equal_spec_null_mismatch`; the four payload same-kind cases run
`ve_prefix → ve_dispatch → ve_{bool,int,native}_handler` with the matching bridge.
Closure/native pointer identity is bridged by the injectivity hypotheses `hφc`/`hN`.
The `str`-`str` case is supplied via `ve_str_handler` (in the str section below); every
other case is discharged here. -/
/-- Run `ve_prefix → ve_dispatch` from the entry precondition, landing at `handlerAddr va`
with the buffer pointers/ra/frame preserved. Shared by every same-kind payload case. -/
theorem ve_to_handler
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config)
    (hkeq : kindTag va = kindTag vb)
    (hG : GoodState c.σ) (hloaded : Value_equalLoaded c.σ.mem) (hjt : JumpTable c.σ.mem)
    (hmem : c.σ.mem = m0) (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000285c#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some bufa) (ha1 : c.σ.regs.get? Register.x11 = some bufb)
    (hra : c.σ.regs.get? Register.x1 = some r)
    (vmi : BitVec 64) (hmi : c.σ.regs.get? Register.minstret = some vmi) (htick : c.tick < 2)
    (hra' : ValueRepr m0 N φc bufa.toNat va) (hrb' : ValueRepr m0 N φc bufb.toNat vb)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hframe : ∀ R : Register, NotWrittenVE R → c.σ.regs.get? R = g R) :
    ∃ (σd : MState) (idd : Nat),
      Steps c ⟨σd, idd, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ∧ idd < 2 ∧
      GoodState σd ∧ σd.mem = m0 ∧ σd.sailOutput = o ∧ σd.regs.get? Register.PC = some (handlerAddr va) ∧
      σd.regs.get? Register.x10 = some bufa ∧ σd.regs.get? Register.x11 = some bufb ∧
      σd.regs.get? Register.x1 = some r ∧ (∃ w, σd.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, NotWrittenVE R → σd.regs.get? R = g R) := by
  have hloaded0 : Value_equalLoaded m0 := hmem ▸ hloaded
  have hjt0 : JumpTable m0 := hmem ▸ hjt
  obtain ⟨σp, ip, hstepsp, hip, hGp, hmemp, houtp, hpcp, hx15p, ha0p, ha1p, hrap, ⟨vmip, hmip⟩, hframep⟩ :=
    ve_prefix g bufa bufb r N φc va vb m0 o c hG hloaded hmem hout hpc ha0 ha1 hra vmi hmi
      htick hra' hrb' hrega hregb hkeq hframe
  have hx15p' : σp.regs.get? Register.x15 = some (BitVec.ofNat 64 (kindTag va)) := by rw [hx15p, hkeq]
  obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, hmid, hframed⟩ :=
    ve_dispatch g bufa bufb r va m0 o c σp ip (c.steps + 1 + 1 + 1 + 1 + 1)
      hstepsp hip hGp hmemp houtp hloaded0 hjt0 hpcp hx15p' ha0p ha1p hrap vmip hmip hframep
  exact ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, hmid, hframed⟩

theorem value_equal_spec_nonstr
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
    (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
    (hnotstr : ∀ sa sb, ¬ (va = .str sa ∧ vb = .str sb)) :
    Triple (ve_pre g bufa bufb r N φc va vb m0 o) (ve_post g r va vb m0 o) := by
  -- If kinds mismatch, use the mismatch theorem directly.
  rcases Classical.em (kindTag va = kindTag vb) with hkeq | hkeq
  case inr => exact value_equal_spec_null_mismatch g bufa bufb r N φc va vb m0 (Or.inl hkeq) o
  intro c hpre
  obtain ⟨hG, hloaded, hjt, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hra', hrb', hrega, hregb, hrettgt, hframe⟩ := hpre
  have hloaded0 : Value_equalLoaded m0 := hmem ▸ hloaded
  cases va with
  | null =>
    cases vb
    case null =>
      exact value_equal_spec_null_mismatch g bufa bufb r N φc _ _ m0 (Or.inr ⟨rfl, rfl⟩) o c
        ⟨hG, hloaded, hjt, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
          hra', hrb', hrega, hregb, hrettgt, hframe⟩
    all_goals (exfalso; simp [kindTag] at hkeq)
  | bool b1 =>
    cases vb
    case bool b2 =>
      obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
        ve_to_handler g bufa bufb r N φc (Value.bool b1) (Value.bool b2) m0 o c hkeq hG hloaded hjt
          hmem hout hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
      obtain ⟨_, hpb1⟩ := hra'
      obtain ⟨_, hpb2⟩ := hrb'
      rw [show handlerAddr (Value.bool b1) = 0x800028b0#64 from rfl] at hpcd
      obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, ha0_2, hra_2, hmi2, hmem2, hout2, hframe2⟩ :=
        ve_bool_handler g bufa bufb r m0 o c σd idd _ b1 b2 hstepsd hidd hGd hmemd houtd hloaded0
          hpcd ha0d ha1d hrad vmid hmid hrega hregb hrettgt hframed hpb1 hpb2
      exact ⟨⟨σ2, i2, _⟩, hs2, hG2, hpc2, by rw [ha0_2]; rfl, hra_2, hmi2, hi2, hmem2, hout2, hframe2⟩
    all_goals (exfalso; simp [kindTag] at hkeq)
  | int n1 =>
    cases vb
    case int n2 =>
      obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
        ve_to_handler g bufa bufb r N φc (Value.int n1) (Value.int n2) m0 o c hkeq hG hloaded hjt
          hmem hout hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
      obtain ⟨_, hpb1⟩ := hra'
      obtain ⟨_, hpb2⟩ := hrb'
      simp only [readI64, Option.map_eq_some_iff] at hpb1 hpb2
      obtain ⟨p1, hp1, hpn1⟩ := hpb1
      obtain ⟨p2, hp2, hpn2⟩ := hpb2
      rw [show handlerAddr (Value.int n1) = 0x80002894#64 from rfl] at hpcd
      obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, ha0_2, hra_2, hmi2, hmem2, hout2, hframe2⟩ :=
        ve_int_handler g bufa bufb r m0 o c σd idd _ p1 p2 hstepsd hidd hGd hmemd houtd hloaded0
          hpcd ha0d ha1d hrad vmid hmid hrega hregb hrettgt hframed hp1 hp2
      refine ⟨⟨σ2, i2, _⟩, hs2, hG2, hpc2, ?_, hra_2, hmi2, hi2, hmem2, hout2, hframe2⟩
      rw [ha0_2, int_eq_bridge p1 p2 n1 n2 hpn1 hpn2]; rfl
    all_goals (exfalso; simp [kindTag] at hkeq)
  | str sa =>
    cases vb
    case str sb => exact absurd ⟨rfl, rfl⟩ (hnotstr sa sb)
    all_goals (exfalso; simp [kindTag] at hkeq)
  | closure ca1 =>
    cases vb
    case closure ca2 =>
      obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
        ve_to_handler g bufa bufb r N φc (Value.closure ca1) (Value.closure ca2) m0 o c hkeq hG hloaded hjt
          hmem hout hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
      obtain ⟨_, hpb1, _⟩ := hra'
      obtain ⟨_, hpb2, _⟩ := hrb'
      rw [show handlerAddr (Value.closure ca1) = 0x80002894#64 from rfl] at hpcd
      obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, ha0_2, hra_2, hmi2, hmem2, hout2, hframe2⟩ :=
        ve_int_handler g bufa bufb r m0 o c σd idd _ (φc ca1) (φc ca2) hstepsd hidd hGd hmemd houtd hloaded0
          hpcd ha0d ha1d hrad vmid hmid hrega hregb hrettgt hframed hpb1 hpb2
      refine ⟨⟨σ2, i2, _⟩, hs2, hG2, hpc2, ?_, hra_2, hmi2, hi2, hmem2, hout2, hframe2⟩
      rw [ha0_2,
        ptr_eq_bridge φc ca1 ca2 (φc ca1) (φc ca2) rfl rfl
          (read64_lt m0 (bufa.toNat + 8) _ hpb1) (read64_lt m0 (bufb.toNat + 8) _ hpb2)
          (hφc ca1 ca2)]
      rfl
    all_goals (exfalso; simp [kindTag] at hkeq)
  | native f1 =>
    cases vb
    case native f2 =>
      obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
        ve_to_handler g bufa bufb r N φc (Value.native f1) (Value.native f2) m0 o c hkeq hG hloaded hjt
          hmem hout hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
      obtain ⟨_, _, hpb1⟩ := hra'
      obtain ⟨_, _, hpb2⟩ := hrb'
      rw [show handlerAddr (Value.native f1) = 0x800028e8#64 from rfl] at hpcd
      obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, ha0_2, hra_2, hmi2, hmem2, hout2, hframe2⟩ :=
        ve_native_handler g bufa bufb r m0 o c σd idd _ (N.addr f1) (N.addr f2) hstepsd hidd hGd hmemd houtd hloaded0
          hpcd ha0d ha1d hrad vmid hmid hrega hregb hrettgt hframed hpb1 hpb2
      refine ⟨⟨σ2, i2, _⟩, hs2, hG2, hpc2, ?_, hra_2, hmi2, hi2, hmem2, hout2, hframe2⟩
      rw [ha0_2,
        ptr_eq_bridge N.addr f1 f2 (N.addr f1) (N.addr f2) rfl rfl
          (read64_lt m0 (bufa.toNat + 16) _ hpb1) (read64_lt m0 (bufb.toNat + 16) _ hpb2)
          (hN f1 f2)]
      rfl
    all_goals (exfalso; simp [kindTag] at hkeq)

end Vsa.Sim
