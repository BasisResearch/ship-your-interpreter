import Vsa.Sim.EnvGetSpec7
import Vsa.Sim.EnvSetSites

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `env_set` code bytes survive a disjoint eight-byte stack spill. -/
theorem loaded_env_set_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80002cdc ∨ 0x80002da8 ≤ a8)
    (h : Env_setLoaded mem) : Env_setLoaded (writeMap8 mem a8 d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_setChunk0] at h0 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_setChunk1] at h1 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_setChunk2] at h2 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_setChunk3] at h3 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-- Count-agnostic entry facts for the first twelve instructions of `env_set`.
The `out` parameter is the caller's pointer to the replacement `Value`. -/
structure SetPrologueHeadSt
    (env name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Env_setLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002cdc#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some env
  a1 : c.σ.regs.get? Register.x11 = some name
  a2 : c.σ.regs.get? Register.x12 = some out
  ra : c.σ.regs.get? Register.x1 = some r0
  sp : c.σ.regs.get? Register.x2 = some sp0
  cs8 : c.σ.regs.get? Register.x8 = some r8
  cs9 : c.σ.regs.get? Register.x9 = some r9
  cs18 : c.σ.regs.get? Register.x18 = some r18
  cs19 : c.σ.regs.get? Register.x19 = some r19
  cs20 : c.σ.regs.get? Register.x20 = some r20
  cs21 : c.σ.regs.get? Register.x21 = some r21
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  envNe : (env == (0#64 : BitVec 64)) = false
  read_len : read32 m0 env.toNat = some len
  read_pn : read64 m0 (env.toNat + 8) = some pn
  spDrop : 0x40 ≤ sp0.toNat
  spLo : 0x80000000 ≤ sp0.toNat - 64
  spHi : sp0.toNat ≤ 0x100000000
  spWin : tohostAddr + 64 ≤ sp0.toNat - 64
  spAlign : sp0.toNat % 8 = 0
  spCode : sp0.toNat ≤ 0x80002cdc ∨ 0x80002da8 ≤ sp0.toNat - 64
  envHi : env.toNat + 24 ≤ 0x100000000
  envStackDisj : env.toNat + 24 ≤ sp0.toNat - 64 ∨ sp0.toNat ≤ env.toNat

/-- State after `env_set` has saved its caller frame and marshalled env/name/value,
before loading the current frame count. -/
structure SetPrologueHeadPost
    (env name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (m0 : Mem) (c0 c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80002d0c#64 : BitVec 64)
  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  out5 : c.σ.regs.get? Register.x21 = some out
  ra : c.σ.regs.get? Register.x1 = some r0
  sp : c.σ.regs.get? Register.x2 = some (sp0 - 64#64)
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  mem : ∃ m', c.σ.mem = m' ∧ Env_setLoaded m' ∧
    read64 m' ((sp0 - 64#64).toNat + 56) = some r0.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 48) = some r8.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 40) = some r9.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 32) = some r18.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 24) = some r19.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 16) = some r20.toNat ∧
    read64 m' ((sp0 - 64#64).toNat + 8) = some r21.toNat ∧
    (∀ a, ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64) →
      m'[a]? = m0[a]?)
  output : c.σ.sailOutput = c0.σ.sailOutput

 theorem env_set_prologue_head
    (env name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (m0 : Mem) (c : Config)
    (hSt : SetPrologueHeadSt env name out sp0 r0 r8 r9 r18 r19 r20 r21 len pn m0 c) :
    ∃ c', Steps c c' ∧
      SetPrologueHeadPost env name out sp0 r0 r8 r9 r18 r19 r20 r21 m0 c c' := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have hmem := hSt.mem
  have hloaded0 : Env_setLoaded m0 := hmem ▸ hSt.loadedG
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- the post-c14 stack pointer `sp = sp0 - 64`, its `.toNat`, and geometry.
  have hspNat : (sp0 + sign_extend (m := 64) (0xfc0#12)).toNat = sp0.toNat - 64 := by
    have hsext : (sign_extend (m := 64) (0xfc0#12) : BitVec 64) = BitVec.ofNat 64 (2^64 - 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hsext]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (2^64 - 64) < 2^64)]
    have hd := hSt.spDrop; have hlt := sp0.isLt
    -- sp0.toNat + (2^64 - 64) = (sp0.toNat - 64) + 2^64, and (x + 2^64) % 2^64 = x for x < 2^64
    rw [show sp0.toNat + (2^64 - 64) = (sp0.toNat - 64) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hspEq : (sp0 + sign_extend (m := 64) (0xfc0#12)) = sp0 - 64#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hspNat, BitVec.toNat_sub]
    have hd := hSt.spDrop; have hlt := sp0.isLt
    have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
    rw [h64, show 2^64 - 64 + sp0.toNat = (sp0.toNat - 64) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- spill-slot addresses (all within [sp, sp+64), sp = sp0-64)
  have hspBase : (sp0 - 64#64).toNat = sp0.toNat - 64 := by rw [← hspEq, hspNat]
  -- ============ c10: beqz a0 NOT taken (env ≠ 0) → c14 ============
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002cdc_nottaken_es c.σ c.tick c.steps (0x80002cdc#64) vmi env
      hSt.good hSt.pc hmi hSt.a0 hSt.loadedG rfl hSt.envNe hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hmem1e : σ1.mem = m0 := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002ce0#64) := by
    have := obs_bnottaken_pc hobs1
    rwa [show BitVec.addInt (0x80002cdc#64) 4 = (0x80002ce0#64:BitVec 64) from by decide] at this
  have bcarry1 : ∀ (R : Register) (w : RegisterType R),
      (Register.minstret == R) = false → (Register.PC == R) = false →
      (Register.nextPC == R) = false → (Register.minstret_increment == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → c.σ.regs.get? R = some w → σ1.regs.get? R = some w := by
    intro R w h1 h2 h4 h5 hmc hmt hmi hσ; exact obs_bnottaken_other hobs1 R hmc hmt hmi h1 h2 h4 h5 hσ
  have hsp1 := bcarry1 Register.x2 sp0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.sp
  have ha0_1 := bcarry1 Register.x10 env (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0
  have ha1_1 := bcarry1 Register.x11 name (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1
  have ha2_1 := bcarry1 Register.x12 out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2
  have hra1 := bcarry1 Register.x1 r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra
  have h8_1 := bcarry1 Register.x8 r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs8
  have h9_1 := bcarry1 Register.x9 r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs9
  have h18_1 := bcarry1 Register.x18 r18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs18
  have h19_1 := bcarry1 Register.x19 r19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs19
  have h20_1 := bcarry1 Register.x20 r20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs20
  have h21_1 := bcarry1 Register.x21 r21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs21
  obtain ⟨vmi1, hmi1⟩ := obs_bnottaken_minstret hobs1
  have hcode1 : Env_setLoaded σ1.mem := by rw [hmem1e]; exact hloaded0
  -- ============ c14: addi sp,sp,-64 → x2 := sp0 - 64 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002ce0_es σ1 i1 (c.steps+1) (0x80002ce0#64) vmi1 sp0 hG1 hpc1 hmi1 hsp1 hcode1 rfl hi1
  have hstep2 : Step (⟨σ1,i1,c.steps+1⟩ : Config) ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hmem2e : σ2.mem = m0 := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002ce4#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80002ce0#64) 4 = (0x80002ce4#64:BitVec 64) from by decide] at this
  have hsp2 : σ2.regs.get? Register.x2 = some (sp0 - 64#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hspEq] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have hra2 := obs_alu_other' hobs2 Register.x1 (by decide) hra1
  have h8_2 := obs_alu_other' hobs2 Register.x8 (by decide) h8_1
  have h9_2 := obs_alu_other' hobs2 Register.x9 (by decide) h9_1
  have h18_2 := obs_alu_other' hobs2 Register.x18 (by decide) h18_1
  have h19_2 := obs_alu_other' hobs2 Register.x19 (by decide) h19_1
  have h20_2 := obs_alu_other' hobs2 Register.x20 (by decide) h20_1
  have h21_2 := obs_alu_other' hobs2 Register.x21 (by decide) h21_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Env_setLoaded σ2.mem := by rw [hmem2e]; exact hloaded0
  -- store-address helpers: (sp0-64 + sext off).toNat = (sp0.toNat - 64) + off
  have hoff : ∀ (off : BitVec 12) (k : Nat), (sign_extend (m := 64) off : BitVec 64).toNat = k →
      k < 0x40 → ((sp0 - 64#64) + sign_extend (m := 64) off).toNat = (sp0.toNat - 64) + k := by
    intro off k hk hlt
    rw [BitVec.toNat_add, hspBase, hk]
    have := hSt.spHi; have := hSt.spDrop
    rw [Nat.mod_eq_of_lt (by omega)]
  -- concrete offset values
  have ho8  : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  have ho16 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
  have ho24 : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
  have ho32 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
  have ho40 : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
  have ho48 : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
  have ho56 : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide
  have hspb := hSt.spWin; have hspHi := hSt.spHi; have hspLo := hSt.spLo
  have hspAl := hSt.spAlign; have hspDr := hSt.spDrop
  have hspalign : (sp0.toNat - 64) % 8 = 0 := by omega
  -- the running memory after K spills; each `mkDisj` is `read64` at a spill slot
  -- against the writeMap8 window, disjoint (distinct 8-aligned slots).
  -- Spill store-address side conditions helper (RAM, above-HTIF, aligned)
  rw [htoh] at hspb
  have sc : ∀ (k : Nat), k < 0x40 → k % 8 = 0 →
      (0x80000000 ≤ (sp0.toNat - 64) + k) ∧ ((sp0.toNat - 64) + k + 8 ≤ 0x100000000) ∧
      (tohostAddr + 16 ≤ (sp0.toNat - 64) + k) ∧ (((sp0.toNat - 64) + k) % 8 = 0) := by
    intro k hk hkm
    refine ⟨by omega, by omega, by rw [htoh]; omega, by omega⟩
  -- ============ c18: sd s3(x19),24(sp) → *(sp+24) := r19 ============
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002ce4_es σ2 i2 (c.steps+1+1) (0x80002ce4#64) vmi2 (sp0 - 64#64) r19
      hG2 hpc2 hmi2 hsp2 h19_2 hcode2 rfl
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.2.2) hi2
  have hstep3 : Step (⟨σ2,i2,c.steps+1+1⟩ : Config) ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hm3 : σ3.mem = writeMap8 m0 ((sp0.toNat - 64) + 24) (sdData_val r19) := by
    rw [hmem3, mem_afterNextPC, mem_afterPrelude, hmem2e, hoff _ 24 ho24 (by decide)]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002ce8#64) := by
    have := obs_store_pc hobs3; rwa [show BitVec.addInt (0x80002ce4#64) 4 = (0x80002ce8#64:BitVec 64) from by decide] at this
  have hsp3 := obs_store_other' hobs3 Register.x2 (by decide) hsp2
  have h20_3 := obs_store_other' hobs3 Register.x20 (by decide) h20_2
  have h21_3 := obs_store_other' hobs3 Register.x21 (by decide) h21_2
  have hra3 := obs_store_other' hobs3 Register.x1 (by decide) hra2
  have h8_3 := obs_store_other' hobs3 Register.x8 (by decide) h8_2
  have h9_3 := obs_store_other' hobs3 Register.x9 (by decide) h9_2
  have h18_3 := obs_store_other' hobs3 Register.x18 (by decide) h18_2
  have h19_3 := obs_store_other' hobs3 Register.x19 (by decide) h19_2
  have ha0_3 := obs_store_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_store_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_store_other' hobs3 Register.x12 (by decide) ha2_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hspCode := hSt.spCode
  have hcodeDisj : ∀ k, k < 0x40 → ((sp0.toNat - 64) + k + 8 ≤ 0x80002cdc ∨ 0x80002da8 ≤ (sp0.toNat - 64) + k) := by
    intro k hk
    rcases hspCode with h | h
    · left; omega
    · right; omega
  have hcode3 : Env_setLoaded σ3.mem := by
    rw [hm3]; exact loaded_env_set_writeMap8 m0 _ _ (hcodeDisj 24 (by decide)) hloaded0
  -- ============ c1c: sd s4(x20),16(sp) → *(sp+16) := r20 ============
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002ce8_es σ3 i3 (c.steps+1+1+1) (0x80002ce8#64) vmi3 (sp0 - 64#64) r20
      hG3 hpc3 hmi3 hsp3 h20_3 hcode3 rfl
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.2.2) hi3
  have hstep4 : Step (⟨σ3,i3,c.steps+1+1+1⟩ : Config) ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hm4 : σ4.mem = writeMap8 σ3.mem ((sp0.toNat - 64) + 16) (sdData_val r20) := by
    rw [hmem4, mem_afterNextPC, mem_afterPrelude, hoff _ 16 ho16 (by decide)]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002cec#64) := by
    have := obs_store_pc hobs4; rwa [show BitVec.addInt (0x80002ce8#64) 4 = (0x80002cec#64:BitVec 64) from by decide] at this
  have hsp4 := obs_store_other' hobs4 Register.x2 (by decide) hsp3
  have h21_4 := obs_store_other' hobs4 Register.x21 (by decide) h21_3
  have hra4 := obs_store_other' hobs4 Register.x1 (by decide) hra3
  have h8_4 := obs_store_other' hobs4 Register.x8 (by decide) h8_3
  have h9_4 := obs_store_other' hobs4 Register.x9 (by decide) h9_3
  have h18_4 := obs_store_other' hobs4 Register.x18 (by decide) h18_3
  have h19_4 := obs_store_other' hobs4 Register.x19 (by decide) h19_3
  have h20_4 := obs_store_other' hobs4 Register.x20 (by decide) h20_3
  have ha0_4 := obs_store_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_store_other' hobs4 Register.x12 (by decide) ha2_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hcode4 : Env_setLoaded σ4.mem := by
    rw [hm4]; exact loaded_env_set_writeMap8 σ3.mem _ _ (hcodeDisj 16 (by decide)) hcode3
  -- ============ c20: sd s5(x21),8(sp) → *(sp+8) := r21 ============
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002cec_es σ4 i4 (c.steps+1+1+1+1) (0x80002cec#64) vmi4 (sp0 - 64#64) r21
      hG4 hpc4 hmi4 hsp4 h21_4 hcode4 rfl
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.2.2) hi4
  have hstep5 : Step (⟨σ4,i4,c.steps+1+1+1+1⟩ : Config) ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hm5 : σ5.mem = writeMap8 σ4.mem ((sp0.toNat - 64) + 8) (sdData_val r21) := by
    rw [hmem5, mem_afterNextPC, mem_afterPrelude, hoff _ 8 ho8 (by decide)]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002cf0#64) := by
    have := obs_store_pc hobs5; rwa [show BitVec.addInt (0x80002cec#64) 4 = (0x80002cf0#64:BitVec 64) from by decide] at this
  have hsp5 := obs_store_other' hobs5 Register.x2 (by decide) hsp4
  have hra5 := obs_store_other' hobs5 Register.x1 (by decide) hra4
  have h8_5 := obs_store_other' hobs5 Register.x8 (by decide) h8_4
  have h9_5 := obs_store_other' hobs5 Register.x9 (by decide) h9_4
  have h18_5 := obs_store_other' hobs5 Register.x18 (by decide) h18_4
  have h19_5 := obs_store_other' hobs5 Register.x19 (by decide) h19_4
  have h20_5 := obs_store_other' hobs5 Register.x20 (by decide) h20_4
  have h21_5 := obs_store_other' hobs5 Register.x21 (by decide) h21_4
  have ha0_5 := obs_store_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_store_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_store_other' hobs5 Register.x12 (by decide) ha2_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hcode5 : Env_setLoaded σ5.mem := by
    rw [hm5]; exact loaded_env_set_writeMap8 σ4.mem _ _ (hcodeDisj 8 (by decide)) hcode4
  -- ============ c24: sd ra(x1),56(sp) → *(sp+56) := r0 ============
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002cf0_es σ5 i5 (c.steps+1+1+1+1+1) (0x80002cf0#64) vmi5 (sp0 - 64#64) r0
      hG5 hpc5 hmi5 hsp5 hra5 hcode5 rfl
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.2.2) hi5
  have hstep6 : Step (⟨σ5,i5,c.steps+1+1+1+1+1⟩ : Config) ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hm6 : σ6.mem = writeMap8 σ5.mem ((sp0.toNat - 64) + 56) (sdData_val r0) := by
    rw [hmem6, mem_afterNextPC, mem_afterPrelude, hoff _ 56 ho56 (by decide)]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002cf4#64) := by
    have := obs_store_pc hobs6; rwa [show BitVec.addInt (0x80002cf0#64) 4 = (0x80002cf4#64:BitVec 64) from by decide] at this
  have hsp6 := obs_store_other' hobs6 Register.x2 (by decide) hsp5
  have h8_6 := obs_store_other' hobs6 Register.x8 (by decide) h8_5
  have h9_6 := obs_store_other' hobs6 Register.x9 (by decide) h9_5
  have h18_6 := obs_store_other' hobs6 Register.x18 (by decide) h18_5
  have h19_6 := obs_store_other' hobs6 Register.x19 (by decide) h19_5
  have h20_6 := obs_store_other' hobs6 Register.x20 (by decide) h20_5
  have h21_6 := obs_store_other' hobs6 Register.x21 (by decide) h21_5
  have ha0_6 := obs_store_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_store_other' hobs6 Register.x11 (by decide) ha1_5
  have ha2_6 := obs_store_other' hobs6 Register.x12 (by decide) ha2_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hcode6 : Env_setLoaded σ6.mem := by
    rw [hm6]; exact loaded_env_set_writeMap8 σ5.mem _ _ (hcodeDisj 56 (by decide)) hcode5
  -- ============ c28: sd s0(x8),48(sp) → *(sp+48) := r8 ============
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80002cf4_es σ6 i6 (c.steps+1+1+1+1+1+1) (0x80002cf4#64) vmi6 (sp0 - 64#64) r8
      hG6 hpc6 hmi6 hsp6 h8_6 hcode6 rfl
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.2.2) hi6
  have hstep7 : Step (⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ : Config) ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hm7 : σ7.mem = writeMap8 σ6.mem ((sp0.toNat - 64) + 48) (sdData_val r8) := by
    rw [hmem7, mem_afterNextPC, mem_afterPrelude, hoff _ 48 ho48 (by decide)]
  have hpc7 : σ7.regs.get? Register.PC = some (0x80002cf8#64) := by
    have := obs_store_pc hobs7; rwa [show BitVec.addInt (0x80002cf4#64) 4 = (0x80002cf8#64:BitVec 64) from by decide] at this
  have hsp7 := obs_store_other' hobs7 Register.x2 (by decide) hsp6
  have h9_7 := obs_store_other' hobs7 Register.x9 (by decide) h9_6
  have h18_7 := obs_store_other' hobs7 Register.x18 (by decide) h18_6
  have h19_7 := obs_store_other' hobs7 Register.x19 (by decide) h19_6
  have h20_7 := obs_store_other' hobs7 Register.x20 (by decide) h20_6
  have h21_7 := obs_store_other' hobs7 Register.x21 (by decide) h21_6
  have ha0_7 := obs_store_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_store_other' hobs7 Register.x11 (by decide) ha1_6
  have ha2_7 := obs_store_other' hobs7 Register.x12 (by decide) ha2_6
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hcode7 : Env_setLoaded σ7.mem := by
    rw [hm7]; exact loaded_env_set_writeMap8 σ6.mem _ _ (hcodeDisj 48 (by decide)) hcode6
  -- ============ c2c: sd s1(x9),40(sp) → *(sp+40) := r9 ============
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80002cf8_es σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80002cf8#64) vmi7 (sp0 - 64#64) r9
      hG7 hpc7 hmi7 hsp7 h9_7 hcode7 rfl
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.2.2) hi7
  have hstep8 : Step (⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ : Config) ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hm8 : σ8.mem = writeMap8 σ7.mem ((sp0.toNat - 64) + 40) (sdData_val r9) := by
    rw [hmem8, mem_afterNextPC, mem_afterPrelude, hoff _ 40 ho40 (by decide)]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80002cfc#64) := by
    have := obs_store_pc hobs8; rwa [show BitVec.addInt (0x80002cf8#64) 4 = (0x80002cfc#64:BitVec 64) from by decide] at this
  have hsp8 := obs_store_other' hobs8 Register.x2 (by decide) hsp7
  have h18_8 := obs_store_other' hobs8 Register.x18 (by decide) h18_7
  have h19_8 := obs_store_other' hobs8 Register.x19 (by decide) h19_7
  have h20_8 := obs_store_other' hobs8 Register.x20 (by decide) h20_7
  have h21_8 := obs_store_other' hobs8 Register.x21 (by decide) h21_7
  have ha0_8 := obs_store_other' hobs8 Register.x10 (by decide) ha0_7
  have ha1_8 := obs_store_other' hobs8 Register.x11 (by decide) ha1_7
  have ha2_8 := obs_store_other' hobs8 Register.x12 (by decide) ha2_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hcode8 : Env_setLoaded σ8.mem := by
    rw [hm8]; exact loaded_env_set_writeMap8 σ7.mem _ _ (hcodeDisj 40 (by decide)) hcode7
  -- ============ c30: sd s2(x18),32(sp) → *(sp+32) := r18 ============
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80002cfc_es σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80002cfc#64) vmi8 (sp0 - 64#64) r18
      hG8 hpc8 hmi8 hsp8 h18_8 hcode8 rfl
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.2.2) hi8
  have hstep9 : Step (⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ : Config) ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hm9 : σ9.mem = writeMap8 σ8.mem ((sp0.toNat - 64) + 32) (sdData_val r18) := by
    rw [hmem9, mem_afterNextPC, mem_afterPrelude, hoff _ 32 ho32 (by decide)]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80002d00#64) := by
    have := obs_store_pc hobs9; rwa [show BitVec.addInt (0x80002cfc#64) 4 = (0x80002d00#64:BitVec 64) from by decide] at this
  have hsp9 := obs_store_other' hobs9 Register.x2 (by decide) hsp8
  have ha0_9 := obs_store_other' hobs9 Register.x10 (by decide) ha0_8
  have ha1_9 := obs_store_other' hobs9 Register.x11 (by decide) ha1_8
  have ha2_9 := obs_store_other' hobs9 Register.x12 (by decide) ha2_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
  have hcode9 : Env_setLoaded σ9.mem := by
    rw [hm9]; exact loaded_env_set_writeMap8 σ8.mem _ _ (hcodeDisj 32 (by decide)) hcode8
  -- σ9.mem as the 7-fold writeMap8 of m0
  have hm9full : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
      (writeMap8 (writeMap8 m0 ((sp0.toNat-64)+24) (sdData_val r19))
        ((sp0.toNat-64)+16) (sdData_val r20)) ((sp0.toNat-64)+8) (sdData_val r21))
        ((sp0.toNat-64)+56) (sdData_val r0)) ((sp0.toNat-64)+48) (sdData_val r8))
        ((sp0.toNat-64)+40) (sdData_val r9)) ((sp0.toNat-64)+32) (sdData_val r18) := by
    rw [hm9, hm8, hm7, hm6, hm5, hm4, hm3]
  -- env-header window disjointness against every spill slot (used to survive reads)
  have hdisjSlot8 : ∀ (a slotoff : Nat), env.toNat ≤ a → a + 8 ≤ env.toNat + 24 →
      slotoff ≤ 56 → (a + 8 ≤ (sp0.toNat-64)+slotoff ∨ (sp0.toNat-64)+slotoff + 8 ≤ a) := by
    intro a slotoff ha1 ha2 hs
    have hd := hSt.spDrop
    rcases hSt.envStackDisj with h | h
    · left; omega
    · right; omega
  have hdisjSlot4 : ∀ (a slotoff : Nat), env.toNat ≤ a → a + 4 ≤ env.toNat + 24 →
      slotoff ≤ 56 → (a + 4 ≤ (sp0.toNat-64)+slotoff ∨ (sp0.toNat-64)+slotoff + 8 ≤ a) := by
    intro a slotoff ha1 ha2 hs
    have hd := hSt.spDrop
    rcases hSt.envStackDisj with h | h
    · left; omega
    · right; omega
  have henvHi := hSt.envHi
  -- read64 at env+16 survives all 7 writes
  have hread_pv_env : read64 σ9.mem (env.toNat + 16) = read64 m0 (env.toNat + 16) := by
    rw [hm9full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 32 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 40 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 48 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 56 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 8 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 16 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 24 (by omega) (by omega) (by decide))]
  -- read32 at env survives all 7 writes (env count)
  have hread_len : read32 σ9.mem env.toNat = some len := by
    have hsurv : read32 σ9.mem env.toNat = read32 m0 env.toNat := by
      rw [hm9full,
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 32 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 40 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 48 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 56 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 8 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 16 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 24 (by omega) (by omega) (by decide))]
    rw [hsurv]; exact hSt.read_len
  -- read64 at env+8 survives all 7 writes (env names)
  have hread_pn : read64 σ9.mem (env.toNat + 8) = some pn := by
    have hsurv : read64 σ9.mem (env.toNat + 8) = read64 m0 (env.toNat + 8) := by
      rw [hm9full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 32 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 40 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 48 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 56 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 8 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 16 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 24 (by omega) (by omega) (by decide))]
    rw [hsurv]; exact hSt.read_pn
  -- ============ c34: mv s4,a0 → x20 := env ============
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80002d00_es σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80002d00#64) vmi9 env
      hG9 hpc9 hmi9 ha0_9 hcode9 rfl hi9
  have hmem10e : σ10.mem = σ9.mem := hmem10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80002d04#64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x80002d00#64) 4 = (0x80002d04#64:BitVec 64) from by decide] at this
  have h20_10 : σ10.regs.get? Register.x20 = some env := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (env + sign_extend (m := 64) (0x000#12) : BitVec 64) = env from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have ha1_10 := obs_alu_other' hobs10 Register.x11 (by decide) ha1_9
  have ha2_10 := obs_alu_other' hobs10 Register.x12 (by decide) ha2_9
  have hsp10 := obs_alu_other' hobs10 Register.x2 (by decide) hsp9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hcode10 : Env_setLoaded σ10.mem := by rw [hmem10e]; exact hcode9
  -- ============ c38: mv s3,a1 → x19 := name ============
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80002d04_es σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80002d04#64) vmi10 name hG10 hpc10 hmi10 ha1_10 hcode10 rfl hi10
  have hmem11e : σ11.mem = σ9.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80002d08#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80002d04#64) 4 = (0x80002d08#64:BitVec 64) from by decide] at this
  have h19_11 : σ11.regs.get? Register.x19 = some name := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (name + sign_extend (m := 64) (0x000#12) : BitVec 64) = name from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have h20_11 := obs_alu_other' hobs11 Register.x20 (by decide) h20_10
  have ha2_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
  have hsp11 := obs_alu_other' hobs11 Register.x2 (by decide) hsp10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hcode11 : Env_setLoaded σ11.mem := by rw [hmem11e]; exact hcode9
  -- ============ c3c: mv s5,a2 → x21 := out ============
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80002d08_es σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80002d08#64) vmi11 out hG11 hpc11 hmi11 ha2_11 hcode11 rfl hi11
  have hmem12e : σ12.mem = σ9.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x80002d0c#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80002d08#64) 4 = (0x80002d0c#64:BitVec 64) from by decide] at this
  have h21_12 : σ12.regs.get? Register.x21 = some out := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (out + sign_extend (m := 64) (0x000#12) : BitVec 64) = out from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have h20_12 := obs_alu_other' hobs12 Register.x20 (by decide) h20_11
  have h19_12 := obs_alu_other' hobs12 Register.x19 (by decide) h19_11
  have hsp12 := obs_alu_other' hobs12 Register.x2 (by decide) hsp11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hcode12 : Env_setLoaded σ12.mem := by rw [hmem12e]; exact hcode9

  have hra12 : σ12.regs.get? Register.x1 = some r0 := by
    have h0 := obs_store_other' hobs6 Register.x1 (by decide) hra5
    have h1 := obs_store_other' hobs7 Register.x1 (by decide) h0
    have h2 := obs_store_other' hobs8 Register.x1 (by decide) h1
    have h3 := obs_store_other' hobs9 Register.x1 (by decide) h2
    have h4 := obs_alu_other' hobs10 Register.x1 (by decide) h3
    have h5 := obs_alu_other' hobs11 Register.x1 (by decide) h4
    exact obs_alu_other' hobs12 Register.x1 (by decide) h5
  have hchain : Steps c ⟨σ12, i12, _⟩ :=
    (Steps.single hstep1).trans (Steps.single hstep2) |>.trans (Steps.single hstep3)
      |>.trans (Steps.single hstep4) |>.trans (Steps.single hstep5) |>.trans (Steps.single hstep6)
      |>.trans (Steps.single hstep7) |>.trans (Steps.single hstep8) |>.trans (Steps.single hstep9)
      |>.trans (Steps.single hs10) |>.trans (Steps.single hs11) |>.trans (Steps.single hs12)
  have hm12full : σ12.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
      (writeMap8 (writeMap8 m0 ((sp0.toNat-64)+24) (sdData_val r19))
        ((sp0.toNat-64)+16) (sdData_val r20)) ((sp0.toNat-64)+8) (sdData_val r21))
        ((sp0.toNat-64)+56) (sdData_val r0)) ((sp0.toNat-64)+48) (sdData_val r8))
        ((sp0.toNat-64)+40) (sdData_val r9)) ((sp0.toNat-64)+32) (sdData_val r18) := by
    rw [hmem12e]
    exact hm9full
  have hbn : ∀ off, ((sp0 - 64#64).toNat + off) = (sp0.toNat - 64) + off := by
    intro off
    rw [hspBase]
  refine ⟨⟨σ12, i12, _⟩, hchain, ?_⟩
  refine ⟨hG12, hi12, hpc12, h20_12, h19_12, h21_12, hra12, hsp12,
    ⟨vmi12, hmi12⟩, ?_, ?_⟩
  · refine ⟨σ12.mem, rfl, hcode12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full, read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · rw [hbn, hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8 _ _ _, sdData_toNat]
    · intro a hnot
      rw [hm12full]
      have hd := hSt.spDrop
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]
  · rw [hobs12.out, sailOutput_sigmaPost_alu,
      hobs11.out, sailOutput_sigmaPost_alu,
      hobs10.out, sailOutput_sigmaPost_alu,
      hobs9.out, sailOutput_sigmaPost_store,
      hobs8.out, sailOutput_sigmaPost_store,
      hobs7.out, sailOutput_sigmaPost_store,
      hobs6.out, sailOutput_sigmaPost_store,
      hobs5.out, sailOutput_sigmaPost_store,
      hobs4.out, sailOutput_sigmaPost_store,
      hobs3.out, sailOutput_sigmaPost_store,
      hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_branch_nottaken]

#print axioms env_set_prologue_head

end Vsa.Sim
