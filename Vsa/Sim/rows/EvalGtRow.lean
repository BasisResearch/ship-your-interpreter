import Vsa.Sim.EvalBinSim4

/-!
# `EvalGtRow` — Wave-D M4 row: `evalGtSim` (the `EvalE.binary .gt` int comparison)

Mirrors `blockC_lt`/`evalLtSim` (EvalBinSim4) for the `.gt` operator (token 22,
CSWTCH.18 slot `opTableBase+44`). Same operator-dispatch σ-walk + shared cmp arm
(0x80003628); the ladder is `beq@0x800036a8` NOT-taken (22≠21) → `beq@0x800036b0`
TAKEN (22=22) → `sgtz a1,a1` fixup @0x80003ae4 → `gt_fixup_bridge`, then
`value_bool` → `PreEpilogueVD .bool(a > b)`.

Reuses `CmpTailSites*`, `CmpBridges.gt_fixup_bridge`, `GtSlotPinned`,
`value_bool_spec_full`, `blockB_binary`, `blockD_v_rec`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem blockC_gt
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 22 ∧      -- op token = binOpTok .gt
        GtSlotPinned c.σ.mem ∧
        (∀ k : Nat, ∃ w : BitVec 8, c.σ.mem[k]? = some w) ∧
        c.σ.regs.get? Register.x19 = some Wl ∧
        read64 c.σ.mem (sp.toNat - 960) = some Wl.toNat ∧
        read64 c.σ.mem (sp.toNat - 1088) = some (2#64 : BitVec 64).toNat ∧
        aExpr.toNat % 4 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        String.join out0.toList = st''.out ∧
        c.σ.sailOutput = out0 ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        Value_boolLoaded c.σ.mem ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo) ∧
        (opTableBase + 4 ≤ SL.lo ∨ sp.toNat ≤ opTableBase) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        gpre Register.x19 = some v19 ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfm φcm φfe φce : Addr → Nat),
        PhiExtends φf φfm st'.store.frames.size ∧
        PhiExtends φc φcm st'.store.closures.size ∧
        PhiExtends φfm φfe st''.store.frames.size ∧
        PhiExtends φcm φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (a > b)) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hFullPop, hX19, hWlBuf, hKindResp,
    hexprAl, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl,
    hVbool, hcodeStk, hviStk, hTableStk, hsretInSL,
    hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi,
    hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨w19, hgprex19', hs3slot⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hMemExt, hmemframe⟩ := hTS
  have hw19 : w19 = v19 := by rw [hgprex19] at hgprex19'; exact (Option.some.inj hgprex19').symm
  obtain ⟨φfm, φcm, hpfm, hpcm, ⟨φcr, hpcr, hvalR⟩, ⟨φcl, hvalL⟩,
    φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hx8c : c.σ.regs.get? Register.x8 = some aExpr :=
    (hframe Register.x8 (by decide) (by decide)).trans hgx8
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  have hline4 : (aExpr + sign_extend (m := 64) (0x004#12)).toNat = aExpr.toNat + 4 := by
    have hs : (sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) 22 hopTok
  obtain ⟨lb0, hlb0⟩ := hFullPop (aExpr.toNat + 4)
  obtain ⟨lb1, hlb1⟩ := hFullPop (aExpr.toNat + 4 + 1)
  obtain ⟨lb2, hlb2⟩ := hFullPop (aExpr.toNat + 4 + 2)
  obtain ⟨lb3, hlb3⟩ := hFullPop (aExpr.toNat + 4 + 3)
  have hvalR' : ValueRepr c.σ.mem N φcr (sp.toNat - 944) (.int b) := hvalR
  obtain ⟨hkindR, pR, hpayR64, hpRb⟩ := valueRepr_int_pay64 hvalR'
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 2 hkindR
  obtain ⟨rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7, hrpb0, hrpb1, hrpb2, hrpb3, hrpb4, hrpb5, hrpb6, hrpb7, hrprec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 944 + 8) pR hpayR64
  let Wr : BitVec 64 := sign_extend (m := 64)
    ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))
  have hWrNat : Wr.toNat = pR := by
    show (sign_extend (m := 64)
      ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))).toNat = pR
    rw [sext_full, word8_toNat_recon, hrprec]
  have hWr_toInt : Wr.toInt = b := by
    have hpe : Wr = BitVec.ofNat 64 pR := by rw [← hWrNat]; exact (ofNat_toNat_self64 Wr).symm
    rw [hpe]; exact hpRb
  have hvalL' : ValueRepr c.σ.mem N φcl (sp.toNat - 968) (.int a) := hvalL
  obtain ⟨hkindL, pL, hpayL64, hpLa⟩ := valueRepr_int_pay64 hvalL'
  have hpayL64' : read64 c.σ.mem (sp.toNat - 960) = some pL := by
    have e : sp.toNat - 968 + 8 = sp.toNat - 960 := by omega
    rw [e] at hpayL64; exact hpayL64
  have hWlNat : Wl.toNat = pL := by
    have := hWlBuf.symm.trans hpayL64'; exact Option.some.inj this
  have hWl_toInt : Wl.toInt = a := by
    have hpe : Wl = BitVec.ofNat 64 pL := by rw [← hWlNat]; exact (ofNat_toNat_self64 Wl).symm
    rw [hpe]; exact hpLa
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (22#64 : BitVec 64) := by
    rw [sext_word_small _ 22 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  have hRkindVal : (sign_extend (m := 64) ((((rkb3.append rkb2).append rkb1).append rkb0) : BitVec (8*4)))
      = (2#64 : BitVec 64) := by
    rw [sext_word_small _ 2 (by decide) (by rw [word_toNat_recon]; exact hrkbrec)]
  have haddr144 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  have haddr152 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by omega) hsp1088
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088
  have haddr136 : ((sp - 1088#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 952 :=
    spill_addr sp (0x088#12) 952 (by decide) (by omega) hsp1088
  have haddr160 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by omega) hsp1088
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr240 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat = sp.toNat - 848 :=
    spill_addr sp (0x0f0#12) 848 (by decide) (by omega) hsp1088
  have haddr248 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat = sp.toNat - 840 :=
    spill_addr sp (0x0f8#12) 840 (by decide) (by omega) hsp1088
  have haddr256 : ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat = sp.toNat - 832 :=
    spill_addr sp (0x100#12) 832 (by decide) (by omega) hsp1088
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by omega) hsp1088
  --------------------------------------------------------------------------------
  -- 0x8000351c: lw a2,8(s0) → x12 := 20#64
  --------------------------------------------------------------------------------
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000351c_ee c.σ c.tick c.steps (0x8000351c#64) vmi aExpr ob0 ob1 ob2 ob3
      hG hpc hmi hx8c hcode rfl
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; exact hob0) (by rw [hop8]; exact hob1)
      (by rw [hop8]; exact hob2) (by rw [hop8]; exact hob3) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003520#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000351c#64) 4 = (0x80003520#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some (22#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hopVal] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl := obs_alu_other hobs1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX19
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8c
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout0eq
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003520: li a4,12 → x14 := 12#64
  --------------------------------------------------------------------------------
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003520_ee σ1 i1 (c.steps + 1) (0x80003520#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003524#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003520#64) 4 = (0x80003524#64 : BitVec 64) from by decide] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (12#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12)) = (12#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12_2 : σ2.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl := obs_alu_other hobs2 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aExpr := obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003524: lw s0,4(s0) → x8 := e->line (dead)
  --------------------------------------------------------------------------------
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80003524_ee σ2 i2 (c.steps + 1 + 1) (0x80003524#64) vmi2 aExpr lb0 lb1 lb2 lb3
      hG2 hpc2 hmi2 hx8_2 hcode2 rfl
      (by rw [hline4]; omega) (by rw [hline4]; omega)
      (by rw [hline4, htoh]; right; omega) (by rw [hline4]; omega)
      (by rw [hline4, hmem2e]; exact hlb0) (by rw [hline4, hmem2e]; exact hlb1)
      (by rw [hline4, hmem2e]; exact hlb2) (by rw [hline4, hmem2e]; exact hlb3) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003528#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80003524#64) 4 = (0x80003528#64 : BitVec 64) from by decide] at this
  have hx14_3 : σ3.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hx12_3 : σ3.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other hobs3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have hx19_3 : σ3.regs.get? Register.x19 = some Wl := obs_alu_other hobs3 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003528: addiw a5,a2,-11 → x15 := 9#64
  --------------------------------------------------------------------------------
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003528_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x80003528#64) vmi3 (22#64) hG3 hpc3 hmi3 hx12_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = c.σ.mem := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000352c#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80003528#64) 4 = (0x8000352c#64 : BitVec 64) from by decide] at this
  have hx15_4 : σ4.regs.get? Register.x15 = some (11#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((22#64 : BitVec 64) + sign_extend (m := 64) (0xff5#12)) 31 0)) = (11#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_4 : σ4.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_alu_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have hx19_4 : σ4.regs.get? Register.x19 = some Wl := obs_alu_other hobs4 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_3
  have hx12_4 : σ4.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000352c: lw a0,144(sp) → x10 := vr.kind = 2#64
  --------------------------------------------------------------------------------
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_8000352c_ee σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000352c#64) vmi4 (sp - 1088#64)
      rkb0 rkb1 rkb2 rkb3 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmem4e]; exact hrkb0) (by rw [haddr144, hmem4e]; exact hrkb1)
      (by rw [haddr144, hmem4e]; exact hrkb2) (by rw [haddr144, hmem4e]; exact hrkb3) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003530#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000352c#64) 4 = (0x80003530#64 : BitVec 64) from by decide] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some (2#64) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hRkindVal] at this
  have hx15_5 : σ5.regs.get? Register.x15 = some (11#64) := obs_alu_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_4
  have hx14_5 : σ5.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have hx19_5 : σ5.regs.get? Register.x19 = some Wl := obs_alu_other hobs5 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_4
  have hx12_5 : σ5.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003530: ld a7,152(sp) → x17 := vr.payload word = Wr
  --------------------------------------------------------------------------------
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003530_ee σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003530#64) vmi5 (sp - 1088#64)
      rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmem5e]; have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
          rw [← e]; exact hrpb0)
      (by rw [haddr152, hmem5e]; have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
          rw [show sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1 from by omega]; exact hrpb1)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2 from by omega]; exact hrpb2)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3 from by omega]; exact hrpb3)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4 from by omega]; exact hrpb4)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5 from by omega]; exact hrpb5)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6 from by omega]; exact hrpb6)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7 from by omega]; exact hrpb7) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003534#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80003530#64) 4 = (0x80003534#64 : BitVec 64) from by decide] at this
  have hx17_6 : σ6.regs.get? Register.x17 = some Wr := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact this
  have hx10_6 : σ6.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
  have hx15_6 : σ6.regs.get? Register.x15 = some (11#64) := obs_alu_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_5
  have hx14_6 : σ6.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_5
  have hx19_6 : σ6.regs.get? Register.x19 = some Wl := obs_alu_other hobs6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_5
  have hx12_6 : σ6.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003534: bltu a4,a5 (NOT taken; 12 <u 9 is false)
  --------------------------------------------------------------------------------
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003534_nottaken_ee σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003534#64) vmi6 (12#64) (11#64)
      hG6 hpc6 hmi6 hx14_6 hx15_6 hcode6 rfl (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, _⟩ ⟨σ7, i7, _⟩ := hs7'
  have hmem7e : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003538#64) := by
    have := obs_branch_nottaken_pc hobs7
    rwa [show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64) from by decide] at this
  have hx15_7 : σ7.regs.get? Register.x15 = some (11#64) := obs_branch_nottaken_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hx17_7 : σ7.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hobs7 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_6
  have hx10_7 : σ7.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_6
  have hx19_7 : σ7.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_6
  have hx12_7 : σ7.regs.get? Register.x12 = some (22#64) := obs_branch_nottaken_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  obtain ⟨vmi7, hmi7⟩ := obs_branch_nottaken_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_branch_nottaken]; exact hout6
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003538: slli a4,a5,0x20 → x14 := 9<<32
  --------------------------------------------------------------------------------
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003538_ee σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003538#64) vmi7 (11#64) hG7 hpc7 hmi7 hx15_7 hcode7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = c.σ.mem := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000353c#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80003538#64) 4 = (0x8000353c#64 : BitVec 64) from by decide] at this
  have hx14_8 : σ8.regs.get? Register.x14 = some (0xb00000000#64) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_left (11#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0)) = (0xb00000000#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_8 : σ8.regs.get? Register.x17 = some Wr := obs_alu_other hobs8 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_7
  have hx10_8 : σ8.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_7
  have hs1_8 : σ8.regs.get? Register.x9 = some sret := obs_alu_other hobs8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_7
  have hx19_8 : σ8.regs.get? Register.x19 = some Wl := obs_alu_other hobs8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_7
  have hx12_8 : σ8.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_alu]; exact hout7
  have hcode8 : Eval_exprLoaded σ8.mem := by rw [hmem8e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000353c: srli a5,a4,0x1e → x15 := 36
  --------------------------------------------------------------------------------
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_8000353c_ee σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000353c#64) vmi8 (0xb00000000#64) hG8 hpc8 hmi8 hx14_8 hcode8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = c.σ.mem := by rw [hmem9]; exact hmem8e
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003540#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000353c#64) 4 = (0x80003540#64 : BitVec 64) from by decide] at this
  have hx15_9 : σ9.regs.get? Register.x15 = some (44#64) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_right (0xb00000000#64 : BitVec 64) (Sail.BitVec.extractLsb (0x1e#6) 5 0)) = (44#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_9 : σ9.regs.get? Register.x17 = some Wr := obs_alu_other hobs9 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_8
  have hx10_9 : σ9.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_8
  have hs1_9 : σ9.regs.get? Register.x9 = some sret := obs_alu_other hobs9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_8
  have hx19_9 : σ9.regs.get? Register.x19 = some Wl := obs_alu_other hobs9 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_8
  have hx12_9 : σ9.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs9 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_alu]; exact hout8
  have hcode9 : Eval_exprLoaded σ9.mem := by rw [hmem9e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003540: auipc a4,0x17 → x14 := 0x80003540 + 0x17000
  --------------------------------------------------------------------------------
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80003540_ee σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003540#64) vmi9 hG9 hpc9 hmi9 hcode9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = c.σ.mem := by rw [hmem10]; exact hmem9e
  have hpc10 : σ10.regs.get? Register.PC = some (0x80003544#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80003540#64) 4 = (0x80003544#64 : BitVec 64) from by decide] at this
  have hx14_10 : σ10.regs.get? Register.x14 = some ((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) :=
    obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_10 : σ10.regs.get? Register.x15 = some (44#64) := obs_alu_other hobs10 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_9
  have hx17_10 : σ10.regs.get? Register.x17 = some Wr := obs_alu_other hobs10 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_9
  have hx10_10 : σ10.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_9
  have hs1_10 : σ10.regs.get? Register.x9 = some sret := obs_alu_other hobs10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_9
  have hx19_10 : σ10.regs.get? Register.x19 = some Wl := obs_alu_other hobs10 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_9
  have hx12_10 : σ10.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_alu]; exact hout9
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003544: addi a4,a4,-1468 → x14 := 0x80019f84 (op table base)
  --------------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80003544_ee σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003544#64) vmi10 ((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      hG10 hpc10 hmi10 hx14_10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = c.σ.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80003548#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80003544#64) 4 = (0x80003548#64 : BitVec 64) from by decide] at this
  have hx14_11 : σ11.regs.get? Register.x14 = some (0x80019f84#64) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12)) = (0x80019f84#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_11 : σ11.regs.get? Register.x15 = some (44#64) := obs_alu_other hobs11 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_10
  have hx17_11 : σ11.regs.get? Register.x17 = some Wr := obs_alu_other hobs11 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_10
  have hx10_11 : σ11.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_10
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_alu_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_10
  have hx19_11 : σ11.regs.get? Register.x19 = some Wl := obs_alu_other hobs11 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_10
  have hx12_11 : σ11.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_alu]; exact hout10
  have hcode11 : Eval_exprLoaded σ11.mem := by rw [hmem11e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003548: add a5,a5,a4 → x15 := 36 + 0x80019f84 = 0x80019fb0
  --------------------------------------------------------------------------------
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80003548_ee σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003548#64) vmi11 (44#64) (0x80019f84#64) hG11 hpc11 hmi11 hx15_11 hx14_11 hcode11 rfl hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs12'
  have hmem12e : σ12.mem = c.σ.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000354c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80003548#64) 4 = (0x8000354c#64 : BitVec 64) from by decide] at this
  have hx15_12 : σ12.regs.get? Register.x15 = some (0x80019fb0#64) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((44#64 : BitVec 64) + (0x80019f84#64 : BitVec 64)) = (0x80019fb0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_11
  have hx17_12 : σ12.regs.get? Register.x17 = some Wr := obs_alu_other hobs12 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_11
  have hx10_12 : σ12.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_11
  have hs1_12 : σ12.regs.get? Register.x9 = some sret := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_11
  have hx19_12 : σ12.regs.get? Register.x19 = some Wl := obs_alu_other hobs12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_11
  have hx12_12 : σ12.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = out0 := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact hout11
  have hcode12 : Eval_exprLoaded σ12.mem := by rw [hmem12e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000354c: lw a5,0(a5) → x15 := sext(slot bytes @0x80019fb0)
  --------------------------------------------------------------------------------
  obtain ⟨hsb0, hsb1, hsb2, hsb3⟩ := hSlot
  have hslotAddr : ((0x80019fb0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = 0x80019fb0 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero]; decide
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_8000354c_ee σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000354c#64) vmi12 (0x80019fb0#64)
      (0xa4#8) (0x96#8) (0xfe#8) (0xff#8) hG12 hpc12 hmi12 hx15_12 hcode12 rfl
      (by rw [hslotAddr]; omega) (by rw [hslotAddr]; omega)
      (by rw [hslotAddr]; rw [htoh]; left; omega) (by rw [hslotAddr])
      (by rw [hslotAddr]; exact (hmem12e ▸ hsb0)) (by rw [hslotAddr]; exact (hmem12e ▸ hsb1))
      (by rw [hslotAddr]; exact (hmem12e ▸ hsb2)) (by rw [hslotAddr]; exact (hmem12e ▸ hsb3)) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13'
  have hmem13e : σ13.mem = c.σ.mem := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80003550#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x8000354c#64) 4 = (0x80003550#64 : BitVec 64) from by decide] at this
  have hx15_13 : σ13.regs.get? Register.x15 = some (0xfffffffffffe96a4#64) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((0xff#8).append (0xfe#8)).append (0x96#8)).append (0xa4#8) : BitVec (8*4)))
      = (0xfffffffffffe96a4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_13 : σ13.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs13 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_12
  have hx17_13 : σ13.regs.get? Register.x17 = some Wr := obs_alu_other hobs13 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_12
  have hx10_13 : σ13.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_12
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_alu_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_12
  have hx19_13 : σ13.regs.get? Register.x19 = some Wl := obs_alu_other hobs13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_12
  have hx12_13 : σ13.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs13 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_alu]; exact hout12
  have hcode13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003550: ld a6,0(sp) → x16 := respilled vl.kind = 2#64
  --------------------------------------------------------------------------------
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) (2#64 : BitVec 64).toNat hKindResp
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_80003550_ee σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003550#64) vmi13 (sp - 1088#64)
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 hG13 hpc13 hmi13 hsp_13 hcode13 rfl
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; right; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, hmem13e]; exact hkb0) (by rw [haddr0, hmem13e]; exact hkb1)
      (by rw [haddr0, hmem13e]; exact hkb2) (by rw [haddr0, hmem13e]; exact hkb3)
      (by rw [haddr0, hmem13e]; exact hkb4) (by rw [haddr0, hmem13e]; exact hkb5)
      (by rw [haddr0, hmem13e]; exact hkb6) (by rw [haddr0, hmem13e]; exact hkb7) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14'
  have hmem14e : σ14.mem = c.σ.mem := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80003554#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80003550#64) 4 = (0x80003554#64 : BitVec 64) from by decide] at this
  have hx16_14 : σ14.regs.get? Register.x16 = some (2#64) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8)))
        = (2#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; rw [sext_full, word8_toNat_recon, hkbrec]] at this
  have hx15_14 : σ14.regs.get? Register.x15 = some (0xfffffffffffe96a4#64) := obs_alu_other hobs14 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_13
  have hx14_14 : σ14.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs14 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_13
  have hx17_14 : σ14.regs.get? Register.x17 = some Wr := obs_alu_other hobs14 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_13
  have hx10_14 : σ14.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_13
  have hs1_14 : σ14.regs.get? Register.x9 = some sret := obs_alu_other hobs14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_13
  have hx19_14 : σ14.regs.get? Register.x19 = some Wl := obs_alu_other hobs14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_13
  have hx12_14 : σ14.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = out0 := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hcode14 : Eval_exprLoaded σ14.mem := by rw [hmem14e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003554: add a5,a5,a4 → x15 := 0x80003628 (jr target = shared cmp arm)
  --------------------------------------------------------------------------------
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_80003554_ee σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003554#64) vmi14
      (0xfffffffffffe96a4#64) (0x80019f84#64)
      hG14 hpc14 hmi14 hx15_14 hx14_14 hcode14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15'
  have hmem15e : σ15.mem = c.σ.mem := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x80003558#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80003554#64) 4 = (0x80003558#64 : BitVec 64) from by decide] at this
  have hx15_15 : σ15.regs.get? Register.x15 = some (0x80003628#64) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0xfffffffffffe96a4#64 : BitVec 64) + (0x80019f84#64 : BitVec 64))
        = (0x80003628#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_15 : σ15.regs.get? Register.x17 = some Wr := obs_alu_other hobs15 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_14
  have hx10_15 : σ15.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs15 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_14
  have hx16_15 : σ15.regs.get? Register.x16 = some (2#64) := obs_alu_other hobs15 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_14
  have hs1_15 : σ15.regs.get? Register.x9 = some sret := obs_alu_other hobs15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_14
  have hx19_15 : σ15.regs.get? Register.x19 = some Wl := obs_alu_other hobs15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_14
  have hx12_15 : σ15.regs.get? Register.x12 = some (22#64) := obs_alu_other hobs15 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hout15 : σ15.sailOutput = out0 := by rw [hobs15.out, sailOutput_sigmaPost_alu]; exact hout14
  have hcode15 : Eval_exprLoaded σ15.mem := by rw [hmem15e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003558: jr a5 → PC := 0x80003628 (shared comparison arm)
  --------------------------------------------------------------------------------
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_80003558_ee σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003558#64) vmi15 (0x80003628#64)
      hG15 hpc15 hmi15 hx15_15 hcode15 rfl (by decide) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16'
  have hmem16e : σ16.mem = c.σ.mem := by rw [hmem16]; exact hmem15e
  have hpc16 : σ16.regs.get? Register.PC = some (0x80003628#64) := by
    have := obs_jr_pc hobs16
    rwa [show (BitVec.update ((0x80003628#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = (0x80003628#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_16 : σ16.regs.get? Register.x17 = some Wr := obs_jr_other hobs16 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_15
  have hx10_16 : σ16.regs.get? Register.x10 = some (2#64) := obs_jr_other hobs16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_15
  have hx16_16 : σ16.regs.get? Register.x16 = some (2#64) := obs_jr_other hobs16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_15
  have hs1_16 : σ16.regs.get? Register.x9 = some sret := obs_jr_other hobs16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_15
  have hx19_16 : σ16.regs.get? Register.x19 = some Wl := obs_jr_other hobs16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_15
  have hx12_16 : σ16.regs.get? Register.x12 = some (22#64) := obs_jr_other hobs16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_15
  obtain ⟨vmi16, hmi16⟩ := obs_jr_minstret hobs16
  have hout16 : σ16.sailOutput = out0 := by rw [hobs16.out, sailOutput_sigmaPost_jump_x0]; exact hout15
  have hcode16 : Eval_exprLoaded σ16.mem := by rw [hmem16e]; exact hcode
  have hVbool16 : Value_boolLoaded σ16.mem := by rw [hmem16e]; exact hVbool
  let u16 : Nat := c.steps + 16
  have hu16eq : (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = u16 := by
    show _ = c.steps + 16; omega
  rw [hu16eq] at hstep16
  -- dead staging-load bytes (all present via hFullPop)
  obtain ⟨e968_0, he968_0⟩ := hFullPop (sp.toNat - 968)
  obtain ⟨e968_1, he968_1⟩ := hFullPop (sp.toNat - 968 + 1)
  obtain ⟨e968_2, he968_2⟩ := hFullPop (sp.toNat - 968 + 2)
  obtain ⟨e968_3, he968_3⟩ := hFullPop (sp.toNat - 968 + 3)
  obtain ⟨e968_4, he968_4⟩ := hFullPop (sp.toNat - 968 + 4)
  obtain ⟨e968_5, he968_5⟩ := hFullPop (sp.toNat - 968 + 5)
  obtain ⟨e968_6, he968_6⟩ := hFullPop (sp.toNat - 968 + 6)
  obtain ⟨e968_7, he968_7⟩ := hFullPop (sp.toNat - 968 + 7)
  obtain ⟨e952_0, he952_0⟩ := hFullPop (sp.toNat - 952)
  obtain ⟨e952_1, he952_1⟩ := hFullPop (sp.toNat - 952 + 1)
  obtain ⟨e952_2, he952_2⟩ := hFullPop (sp.toNat - 952 + 2)
  obtain ⟨e952_3, he952_3⟩ := hFullPop (sp.toNat - 952 + 3)
  obtain ⟨e952_4, he952_4⟩ := hFullPop (sp.toNat - 952 + 4)
  obtain ⟨e952_5, he952_5⟩ := hFullPop (sp.toNat - 952 + 5)
  obtain ⟨e952_6, he952_6⟩ := hFullPop (sp.toNat - 952 + 6)
  obtain ⟨e952_7, he952_7⟩ := hFullPop (sp.toNat - 952 + 7)
  obtain ⟨e944_0, he944_0⟩ := hFullPop (sp.toNat - 944)
  obtain ⟨e944_1, he944_1⟩ := hFullPop (sp.toNat - 944 + 1)
  obtain ⟨e944_2, he944_2⟩ := hFullPop (sp.toNat - 944 + 2)
  obtain ⟨e944_3, he944_3⟩ := hFullPop (sp.toNat - 944 + 3)
  obtain ⟨e944_4, he944_4⟩ := hFullPop (sp.toNat - 944 + 4)
  obtain ⟨e944_5, he944_5⟩ := hFullPop (sp.toNat - 944 + 5)
  obtain ⟨e944_6, he944_6⟩ := hFullPop (sp.toNat - 944 + 6)
  obtain ⟨e944_7, he944_7⟩ := hFullPop (sp.toNat - 944 + 7)
  obtain ⟨e928_0, he928_0⟩ := hFullPop (sp.toNat - 928)
  obtain ⟨e928_1, he928_1⟩ := hFullPop (sp.toNat - 928 + 1)
  obtain ⟨e928_2, he928_2⟩ := hFullPop (sp.toNat - 928 + 2)
  obtain ⟨e928_3, he928_3⟩ := hFullPop (sp.toNat - 928 + 3)
  obtain ⟨e928_4, he928_4⟩ := hFullPop (sp.toNat - 928 + 4)
  obtain ⟨e928_5, he928_5⟩ := hFullPop (sp.toNat - 928 + 5)
  obtain ⟨e928_6, he928_6⟩ := hFullPop (sp.toNat - 928 + 6)
  obtain ⟨e928_7, he928_7⟩ := hFullPop (sp.toNat - 928 + 7)
  --------------------------------------------------------------------------------
  -- 0x80003628: addi x15,x10,0xffd → x15 := 2 + (-3) = -1
  --------------------------------------------------------------------------------
  obtain ⟨τ1, j1, ht1', hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_80003628 σ16 i16 u16 (0x80003628#64) vmi16 (2#64) hG16 hpc16 hmi16 hx10_16 hcode16 rfl hi16
  have hstepτ1 : Step ⟨σ16, i16, u16⟩ ⟨τ1, j1, u16 + 1⟩ := ht1'
  have hmemτ1e : τ1.mem = c.σ.mem := by rw [hmemτ1]; exact hmem16e
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x8000362c#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x80003628#64) 4 = (0x8000362c#64 : BitVec 64) from by decide] at this
  have hx15τ1 : τ1.regs.get? Register.x15 = some (0xffffffffffffffff#64) := by
    have := obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((2#64 : BitVec 64) + sign_extend (m := 64) (0xffd#12)) = (0xffffffffffffffff#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ1 : τ1.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_16
  have hx16τ1 : τ1.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_16
  have hx17τ1 : τ1.regs.get? Register.x17 = some Wr := obs_alu_other hoτ1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_16
  have hx10τ1 : τ1.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_16
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_16
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_16
  have hx19τ1 : τ1.regs.get? Register.x19 = some Wl := obs_alu_other hoτ1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_16
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = out0 := by rw [hoτ1.out, sailOutput_sigmaPost_alu]; exact hout16
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000362c: bne x15,x0 → 0x80003638 TAKEN (x15 = -1 ≠ 0)
  --------------------------------------------------------------------------------
  obtain ⟨τ2, j2, ht2', hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_8000362c_taken τ1 j1 (u16 + 1) (0x8000362c#64) vmiτ1 (0xffffffffffffffff#64) hGτ1 hpcτ1 hmiτ1 hx15τ1 hcodeτ1 rfl (by decide) hj1
  have hstepτ2 : Step ⟨τ1, j1, u16 + 1⟩ ⟨τ2, j2, u16 + 1 + 1⟩ := ht2'
  have hmemτ2e : τ2.mem = c.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003638#64) := by
    have := obs_branch_taken_pc hoτ2
    rwa [site_8000362c_taken_tgt] at this
  have hx12τ2 : τ2.regs.get? Register.x12 = some (22#64) := obs_branch_taken_other hoτ2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ1
  have hx16τ2 : τ2.regs.get? Register.x16 = some (2#64) := obs_branch_taken_other hoτ2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ1
  have hx17τ2 : τ2.regs.get? Register.x17 = some Wr := obs_branch_taken_other hoτ2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ1
  have hx10τ2 : τ2.regs.get? Register.x10 = some (2#64) := obs_branch_taken_other hoτ2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ1
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_branch_taken_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_taken_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  have hx19τ2 : τ2.regs.get? Register.x19 = some Wl := obs_branch_taken_other hoτ2 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_branch_taken_minstret hoτ2
  have houtτ2 : τ2.sailOutput = out0 := by rw [hoτ2.out, sailOutput_sigmaPost_branch_taken]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003638: addiw x15,x12,0xfec → x15 := 20-20 = 0
  --------------------------------------------------------------------------------
  obtain ⟨τ3, j3, ht3', hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003638 τ2 j2 (u16 + 1 + 1) (0x80003638#64) vmiτ2 (22#64) hGτ2 hpcτ2 hmiτ2 hx12τ2 hcodeτ2 rfl hj2
  have hstepτ3 : Step ⟨τ2, j2, u16 + 1 + 1⟩ ⟨τ3, j3, u16 + 1 + 1 + 1⟩ := ht3'
  have hmemτ3e : τ3.mem = c.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x8000363c#64) := by
    have := obs_alu_pc hoτ3
    rwa [show BitVec.addInt (0x80003638#64) 4 = (0x8000363c#64 : BitVec 64) from by decide] at this
  have hx15τ3 : τ3.regs.get? Register.x15 = some (2#64) := by
    have := obs_alu_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (Sail.BitVec.extractLsb ((22#64 : BitVec 64) + sign_extend (m := 64) (0xfec#12)) 31 0)) = (2#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ3 : τ3.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ2
  have hx16τ3 : τ3.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ2
  have hx17τ3 : τ3.regs.get? Register.x17 = some Wr := obs_alu_other hoτ3 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ2
  have hx10τ3 : τ3.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_alu_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  have hx19τ3 : τ3.regs.get? Register.x19 = some Wl := obs_alu_other hoτ3 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_alu_minstret hoτ3
  have houtτ3 : τ3.sailOutput = out0 := by rw [hoτ3.out, sailOutput_sigmaPost_alu]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000363c: addi x14,x0,0x3 → x14 := 3
  --------------------------------------------------------------------------------
  obtain ⟨τ4, j4, ht4', hj4, hGτ4, hmemτ4, hoτ4⟩ :=
    site_8000363c τ3 j3 (u16 + 1 + 1 + 1) (0x8000363c#64) vmiτ3 hGτ3 hpcτ3 hmiτ3 hcodeτ3 rfl hj3
  have hstepτ4 : Step ⟨τ3, j3, u16 + 1 + 1 + 1⟩ ⟨τ4, j4, u16 + 1 + 1 + 1 + 1⟩ := ht4'
  have hmemτ4e : τ4.mem = c.σ.mem := by rw [hmemτ4]; exact hmemτ3e
  have hpcτ4 : τ4.regs.get? Register.PC = some (0x80003640#64) := by
    have := obs_alu_pc hoτ4
    rwa [show BitVec.addInt (0x8000363c#64) 4 = (0x80003640#64 : BitVec 64) from by decide] at this
  have hx14τ4 : τ4.regs.get? Register.x14 = some (3#64) := by
    have := obs_alu_rd hoτ4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = (3#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15τ4 : τ4.regs.get? Register.x15 = some (2#64) := obs_alu_other hoτ4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ3
  have hx12τ4 : τ4.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ3
  have hx16τ4 : τ4.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ3
  have hx17τ4 : τ4.regs.get? Register.x17 = some Wr := obs_alu_other hoτ4 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ3
  have hx10τ4 : τ4.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ3
  have hs1τ4 : τ4.regs.get? Register.x9 = some sret := obs_alu_other hoτ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ3
  have hspτ4 : τ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ3
  have hx19τ4 : τ4.regs.get? Register.x19 = some Wl := obs_alu_other hoτ4 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ3
  obtain ⟨vmiτ4, hmiτ4⟩ := obs_alu_minstret hoτ4
  have houtτ4 : τ4.sailOutput = out0 := by rw [hoτ4.out, sailOutput_sigmaPost_alu]; exact houtτ3
  have hcodeτ4 : Eval_exprLoaded τ4.mem := by rw [hmemτ4e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003640: auipc x13,0x16 → x13 (dead); 0x80003644: addi x13,x13,0xd40 (dead)
  --------------------------------------------------------------------------------
  obtain ⟨τ5, j5, ht5', hj5, hGτ5, hmemτ5, hoτ5⟩ :=
    site_80003640_ee τ4 j4 (u16 + 1 + 1 + 1 + 1) (0x80003640#64) vmiτ4 hGτ4 hpcτ4 hmiτ4 hcodeτ4 rfl hj4
  have hstepτ5 : Step ⟨τ4, j4, u16 + 1 + 1 + 1 + 1⟩ ⟨τ5, j5, u16 + 1 + 1 + 1 + 1 + 1⟩ := ht5'
  have hmemτ5e : τ5.mem = c.σ.mem := by rw [hmemτ5]; exact hmemτ4e
  have hpcτ5 : τ5.regs.get? Register.PC = some (0x80003644#64) := by
    have := obs_alu_pc hoτ5
    rwa [show BitVec.addInt (0x80003640#64) 4 = (0x80003644#64 : BitVec 64) from by decide] at this
  have hx13τ5 : τ5.regs.get? Register.x13 = some ((0x80003640#64 : BitVec 64) + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12)) :=
    obs_alu_rd hoτ5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14τ5 : τ5.regs.get? Register.x14 = some (3#64) := obs_alu_other hoτ5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ4
  have hx15τ5 : τ5.regs.get? Register.x15 = some (2#64) := obs_alu_other hoτ5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ4
  have hx12τ5 : τ5.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ4
  have hx16τ5 : τ5.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ4
  have hx17τ5 : τ5.regs.get? Register.x17 = some Wr := obs_alu_other hoτ5 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ4
  have hx10τ5 : τ5.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ4
  have hs1τ5 : τ5.regs.get? Register.x9 = some sret := obs_alu_other hoτ5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ4
  have hspτ5 : τ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ4
  have hx19τ5 : τ5.regs.get? Register.x19 = some Wl := obs_alu_other hoτ5 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ4
  obtain ⟨vmiτ5, hmiτ5⟩ := obs_alu_minstret hoτ5
  have houtτ5 : τ5.sailOutput = out0 := by rw [hoτ5.out, sailOutput_sigmaPost_alu]; exact houtτ4
  have hcodeτ5 : Eval_exprLoaded τ5.mem := by rw [hmemτ5e]; exact hcode
  obtain ⟨τ6, j6, ht6', hj6, hGτ6, hmemτ6, hoτ6⟩ :=
    site_80003644 τ5 j5 (u16 + 1 + 1 + 1 + 1 + 1) (0x80003644#64) vmiτ5 ((0x80003640#64 : BitVec 64) + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12)) hGτ5 hpcτ5 hmiτ5 hx13τ5 hcodeτ5 rfl hj5
  have hstepτ6 : Step ⟨τ5, j5, u16 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ6, j6, u16 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht6'
  have hmemτ6e : τ6.mem = c.σ.mem := by rw [hmemτ6]; exact hmemτ5e
  have hpcτ6 : τ6.regs.get? Register.PC = some (0x80003648#64) := by
    have := obs_alu_pc hoτ6
    rwa [show BitVec.addInt (0x80003644#64) 4 = (0x80003648#64 : BitVec 64) from by decide] at this
  have hx14τ6 : τ6.regs.get? Register.x14 = some (3#64) := obs_alu_other hoτ6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ5
  have hx15τ6 : τ6.regs.get? Register.x15 = some (2#64) := obs_alu_other hoτ6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ5
  have hx12τ6 : τ6.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ5
  have hx16τ6 : τ6.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ5
  have hx17τ6 : τ6.regs.get? Register.x17 = some Wr := obs_alu_other hoτ6 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ5
  have hx10τ6 : τ6.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ5
  have hs1τ6 : τ6.regs.get? Register.x9 = some sret := obs_alu_other hoτ6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ5
  have hspτ6 : τ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ5
  have hx19τ6 : τ6.regs.get? Register.x19 = some Wl := obs_alu_other hoτ6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ5
  obtain ⟨vmiτ6, hmiτ6⟩ := obs_alu_minstret hoτ6
  have houtτ6 : τ6.sailOutput = out0 := by rw [hoτ6.out, sailOutput_sigmaPost_alu]; exact houtτ5
  have hcodeτ6 : Eval_exprLoaded τ6.mem := by rw [hmemτ6e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003648: beq x15,x14 NOT taken (x15=0 ≠ x14=3)
  --------------------------------------------------------------------------------
  obtain ⟨τ7, j7, ht7', hj7, hGτ7, hmemτ7, hoτ7⟩ :=
    site_80003648_nottaken τ6 j6 (u16 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003648#64) vmiτ6 (2#64) (3#64) hGτ6 hpcτ6 hmiτ6 hx15τ6 hx14τ6 hcodeτ6 rfl (by decide) hj6
  have hstepτ7 : Step ⟨τ6, j6, u16 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ7, j7, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht7'
  have hmemτ7e : τ7.mem = c.σ.mem := by rw [hmemτ7]; exact hmemτ6e
  have hpcτ7 : τ7.regs.get? Register.PC = some (0x8000364c#64) := by
    have := obs_branch_nottaken_pc hoτ7
    rwa [show BitVec.addInt (0x80003648#64) 4 = (0x8000364c#64 : BitVec 64) from by decide] at this
  have hx15τ7 : τ7.regs.get? Register.x15 = some (2#64) := obs_branch_nottaken_other hoτ7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ6
  have hx12τ7 : τ7.regs.get? Register.x12 = some (22#64) := obs_branch_nottaken_other hoτ7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ6
  have hx16τ7 : τ7.regs.get? Register.x16 = some (2#64) := obs_branch_nottaken_other hoτ7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ6
  have hx17τ7 : τ7.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ7 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ6
  have hx10τ7 : τ7.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hoτ7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ6
  have hs1τ7 : τ7.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ6
  have hspτ7 : τ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ6
  have hx19τ7 : τ7.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ6
  obtain ⟨vmiτ7, hmiτ7⟩ := obs_branch_nottaken_minstret hoτ7
  have houtτ7 : τ7.sailOutput = out0 := by rw [hoτ7.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ6
  have hcodeτ7 : Eval_exprLoaded τ7.mem := by rw [hmemτ7e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000364c: slli x14,x15,0x20 → x14 := 0 (x15=0)
  --------------------------------------------------------------------------------
  obtain ⟨τ8, j8, ht8', hj8, hGτ8, hmemτ8, hoτ8⟩ :=
    site_8000364c_ee τ7 j7 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000364c#64) vmiτ7 (2#64) hGτ7 hpcτ7 hmiτ7 hx15τ7 hcodeτ7 rfl hj7
  have hstepτ8 : Step ⟨τ7, j7, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ8, j8, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht8'
  have hmemτ8e : τ8.mem = c.σ.mem := by rw [hmemτ8]; exact hmemτ7e
  have hpcτ8 : τ8.regs.get? Register.PC = some (0x80003650#64) := by
    have := obs_alu_pc hoτ8
    rwa [show BitVec.addInt (0x8000364c#64) 4 = (0x80003650#64 : BitVec 64) from by decide] at this
  have hx14τ8 : τ8.regs.get? Register.x14 = some (0x200000000#64) := by
    have := obs_alu_rd hoτ8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_left (2#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0)) = (0x200000000#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ8 : τ8.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ7
  have hx16τ8 : τ8.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ7
  have hx17τ8 : τ8.regs.get? Register.x17 = some Wr := obs_alu_other hoτ8 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ7
  have hx10τ8 : τ8.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ7
  have hs1τ8 : τ8.regs.get? Register.x9 = some sret := obs_alu_other hoτ8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ7
  have hspτ8 : τ8.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ7
  have hx19τ8 : τ8.regs.get? Register.x19 = some Wl := obs_alu_other hoτ8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ7
  obtain ⟨vmiτ8, hmiτ8⟩ := obs_alu_minstret hoτ8
  have houtτ8 : τ8.sailOutput = out0 := by rw [hoτ8.out, sailOutput_sigmaPost_alu]; exact houtτ7
  have hcodeτ8 : Eval_exprLoaded τ8.mem := by rw [hmemτ8e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003650: srli x15,x14,0x1d → x15 := 0
  --------------------------------------------------------------------------------
  obtain ⟨τ9, j9, ht9', hj9, hGτ9, hmemτ9, hoτ9⟩ :=
    site_80003650_ee τ8 j8 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003650#64) vmiτ8 (0x200000000#64) hGτ8 hpcτ8 hmiτ8 hx14τ8 hcodeτ8 rfl hj8
  have hstepτ9 : Step ⟨τ8, j8, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ9, j9, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht9'
  have hmemτ9e : τ9.mem = c.σ.mem := by rw [hmemτ9]; exact hmemτ8e
  have hpcτ9 : τ9.regs.get? Register.PC = some (0x80003654#64) := by
    have := obs_alu_pc hoτ9
    rwa [show BitVec.addInt (0x80003650#64) 4 = (0x80003654#64 : BitVec 64) from by decide] at this
  have hx15τ9 : τ9.regs.get? Register.x15 = some (16#64) := by
    have := obs_alu_rd hoτ9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_right (0x200000000#64 : BitVec 64) (Sail.BitVec.extractLsb (0x1d#6) 5 0)) = (16#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ9 : τ9.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ9 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ8
  have hx16τ9 : τ9.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ9 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ8
  have hx17τ9 : τ9.regs.get? Register.x17 = some Wr := obs_alu_other hoτ9 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ8
  have hx10τ9 : τ9.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ8
  have hs1τ9 : τ9.regs.get? Register.x9 = some sret := obs_alu_other hoτ9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ8
  have hspτ9 : τ9.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ8
  have hx19τ9 : τ9.regs.get? Register.x19 = some Wl := obs_alu_other hoτ9 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ8
  obtain ⟨vmiτ9, hmiτ9⟩ := obs_alu_minstret hoτ9
  have houtτ9 : τ9.sailOutput = out0 := by rw [hoτ9.out, sailOutput_sigmaPost_alu]; exact houtτ8
  have hcodeτ9 : Eval_exprLoaded τ9.mem := by rw [hmemτ9e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003654: auipc x14,0x17 → x14 := 0x80003654 + 0x17000
  --------------------------------------------------------------------------------
  obtain ⟨τ10, j10, ht10', hj10, hGτ10, hmemτ10, hoτ10⟩ :=
    site_80003654_ee τ9 j9 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003654#64) vmiτ9 hGτ9 hpcτ9 hmiτ9 hcodeτ9 rfl hj9
  have hstepτ10 : Step ⟨τ9, j9, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ10, j10, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht10'
  have hmemτ10e : τ10.mem = c.σ.mem := by rw [hmemτ10]; exact hmemτ9e
  have hpcτ10 : τ10.regs.get? Register.PC = some (0x80003658#64) := by
    have := obs_alu_pc hoτ10
    rwa [show BitVec.addInt (0x80003654#64) 4 = (0x80003658#64 : BitVec 64) from by decide] at this
  have hx14τ10 : τ10.regs.get? Register.x14 = some ((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) :=
    obs_alu_rd hoτ10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15τ10 : τ10.regs.get? Register.x15 = some (16#64) := obs_alu_other hoτ10 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ9
  have hx12τ10 : τ10.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ9
  have hx16τ10 : τ10.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ10 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ9
  have hx17τ10 : τ10.regs.get? Register.x17 = some Wr := obs_alu_other hoτ10 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ9
  have hx10τ10 : τ10.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ9
  have hs1τ10 : τ10.regs.get? Register.x9 = some sret := obs_alu_other hoτ10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ9
  have hspτ10 : τ10.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ9
  have hx19τ10 : τ10.regs.get? Register.x19 = some Wl := obs_alu_other hoτ10 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ9
  obtain ⟨vmiτ10, hmiτ10⟩ := obs_alu_minstret hoτ10
  have houtτ10 : τ10.sailOutput = out0 := by rw [hoτ10.out, sailOutput_sigmaPost_alu]; exact houtτ9
  have hcodeτ10 : Eval_exprLoaded τ10.mem := by rw [hmemτ10e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003658: addi x14,x14,0x98c → x14 := CSWTCH.25 base = 0x80019fe0
  --------------------------------------------------------------------------------
  obtain ⟨τ11, j11, ht11', hj11, hGτ11, hmemτ11, hoτ11⟩ :=
    site_80003658 τ10 j10 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003658#64) vmiτ10 ((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) hGτ10 hpcτ10 hmiτ10 hx14τ10 hcodeτ10 rfl hj10
  have hstepτ11 : Step ⟨τ10, j10, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ11, j11, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht11'
  have hmemτ11e : τ11.mem = c.σ.mem := by rw [hmemτ11]; exact hmemτ10e
  have hpcτ11 : τ11.regs.get? Register.PC = some (0x8000365c#64) := by
    have := obs_alu_pc hoτ11
    rwa [show BitVec.addInt (0x80003658#64) 4 = (0x8000365c#64 : BitVec 64) from by decide] at this
  have hx14τ11 : τ11.regs.get? Register.x14 = some (0x80019fe0#64) := by
    have := obs_alu_rd hoτ11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) + sign_extend (m := 64) (0x98c#12)) = (0x80019fe0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15τ11 : τ11.regs.get? Register.x15 = some (16#64) := obs_alu_other hoτ11 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ10
  have hx12τ11 : τ11.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ10
  have hx16τ11 : τ11.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ11 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ10
  have hx17τ11 : τ11.regs.get? Register.x17 = some Wr := obs_alu_other hoτ11 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ10
  have hx10τ11 : τ11.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ10
  have hs1τ11 : τ11.regs.get? Register.x9 = some sret := obs_alu_other hoτ11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ10
  have hspτ11 : τ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ10
  have hx19τ11 : τ11.regs.get? Register.x19 = some Wl := obs_alu_other hoτ11 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ10
  obtain ⟨vmiτ11, hmiτ11⟩ := obs_alu_minstret hoτ11
  have houtτ11 : τ11.sailOutput = out0 := by rw [hoτ11.out, sailOutput_sigmaPost_alu]; exact houtτ10
  have hcodeτ11 : Eval_exprLoaded τ11.mem := by rw [hmemτ11e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000365c: add x15,x14,x15 → x15 := 0x80019fe0 + 0 = 0x80019fe0
  --------------------------------------------------------------------------------
  obtain ⟨τ12, j12, ht12', hj12, hGτ12, hmemτ12, hoτ12⟩ :=
    site_8000365c τ11 j11 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000365c#64) vmiτ11 (0x80019fe0#64) (16#64) hGτ11 hpcτ11 hmiτ11 hx14τ11 hx15τ11 hcodeτ11 rfl hj11
  have hstepτ12 : Step ⟨τ11, j11, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ12, j12, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht12'
  have hmemτ12e : τ12.mem = c.σ.mem := by rw [hmemτ12]; exact hmemτ11e
  have hpcτ12 : τ12.regs.get? Register.PC = some (0x80003660#64) := by
    have := obs_alu_pc hoτ12
    rwa [show BitVec.addInt (0x8000365c#64) 4 = (0x80003660#64 : BitVec 64) from by decide] at this
  have hx15τ12 : τ12.regs.get? Register.x15 = some (0x80019ff0#64) := by
    have := obs_alu_rd hoτ12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x80019fe0#64 : BitVec 64) + (16#64 : BitVec 64)) = (0x80019ff0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ12 : τ12.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ11
  have hx16τ12 : τ12.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ12 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ11
  have hx17τ12 : τ12.regs.get? Register.x17 = some Wr := obs_alu_other hoτ12 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ11
  have hx10τ12 : τ12.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ11
  have hs1τ12 : τ12.regs.get? Register.x9 = some sret := obs_alu_other hoτ12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ11
  have hspτ12 : τ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ11
  have hx19τ12 : τ12.regs.get? Register.x19 = some Wl := obs_alu_other hoτ12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ11
  obtain ⟨vmiτ12, hmiτ12⟩ := obs_alu_minstret hoτ12
  have houtτ12 : τ12.sailOutput = out0 := by rw [hoτ12.out, sailOutput_sigmaPost_alu]; exact houtτ11
  have hcodeτ12 : Eval_exprLoaded τ12.mem := by rw [hmemτ12e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003660: ld x13,0x0(x15) → x13 := error-msg ptr @0x80019fe0 (dead)
  --------------------------------------------------------------------------------
  obtain ⟨cs0, hcs0⟩ := hFullPop 0x80019ff0
  obtain ⟨cs1, hcs1⟩ := hFullPop (0x80019ff0 + 1)
  obtain ⟨cs2, hcs2⟩ := hFullPop (0x80019ff0 + 2)
  obtain ⟨cs3, hcs3⟩ := hFullPop (0x80019ff0 + 3)
  obtain ⟨cs4, hcs4⟩ := hFullPop (0x80019ff0 + 4)
  obtain ⟨cs5, hcs5⟩ := hFullPop (0x80019ff0 + 5)
  obtain ⟨cs6, hcs6⟩ := hFullPop (0x80019ff0 + 6)
  obtain ⟨cs7, hcs7⟩ := hFullPop (0x80019ff0 + 7)
  have hcsAddr : ((0x80019ff0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = 0x80019ff0 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero]; decide
  obtain ⟨τ13, j13, ht13', hj13, hGτ13, hmemτ13, hoτ13⟩ :=
    site_80003660 τ12 j12 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003660#64) vmiτ12 (0x80019ff0#64)
      cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 hGτ12 hpcτ12 hmiτ12 hx15τ12 hcodeτ12 rfl
      (by rw [hcsAddr]; omega) (by rw [hcsAddr]; omega)
      (by rw [hcsAddr, htoh]; left; omega) (by rw [hcsAddr])
      (by rw [hcsAddr, hmemτ12e]; exact hcs0) (by rw [hcsAddr, hmemτ12e]; exact hcs1)
      (by rw [hcsAddr, hmemτ12e]; exact hcs2) (by rw [hcsAddr, hmemτ12e]; exact hcs3)
      (by rw [hcsAddr, hmemτ12e]; exact hcs4) (by rw [hcsAddr, hmemτ12e]; exact hcs5)
      (by rw [hcsAddr, hmemτ12e]; exact hcs6) (by rw [hcsAddr, hmemτ12e]; exact hcs7) hj12
  have hstepτ13 : Step ⟨τ12, j12, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ13, j13, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht13'
  have hmemτ13e : τ13.mem = c.σ.mem := by rw [hmemτ13]; exact hmemτ12e
  have hpcτ13 : τ13.regs.get? Register.PC = some (0x80003664#64) := by
    have := obs_alu_pc hoτ13
    rwa [show BitVec.addInt (0x80003660#64) 4 = (0x80003664#64 : BitVec 64) from by decide] at this
  have hx12τ13 : τ13.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ13 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ12
  have hx16τ13 : τ13.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ13 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ12
  have hx17τ13 : τ13.regs.get? Register.x17 = some Wr := obs_alu_other hoτ13 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ12
  have hx10τ13 : τ13.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ12
  have hs1τ13 : τ13.regs.get? Register.x9 = some sret := obs_alu_other hoτ13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ12
  have hspτ13 : τ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ12
  have hx19τ13 : τ13.regs.get? Register.x19 = some Wl := obs_alu_other hoτ13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ12
  obtain ⟨vmiτ13, hmiτ13⟩ := obs_alu_minstret hoτ13
  have houtτ13 : τ13.sailOutput = out0 := by rw [hoτ13.out, sailOutput_sigmaPost_alu]; exact houtτ12
  have hcodeτ13 : Eval_exprLoaded τ13.mem := by rw [hmemτ13e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003664: ld x14,0x78(x2) @sp-968 (dead); 0x80003668: ld x15,0x88(x2) @sp-952 (dead)
  --------------------------------------------------------------------------------
  obtain ⟨τ14, j14, ht14', hj14, hGτ14, hmemτ14, hoτ14⟩ :=
    site_80003664 τ13 j13 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003664#64) vmiτ13 (sp - 1088#64)
      e968_0 e968_1 e968_2 e968_3 e968_4 e968_5 e968_6 e968_7 hGτ13 hpcτ13 hmiτ13 hspτ13 hcodeτ13 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmemτ13e]; exact he968_0) (by rw [haddr120, hmemτ13e]; exact he968_1)
      (by rw [haddr120, hmemτ13e]; exact he968_2) (by rw [haddr120, hmemτ13e]; exact he968_3)
      (by rw [haddr120, hmemτ13e]; exact he968_4) (by rw [haddr120, hmemτ13e]; exact he968_5)
      (by rw [haddr120, hmemτ13e]; exact he968_6) (by rw [haddr120, hmemτ13e]; exact he968_7) hj13
  have hstepτ14 : Step ⟨τ13, j13, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ14, j14, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht14'
  have hmemτ14e : τ14.mem = c.σ.mem := by rw [hmemτ14]; exact hmemτ13e
  have hpcτ14 : τ14.regs.get? Register.PC = some (0x80003668#64) := by
    have := obs_alu_pc hoτ14
    rwa [show BitVec.addInt (0x80003664#64) 4 = (0x80003668#64 : BitVec 64) from by decide] at this
  have hx14τ14 : τ14.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e968_7.append e968_6).append e968_5).append e968_4).append e968_3).append e968_2).append e968_1).append e968_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12τ14 : τ14.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ13
  have hx16τ14 : τ14.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ14 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ13
  have hx17τ14 : τ14.regs.get? Register.x17 = some Wr := obs_alu_other hoτ14 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ13
  have hx10τ14 : τ14.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ13
  have hs1τ14 : τ14.regs.get? Register.x9 = some sret := obs_alu_other hoτ14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ13
  have hspτ14 : τ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ13
  have hx19τ14 : τ14.regs.get? Register.x19 = some Wl := obs_alu_other hoτ14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ13
  obtain ⟨vmiτ14, hmiτ14⟩ := obs_alu_minstret hoτ14
  have houtτ14 : τ14.sailOutput = out0 := by rw [hoτ14.out, sailOutput_sigmaPost_alu]; exact houtτ13
  have hcodeτ14 : Eval_exprLoaded τ14.mem := by rw [hmemτ14e]; exact hcode
  obtain ⟨τ15, j15, ht15', hj15, hGτ15, hmemτ15, hoτ15⟩ :=
    site_80003668 τ14 j14 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003668#64) vmiτ14 (sp - 1088#64)
      e952_0 e952_1 e952_2 e952_3 e952_4 e952_5 e952_6 e952_7 hGτ14 hpcτ14 hmiτ14 hspτ14 hcodeτ14 rfl
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, hmemτ14e]; exact he952_0) (by rw [haddr136, hmemτ14e]; exact he952_1)
      (by rw [haddr136, hmemτ14e]; exact he952_2) (by rw [haddr136, hmemτ14e]; exact he952_3)
      (by rw [haddr136, hmemτ14e]; exact he952_4) (by rw [haddr136, hmemτ14e]; exact he952_5)
      (by rw [haddr136, hmemτ14e]; exact he952_6) (by rw [haddr136, hmemτ14e]; exact he952_7) hj14
  have hstepτ15 : Step ⟨τ14, j14, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ15, j15, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht15'
  have hmemτ15e : τ15.mem = c.σ.mem := by rw [hmemτ15]; exact hmemτ14e
  have hpcτ15 : τ15.regs.get? Register.PC = some (0x8000366c#64) := by
    have := obs_alu_pc hoτ15
    rwa [show BitVec.addInt (0x80003668#64) 4 = (0x8000366c#64 : BitVec 64) from by decide] at this
  have hx15τ15 : τ15.regs.get? Register.x15 = some (sign_extend (m := 64) ((((((((e952_7.append e952_6).append e952_5).append e952_4).append e952_3).append e952_2).append e952_1).append e952_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ15 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14τ15 : τ15.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e968_7.append e968_6).append e968_5).append e968_4).append e968_3).append e968_2).append e968_1).append e968_0) : BitVec (8*8))) := obs_alu_other hoτ15 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ14
  have hx12τ15 : τ15.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ15 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ14
  have hx16τ15 : τ15.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ15 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ14
  have hx17τ15 : τ15.regs.get? Register.x17 = some Wr := obs_alu_other hoτ15 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ14
  have hx10τ15 : τ15.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ15 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ14
  have hs1τ15 : τ15.regs.get? Register.x9 = some sret := obs_alu_other hoτ15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ14
  have hspτ15 : τ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ14
  have hx19τ15 : τ15.regs.get? Register.x19 = some Wl := obs_alu_other hoτ15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ14
  obtain ⟨vmiτ15, hmiτ15⟩ := obs_alu_minstret hoτ15
  have houtτ15 : τ15.sailOutput = out0 := by rw [hoτ15.out, sailOutput_sigmaPost_alu]; exact houtτ14
  have hcodeτ15 : Eval_exprLoaded τ15.mem := by rw [hmemτ15e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000366c: addi x11,x0,0x2 → x11 := 2
  --------------------------------------------------------------------------------
  obtain ⟨τ16, j16, ht16', hj16, hGτ16, hmemτ16, hoτ16⟩ :=
    site_8000366c τ15 j15 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000366c#64) vmiτ15 hGτ15 hpcτ15 hmiτ15 hcodeτ15 rfl hj15
  have hstepτ16 : Step ⟨τ15, j15, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ16, j16, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht16'
  have hmemτ16e : τ16.mem = c.σ.mem := by rw [hmemτ16]; exact hmemτ15e
  have hpcτ16 : τ16.regs.get? Register.PC = some (0x80003670#64) := by
    have := obs_alu_pc hoτ16
    rwa [show BitVec.addInt (0x8000366c#64) 4 = (0x80003670#64 : BitVec 64) from by decide] at this
  have hx11τ16 : τ16.regs.get? Register.x11 = some (2#64) := by
    have := obs_alu_rd hoτ16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = (2#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14τ16 : τ16.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e968_7.append e968_6).append e968_5).append e968_4).append e968_3).append e968_2).append e968_1).append e968_0) : BitVec (8*8))) := obs_alu_other hoτ16 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ15
  have hx15τ16 : τ16.regs.get? Register.x15 = some (sign_extend (m := 64) ((((((((e952_7.append e952_6).append e952_5).append e952_4).append e952_3).append e952_2).append e952_1).append e952_0) : BitVec (8*8))) := obs_alu_other hoτ16 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ15
  have hx16τ16 : τ16.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ15
  have hx17τ16 : τ16.regs.get? Register.x17 = some Wr := obs_alu_other hoτ16 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ15
  have hs1τ16 : τ16.regs.get? Register.x9 = some sret := obs_alu_other hoτ16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ15
  have hspτ16 : τ16.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ15
  have hx19τ16 : τ16.regs.get? Register.x19 = some Wl := obs_alu_other hoτ16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ15
  have hx10τ16 : τ16.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ15
  obtain ⟨vmiτ16, hmiτ16⟩ := obs_alu_minstret hoτ16
  have houtτ16 : τ16.sailOutput = out0 := by rw [hoτ16.out, sailOutput_sigmaPost_alu]; exact houtτ15
  have hcodeτ16 : Eval_exprLoaded τ16.mem := by rw [hmemτ16e]; exact hcode
  -- the two loaded dead words to be stored (a4 = V968, a5 = V952)
  let V968 : BitVec 64 := sign_extend (m := 64) ((((((((e968_7.append e968_6).append e968_5).append e968_4).append e968_3).append e968_2).append e968_1).append e968_0) : BitVec (8*8))
  let V952 : BitVec 64 := sign_extend (m := 64) ((((((((e952_7.append e952_6).append e952_5).append e952_4).append e952_3).append e952_2).append e952_1).append e952_0) : BitVec (8*8))
  --------------------------------------------------------------------------------
  -- 0x80003670: sd x14,0xf0(x2) → m1 @sp-848; 0x80003674: sd x15,0x100(x2) → m2 @sp-832
  --------------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 832) (sdData_val V952)
  obtain ⟨τ17, j17, ht17', hj17, hGτ17, hmemτ17, hoτ17⟩ :=
    site_80003670 τ16 j16 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003670#64) vmiτ16 (sp - 1088#64) V968
      hGτ16 hpcτ16 hmiτ16 hspτ16 hx14τ16 hcodeτ16 rfl
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega) hj16
  have hstepτ17 : Step ⟨τ16, j16, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ17, j17, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht17'
  have hmemτ17e : τ17.mem = m1 := by rw [hmemτ17, mem_afterNextPC, haddr240]; rw [hmemτ16e]
  have hpcτ17 : τ17.regs.get? Register.PC = some (0x80003674#64) := by
    have := obs_store_pc_val hoτ17
    rwa [show BitVec.addInt (0x80003670#64) 4 = (0x80003674#64 : BitVec 64) from by decide] at this
  have hx15τ17 := obs_store_other_val hoτ17 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ16
  have hx10τ17 := obs_store_other_val hoτ17 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ16
  have hx11τ17 := obs_store_other_val hoτ17 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ16
  have hx16τ17 := obs_store_other_val hoτ17 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ16
  have hx17τ17 := obs_store_other_val hoτ17 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ16
  have hs1τ17 := obs_store_other_val hoτ17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ16
  have hspτ17 := obs_store_other_val hoτ17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ16
  have hx19τ17 := obs_store_other_val hoτ17 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ16
  obtain ⟨vmiτ17, hmiτ17⟩ := obs_store_minstret_val hoτ17
  have houtτ17 : τ17.sailOutput = out0 := by rw [hoτ17.out, sailOutput_sigmaPost_store]; exact houtτ16
  have hcodeτ17 : Eval_exprLoaded τ17.mem := by
    rw [hmemτ17e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val V968)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  obtain ⟨τ18, j18, ht18', hj18, hGτ18, hmemτ18, hoτ18⟩ :=
    site_80003674 τ17 j17 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003674#64) vmiτ17 (sp - 1088#64) V952
      hGτ17 hpcτ17 hmiτ17 hspτ17 hx15τ17 hcodeτ17 rfl
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega) hj17
  have hstepτ18 : Step ⟨τ17, j17, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ18, j18, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht18'
  have hmemτ18e : τ18.mem = m2 := by rw [hmemτ18, mem_afterNextPC, haddr256]; rw [hmemτ17e]
  have hpcτ18 : τ18.regs.get? Register.PC = some (0x80003678#64) := by
    have := obs_store_pc_val hoτ18
    rwa [show BitVec.addInt (0x80003674#64) 4 = (0x80003678#64 : BitVec 64) from by decide] at this
  have hx10τ18 := obs_store_other_val hoτ18 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ17
  have hx11τ18 := obs_store_other_val hoτ18 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ17
  have hx16τ18 := obs_store_other_val hoτ18 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ17
  have hx17τ18 := obs_store_other_val hoτ18 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ17
  have hs1τ18 := obs_store_other_val hoτ18 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ17
  have hspτ18 := obs_store_other_val hoτ18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ17
  have hx19τ18 := obs_store_other_val hoτ18 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ17
  obtain ⟨vmiτ18, hmiτ18⟩ := obs_store_minstret_val hoτ18
  have houtτ18 : τ18.sailOutput = out0 := by rw [hoτ18.out, sailOutput_sigmaPost_store]; exact houtτ17
  have hcodem1 : Eval_exprLoaded m1 := by rw [← hmemτ17e]; exact hcodeτ17
  have hcodeτ18 : Eval_exprLoaded τ18.mem := by
    rw [hmemτ18e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-832) k (sdData_val V952)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem1
  --------------------------------------------------------------------------------
  -- 0x80003678: bne x16,x11 NOT taken (x16=2, x11=2)
  --------------------------------------------------------------------------------
  obtain ⟨τ19, j19, ht19', hj19, hGτ19, hmemτ19, hoτ19⟩ :=
    site_80003678_nottaken τ18 j18 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003678#64) vmiτ18 (2#64) (2#64) hGτ18 hpcτ18 hmiτ18 hx16τ18 hx11τ18 hcodeτ18 rfl (by decide) hj18
  have hstepτ19 : Step ⟨τ18, j18, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ19, j19, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht19'
  have hmemτ19e : τ19.mem = m2 := by rw [hmemτ19]; exact hmemτ18e
  have hpcτ19 : τ19.regs.get? Register.PC = some (0x8000367c#64) := by
    have := obs_branch_nottaken_pc hoτ19
    rwa [show BitVec.addInt (0x80003678#64) 4 = (0x8000367c#64 : BitVec 64) from by decide] at this
  have hx10τ19 : τ19.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hoτ19 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ18
  have hx16τ19 : τ19.regs.get? Register.x16 = some (2#64) := obs_branch_nottaken_other hoτ19 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ18
  have hx17τ19 : τ19.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ19 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ18
  have hs1τ19 : τ19.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ19 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ18
  have hspτ19 : τ19.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ18
  have hx19τ19 : τ19.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ19 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ18
  obtain ⟨vmiτ19, hmiτ19⟩ := obs_branch_nottaken_minstret hoτ19
  have houtτ19 : τ19.sailOutput = out0 := by rw [hoτ19.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ18
  have hcodem2 : Eval_exprLoaded m2 := by rw [← hmemτ18e]; exact hcodeτ18
  have hcodeτ19 : Eval_exprLoaded τ19.mem := by rw [hmemτ19e]; exact hcodem2
  -- `m2` agrees with `c.σ.mem` outside the two store windows [sp-848,+8), [sp-832,+8)
  have hAgM2 : ∀ k : Nat, k + 8 ≤ sp.toNat - 848 → c.σ.mem[k]? = m2[k]? := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V952))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V952) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V968) (by omega)]
  obtain ⟨e936_0, he936_0⟩ := hFullPop (sp.toNat - 936)
  obtain ⟨e936_1, he936_1⟩ := hFullPop (sp.toNat - 936 + 1)
  obtain ⟨e936_2, he936_2⟩ := hFullPop (sp.toNat - 936 + 2)
  obtain ⟨e936_3, he936_3⟩ := hFullPop (sp.toNat - 936 + 3)
  obtain ⟨e936_4, he936_4⟩ := hFullPop (sp.toNat - 936 + 4)
  obtain ⟨e936_5, he936_5⟩ := hFullPop (sp.toNat - 936 + 5)
  obtain ⟨e936_6, he936_6⟩ := hFullPop (sp.toNat - 936 + 6)
  obtain ⟨e936_7, he936_7⟩ := hFullPop (sp.toNat - 936 + 7)
  --------------------------------------------------------------------------------
  -- 0x8000367c: ld x14,0x90(x2)@sp-944; 0x80003680: ld x11,0x98(x2)@sp-936; 0x80003684: ld x15,0xa0(x2)@sp-928
  --------------------------------------------------------------------------------
  obtain ⟨τ20, j20, ht20', hj20, hGτ20, hmemτ20, hoτ20⟩ :=
    site_8000367c τ19 j19 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000367c#64) vmiτ19 (sp - 1088#64)
      e944_0 e944_1 e944_2 e944_3 e944_4 e944_5 e944_6 e944_7 hGτ19 hpcτ19 hmiτ19 hspτ19 hcodeτ19 rfl
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944) (by omega)]; exact he944_0)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 1) (by omega)]; exact he944_1)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 2) (by omega)]; exact he944_2)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 3) (by omega)]; exact he944_3)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 4) (by omega)]; exact he944_4)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 5) (by omega)]; exact he944_5)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 6) (by omega)]; exact he944_6)
      (by rw [haddr144, hmemτ19e]; rw [← hAgM2 (sp.toNat - 944 + 7) (by omega)]; exact he944_7) hj19
  have hstepτ20 : Step ⟨τ19, j19, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ20, j20, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht20'
  have hmemτ20e : τ20.mem = m2 := by rw [hmemτ20]; exact hmemτ19e
  have hpcτ20 : τ20.regs.get? Register.PC = some (0x80003680#64) := by
    have := obs_alu_pc hoτ20
    rwa [show BitVec.addInt (0x8000367c#64) 4 = (0x80003680#64 : BitVec 64) from by decide] at this
  have hx14τ20 : τ20.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e944_7.append e944_6).append e944_5).append e944_4).append e944_3).append e944_2).append e944_1).append e944_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ20 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx16τ20 : τ20.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ20 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ19
  have hx17τ20 : τ20.regs.get? Register.x17 = some Wr := obs_alu_other hoτ20 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ19
  have hx10τ20 : τ20.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ20 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ19
  have hs1τ20 : τ20.regs.get? Register.x9 = some sret := obs_alu_other hoτ20 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ19
  have hspτ20 : τ20.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ19
  have hx19τ20 : τ20.regs.get? Register.x19 = some Wl := obs_alu_other hoτ20 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ19
  obtain ⟨vmiτ20, hmiτ20⟩ := obs_alu_minstret hoτ20
  have houtτ20 : τ20.sailOutput = out0 := by rw [hoτ20.out, sailOutput_sigmaPost_alu]; exact houtτ19
  have hcodeτ20 : Eval_exprLoaded τ20.mem := by rw [hmemτ20e]; exact hcodem2
  obtain ⟨τ21, j21, ht21', hj21, hGτ21, hmemτ21, hoτ21⟩ :=
    site_80003680 τ20 j20 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003680#64) vmiτ20 (sp - 1088#64)
      e936_0 e936_1 e936_2 e936_3 e936_4 e936_5 e936_6 e936_7 hGτ20 hpcτ20 hmiτ20 hspτ20 hcodeτ20 rfl
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936) (by omega)]; exact he936_0)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 1) (by omega)]; exact he936_1)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 2) (by omega)]; exact he936_2)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 3) (by omega)]; exact he936_3)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 4) (by omega)]; exact he936_4)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 5) (by omega)]; exact he936_5)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 6) (by omega)]; exact he936_6)
      (by rw [haddr152, hmemτ20e]; rw [← hAgM2 (sp.toNat - 936 + 7) (by omega)]; exact he936_7) hj20
  have hstepτ21 : Step ⟨τ20, j20, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ21, j21, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht21'
  have hmemτ21e : τ21.mem = m2 := by rw [hmemτ21]; exact hmemτ20e
  have hpcτ21 : τ21.regs.get? Register.PC = some (0x80003684#64) := by
    have := obs_alu_pc hoτ21
    rwa [show BitVec.addInt (0x80003680#64) 4 = (0x80003684#64 : BitVec 64) from by decide] at this
  have hx14τ21 : τ21.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e944_7.append e944_6).append e944_5).append e944_4).append e944_3).append e944_2).append e944_1).append e944_0) : BitVec (8*8))) := obs_alu_other hoτ21 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ20
  have hx11τ21 : τ21.regs.get? Register.x11 = some (sign_extend (m := 64) ((((((((e936_7.append e936_6).append e936_5).append e936_4).append e936_3).append e936_2).append e936_1).append e936_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx16τ21 : τ21.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ21 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ20
  have hx17τ21 : τ21.regs.get? Register.x17 = some Wr := obs_alu_other hoτ21 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ20
  have hx10τ21 : τ21.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ21 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ20
  have hs1τ21 : τ21.regs.get? Register.x9 = some sret := obs_alu_other hoτ21 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ20
  have hspτ21 : τ21.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ20
  have hx19τ21 : τ21.regs.get? Register.x19 = some Wl := obs_alu_other hoτ21 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ20
  obtain ⟨vmiτ21, hmiτ21⟩ := obs_alu_minstret hoτ21
  have houtτ21 : τ21.sailOutput = out0 := by rw [hoτ21.out, sailOutput_sigmaPost_alu]; exact houtτ20
  have hcodeτ21 : Eval_exprLoaded τ21.mem := by rw [hmemτ21e]; exact hcodem2
  obtain ⟨τ22, j22, ht22', hj22, hGτ22, hmemτ22, hoτ22⟩ :=
    site_80003684 τ21 j21 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003684#64) vmiτ21 (sp - 1088#64)
      e928_0 e928_1 e928_2 e928_3 e928_4 e928_5 e928_6 e928_7 hGτ21 hpcτ21 hmiτ21 hspτ21 hcodeτ21 rfl
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928) (by omega)]; exact he928_0)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 1) (by omega)]; exact he928_1)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 2) (by omega)]; exact he928_2)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 3) (by omega)]; exact he928_3)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 4) (by omega)]; exact he928_4)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 5) (by omega)]; exact he928_5)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 6) (by omega)]; exact he928_6)
      (by rw [haddr160, hmemτ21e]; rw [← hAgM2 (sp.toNat - 928 + 7) (by omega)]; exact he928_7) hj21
  have hstepτ22 : Step ⟨τ21, j21, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ22, j22, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht22'
  have hmemτ22e : τ22.mem = m2 := by rw [hmemτ22]; exact hmemτ21e
  have hpcτ22 : τ22.regs.get? Register.PC = some (0x80003688#64) := by
    have := obs_alu_pc hoτ22
    rwa [show BitVec.addInt (0x80003684#64) 4 = (0x80003688#64 : BitVec 64) from by decide] at this
  have hx15τ22 : τ22.regs.get? Register.x15 = some (sign_extend (m := 64) ((((((((e928_7.append e928_6).append e928_5).append e928_4).append e928_3).append e928_2).append e928_1).append e928_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14τ22 : τ22.regs.get? Register.x14 = some (sign_extend (m := 64) ((((((((e944_7.append e944_6).append e944_5).append e944_4).append e944_3).append e944_2).append e944_1).append e944_0) : BitVec (8*8))) := obs_alu_other hoτ22 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ21
  have hx11τ22 : τ22.regs.get? Register.x11 = some (sign_extend (m := 64) ((((((((e936_7.append e936_6).append e936_5).append e936_4).append e936_3).append e936_2).append e936_1).append e936_0) : BitVec (8*8))) := obs_alu_other hoτ22 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ21
  have hx16τ22 : τ22.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ22 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ21
  have hx17τ22 : τ22.regs.get? Register.x17 = some Wr := obs_alu_other hoτ22 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ21
  have hx10τ22 : τ22.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ22 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ21
  have hs1τ22 : τ22.regs.get? Register.x9 = some sret := obs_alu_other hoτ22 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ21
  have hspτ22 : τ22.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ22 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ21
  have hx19τ22 : τ22.regs.get? Register.x19 = some Wl := obs_alu_other hoτ22 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ21
  obtain ⟨vmiτ22, hmiτ22⟩ := obs_alu_minstret hoτ22
  have houtτ22 : τ22.sailOutput = out0 := by rw [hoτ22.out, sailOutput_sigmaPost_alu]; exact houtτ21
  have hcodeτ22 : Eval_exprLoaded τ22.mem := by rw [hmemτ22e]; exact hcodem2
  --------------------------------------------------------------------------------
  -- 0x80003688: sd x14,0xf0@sp-848→m3; 0x8000368c: sd x11,0xf8@sp-840→m4; 0x80003690: sd x15,0x100@sp-832→m5
  --------------------------------------------------------------------------------
  let V944 : BitVec 64 := sign_extend (m := 64) ((((((((e944_7.append e944_6).append e944_5).append e944_4).append e944_3).append e944_2).append e944_1).append e944_0) : BitVec (8*8))
  let V936 : BitVec 64 := sign_extend (m := 64) ((((((((e936_7.append e936_6).append e936_5).append e936_4).append e936_3).append e936_2).append e936_1).append e936_0) : BitVec (8*8))
  let V928 : BitVec 64 := sign_extend (m := 64) ((((((((e928_7.append e928_6).append e928_5).append e928_4).append e928_3).append e928_2).append e928_1).append e928_0) : BitVec (8*8))
  let m3 : Mem := writeMap8 m2 (sp.toNat - 848) (sdData_val V944)
  let m4 : Mem := writeMap8 m3 (sp.toNat - 840) (sdData_val V936)
  let m5 : Mem := writeMap8 m4 (sp.toNat - 832) (sdData_val V928)
  obtain ⟨τ23, j23, ht23', hj23, hGτ23, hmemτ23, hoτ23⟩ :=
    site_80003688 τ22 j22 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003688#64) vmiτ22 (sp - 1088#64) V944
      hGτ22 hpcτ22 hmiτ22 hspτ22 hx14τ22 hcodeτ22 rfl
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega) hj22
  have hstepτ23 : Step ⟨τ22, j22, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ23, j23, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht23'
  have hmemτ23e : τ23.mem = m3 := by rw [hmemτ23, mem_afterNextPC, haddr240]; rw [hmemτ22e]
  have hpcτ23 : τ23.regs.get? Register.PC = some (0x8000368c#64) := by
    have := obs_store_pc_val hoτ23
    rwa [show BitVec.addInt (0x80003688#64) 4 = (0x8000368c#64 : BitVec 64) from by decide] at this
  have hx11τ23 := obs_store_other_val hoτ23 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ22
  have hx15τ23 := obs_store_other_val hoτ23 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ22
  have hx16τ23 := obs_store_other_val hoτ23 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ22
  have hx17τ23 := obs_store_other_val hoτ23 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ22
  have hx10τ23 := obs_store_other_val hoτ23 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ22
  have hs1τ23 := obs_store_other_val hoτ23 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ22
  have hspτ23 := obs_store_other_val hoτ23 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ22
  have hx19τ23 := obs_store_other_val hoτ23 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ22
  obtain ⟨vmiτ23, hmiτ23⟩ := obs_store_minstret_val hoτ23
  have houtτ23 : τ23.sailOutput = out0 := by rw [hoτ23.out, sailOutput_sigmaPost_store]; exact houtτ22
  have hcodeτ23 : Eval_exprLoaded τ23.mem := by
    rw [hmemτ23e]
    exact loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-848) k (sdData_val V944)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem2
  obtain ⟨τ24, j24, ht24', hj24, hGτ24, hmemτ24, hoτ24⟩ :=
    site_8000368c τ23 j23 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000368c#64) vmiτ23 (sp - 1088#64) V936
      hGτ23 hpcτ23 hmiτ23 hspτ23 hx11τ23 hcodeτ23 rfl
      (by rw [haddr248]; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, htoh]; omega) (by rw [haddr248]; omega) hj23
  have hstepτ24 : Step ⟨τ23, j23, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ24, j24, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht24'
  have hmemτ24e : τ24.mem = m4 := by rw [hmemτ24, mem_afterNextPC, haddr248]; rw [hmemτ23e]
  have hpcτ24 : τ24.regs.get? Register.PC = some (0x80003690#64) := by
    have := obs_store_pc_val hoτ24
    rwa [show BitVec.addInt (0x8000368c#64) 4 = (0x80003690#64 : BitVec 64) from by decide] at this
  have hx15τ24 := obs_store_other_val hoτ24 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ23
  have hx16τ24 := obs_store_other_val hoτ24 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ23
  have hx17τ24 := obs_store_other_val hoτ24 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ23
  have hx10τ24 := obs_store_other_val hoτ24 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ23
  have hs1τ24 := obs_store_other_val hoτ24 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ23
  have hspτ24 := obs_store_other_val hoτ24 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ23
  have hx19τ24 := obs_store_other_val hoτ24 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ23
  obtain ⟨vmiτ24, hmiτ24⟩ := obs_store_minstret_val hoτ24
  have houtτ24 : τ24.sailOutput = out0 := by rw [hoτ24.out, sailOutput_sigmaPost_store]; exact houtτ23
  have hcodem3 : Eval_exprLoaded m3 := by rw [← hmemτ23e]; exact hcodeτ23
  have hcodeτ24 : Eval_exprLoaded τ24.mem := by
    rw [hmemτ24e]
    exact loaded_eval_expr_agreeP m3 m4
      (fun k hk => (getElem_writeMap8_disjoint m3 (sp.toNat-840) k (sdData_val V936)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem3
  obtain ⟨τ25, j25, ht25', hj25, hGτ25, hmemτ25, hoτ25⟩ :=
    site_80003690 τ24 j24 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003690#64) vmiτ24 (sp - 1088#64) V928
      hGτ24 hpcτ24 hmiτ24 hspτ24 hx15τ24 hcodeτ24 rfl
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega) hj24
  have hstepτ25 : Step ⟨τ24, j24, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ25, j25, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht25'
  have hmemτ25e : τ25.mem = m5 := by rw [hmemτ25, mem_afterNextPC, haddr256]; rw [hmemτ24e]
  have hpcτ25 : τ25.regs.get? Register.PC = some (0x80003694#64) := by
    have := obs_store_pc_val hoτ25
    rwa [show BitVec.addInt (0x80003690#64) 4 = (0x80003694#64 : BitVec 64) from by decide] at this
  have hx16τ25 := obs_store_other_val hoτ25 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ24
  have hx17τ25 := obs_store_other_val hoτ25 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ24
  have hx10τ25 := obs_store_other_val hoτ25 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ24
  have hs1τ25 := obs_store_other_val hoτ25 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ24
  have hspτ25 := obs_store_other_val hoτ25 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ24
  have hx19τ25 := obs_store_other_val hoτ25 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ24
  obtain ⟨vmiτ25, hmiτ25⟩ := obs_store_minstret_val hoτ25
  have houtτ25 : τ25.sailOutput = out0 := by rw [hoτ25.out, sailOutput_sigmaPost_store]; exact houtτ24
  have hcodem4 : Eval_exprLoaded m4 := by rw [← hmemτ24e]; exact hcodeτ24
  have hcodeτ25 : Eval_exprLoaded τ25.mem := by
    rw [hmemτ25e]
    exact loaded_eval_expr_agreeP m4 m5
      (fun k hk => (getElem_writeMap8_disjoint m4 (sp.toNat-832) k (sdData_val V928)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem4
  have hcodem5 : Eval_exprLoaded m5 := by rw [← hmemτ25e]; exact hcodeτ25
  --------------------------------------------------------------------------------
  -- 0x80003694: bne x10,x16 NOT taken (x10=2, x16=2)
  --------------------------------------------------------------------------------
  obtain ⟨τ26, j26, ht26', hj26, hGτ26, hmemτ26, hoτ26⟩ :=
    site_80003694_nottaken τ25 j25 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003694#64) vmiτ25 (2#64) (2#64) hGτ25 hpcτ25 hmiτ25 hx10τ25 hx16τ25 hcodeτ25 rfl (by decide) hj25
  have hstepτ26 : Step ⟨τ25, j25, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ26, j26, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht26'
  have hmemτ26e : τ26.mem = m5 := by rw [hmemτ26]; exact hmemτ25e
  have hpcτ26 : τ26.regs.get? Register.PC = some (0x80003698#64) := by
    have := obs_branch_nottaken_pc hoτ26
    rwa [show BitVec.addInt (0x80003694#64) 4 = (0x80003698#64 : BitVec 64) from by decide] at this
  have hx17τ26 : τ26.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ26 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ25
  have hs1τ26 : τ26.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ26 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ25
  have hspτ26 : τ26.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ26 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ25
  have hx19τ26 : τ26.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ26 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ25
  obtain ⟨vmiτ26, hmiτ26⟩ := obs_branch_nottaken_minstret hoτ26
  have houtτ26 : τ26.sailOutput = out0 := by rw [hoτ26.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ25
  have hcodeτ26 : Eval_exprLoaded τ26.mem := by rw [hmemτ26e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x80003698: slt x14,x17,x19 → x14 := zext(slt Wr Wl); 0x8000369c: slt x15,x19,x17 → x15 := zext(slt Wl Wr)
  --------------------------------------------------------------------------------
  obtain ⟨τ27, j27, ht27', hj27, hGτ27, hmemτ27, hoτ27⟩ :=
    site_80003698_ee τ26 j26 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003698#64) vmiτ26 Wr Wl hGτ26 hpcτ26 hmiτ26 hx17τ26 hx19τ26 hcodeτ26 rfl hj26
  have hstepτ27 : Step ⟨τ26, j26, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ27, j27, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht27'
  have hmemτ27e : τ27.mem = m5 := by rw [hmemτ27]; exact hmemτ26e
  have hpcτ27 : τ27.regs.get? Register.PC = some (0x8000369c#64) := by
    have := obs_alu_pc hoτ27
    rwa [show BitVec.addInt (0x80003698#64) 4 = (0x8000369c#64 : BitVec 64) from by decide] at this
  have hx14τ27 : τ27.regs.get? Register.x14 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wr Wl))) :=
    obs_alu_rd hoτ27 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx17τ27 : τ27.regs.get? Register.x17 = some Wr := obs_alu_other hoτ27 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ26
  have hs1τ27 : τ27.regs.get? Register.x9 = some sret := obs_alu_other hoτ27 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ26
  have hspτ27 : τ27.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ27 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ26
  have hx19τ27 : τ27.regs.get? Register.x19 = some Wl := obs_alu_other hoτ27 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ26
  obtain ⟨vmiτ27, hmiτ27⟩ := obs_alu_minstret hoτ27
  have houtτ27 : τ27.sailOutput = out0 := by rw [hoτ27.out, sailOutput_sigmaPost_alu]; exact houtτ26
  have hcodeτ27 : Eval_exprLoaded τ27.mem := by rw [hmemτ27e]; exact hcodem5
  obtain ⟨τ28, j28, ht28', hj28, hGτ28, hmemτ28, hoτ28⟩ :=
    site_8000369c_ee τ27 j27 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000369c#64) vmiτ27 Wr Wl hGτ27 hpcτ27 hmiτ27 hx17τ27 hx19τ27 hcodeτ27 rfl hj27
  have hstepτ28 : Step ⟨τ27, j27, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ28, j28, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht28'
  have hmemτ28e : τ28.mem = m5 := by rw [hmemτ28]; exact hmemτ27e
  have hpcτ28 : τ28.regs.get? Register.PC = some (0x800036a0#64) := by
    have := obs_alu_pc hoτ28
    rwa [show BitVec.addInt (0x8000369c#64) 4 = (0x800036a0#64 : BitVec 64) from by decide] at this
  have hx15τ28 : τ28.regs.get? Register.x15 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wl Wr))) :=
    obs_alu_rd hoτ28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14τ28 : τ28.regs.get? Register.x14 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wr Wl))) := obs_alu_other hoτ28 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14τ27
  have hs1τ28 : τ28.regs.get? Register.x9 = some sret := obs_alu_other hoτ28 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ27
  have hspτ28 : τ28.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ28 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ27
  have hx19τ28 : τ28.regs.get? Register.x19 = some Wl := obs_alu_other hoτ28 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ27
  obtain ⟨vmiτ28, hmiτ28⟩ := obs_alu_minstret hoτ28
  have houtτ28 : τ28.sailOutput = out0 := by rw [hoτ28.out, sailOutput_sigmaPost_alu]; exact houtτ27
  have hcodeτ28 : Eval_exprLoaded τ28.mem := by rw [hmemτ28e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x800036a0: subw x11,x14,x15 → x11 := cmpScalar Wl Wr
  --------------------------------------------------------------------------------
  obtain ⟨τ29, j29, ht29', hj29, hGτ29, hmemτ29, hoτ29⟩ :=
    site_800036a0 τ28 j28 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800036a0#64) vmiτ28 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wr Wl))) (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wl Wr))) hGτ28 hpcτ28 hmiτ28 hx14τ28 hx15τ28 hcodeτ28 rfl hj28
  have hstepτ29 : Step ⟨τ28, j28, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ29, j29, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht29'
  have hmemτ29e : τ29.mem = m5 := by rw [hmemτ29]; exact hmemτ28e
  have hpcτ29 : τ29.regs.get? Register.PC = some (0x800036a4#64) := by
    have := obs_alu_pc hoτ29
    rwa [show BitVec.addInt (0x800036a0#64) 4 = (0x800036a4#64 : BitVec 64) from by decide] at this
  have hx11τ29 : τ29.regs.get? Register.x11 = some (cmpScalar Wl Wr) := by
    have := obs_alu_rd hoτ29 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact this
  have hs1τ29 : τ29.regs.get? Register.x9 = some sret := obs_alu_other hoτ29 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ28
  have hspτ29 : τ29.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ29 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ28
  have hx19τ29 : τ29.regs.get? Register.x19 = some Wl := obs_alu_other hoτ29 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ28
  obtain ⟨vmiτ29, hmiτ29⟩ := obs_alu_minstret hoτ29
  have houtτ29 : τ29.sailOutput = out0 := by rw [hoτ29.out, sailOutput_sigmaPost_alu]; exact houtτ28
  have hcodeτ29 : Eval_exprLoaded τ29.mem := by rw [hmemτ29e]; exact hcodem5
  -- the cmp scalar value (surviving the beq ladder into the lt fixup)
  let cmpV : BitVec 64 := cmpScalar Wl Wr
  -- running step count at τ29 = u16 + 29
  let u29 : Nat := u16 + 29
  have hu29eq : (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = u29 := by
    show _ = u16 + 29; omega
  rw [hu29eq] at hstepτ29
  --------------------------------------------------------------------------------
  -- 0x800036a4: li x15,0x15 (=21)
  --------------------------------------------------------------------------------
  obtain ⟨τ30, j30, ht30', hj30, hGτ30, hmemτ30, hoτ30⟩ :=
    site_800036a4 τ29 j29 u29 (0x800036a4#64) vmiτ29 hGτ29 hpcτ29 hmiτ29 hcodeτ29 rfl hj29
  have hstepτ30 : Step ⟨τ29, j29, u29⟩ ⟨τ30, j30, u29 + 1⟩ := ht30'
  have hmemτ30e : τ30.mem = m5 := by rw [hmemτ30]; exact hmemτ29e
  have hpcτ30 : τ30.regs.get? Register.PC = some (0x800036a8#64) := by
    have := obs_alu_pc hoτ30
    rwa [show BitVec.addInt (0x800036a4#64) 4 = (0x800036a8#64 : BitVec 64) from by decide] at this
  have hx15τ30 : τ30.regs.get? Register.x15 = some (21#64) := by
    have := obs_alu_rd hoτ30 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x015#12)) = (21#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ30 : τ30.regs.get? Register.x12 = some (22#64) := by
    have h29 : τ29.regs.get? Register.x12 = some (22#64) := by
      have h28 : τ28.regs.get? Register.x12 = some (22#64) := by
        have h27 : τ27.regs.get? Register.x12 = some (22#64) := by
          have h26 : τ26.regs.get? Register.x12 = some (22#64) := by
            have h25 : τ25.regs.get? Register.x12 = some (22#64) := by
              have h24 : τ24.regs.get? Register.x12 = some (22#64) := by
                have h23 : τ23.regs.get? Register.x12 = some (22#64) := by
                  have h22 : τ22.regs.get? Register.x12 = some (22#64) := by
                    have h21 : τ21.regs.get? Register.x12 = some (22#64) :=
                      obs_alu_other hoτ21 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                        (obs_alu_other hoτ20 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                          (obs_branch_nottaken_other hoτ19 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                            (obs_store_other_val hoτ18 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                              (obs_store_other_val hoτ17 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                                (obs_alu_other hoτ16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ15)))))
                    exact obs_alu_other hoτ22 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h21
                  exact obs_store_other_val hoτ23 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h22
                exact obs_store_other_val hoτ24 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h23
              exact obs_store_other_val hoτ25 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h24
            exact obs_branch_nottaken_other hoτ26 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h25
          exact obs_alu_other hoτ27 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h26
        exact obs_alu_other hoτ28 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27
      exact obs_alu_other hoτ29 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h28
    exact obs_alu_other hoτ30 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h29
  have hx11τ30 : τ30.regs.get? Register.x11 = some cmpV := obs_alu_other hoτ30 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ29
  have hs1τ30 : τ30.regs.get? Register.x9 = some sret := obs_alu_other hoτ30 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ29
  have hspτ30 : τ30.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ30 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ29
  have hx19τ30 : τ30.regs.get? Register.x19 = some Wl := obs_alu_other hoτ30 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ29
  obtain ⟨vmiτ30, hmiτ30⟩ := obs_alu_minstret hoτ30
  have houtτ30 : τ30.sailOutput = out0 := by rw [hoτ30.out, sailOutput_sigmaPost_alu]; exact houtτ29
  have hcodeτ30 : Eval_exprLoaded τ30.mem := by rw [hmemτ30e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x800036a8: beq x12,x15 NOT taken (22 ≠ 21)
  --------------------------------------------------------------------------------
  obtain ⟨τ31, j31, ht31', hj31, hGτ31, hmemτ31, hoτ31⟩ :=
    site_800036a8_nottaken τ30 j30 (u29 + 1) (0x800036a8#64) vmiτ30 (22#64) (21#64) hGτ30 hpcτ30 hmiτ30 hx12τ30 hx15τ30 hcodeτ30 rfl (by decide) hj30
  have hstepτ31 : Step ⟨τ30, j30, u29 + 1⟩ ⟨τ31, j31, u29 + 1 + 1⟩ := ht31'
  have hmemτ31e : τ31.mem = m5 := by rw [hmemτ31]; exact hmemτ30e
  have hpcτ31 : τ31.regs.get? Register.PC = some (0x800036ac#64) := by
    have := obs_branch_nottaken_pc hoτ31
    rwa [show BitVec.addInt (0x800036a8#64) 4 = (0x800036ac#64 : BitVec 64) from by decide] at this
  have hx12τ31 : τ31.regs.get? Register.x12 = some (22#64) := obs_branch_nottaken_other hoτ31 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ30
  have hx11τ31 : τ31.regs.get? Register.x11 = some cmpV := obs_branch_nottaken_other hoτ31 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ30
  have hs1τ31 : τ31.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ31 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ30
  have hspτ31 : τ31.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ31 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ30
  have hx19τ31 : τ31.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ31 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ30
  obtain ⟨vmiτ31, hmiτ31⟩ := obs_branch_nottaken_minstret hoτ31
  have houtτ31 : τ31.sailOutput = out0 := by rw [hoτ31.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ30
  have hcodeτ31 : Eval_exprLoaded τ31.mem := by rw [hmemτ31e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x800036ac: li x15,0x16 (=22)
  --------------------------------------------------------------------------------
  obtain ⟨τ32, j32, ht32', hj32, hGτ32, hmemτ32, hoτ32⟩ :=
    site_800036ac τ31 j31 (u29 + 1 + 1) (0x800036ac#64) vmiτ31 hGτ31 hpcτ31 hmiτ31 hcodeτ31 rfl hj31
  have hstepτ32 : Step ⟨τ31, j31, u29 + 1 + 1⟩ ⟨τ32, j32, u29 + 1 + 1 + 1⟩ := ht32'
  have hmemτ32e : τ32.mem = m5 := by rw [hmemτ32]; exact hmemτ31e
  have hpcτ32 : τ32.regs.get? Register.PC = some (0x800036b0#64) := by
    have := obs_alu_pc hoτ32
    rwa [show BitVec.addInt (0x800036ac#64) 4 = (0x800036b0#64 : BitVec 64) from by decide] at this
  have hx15τ32 : τ32.regs.get? Register.x15 = some (22#64) := by
    have := obs_alu_rd hoτ32 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x016#12)) = (22#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12τ32 : τ32.regs.get? Register.x12 = some (22#64) := obs_alu_other hoτ32 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ31
  have hx11τ32 : τ32.regs.get? Register.x11 = some cmpV := obs_alu_other hoτ32 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ31
  have hs1τ32 : τ32.regs.get? Register.x9 = some sret := obs_alu_other hoτ32 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ31
  have hspτ32 : τ32.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ32 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ31
  have hx19τ32 : τ32.regs.get? Register.x19 = some Wl := obs_alu_other hoτ32 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ31
  obtain ⟨vmiτ32, hmiτ32⟩ := obs_alu_minstret hoτ32
  have houtτ32 : τ32.sailOutput = out0 := by rw [hoτ32.out, sailOutput_sigmaPost_alu]; exact houtτ31
  have hcodeτ32 : Eval_exprLoaded τ32.mem := by rw [hmemτ32e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x800036b0: beq x12,x15 → 0x80003ae4 TAKEN (22 = 22)
  --------------------------------------------------------------------------------
  obtain ⟨τ33, j33, ht33', hj33, hGτ33, hmemτ33, hoτ33⟩ :=
    site_800036b0_taken τ32 j32 (u29 + 1 + 1 + 1) (0x800036b0#64) vmiτ32 (22#64) (22#64) hGτ32 hpcτ32 hmiτ32 hx12τ32 hx15τ32 hcodeτ32 rfl (by decide) hj32
  have hstepτ33 : Step ⟨τ32, j32, u29 + 1 + 1 + 1⟩ ⟨τ33, j33, u29 + 1 + 1 + 1 + 1⟩ := ht33'
  have hmemτ33e : τ33.mem = m5 := by rw [hmemτ33]; exact hmemτ32e
  have hpcτ33 : τ33.regs.get? Register.PC = some (0x80003ae4#64) := by
    have := obs_branch_taken_pc hoτ33
    rwa [site_800036b0_taken_tgt] at this
  have hx11τ33 : τ33.regs.get? Register.x11 = some cmpV := obs_branch_taken_other hoτ33 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ32
  have hs1τ33 : τ33.regs.get? Register.x9 = some sret := obs_branch_taken_other hoτ33 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ32
  have hspτ33 : τ33.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_taken_other hoτ33 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ32
  have hx19τ33 : τ33.regs.get? Register.x19 = some Wl := obs_branch_taken_other hoτ33 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ32
  obtain ⟨vmiτ33, hmiτ33⟩ := obs_branch_taken_minstret hoτ33
  have houtτ33 : τ33.sailOutput = out0 := by rw [hoτ33.out, sailOutput_sigmaPost_branch_taken]; exact houtτ32
  have hcodeτ33 : Eval_exprLoaded τ33.mem := by rw [hmemτ33e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x80003ae4: sgtz x11,x11 (slt x11,x0,x11) → x11 := gt fixup
  --------------------------------------------------------------------------------
  obtain ⟨τ34, j34, ht34', hj34, hGτ34, hmemτ34, hoτ34⟩ :=
    site_80003ae4_ee τ33 j33 (u29 + 1 + 1 + 1 + 1) (0x80003ae4#64) vmiτ33 cmpV hGτ33 hpcτ33 hmiτ33 hx11τ33 hcodeτ33 rfl hj33
  have hstepτ34 : Step ⟨τ33, j33, u29 + 1 + 1 + 1 + 1⟩ ⟨τ34, j34, u29 + 1 + 1 + 1 + 1 + 1⟩ := ht34'
  have hmemτ34e : τ34.mem = m5 := by rw [hmemτ34]; exact hmemτ33e
  have hpcτ34 : τ34.regs.get? Register.PC = some (0x80003ae8#64) := by
    have := obs_alu_pc hoτ34
    rwa [show BitVec.addInt (0x80003ae4#64) 4 = (0x80003ae8#64 : BitVec 64) from by decide] at this
  have hx11τ34 : τ34.regs.get? Register.x11 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) :=
    obs_alu_rd hoτ34 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1τ34 : τ34.regs.get? Register.x9 = some sret := obs_alu_other hoτ34 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ33
  have hspτ34 : τ34.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ34 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ33
  have hx19τ34 : τ34.regs.get? Register.x19 = some Wl := obs_alu_other hoτ34 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ33
  obtain ⟨vmiτ34, hmiτ34⟩ := obs_alu_minstret hoτ34
  have houtτ34 : τ34.sailOutput = out0 := by rw [hoτ34.out, sailOutput_sigmaPost_alu]; exact houtτ33
  have hcodeτ34 : Eval_exprLoaded τ34.mem := by rw [hmemτ34e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x80003ae8: mv a0,s1 → x10 := sret
  --------------------------------------------------------------------------------
  obtain ⟨τ35, j35, ht35', hj35, hGτ35, hmemτ35, hoτ35⟩ :=
    site_80003ae8 τ34 j34 (u29 + 1 + 1 + 1 + 1 + 1) (0x80003ae8#64) vmiτ34 sret hGτ34 hpcτ34 hmiτ34 hs1τ34 hcodeτ34 rfl hj34
  have hstepτ35 : Step ⟨τ34, j34, u29 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ35, j35, u29 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht35'
  have hmemτ35e : τ35.mem = m5 := by rw [hmemτ35]; exact hmemτ34e
  have hpcτ35 : τ35.regs.get? Register.PC = some (0x80003aec#64) := by
    have := obs_alu_pc hoτ35
    rwa [show BitVec.addInt (0x80003ae8#64) 4 = (0x80003aec#64 : BitVec 64) from by decide] at this
  have hx10τ35 : τ35.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hoτ35 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12)) = sret from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
      rw [this]; have := sret.isLt; omega] at this
  have hx11τ35 : τ35.regs.get? Register.x11 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) := obs_alu_other hoτ35 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ34
  have hs1τ35 : τ35.regs.get? Register.x9 = some sret := obs_alu_other hoτ35 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ34
  have hspτ35 : τ35.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ35 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ34
  have hx19τ35 : τ35.regs.get? Register.x19 = some Wl := obs_alu_other hoτ35 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ34
  obtain ⟨vmiτ35, hmiτ35⟩ := obs_alu_minstret hoτ35
  have houtτ35 : τ35.sailOutput = out0 := by rw [hoτ35.out, sailOutput_sigmaPost_alu]; exact houtτ34
  have hcodeτ35 : Eval_exprLoaded τ35.mem := by rw [hmemτ35e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x80003aec: jal value_bool → PC := 0x800027f8, x1 := 0x80003af0
  --------------------------------------------------------------------------------
  have hVbool5 : Value_boolLoaded m5 := by
    have h1 : Value_boolLoaded m1 := loaded_bool_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968) (by rcases hviStk with h | h <;> omega) hVbool
    have h2 : Value_boolLoaded m2 := loaded_bool_writeMap8 m1 (sp.toNat - 832) (sdData_val V952) (by rcases hviStk with h | h <;> omega) h1
    have h3 : Value_boolLoaded m3 := loaded_bool_writeMap8 m2 (sp.toNat - 848) (sdData_val V944) (by rcases hviStk with h | h <;> omega) h2
    have h4 : Value_boolLoaded m4 := loaded_bool_writeMap8 m3 (sp.toNat - 840) (sdData_val V936) (by rcases hviStk with h | h <;> omega) h3
    exact loaded_bool_writeMap8 m4 (sp.toNat - 832) (sdData_val V928) (by rcases hviStk with h | h <;> omega) h4
  obtain ⟨τ36, j36, ht36', hj36, hGτ36, hmemτ36, hoτ36⟩ :=
    site_80003aec τ35 j35 (u29 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003aec#64) vmiτ35 hGτ35 hpcτ35 hmiτ35 hcodeτ35 rfl hj35
  have hstepτ36 : Step ⟨τ35, j35, u29 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ36, j36, u29 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht36'
  have hmemτ36e : τ36.mem = m5 := by rw [hmemτ36]; exact hmemτ35e
  have hpcτ36 : τ36.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hoτ36
    rwa [show ((0x80003aec#64 : BitVec 64) + sign_extend (m := 64) (0x1fed0c#21)) = 0x800027f8#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlinkτ36 : τ36.regs.get? Register.x1 = some (0x80003af0#64) := by
    have := obs_jal_rd hoτ36 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003aec#64 : BitVec 64) 4 = (0x80003af0#64:BitVec 64) from by decide] at this
  have hx10τ36 : τ36.regs.get? Register.x10 = some sret := obs_jal_other hoτ36 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ35
  have hx11τ36 : τ36.regs.get? Register.x11 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) := obs_jal_other hoτ36 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ35
  have hs1τ36 : τ36.regs.get? Register.x9 = some sret := obs_jal_other hoτ36 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ35
  have hspτ36 : τ36.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ36 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ35
  have hx19τ36 : τ36.regs.get? Register.x19 = some Wl := obs_jal_other hoτ36 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ35
  obtain ⟨vmiτ36, hmiτ36⟩ := obs_jal_minstret hoτ36
  have houtτ36 : τ36.sailOutput = out0 := by rw [hoτ36.out, sailOutput_sigmaPost_jal]; exact houtτ35
  have hVboolτ36 : Value_boolLoaded τ36.mem := by rw [hmemτ36e]; exact hVbool5
  --------------------------------------------------------------------------------
  -- value_bool callee
  --------------------------------------------------------------------------------
  have hBoolReg : BoolRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  obtain ⟨cvb, hsvb, hGvb, hpcvb, hx10vb, hravb, ⟨vmivb, hmivb⟩, htickvb, hvalvb, houtvb, hmemframevb, hpresvb, hframevb⟩ :=
    value_bool_spec_full (fun R => τ36.regs.get? R) sret (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) (0x80003af0#64) N φc' τ36.mem out0
      ⟨τ36, j36, u29 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hGτ36, hVboolτ36, rfl, hpcτ36, hx10τ36, hx11τ36, hlinkτ36, ⟨vmiτ36, hmiτ36⟩, hj36, hBoolReg,
        (by rw [show (BitVec.update ((0x80003af0#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x80003af0#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide),
        houtτ36, fun R _ => rfl⟩
  have hval_bridge : (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV)) != 0#64) = decide (a > b) := by
    rw [show cmpV = cmpScalar Wl Wr from rfl, gt_fixup_bridge Wl Wr, hWl_toInt, hWr_toInt]
  have hvalfinal : ValueRepr cvb.σ.mem N φc' sret.toNat (.bool (a > b)) := by
    rw [show ((.bool (a > b)) : Value) = .bool (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV)) != 0#64) from by rw [hval_bridge]]
    exact hvalvb
  have hpcvb' : cvb.σ.regs.get? Register.PC = some (0x80003af0#64) := by
    rw [hpcvb, show (BitVec.update ((0x80003af0#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x80003af0#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hcodeτ36 : Eval_exprLoaded τ36.mem := by rw [hmemτ36e]; exact hcodem5
  have hcode_vb : Eval_exprLoaded cvb.σ.mem :=
    loaded_eval_expr_agreeP τ36.mem cvb.σ.mem
      (fun k hk => hmemframevb k (by rcases hsretEvalCode with h | h <;> omega)) hcodeτ36
  have hs1_vb : cvb.σ.regs.get? Register.x9 = some sret := by
    rw [hframevb Register.x9 (by decide)]; exact hs1τ36
  have hsp_vb : cvb.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframevb Register.x2 (by decide)]; exact hspτ36
  have hx19_vb : cvb.σ.regs.get? Register.x19 = some Wl := by
    rw [hframevb Register.x19 (by decide)]; exact hx19τ36
  --------------------------------------------------------------------------------
  -- s3 restore slot [sp-40, sp-32)
  --------------------------------------------------------------------------------
  have hs3m5 : read64 m5 (sp.toNat - 40) = some w19.toNat := by
    show read64 (writeMap8 m4 (sp.toNat - 832) (sdData_val V928)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m4 (sp.toNat - 40) (sp.toNat - 832) (sdData_val V928) (by omega)]
    show read64 (writeMap8 m3 (sp.toNat - 840) (sdData_val V936)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m3 (sp.toNat - 40) (sp.toNat - 840) (sdData_val V936) (by omega)]
    show read64 (writeMap8 m2 (sp.toNat - 848) (sdData_val V944)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m2 (sp.toNat - 40) (sp.toNat - 848) (sdData_val V944) (by omega)]
    show read64 (writeMap8 m1 (sp.toNat - 832) (sdData_val V952)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m1 (sp.toNat - 40) (sp.toNat - 832) (sdData_val V952) (by omega)]
    show read64 (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj c.σ.mem (sp.toNat - 40) (sp.toNat - 848) (sdData_val V968) (by omega)]
    exact hs3slot
  have hs3vb : read64 cvb.σ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (a := sp.toNat - 40) (m := τ36.mem) (m' := cvb.σ.mem)
      (fun k hk => hmemframevb k (by rcases hsretStk with h | h <;> omega))
      (fun j hj => ⟨by omega, by omega⟩)]
    rw [hmemτ36e]; exact hs3m5
  obtain ⟨s3b0, s3b1, s3b2, s3b3, s3b4, s3b5, s3b6, s3b7, hs3b0, hs3b1, hs3b2, hs3b3, hs3b4, hs3b5, hs3b6, hs3b7, hs3rec⟩ :=
    read64_bytes cvb.σ.mem (sp.toNat - 40) w19.toNat hs3vb
  --------------------------------------------------------------------------------
  -- 0x80003af0: ld s3,0x418(sp) → x19 := w19 (restore entry s3)
  --------------------------------------------------------------------------------
  obtain ⟨τ37, j37, ht37', hj37, hGτ37, hmemτ37, hoτ37⟩ :=
    site_80003af0 cvb.σ cvb.tick cvb.steps (0x80003af0#64) vmivb (sp - 1088#64)
      s3b0 s3b1 s3b2 s3b3 s3b4 s3b5 s3b6 s3b7 hGvb hpcvb' hmivb hsp_vb hcode_vb rfl
      (by rw [haddr1048]; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048, htoh]; right; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048]; exact hs3b0) (by rw [haddr1048]; exact hs3b1)
      (by rw [haddr1048]; exact hs3b2) (by rw [haddr1048]; exact hs3b3)
      (by rw [haddr1048]; exact hs3b4) (by rw [haddr1048]; exact hs3b5)
      (by rw [haddr1048]; exact hs3b6) (by rw [haddr1048]; exact hs3b7) htickvb
  have hstepτ37 : Step cvb ⟨τ37, j37, cvb.steps + 1⟩ := by cases cvb; exact ht37'
  have hmemτ37e : τ37.mem = cvb.σ.mem := hmemτ37
  have hpcτ37 : τ37.regs.get? Register.PC = some (0x80003af4#64) := by
    have := obs_alu_pc hoτ37
    rwa [show BitVec.addInt (0x80003af0#64) 4 = (0x80003af4#64 : BitVec 64) from by decide] at this
  have hx19τ37 : τ37.regs.get? Register.x19 = some w19 := by
    have := obs_alu_rd hoτ37 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((s3b7.append s3b6).append s3b5).append s3b4).append s3b3).append s3b2).append s3b1).append s3b0) : BitVec (8*8))) = w19 from by
      apply BitVec.eq_of_toNat_eq; rw [sext_full, word8_toNat_recon, hs3rec]] at this
  have hs1τ37 : τ37.regs.get? Register.x9 = some sret := obs_alu_other hoτ37 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_vb
  have hspτ37 : τ37.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ37 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_vb
  obtain ⟨vmiτ37, hmiτ37⟩ := obs_alu_minstret hoτ37
  have houtτ37 : τ37.sailOutput = out0 := by rw [hoτ37.out, sailOutput_sigmaPost_alu]; exact houtvb
  have hcodeτ37 : Eval_exprLoaded τ37.mem := by rw [hmemτ37e]; exact hcode_vb
  --------------------------------------------------------------------------------
  -- 0x80003af4: j 0x800033ec → shared epilogue entry
  --------------------------------------------------------------------------------
  obtain ⟨τ38, j38, ht38', hj38, hGτ38, hmemτ38, hoτ38⟩ :=
    site_80003af4 τ37 j37 (cvb.steps + 1) (0x80003af4#64) vmiτ37 hGτ37 hpcτ37 hmiτ37 hcodeτ37 rfl
      (by rw [show ((0x80003af4#64:BitVec 64) + sign_extend (m := 64) (0x1ff8f8#21)) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hj37
  have hstepτ38 : Step ⟨τ37, j37, cvb.steps + 1⟩ ⟨τ38, j38, cvb.steps + 1 + 1⟩ := ht38'
  have hmemτ38e : τ38.mem = cvb.σ.mem := by rw [hmemτ38]; exact hmemτ37e
  have hpc_fin : τ38.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hoτ38
    rwa [show ((0x80003af4#64:BitVec 64) + sign_extend (m := 64) (0x1ff8f8#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : τ38.regs.get? Register.x9 = some sret := obs_jr_other hoτ38 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ37
  have hsp_fin : τ38.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hoτ38 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ37
  have hx19_fin : τ38.regs.get? Register.x19 = some w19 := obs_jr_other hoτ38 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ37
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hoτ38
  have hout_fin : τ38.sailOutput = out0 := by rw [hoτ38.out, sailOutput_sigmaPost_jump_x0]; exact houtτ37
  have hcode_fin : Eval_exprLoaded τ38.mem := by rw [hmemτ38e]; exact hcode_vb
  have hcode_fin : Eval_exprLoaded τ38.mem := by rw [hmemτ38e]; exact hcode_vb
  --------------------------------------------------------------------------------
  -- ASSEMBLE `PreEpilogueVD` at 0x800033ec.
  --------------------------------------------------------------------------------
  -- agreement `c.σ.mem ↔ m5` outside the whole stack region `[SL.lo, SL.hi)`
  have hAgSL_m5 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m5[k]? := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (sdData_val V928))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (sdData_val V928) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (sdData_val V936))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (sdData_val V936) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (sdData_val V944))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (sdData_val V944) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V952))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V952) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V968) (by omega)]
  have hSLfin : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = τ38.mem[k]? := by
    intro k hk
    rw [hmemτ38e]
    rw [← hmemframevb k (by rcases hsretInSL with ⟨hl, hr⟩; omega), hmemτ36e]
    exact hAgSL_m5 k hk
  have hstore_fin : StoreRepr τ38.mem N A φf' φc' st''.store :=
    hstoreSurv' τ38.mem (fun k hk => hSLfin k hk)
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ38.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSLfin k hk).trans (hm' k hk))
  have hMemExt_c_5 : MemExtends c.σ.mem m5 :=
    ((memExtends_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968)).trans
      (memExtends_writeMap8 m1 (sp.toNat - 832) (sdData_val V952))).trans
      (((memExtends_writeMap8 m2 (sp.toNat - 848) (sdData_val V944)).trans
        (memExtends_writeMap8 m3 (sp.toNat - 840) (sdData_val V936))).trans
        (memExtends_writeMap8 m4 (sp.toNat - 832) (sdData_val V928)))
  have hMemExt_5_40 : MemExtends m5 τ38.mem := by
    intro k bb hbb
    rw [hmemτ38e]
    exact hpresvb k bb (by rw [hmemτ36e]; exact hbb)
  have hMemExt_fin : MemExtends m0 τ38.mem :=
    (hMemExt.trans hMemExt_c_5).trans hMemExt_5_40
  have hAgTop_m5 : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem m5 := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (sdData_val V928))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (sdData_val V928) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (sdData_val V936))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (sdData_val V936) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (sdData_val V944))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (sdData_val V944) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V952))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V952) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V968) (by omega)]
  have hAgTop : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem τ38.mem := by
    intro k hk
    rw [hmemτ38e, ← hmemframevb k (by rcases hsretStk with h | h <;> omega), hmemτ36e]
    exact hAgTop_m5 k hk
  have hslotRa_f : read64 τ38.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 τ38.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 τ38.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 τ38.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  -- the callee-saved (noise) frame collapse: τ38 ← … ← c.σ (= gpre) then gpre → g.
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      τ38.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    by_cases hx19R : Register.x19 = R
    · subst hx19R
      have : τ38.regs.get? Register.x19 = some v19 := by rw [hx19_fin]; rw [hw19]
      rw [this]; exact hgx19.symm
    · have h19ne : (Register.x19 == R) = false := by
        rcases hXR : (Register.x19 == R) with _ | _
        · rfl
        · rw [beq_iff_eq] at hXR; exact absurd hXR hx19R
      have fchain : τ38.regs.get? R = c.σ.regs.get? R := by
        have f_38 : τ38.regs.get? R = τ37.regs.get? R :=
          (hoτ38.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_37 : τ37.regs.get? R = cvb.σ.regs.get? R :=
          (hoτ37.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' h19ne hnpc' hmii')
        have fvb : cvb.σ.regs.get? R = τ36.regs.get? R :=
          hframevb R ⟨ne (by decide), ne (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
        have f_36 : τ36.regs.get? R = τ35.regs.get? R :=
          (hoτ36.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (ne (X := Register.x1) (by decide)) hnpc' hmii')
        have f_35 : τ35.regs.get? R = τ34.regs.get? R :=
          (hoτ35.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_34 : τ34.regs.get? R = τ33.regs.get? R :=
          (hoτ34.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_33 : τ33.regs.get? R = τ32.regs.get? R :=
          (hoτ33.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_taken _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_32 : τ32.regs.get? R = τ31.regs.get? R :=
          (hoτ32.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_31 : τ31.regs.get? R = τ30.regs.get? R :=
          (hoτ31.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f_30 : τ30.regs.get? R = τ29.regs.get? R :=
          (hoτ30.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_29 : τ29.regs.get? R = τ28.regs.get? R :=
          (hoτ29.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_28 : τ28.regs.get? R = τ27.regs.get? R :=
          (hoτ28.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_27 : τ27.regs.get? R = τ26.regs.get? R :=
          (hoτ27.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_26 : τ26.regs.get? R = τ25.regs.get? R :=
          (hoτ26.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f_25 : τ25.regs.get? R = τ24.regs.get? R :=
          (hoτ25.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_24 : τ24.regs.get? R = τ23.regs.get? R :=
          (hoτ24.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_23 : τ23.regs.get? R = τ22.regs.get? R :=
          (hoτ23.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_22 : τ22.regs.get? R = τ21.regs.get? R :=
          (hoτ22.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_21 : τ21.regs.get? R = τ20.regs.get? R :=
          (hoτ21.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_20 : τ20.regs.get? R = τ19.regs.get? R :=
          (hoτ20.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_19 : τ19.regs.get? R = τ18.regs.get? R :=
          (hoτ19.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f_18 : τ18.regs.get? R = τ17.regs.get? R :=
          (hoτ18.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_17 : τ17.regs.get? R = τ16.regs.get? R :=
          (hoτ17.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_16 : τ16.regs.get? R = τ15.regs.get? R :=
          (hoτ16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_15 : τ15.regs.get? R = τ14.regs.get? R :=
          (hoτ15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_14 : τ14.regs.get? R = τ13.regs.get? R :=
          (hoτ14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_13 : τ13.regs.get? R = τ12.regs.get? R :=
          (hoτ13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_12 : τ12.regs.get? R = τ11.regs.get? R :=
          (hoτ12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_11 : τ11.regs.get? R = τ10.regs.get? R :=
          (hoτ11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_10 : τ10.regs.get? R = τ9.regs.get? R :=
          (hoτ10.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_9 : τ9.regs.get? R = τ8.regs.get? R :=
          (hoτ9.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_8 : τ8.regs.get? R = τ7.regs.get? R :=
          (hoτ8.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_7 : τ7.regs.get? R = τ6.regs.get? R :=
          (hoτ7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f_6 : τ6.regs.get? R = τ5.regs.get? R :=
          (hoτ6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_5 : τ5.regs.get? R = τ4.regs.get? R :=
          (hoτ5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_4 : τ4.regs.get? R = τ3.regs.get? R :=
          (hoτ4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_3 : τ3.regs.get? R = τ2.regs.get? R :=
          (hoτ3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f_2 : τ2.regs.get? R = τ1.regs.get? R :=
          (hoτ2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_taken _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f_1 : τ1.regs.get? R = σ16.regs.get? R :=
          (hoτ1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g16 : σ16.regs.get? R = σ15.regs.get? R :=
          (hobs16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
        have g15 : σ15.regs.get? R = σ14.regs.get? R :=
          (hobs15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g14 : σ14.regs.get? R = σ13.regs.get? R :=
          (hobs14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g13 : σ13.regs.get? R = σ12.regs.get? R :=
          (hobs13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g12 : σ12.regs.get? R = σ11.regs.get? R :=
          (hobs12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g11 : σ11.regs.get? R = σ10.regs.get? R :=
          (hobs11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g10 : σ10.regs.get? R = σ9.regs.get? R :=
          (hobs10.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g9 : σ9.regs.get? R = σ8.regs.get? R :=
          (hobs9.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g8 : σ8.regs.get? R = σ7.regs.get? R :=
          (hobs8.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g7 : σ7.regs.get? R = σ6.regs.get? R :=
          (hobs7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have g6 : σ6.regs.get? R = σ5.regs.get? R :=
          (hobs6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g5 : σ5.regs.get? R = σ4.regs.get? R :=
          (hobs5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g4 : σ4.regs.get? R = σ3.regs.get? R :=
          (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g3 : σ3.regs.get? R = σ2.regs.get? R :=
          (hobs3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' he8 hnpc' hmii')
        have g2 : σ2.regs.get? R = σ1.regs.get? R :=
          (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g1 : σ1.regs.get? R = c.σ.regs.get? R :=
          (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        rw [f_38, f_37, fvb, f_36, f_35, f_34, f_33, f_32, f_31, f_30, f_29, f_28, f_27,
          f_26, f_25, f_24, f_23, f_22, f_21, f_20, f_19, f_18, f_17, f_16, f_15, f_14, f_13, f_12,
          f_11, f_10, f_9, f_8, f_7, f_6, f_5, f_4, f_3, f_2, f_1,
          g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
      rw [fchain]
      exact (hframe R hR' h19ne).trans (hbridge R hR' he8 he9 he18 he2)
  have hmemframe_fin : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ38.mem[a]? = m0[a]? := by
    intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmemτ38e, ← hmemframevb a hsr, hmemτ36e]
      have hm5c : m5[a]? = c.σ.mem[a]? := by
        show (writeMap8 m4 (sp.toNat - 832) (sdData_val V928))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) a (sdData_val V928) (by omega)]
        show (writeMap8 m3 (sp.toNat - 840) (sdData_val V936))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) a (sdData_val V936) (by omega)]
        show (writeMap8 m2 (sp.toNat - 848) (sdData_val V944))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) a (sdData_val V944) (by omega)]
        show (writeMap8 m1 (sp.toNat - 832) (sdData_val V952))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) a (sdData_val V952) (by omega)]
        show (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) a (sdData_val V968) (by omega)]
      rw [hm5c]; exact hmemframe a ha hA
  -- the full Steps chain c → τ38
  have hchain : Steps c ⟨τ38, j38, cvb.steps + 1 + 1⟩ :=
    (Steps.single hstep1).trans <| (Steps.single hstep2).trans <| (Steps.single hstep3).trans <|
    (Steps.single hstep4).trans <| (Steps.single hstep5).trans <| (Steps.single hstep6).trans <|
    (Steps.single hstep7).trans <| (Steps.single hstep8).trans <| (Steps.single hstep9).trans <|
    (Steps.single hstep10).trans <| (Steps.single hstep11).trans <| (Steps.single hstep12).trans <|
    (Steps.single hstep13).trans <| (Steps.single hstep14).trans <| (Steps.single hstep15).trans <|
    (Steps.single hstep16).trans <| (Steps.single hstepτ1).trans <| (Steps.single hstepτ2).trans <|
    (Steps.single hstepτ3).trans <| (Steps.single hstepτ4).trans <| (Steps.single hstepτ5).trans <|
    (Steps.single hstepτ6).trans <| (Steps.single hstepτ7).trans <| (Steps.single hstepτ8).trans <|
    (Steps.single hstepτ9).trans <| (Steps.single hstepτ10).trans <| (Steps.single hstepτ11).trans <|
    (Steps.single hstepτ12).trans <| (Steps.single hstepτ13).trans <| (Steps.single hstepτ14).trans <|
    (Steps.single hstepτ15).trans <| (Steps.single hstepτ16).trans <| (Steps.single hstepτ17).trans <|
    (Steps.single hstepτ18).trans <| (Steps.single hstepτ19).trans <| (Steps.single hstepτ20).trans <|
    (Steps.single hstepτ21).trans <| (Steps.single hstepτ22).trans <| (Steps.single hstepτ23).trans <|
    (Steps.single hstepτ24).trans <| (Steps.single hstepτ25).trans <| (Steps.single hstepτ26).trans <|
    (Steps.single hstepτ27).trans <| (Steps.single hstepτ28).trans <| (Steps.single hstepτ29).trans <|
    (Steps.single hstepτ30).trans <| (Steps.single hstepτ31).trans <| (Steps.single hstepτ32).trans <|
    (Steps.single hstepτ33).trans <| (Steps.single hstepτ34).trans <| (Steps.single hstepτ35).trans <|
    (Steps.single hstepτ36).trans <|
    hsvb.trans <| (Steps.single hstepτ37).trans (Steps.single hstepτ38)
  refine ⟨⟨τ38, j38, cvb.steps + 1 + 1⟩, hchain, τ38.mem, φfm, φcm, φf', φc', hpfm, hpcm, hpf', hpc',
    ⟨?_, hMemExt_fin, hSurvSL_fin⟩⟩
  refine ⟨hGτ38, hj38, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
    hout_fin, houtStr, rfl, hcode_fin, (by rw [hmemτ38e]; exact hvalfinal),
    hstore_fin, hframeG,
    hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, hmemframe_fin,
    (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩


/-! ## `binOpSem_gt_int` — the spec-side gt bridge -/

theorem binOpSem_gt_int (s : Store) (a b : Int) :
    binOpSem s .gt (.int a) (.int b) = some (.bool (a > b)) := rfl

/-! ## `GtResid` — the blockC_gt residuals about the post-`TwoSubReturn` config -/
structure GtResid
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (Wl : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c'.σ.mem (aExpr.toNat + 8) = some 22
  slot : GtSlotPinned c'.σ.mem
  fullpop : ∀ k : Nat, ∃ w : BitVec 8, c'.σ.mem[k]? = some w
  x19 : c'.σ.regs.get? Register.x19 = some Wl
  wlbuf : read64 c'.σ.mem (sp.toNat - 960) = some Wl.toNat
  kindresp : read64 c'.σ.mem (sp.toNat - 1088) = some (2#64 : BitVec 64).toNat
  exprAl : aExpr.toNat % 4 = 0
  exprLo : 0x80000000 ≤ aExpr.toNat
  exprHi : aExpr.toNat + 16 ≤ 0x100000000
  exprWin : tohostAddr + 8 ≤ aExpr.toNat
  exprSL : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  sretAl : sret.toNat % 8 = 0
  sretLo : 0x80000000 ≤ sret.toNat
  sretHi : sret.toNat + 24 ≤ 0x100000000
  sretWin : tohostAddr + 16 ≤ sret.toNat
  sretVi : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  sretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  raAl : r.toNat % 4 = 0
  vbool : Value_boolLoaded c'.σ.mem
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo
  tableStk : opTableBase + 4 ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ## `evalGtSim` — the `EvalE.binary .gt` int recursive case -/
def EvalGtSimGoal : Prop :=
  ∀ (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalIH st d env el st' (.int a) →
    EvalIH st' d env er st'' (.int b) →
    EvalE st d env (.binary .gt el er) st'' (.bool (a > b)) →
    st'.store.frames.size = st''.store.frames.size →
    st'.store.closures.size = st''.store.closures.size →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .gt el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment ∧
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          GtResid gpre N A SL sp r sret aExpr Wl c') ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st'' (.bool (a > b)) sp r sret m0)

theorem evalGtSim : EvalGtSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 Wl out0 m0 hIHl hIHr _hEvalE hSizeF hSizeC
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hResid,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  have hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) (.int a) →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) (.int a) := by
    intro φ mm mm' hv hag
    have hsproom := hBE.sproom
    obtain ⟨hk, hp⟩ := hv
    have hAg : AgreeP (fun k => sp.toNat - 968 ≤ k ∧ k < sp.toNat - 952) mm mm' := by
      intro k hk'
      exact hag k (by omega) (by rcases hBE.arenaStk with h | h <;> omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [← read32_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hk
    · rw [readI64] at hp ⊢
      rw [← read64_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hp
  obtain ⟨c2, hs2, hTS⟩ :=
    blockB_binary gouter gpre N A SL φf φc st st' st'' d env .gt el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0⟩
  have hR : GtResid gpre N A SL sp r sret aExpr Wl c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_gt gpre g N A SL φf φc st' st'' a b sp r sret aExpr v8 v9 v18 v19 Wl c2.σ.sailOutput m0
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hR.fullpop, hR.x19, hR.wlbuf, hR.kindresp,
        hR.exprAl, hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode, hR.raAl,
        hR.vbool, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.bool (a > b)) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hpfm' : PhiExtends φf φfm st''.store.frames.size := hSizeF ▸ hpfm
  have hpcm' : PhiExtends φc φcm st''.store.closures.size := hSizeC ▸ hpcm
  have hpfF : PhiExtends φf φfe st''.store.frames.size := hpfm'.trans hpfe
  have hpcF : PhiExtends φc φce st''.store.closures.size := hpcm'.trans hpce
  have hExit : EvalExit g N A SL φf φc st'' (.bool (a > b)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans hpf', hpcF.trans hpc', hSurv⟩


#print axioms blockC_gt
#print axioms evalGtSim

end Vsa.Sim
