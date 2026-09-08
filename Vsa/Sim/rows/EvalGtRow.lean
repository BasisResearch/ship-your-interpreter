import Vsa.Sim.EvalBinSim4
import Vsa.Sim.EvalGtChain
import Vsa.Sim.ExitFootprint

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

/-- The exact memory footprint of the `.gt` integer cell from the return of both
children to the epilogue entry: the three dispatch-ladder temporaries
`[sp-848, sp-824)` (written by `sd` at `sp-848`, `sp-840`, `sp-832`) and the
`value_bool` box `[sret, sret+24)`. -/
def gtCellFoot (sp sret : Nat) (k : Nat) : Prop :=
  word8 (sp - 848) k ∨ word8 (sp - 840) k ∨ word8 (sp - 832) k ∨ resultSlot sret k

/-- `blockC_gt` RETAINING the cell's footprint `gtCellFoot` from the return memory
`mret` to the epilogue-entry memory.  `blockC_gt` is its projection. -/
theorem blockC_gt_footprint
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 mret : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 22 ∧      -- op token = binOpTok .gt
        GtSlotPinned c.σ.mem ∧
        BinaryReturnData SL sp sret c ∧
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
          gpre R = g R) ∧
        c.σ.mem = mret)
      (fun c => ∃ (mpre : Mem) (φfm φcm φfe φce : Addr → Nat),
        PhiExtends φf φfm nf ∧
        PhiExtends φc φcm nc ∧
        PhiExtends φfm φfe st'.store.frames.size ∧
        PhiExtends φcm φce st'.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (a > b)) sp r sret v8 v9 v18 out0 m0 mpre c ∧
        MemFootprint (gtCellFoot sp.toNat sret.toNat) mret mpre) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hReadData,
    hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl,
    hVbool, hcodeStk, hviStk, hTableStk, hsretInSL,
    hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi,
    hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge,
    hmret⟩ := hpre
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
  let lb0 := bytesT1 c.σ.mem (aExpr.toNat + 4)
  have hlb0 : bytesT1 c.σ.mem (aExpr.toNat + 4) = lb0 := rfl
  let lb1 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 1)
  have hlb1 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 1) = lb1 := rfl
  let lb2 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 2)
  have hlb2 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 2) = lb2 := rfl
  let lb3 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 3)
  have hlb3 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 3) = lb3 := rfl
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
  have hIntLoads := hReadData.toBinaryReturnLoads.int_readback (by omega) hvalL
  let Wl : BitVec 64 := bytesT8 c.σ.mem (sp.toNat - 960)
  have hX19 : c.σ.regs.get? Register.x19 = some Wl := hIntLoads.payload_register
  have hKindResp := hIntLoads.kind_spill
  have hWl_toInt : Wl.toInt = a := hIntLoads.int_value
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
  -- Block-reflection ladder 0x8000351c → 0x80003aec (replaces the τ1..τ35 threading)
  --------------------------------------------------------------------------------
  -- op-token bytes forced concrete (little-endian, 22 = 0x16,0,0,0) by read32 = 22.
  have hobv : ob0.toNat = 22 ∧ ob1.toNat = 0 ∧ ob2.toNat = 0 ∧ ob3.toNat = 0 := by
    have h0 := ob0.isLt; have h1 := ob1.isLt; have h2 := ob2.isLt; have h3 := ob3.isLt
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hob0' : c.σ.mem[aExpr.toNat + 8]? = some (0x16#8) := by
    have hb : ob0 = 0x16#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.1]; rfl
    rw [← hb]; exact hob0
  have hob1' : c.σ.mem[aExpr.toNat + 8 + 1]? = some (0#8) := by
    have hb : ob1 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.1]; rfl
    rw [← hb]; exact hob1
  have hob2' : c.σ.mem[aExpr.toNat + 8 + 2]? = some (0#8) := by
    have hb : ob2 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.1]; rfl
    rw [← hb]; exact hob2
  have hob3' : c.σ.mem[aExpr.toNat + 8 + 3]? = some (0#8) := by
    have hb : ob3 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.2]; rfl
    rw [← hb]; exact hob3
  -- kind-reload bytes @ v2+0 (= sp-1088), value 2, from the Pre read64.
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) ((2#64 : BitVec 64).toNat) hKindResp
  have hkVal : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7] = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  -- ── chain 0x8000351c → 0x80003628 ─────────────────────────────────────────
  obtain ⟨sC0, iC0, hStepsChain, hiC0, hGC0, hpcC0, hx10C0, hx12C0, hx16C0, hx17C0,
      hx2C0, hx9C0, hx19C0, hmemC0eq, houtC0, hmiC0ex, hframeChain⟩ :=
    evalGtChain_run c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
      lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3 rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
      hG hpc hmi hsp hx8c hs1 hX19 hcode hRkindVal hkVal
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega)
      (by rw [hop8]; exact lpin_of_present hob0') (by rw [hop8]; exact lpin_of_present hob1')
      (by rw [hop8]; exact lpin_of_present hob2') (by rw [hop8]; exact lpin_of_present hob3')
      (by rw [hline4]; omega) (by rw [hline4]; omega)
      (by rw [hline4, htoh]; right; omega)
      (by simpa only [hline4] using hlb0) (by simpa only [hline4] using hlb1)
      (by simpa only [hline4] using hlb2) (by simpa only [hline4] using hlb3)
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144]; exact lpin_of_present hrkb0) (by rw [haddr144]; exact lpin_of_present hrkb1)
      (by rw [haddr144]; exact lpin_of_present hrkb2) (by rw [haddr144]; exact lpin_of_present hrkb3)
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, show sp.toNat - 936 = sp.toNat - 944 + 8 from by omega]; exact lpin_of_present hrpb0)
      (by rw [haddr152, show sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1 from by omega]; exact lpin_of_present hrpb1)
      (by rw [haddr152, show sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2 from by omega]; exact lpin_of_present hrpb2)
      (by rw [haddr152, show sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3 from by omega]; exact lpin_of_present hrpb3)
      (by rw [haddr152, show sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4 from by omega]; exact lpin_of_present hrpb4)
      (by rw [haddr152, show sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5 from by omega]; exact lpin_of_present hrpb5)
      (by rw [haddr152, show sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6 from by omega]; exact lpin_of_present hrpb6)
      (by rw [haddr152, show sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7 from by omega]; exact lpin_of_present hrpb7)
      hSlot
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; right; omega) (by rw [haddr0]; omega)
      (by rw [haddr0]; exact lpin_of_present hkb0) (by rw [haddr0]; exact lpin_of_present hkb1)
      (by rw [haddr0]; exact lpin_of_present hkb2) (by rw [haddr0]; exact lpin_of_present hkb3)
      (by rw [haddr0]; exact lpin_of_present hkb4) (by rw [haddr0]; exact lpin_of_present hkb5)
      (by rw [haddr0]; exact lpin_of_present hkb6) (by rw [haddr0]; exact lpin_of_present hkb7)
      htick
  obtain ⟨vmC0, hmiC0⟩ := hmiC0ex
  have hcodeC0 : Vsa.Sim.Code.Eval_exprLoaded sC0.mem := by rw [hmemC0eq]; exact hcode
  -- ── AB 0x80003628 → 0x8000364c ─────────────────────────────────────────────
  obtain ⟨sAB, iAB, hStepsAB, hiAB, hGAB, hpcAB, hx12AB, hx15AB, hx14AB,
      hx2AB, hx10AB, hx16AB, hx9AB, hx17AB, hx19AB, hmemABeq, houtAB, hmiABex, hframeAB⟩ :=
    evalGtLadderAB sC0 iC0 (c.steps + 16) vmC0 (sp - 1088#64) sret Wr Wl
      hGC0 hpcC0 hmiC0 hx10C0 hx12C0 hx16C0 hx17C0 hx9C0 hx19C0 hx2C0 hcodeC0 hiC0
  obtain ⟨vmAB, hmiAB⟩ := hmiABex
  have hmemAB_c : sAB.mem = c.σ.mem := hmemABeq.trans hmemC0eq
  have hcodeAB : Vsa.Sim.Code.Eval_exprLoaded sAB.mem := by rw [hmemAB_c]; exact hcode
  -- C dead-load / slot bytes (total reads from the reached memory)
  let cs0 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat)
  have hcs0 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat) = cs0 := rfl
  let cs1 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 1)
  have hcs1 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 1) = cs1 := rfl
  let cs2 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 2)
  have hcs2 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 2) = cs2 := rfl
  let cs3 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 3)
  have hcs3 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 3) = cs3 := rfl
  let cs4 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 4)
  have hcs4 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 4) = cs4 := rfl
  let cs5 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 5)
  have hcs5 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 5) = cs5 := rfl
  let cs6 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 6)
  have hcs6 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 6) = cs6 := rfl
  let cs7 := bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 7)
  have hcs7 : bytesT1 c.σ.mem ((0x80019ff0#64 : BitVec 64).toNat + 7) = cs7 := rfl
  let ca0 := bytesT1 c.σ.mem (sp.toNat - 968)
  have hca0 : bytesT1 c.σ.mem (sp.toNat - 968) = ca0 := rfl
  let ca1 := bytesT1 c.σ.mem (sp.toNat - 968 + 1)
  have hca1 : bytesT1 c.σ.mem (sp.toNat - 968 + 1) = ca1 := rfl
  let ca2 := bytesT1 c.σ.mem (sp.toNat - 968 + 2)
  have hca2 : bytesT1 c.σ.mem (sp.toNat - 968 + 2) = ca2 := rfl
  let ca3 := bytesT1 c.σ.mem (sp.toNat - 968 + 3)
  have hca3 : bytesT1 c.σ.mem (sp.toNat - 968 + 3) = ca3 := rfl
  let ca4 := bytesT1 c.σ.mem (sp.toNat - 968 + 4)
  have hca4 : bytesT1 c.σ.mem (sp.toNat - 968 + 4) = ca4 := rfl
  let ca5 := bytesT1 c.σ.mem (sp.toNat - 968 + 5)
  have hca5 : bytesT1 c.σ.mem (sp.toNat - 968 + 5) = ca5 := rfl
  let ca6 := bytesT1 c.σ.mem (sp.toNat - 968 + 6)
  have hca6 : bytesT1 c.σ.mem (sp.toNat - 968 + 6) = ca6 := rfl
  let ca7 := bytesT1 c.σ.mem (sp.toNat - 968 + 7)
  have hca7 : bytesT1 c.σ.mem (sp.toNat - 968 + 7) = ca7 := rfl
  let cbb0 := bytesT1 c.σ.mem (sp.toNat - 952)
  have hcb0 : bytesT1 c.σ.mem (sp.toNat - 952) = cbb0 := rfl
  let cbb1 := bytesT1 c.σ.mem (sp.toNat - 952 + 1)
  have hcb1 : bytesT1 c.σ.mem (sp.toNat - 952 + 1) = cbb1 := rfl
  let cbb2 := bytesT1 c.σ.mem (sp.toNat - 952 + 2)
  have hcb2 : bytesT1 c.σ.mem (sp.toNat - 952 + 2) = cbb2 := rfl
  let cbb3 := bytesT1 c.σ.mem (sp.toNat - 952 + 3)
  have hcb3 : bytesT1 c.σ.mem (sp.toNat - 952 + 3) = cbb3 := rfl
  let cbb4 := bytesT1 c.σ.mem (sp.toNat - 952 + 4)
  have hcb4 : bytesT1 c.σ.mem (sp.toNat - 952 + 4) = cbb4 := rfl
  let cbb5 := bytesT1 c.σ.mem (sp.toNat - 952 + 5)
  have hcb5 : bytesT1 c.σ.mem (sp.toNat - 952 + 5) = cbb5 := rfl
  let cbb6 := bytesT1 c.σ.mem (sp.toNat - 952 + 6)
  have hcb6 : bytesT1 c.σ.mem (sp.toNat - 952 + 6) = cbb6 := rfl
  let cbb7 := bytesT1 c.σ.mem (sp.toNat - 952 + 7)
  have hcb7 : bytesT1 c.σ.mem (sp.toNat - 952 + 7) = cbb7 := rfl
  -- ── C 0x8000364c → 0x8000367c (store block) ────────────────────────────────
  obtain ⟨sC, iC, D1, D2, hStepsC, hiC, hGC, hmemC, hpcC, hx2C, hx10C, hx12C, hx16C,
      hx9C, hx17C, hx19C, houtC, hmiCex, hframeCf⟩ :=
    evalGtLadderC sAB iAB (c.steps + 16 + 7) vmAB (sp - 1088#64) sret Wr Wl
      cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 ca0 ca1 ca2 ca3 ca4 ca5 ca6 ca7
      cbb0 cbb1 cbb2 cbb3 cbb4 cbb5 cbb6 cbb7
      hGAB hpcAB hmiAB hx15AB hx2AB hx16AB hx9AB hx10AB hx12AB hx17AB hx19AB hcodeAB
      (by simpa only [hmemAB_c] using hcs0) (by simpa only [hmemAB_c] using hcs1)
      (by simpa only [hmemAB_c] using hcs2) (by simpa only [hmemAB_c] using hcs3)
      (by simpa only [hmemAB_c] using hcs4) (by simpa only [hmemAB_c] using hcs5)
      (by simpa only [hmemAB_c] using hcs6) (by simpa only [hmemAB_c] using hcs7)
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by simpa only [haddr120, hmemAB_c] using hca0) (by simpa only [haddr120, hmemAB_c] using hca1)
      (by simpa only [haddr120, hmemAB_c] using hca2) (by simpa only [haddr120, hmemAB_c] using hca3)
      (by simpa only [haddr120, hmemAB_c] using hca4) (by simpa only [haddr120, hmemAB_c] using hca5)
      (by simpa only [haddr120, hmemAB_c] using hca6) (by simpa only [haddr120, hmemAB_c] using hca7)
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by simpa only [haddr136, hmemAB_c] using hcb0) (by simpa only [haddr136, hmemAB_c] using hcb1)
      (by simpa only [haddr136, hmemAB_c] using hcb2) (by simpa only [haddr136, hmemAB_c] using hcb3)
      (by simpa only [haddr136, hmemAB_c] using hcb4) (by simpa only [haddr136, hmemAB_c] using hcb5)
      (by simpa only [haddr136, hmemAB_c] using hcb6) (by simpa only [haddr136, hmemAB_c] using hcb7)
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega)
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega)
      hiAB
  obtain ⟨vmC, hmiC⟩ := hmiCex
  -- normalise C's memory image to the sp-relative store addresses
  have hmemC2 : sC.mem = writeMap8 (writeMap8 c.σ.mem (sp.toNat - 848) D1) (sp.toNat - 832) D2 := by
    rw [hmemC, haddr240, haddr256, hmemAB_c]
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) D1
  let m2 : Mem := writeMap8 m1 (sp.toNat - 832) D2
  have hmemC2' : sC.mem = m2 := hmemC2
  have hcodem1 : Vsa.Sim.Code.Eval_exprLoaded m1 :=
    loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  have hcodem2 : Vsa.Sim.Code.Eval_exprLoaded m2 :=
    loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem1
  have hcodeC : Vsa.Sim.Code.Eval_exprLoaded sC.mem := by rw [hmemC2']; exact hcodem2
  -- agreement sC.mem ↔ c.σ.mem on the operand region (below the two C stores)
  have hAgD : ∀ k : Nat, k + 8 ≤ sp.toNat - 848 → sC.mem[k]? = c.σ.mem[k]? := by
    intro k hk
    rw [hmemC2']
    show (writeMap8 m1 (sp.toNat - 832) D2)[k]? = _
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (by omega)]
    show (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]? = _
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (by omega)]
  -- D load bytes @ sp-944/936/928 (abstract, re-read spilled operands)
  let da0 := bytesT1 c.σ.mem (sp.toNat - 944)
  have hda0 : bytesT1 c.σ.mem (sp.toNat - 944) = da0 := rfl
  let da1 := bytesT1 c.σ.mem (sp.toNat - 944 + 1)
  have hda1 : bytesT1 c.σ.mem (sp.toNat - 944 + 1) = da1 := rfl
  let da2 := bytesT1 c.σ.mem (sp.toNat - 944 + 2)
  have hda2 : bytesT1 c.σ.mem (sp.toNat - 944 + 2) = da2 := rfl
  let da3 := bytesT1 c.σ.mem (sp.toNat - 944 + 3)
  have hda3 : bytesT1 c.σ.mem (sp.toNat - 944 + 3) = da3 := rfl
  let da4 := bytesT1 c.σ.mem (sp.toNat - 944 + 4)
  have hda4 : bytesT1 c.σ.mem (sp.toNat - 944 + 4) = da4 := rfl
  let da5 := bytesT1 c.σ.mem (sp.toNat - 944 + 5)
  have hda5 : bytesT1 c.σ.mem (sp.toNat - 944 + 5) = da5 := rfl
  let da6 := bytesT1 c.σ.mem (sp.toNat - 944 + 6)
  have hda6 : bytesT1 c.σ.mem (sp.toNat - 944 + 6) = da6 := rfl
  let da7 := bytesT1 c.σ.mem (sp.toNat - 944 + 7)
  have hda7 : bytesT1 c.σ.mem (sp.toNat - 944 + 7) = da7 := rfl
  let dbb0 := bytesT1 c.σ.mem (sp.toNat - 936)
  have hdb0 : bytesT1 c.σ.mem (sp.toNat - 936) = dbb0 := rfl
  let dbb1 := bytesT1 c.σ.mem (sp.toNat - 936 + 1)
  have hdb1 : bytesT1 c.σ.mem (sp.toNat - 936 + 1) = dbb1 := rfl
  let dbb2 := bytesT1 c.σ.mem (sp.toNat - 936 + 2)
  have hdb2 : bytesT1 c.σ.mem (sp.toNat - 936 + 2) = dbb2 := rfl
  let dbb3 := bytesT1 c.σ.mem (sp.toNat - 936 + 3)
  have hdb3 : bytesT1 c.σ.mem (sp.toNat - 936 + 3) = dbb3 := rfl
  let dbb4 := bytesT1 c.σ.mem (sp.toNat - 936 + 4)
  have hdb4 : bytesT1 c.σ.mem (sp.toNat - 936 + 4) = dbb4 := rfl
  let dbb5 := bytesT1 c.σ.mem (sp.toNat - 936 + 5)
  have hdb5 : bytesT1 c.σ.mem (sp.toNat - 936 + 5) = dbb5 := rfl
  let dbb6 := bytesT1 c.σ.mem (sp.toNat - 936 + 6)
  have hdb6 : bytesT1 c.σ.mem (sp.toNat - 936 + 6) = dbb6 := rfl
  let dbb7 := bytesT1 c.σ.mem (sp.toNat - 936 + 7)
  have hdb7 : bytesT1 c.σ.mem (sp.toNat - 936 + 7) = dbb7 := rfl
  let dc0 := bytesT1 c.σ.mem (sp.toNat - 928)
  have hdc0 : bytesT1 c.σ.mem (sp.toNat - 928) = dc0 := rfl
  let dc1 := bytesT1 c.σ.mem (sp.toNat - 928 + 1)
  have hdc1 : bytesT1 c.σ.mem (sp.toNat - 928 + 1) = dc1 := rfl
  let dc2 := bytesT1 c.σ.mem (sp.toNat - 928 + 2)
  have hdc2 : bytesT1 c.σ.mem (sp.toNat - 928 + 2) = dc2 := rfl
  let dc3 := bytesT1 c.σ.mem (sp.toNat - 928 + 3)
  have hdc3 : bytesT1 c.σ.mem (sp.toNat - 928 + 3) = dc3 := rfl
  let dc4 := bytesT1 c.σ.mem (sp.toNat - 928 + 4)
  have hdc4 : bytesT1 c.σ.mem (sp.toNat - 928 + 4) = dc4 := rfl
  let dc5 := bytesT1 c.σ.mem (sp.toNat - 928 + 5)
  have hdc5 : bytesT1 c.σ.mem (sp.toNat - 928 + 5) = dc5 := rfl
  let dc6 := bytesT1 c.σ.mem (sp.toNat - 928 + 6)
  have hdc6 : bytesT1 c.σ.mem (sp.toNat - 928 + 6) = dc6 := rfl
  let dc7 := bytesT1 c.σ.mem (sp.toNat - 928 + 7)
  have hdc7 : bytesT1 c.σ.mem (sp.toNat - 928 + 7) = dc7 := rfl
  -- ── D 0x8000367c → 0x80003698 (store block) ────────────────────────────────
  obtain ⟨sD, iD, D3, D4, D5, hStepsD, hiD, hGD, hmemD, hpcD, hx2D,
      hx9D, hx12D, hx17D, hx19D, houtD, hmiDex, hframeDf⟩ :=
    evalGtLadderD sC iC (c.steps + 16 + 7 + 12) vmC (sp - 1088#64) sret Wr Wl
      da0 da1 da2 da3 da4 da5 da6 da7 dbb0 dbb1 dbb2 dbb3 dbb4 dbb5 dbb6 dbb7
      dc0 dc1 dc2 dc3 dc4 dc5 dc6 dc7
      hGC hpcC hmiC hx2C hx10C hx16C hx9C hx12C hx17C hx19C hcodeC
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by simpa only [haddr144, hAgD (sp.toNat - 944) (by omega)] using hda0)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 1) (by omega)] using hda1)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 2) (by omega)] using hda2)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 3) (by omega)] using hda3)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 4) (by omega)] using hda4)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 5) (by omega)] using hda5)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 6) (by omega)] using hda6)
      (by simpa only [haddr144, hAgD (sp.toNat - 944 + 7) (by omega)] using hda7)
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by simpa only [haddr152, show sp.toNat - 936 = sp.toNat - 936 from rfl, hAgD (sp.toNat - 936) (by omega)] using hdb0)
      (by simpa only [haddr152, show sp.toNat - 936 + 1 = sp.toNat - 936 + 1 from rfl, hAgD (sp.toNat - 936 + 1) (by omega)] using hdb1)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 2) (by omega)] using hdb2)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 3) (by omega)] using hdb3)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 4) (by omega)] using hdb4)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 5) (by omega)] using hdb5)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 6) (by omega)] using hdb6)
      (by simpa only [haddr152, hAgD (sp.toNat - 936 + 7) (by omega)] using hdb7)
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      (by simpa only [haddr160, hAgD (sp.toNat - 928) (by omega)] using hdc0)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 1) (by omega)] using hdc1)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 2) (by omega)] using hdc2)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 3) (by omega)] using hdc3)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 4) (by omega)] using hdc4)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 5) (by omega)] using hdc5)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 6) (by omega)] using hdc6)
      (by simpa only [haddr160, hAgD (sp.toNat - 928 + 7) (by omega)] using hdc7)
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega)
      (by rw [haddr248]; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, htoh]; omega) (by rw [haddr248]; omega)
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega)
      hiC
  obtain ⟨vmD, hmiD⟩ := hmiDex
  -- normalise D's memory image (three more stores over m2)
  have hmemD2 : sD.mem = writeMap8 (writeMap8 (writeMap8 sC.mem (sp.toNat - 848) D3)
      (sp.toNat - 840) D4) (sp.toNat - 832) D5 := by
    rw [hmemD, haddr240, haddr248, haddr256]
  let m3 : Mem := writeMap8 m2 (sp.toNat - 848) D3
  let m4 : Mem := writeMap8 m3 (sp.toNat - 840) D4
  let m5 : Mem := writeMap8 m4 (sp.toNat - 832) D5
  have hmemD2' : sD.mem = m5 := by rw [hmemD2, hmemC2']
  have hcodem3 : Vsa.Sim.Code.Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem2
  have hcodem4 : Vsa.Sim.Code.Eval_exprLoaded m4 :=
    loaded_eval_expr_agreeP m3 m4
      (fun k hk => (getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem3
  have hcodem5 : Vsa.Sim.Code.Eval_exprLoaded m5 :=
    loaded_eval_expr_agreeP m4 m5
      (fun k hk => (getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem4
  have hcodeD : Vsa.Sim.Code.Eval_exprLoaded sD.mem := by rw [hmemD2']; exact hcodem5
  -- ── EF 0x80003698 → 0x80003ae4 ─────────────────────────────────────────────
  obtain ⟨sEF, iEF, hStepsEF, hiEF, hGEF, hmemEFeq, hpcEF, hx11EF, hx9EF, hx2EF,
      hx19EF, houtEF, hmiEFex, hframeEF⟩ :=
    evalGtLadderEF sD iD (c.steps + 16 + 7 + 12 + 7) vmD Wr Wl sret (sp - 1088#64)
      hGD hpcD hmiD hx17D hx19D hx12D hx9D hx2D hcodeD hiD
  obtain ⟨vmEF, hmiEF⟩ := hmiEFex
  have hmemEF5 : sEF.mem = m5 := by rw [hmemEFeq]; exact hmemD2'
  have hcodeEF : Vsa.Sim.Code.Eval_exprLoaded sEF.mem := by rw [hmemEF5]; exact hcodem5
  -- ── G 0x80003ae4 → 0x80003aec (produces the τ35 pre-jal state) ─────────────
  obtain ⟨τ35, j35, hStepsG, hj35, hGτ35, hmemGeq, hpcτ35, hx11τ35pre, hx10τ35, hs1τ35,
      hspτ35, hx19τ35, houtG, hmiτ35ex, hframeG_lad⟩ :=
    evalGtLadderG sEF iEF (c.steps + 16 + 7 + 12 + 7 + 7) vmEF (cmpScalar Wl Wr) sret
      (sp - 1088#64) Wl
      hGEF hpcEF hmiEF hx11EF hx9EF hx2EF hx19EF hcodeEF hiEF
  obtain ⟨vmiτ35, hmiτ35⟩ := hmiτ35ex
  let cmpV : BitVec 64 := cmpScalar Wl Wr
  let u16 : Nat := c.steps + 16
  let u29 : Nat := u16 + 29
  have hmemτ35e : τ35.mem = m5 := by rw [hmemGeq]; exact hmemEF5
  have hx11τ35 : τ35.regs.get? Register.x11
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) := hx11τ35pre
  have hcodeτ35 : Vsa.Sim.Code.Eval_exprLoaded τ35.mem := by rw [hmemτ35e]; exact hcodem5
  have houtτ35 : τ35.sailOutput = out0 :=
    ((((((houtG.trans houtEF).trans houtD).trans houtC).trans houtAB).trans houtC0).trans hout0eq)
  -- composed ladder Steps (16+7+12+7+7+2 = 51) and the ABI-noise frame
  have hLadderSteps : Steps ⟨c.σ, c.tick, c.steps⟩ ⟨τ35, j35, c.steps + 16 + 7 + 12 + 7 + 7 + 2⟩ :=
    ((((hStepsChain.trans hStepsAB).trans hStepsC).trans hStepsD).trans hStepsEF).trans hStepsG
  have hLadderFrame : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      τ35.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8
    exact ((((((hframeG_lad R hR he8).trans (hframeEF R hR he8)).trans (hframeDf R hR he8)).trans
      (hframeCf R hR he8)).trans (hframeAB R hR he8)).trans (hframeChain R hR he8))
  --------------------------------------------------------------------------------
  -- 0x80003aec: jal value_bool → PC := 0x800027f8, x1 := 0x80003af0
  --------------------------------------------------------------------------------
  have hVbool5 : Value_boolLoaded m5 := by
    have h1 : Value_boolLoaded m1 := loaded_bool_writeMap8 c.σ.mem (sp.toNat - 848) (D1) (by rcases hviStk with h | h <;> omega) hVbool
    have h2 : Value_boolLoaded m2 := loaded_bool_writeMap8 m1 (sp.toNat - 832) (D2) (by rcases hviStk with h | h <;> omega) h1
    have h3 : Value_boolLoaded m3 := loaded_bool_writeMap8 m2 (sp.toNat - 848) (D3) (by rcases hviStk with h | h <;> omega) h2
    have h4 : Value_boolLoaded m4 := loaded_bool_writeMap8 m3 (sp.toNat - 840) (D4) (by rcases hviStk with h | h <;> omega) h3
    exact loaded_bool_writeMap8 m4 (sp.toNat - 832) (D5) (by rcases hviStk with h | h <;> omega) h4
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
    show read64 (writeMap8 m4 (sp.toNat - 832) (D5)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m4 (sp.toNat - 40) (sp.toNat - 832) (D5) (by omega)]
    show read64 (writeMap8 m3 (sp.toNat - 840) (D4)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m3 (sp.toNat - 40) (sp.toNat - 840) (D4) (by omega)]
    show read64 (writeMap8 m2 (sp.toNat - 848) (D3)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m2 (sp.toNat - 40) (sp.toNat - 848) (D3) (by omega)]
    show read64 (writeMap8 m1 (sp.toNat - 832) (D2)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m1 (sp.toNat - 40) (sp.toNat - 832) (D2) (by omega)]
    show read64 (writeMap8 c.σ.mem (sp.toNat - 848) (D1)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj c.σ.mem (sp.toNat - 40) (sp.toNat - 848) (D1) (by omega)]
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
      (by rw [haddr1048, htoh]; right; omega)
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
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (D5))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (D5) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (D4))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (D4) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (D3))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (D3) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (D2))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (D2) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (D1))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (D1) (by omega)]
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
    ((memExtends_writeMap8 c.σ.mem (sp.toNat - 848) (D1)).trans
      (memExtends_writeMap8 m1 (sp.toNat - 832) (D2))).trans
      (((memExtends_writeMap8 m2 (sp.toNat - 848) (D3)).trans
        (memExtends_writeMap8 m3 (sp.toNat - 840) (D4))).trans
        (memExtends_writeMap8 m4 (sp.toNat - 832) (D5)))
  have hMemExt_5_40 : MemExtends m5 τ38.mem := by
    intro k bb hbb
    rw [hmemτ38e]
    exact hpresvb k bb (by rw [hmemτ36e]; exact hbb)
  have hMemExt_fin : MemExtends m0 τ38.mem :=
    (hMemExt.trans hMemExt_c_5).trans hMemExt_5_40
  have hWords_fin : ValueWordsTotal τ38.mem sret.toNat :=
    ValueWordsTotal.mono (hMemExt_c_5.trans hMemExt_5_40)
      hReadData.sret_words
  have hAgTop_m5 : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem m5 := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (D5))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (D5) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (D4))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (D4) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (D3))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (D3) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (D2))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (D2) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (D1))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (D1) (by omega)]
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
        rw [f_38, f_37, fvb, f_36]
        exact hLadderFrame R hR' he8
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
        show (writeMap8 m4 (sp.toNat - 832) (D5))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) a (D5) (by omega)]
        show (writeMap8 m3 (sp.toNat - 840) (D4))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) a (D4) (by omega)]
        show (writeMap8 m2 (sp.toNat - 848) (D3))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) a (D3) (by omega)]
        show (writeMap8 m1 (sp.toNat - 832) (D2))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) a (D2) (by omega)]
        show (writeMap8 c.σ.mem (sp.toNat - 848) (D1))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) a (D1) (by omega)]
      rw [hm5c]; exact hmemframe a ha hA
  -- the full Steps chain c → τ38
  have hchain : Steps c ⟨τ38, j38, cvb.steps + 1 + 1⟩ :=
    hLadderSteps.trans <| (Steps.single hstepτ36).trans <|
    hsvb.trans <| (Steps.single hstepτ37).trans (Steps.single hstepτ38)
  refine ⟨⟨τ38, j38, cvb.steps + 1 + 1⟩, hchain, τ38.mem, φfm, φcm, φf', φc', hpfm, hpcm, hpf', hpc',
    ⟨?_, hMemExt_fin, hWords_fin, hSurvSL_fin⟩, ?_⟩
  refine ⟨hGτ38, hj38, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
    hout_fin, houtStr, rfl, hcode_fin, (by rw [hmemτ38e]; exact hvalfinal),
    hstore_fin, hframeG,
    hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, hmemframe_fin,
    (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩
  -- the footprint: `mret = c.mem → m5` are the three temporaries, `m5 = τ36.mem → τ38.mem`
  -- is the `value_bool` box (the remaining steps write nothing).
  refine ⟨fun k hk => ?_⟩
  unfold gtCellFoot word8 resultSlot at hk
  have hbox : ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) := by omega
  have hm5k : m5[k]? = c.σ.mem[k]? := by
    show (writeMap8 m4 (sp.toNat - 832) D5)[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5 (by omega)]
    show (writeMap8 m3 (sp.toNat - 840) D4)[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4 (by omega)]
    show (writeMap8 m2 (sp.toNat - 848) D3)[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3 (by omega)]
    show (writeMap8 m1 (sp.toNat - 832) D2)[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (by omega)]
    show (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (by omega)]
  show τ38.mem[k]? = mret[k]?
  rw [hmemτ38e, ← hmemframevb k hbox, hmemτ36e, hm5k, hmret]

/-- The footprint-free projection (the landed statement). -/
theorem blockC_gt
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 22 ∧      -- op token = binOpTok .gt
        GtSlotPinned c.σ.mem ∧
        BinaryReturnData SL sp sret c ∧
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
        PhiExtends φf φfm nf ∧
        PhiExtends φc φcm nc ∧
        PhiExtends φfm φfe st'.store.frames.size ∧
        PhiExtends φcm φce st'.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (a > b)) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hReadData, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq, hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl, hVbool, hcodeStk, hviStk, hTableStk, hsretInSL, hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi, hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ := hpre
  obtain ⟨c', hs, mpre, φfm, φcm, φfe, φce, hp1, hp2, hp3, hp4, hPre, _⟩ :=
    blockC_gt_footprint gpre g N A SL φf φc nf nc st' st'' a b sp r sret aExpr v8 v9 v18 v19 out0 m0 c.σ.mem c
      ⟨hTS, hgx8, hopTok, hSlot, hReadData, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq, hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl, hVbool, hcodeStk, hviStk, hTableStk, hsretInSL, hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi, hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge, rfl⟩
  exact ⟨c', hs, mpre, φfm, φcm, φfe, φce, hp1, hp2, hp3, hp4, hPre⟩

#print axioms blockC_gt_footprint
#print axioms blockC_gt


/-! ## `binOpSem_gt_int` — the spec-side gt bridge -/

theorem binOpSem_gt_int (s : Store) (a b : Int) :
    binOpSem s .gt (.int a) (.int b) = some (.bool (a > b)) := rfl

/-! ## `GtResid` — the blockC_gt residuals about the post-`TwoSubReturn` config -/
structure GtResid
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c'.σ.mem (aExpr.toNat + 8) = some 22
  slot : GtSlotPinned c'.σ.mem
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
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalE st d env el st' (.int a) →
    EvalIH st d env el st' (.int a) →
    EvalIH st' d env er st'' (.int b) →
    EvalE st d env (.binary .gt el er) st'' (.bool (a > b)) →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .gt el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
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
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry.
        EvalGround ment SL A sp sret aExpr.toNat (.binary .gt el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`) --
        -- forwarded to `blockB_binary`'s amended pre.
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
            st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          GtResid gpre N A SL sp r sret aExpr c') ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (a > b)) sp r sret m0)

theorem evalGtSim : EvalGtSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr _hEvalE
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR, hResid,
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
  obtain ⟨c2, hs2, hReturned⟩ :=
    blockB_binary_data gouter gpre N A SL φf φc st st' st'' d env .gt el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  have hData := hReturned.extra
  have hR : GtResid gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_gt gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hData,
        hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode, hR.raAl,
        hR.vbool, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.bool (a > b)) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  -- store counts only grow: `st.store ≤ st''.store` (both sub-calls), and `st'` is
  -- The left derivation supplies the intermediate-state growth bound.
  have hmono := evalE_store_mono _hEvalE
  have hleftMono := evalE_store_mono hLeft
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hleftMono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hleftMono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size := hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.bool (a > b)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩


#print axioms blockC_gt
#print axioms evalGtSim

end Vsa.Sim
