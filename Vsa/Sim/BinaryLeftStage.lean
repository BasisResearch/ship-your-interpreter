import Vsa.Sim.BinaryPrefixData
import Vsa.Sim.BinaryPrefixRun
import Vsa.Sim.BinaryPrefixOwnership
import Vsa.Sim.EvalBinSim
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.JalPreCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- The fixed left call contract and its reflected prefix share one endpoint. -/
structure BinaryLeftStaged
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (el : Expr)
    (sp r sret aExpr aEnv aLOp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (before after : Config) : Prop where
  frame : ∀ R, AbiPreservedNoise R → before.σ.regs.get? R = gpre R
  window : BinaryPrefix.Window SL (sp - 1088#64)
  call : JalPreCore el after st d env gpre N A SL φf φc
    0x800034f8#64 0x800034fc#64 0x1ffc6c#21 sp r sret
    ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aEnv aLOp v8 v9 v18
    out0 after.σ.mem
  segment : ∃ bs, CountedSelectedFramedSegResult BinaryPrefix.firstSeg
    (BinaryPrefix.firstInput aExpr (sp - 1088#64) v19 aEnvReg) [bs]
    0x800034e8#64 (BinaryPrefix.firstFoot (sp - 1088#64)) BinaryPrefix.firstKeep
    [(12, aLOp), (10, (sp - 1088#64) + 120#64), (2, sp - 1088#64),
      (19, v19), (13, aEnvReg)] before after

/-- Stage the left operand through the counted reflected prefix. -/
theorem blockB_binary_leftStaged
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (op : BinOp) (el er : Expr)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (c : Config)
    (hRec : BinaryRecContext gpre φf st env aEnvReg)
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        aEnvReg = BitVec.ofNat 64 (φf env) ∧
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
        -- WAVE 47i: the parent node's entry-ground bundle (pass-through from
        -- `blockA_binaryArm`).
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (the amended
        -- `JalPreBundle` tail; mirrors `blockB_binary`'s amended pre).
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 4 c (BinaryLeftStaged gpre N A SL φf φc st d env el
      sp r sret aExpr aEnv aLOp aEnvReg v8 v9 v18 v19 out0 c) := by
  obtain ⟨ment, hArm, hBE, hx11, hx13, henvReg, hx19, hgframe, hg8, hg18, hgx8v, hgx18v, hgx19v,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    _hAEx11, _hAEx8, _hAEx18⟩ := hArm
  obtain ⟨hviInt, hviSlot, hnbs⟩ : Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment := hviCode
  have hnodehi := hBE.node_hi
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088' : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have geometry : BinaryPrefix.Geometry aExpr (sp - 1088#64) :=
    { nodeLo := hexprLo
      nodeHi := hBE.node_hi
      nodeHtif := Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide : 8 ≤ 16) _) hexprWin)
      stackLo := by rw [hspsub]; have := hBE.sproom; omega
      stackHi := by rw [hspsub]; omega
      stackHtif := by
        rw [hspsub, htoh]
        have bound := hspwin
        rw [htoh] at bound
        omega
      stackAlign := by rw [hspsub]; have := hBE.sp16; omega }
  obtain ⟨bs, data⟩ := BinaryPrefix.first_data c.σ.mem aExpr (sp - 1088#64)
    v19 aEnvReg aLOp geometry (by rw [hmem]; exact hcode)
    (by rw [hmem]; exact hpayL)
  obtain ⟨c4, segment⟩ := BinaryPrefix.first_counted aExpr (sp - 1088#64)
    v19 aEnvReg aLOp bs c hG htick hpc
    ⟨ha2, hsp, hx19, hx13, trivial⟩ data.facts data.load.value geometry.stackHi
  obtain ⟨hx12_4, ha0_4, hsp_4, hx19_4, hx13_4, _⟩ := segment.selected_regs
  have hG4 := segment.good
  have hi4 := segment.tick
  have hpc4 : c4.σ.regs.get? Register.PC = some 0x800034f8#64 := segment.pc
  obtain ⟨vmi4, hmi4⟩ := segment.minstret
  have hs1_4 := (segment.reg_frame .x9 (by decide)).trans hs1
  have hx11_4 := (segment.reg_frame .x11 (by decide)).trans hx11
  have hout4 : c4.σ.sailOutput = out0 := segment.output.trans hout
  have hsretL : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088'
  let ma : Mem := writeMap8 ment (sp.toNat - 40) (sdData_val v19)
  let mcall1 : Mem := writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
  have hmem4e : c4.σ.mem = mcall1 := by
    rw [segment.mem, BinaryPrefix.first_log _ _ _ _ _ geometry.stackHi, hmem]
    change writeMap8 (writeMap8 ment ((sp - 1088#64).toNat + 1048)
      (sdData_val v19)) (sp - 1088#64).toNat (sdData_val aEnvReg) = mcall1
    rw [hspsub, show sp.toNat - 1088 + 1048 = sp.toNat - 40 from by omega]
  -- agreement ment ↔ mcall1 outside [SL.lo, sp)
  have hAgMcall1 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ment[k]? = mcall1[k]? := by
    intro k hk
    show ment[k]? = (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg))[k]?
    rw [getElem_writeMap8_disjoint ma (sp.toNat - 1088) k (sdData_val aEnvReg) (by omega)]
    show ment[k]? = (writeMap8 ment (sp.toNat - 40) (sdData_val v19))[k]?
    rw [getElem_writeMap8_disjoint ment (sp.toNat - 40) k (sdData_val v19) (by omega)]
  have hviInt1 : Value_intLoaded mcall1 :=
    loaded_value_int_agreeP ment mcall1
      (fun a ha => hAgMcall1 a (by rcases hBE.viStk with h | h <;> omega)) hviInt
  have hnbs1 : NBSPins mcall1 :=
    hnbs.survive_stack hBE.viStk hBE.tableStk hAgMcall1
  have hviSlot1 : IntSlotPinned mcall1 := by
    apply intSlot_writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega)
    exact intSlot_writeMap8 ment (sp.toNat - 40) (sdData_val v19)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega) hviSlot
  have hstore1 : StoreRepr mcall1 N A φf φc st.store :=
    hstoreSurv mcall1 (fun k hk1 _ => hAgMcall1 k (fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩))
  have hstoreSurv1 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall1[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hag
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩
    rw [hAgMcall1 k hk1']; exact hag k hk1 hk2
  have hsproom := hBE.sproom
  have hspSLhi := hBE.spSLhi
  have hexprL1 : ExprRepr mcall1 aLOp.toNat el :=
    hBE.lexpr_surv mcall1 (fun k hk => hAgMcall1 k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩))
  have hslotpeel : ∀ (a : Nat) (v : BitVec 64), sp.toNat - 32 ≤ a → a + 8 ≤ sp.toNat →
      read64 ment a = some v.toNat → read64 mcall1 a = some v.toNat := by
    intro a v ha1 ha2 hr
    show read64 (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)) a = some v.toNat
    rw [read64_writeMap8_disj ma a (sp.toNat - 1088) (sdData_val aEnvReg) (by omega)]
    show read64 (writeMap8 ment (sp.toNat - 40) (sdData_val v19)) a = some v.toNat
    rw [read64_writeMap8_disj ment a (sp.toNat - 40) (sdData_val v19) (by omega)]
    exact hr
  have hslotRa1 : read64 mcall1 (sp.toNat - 8) = some r.toNat :=
    hslotpeel (sp.toNat - 8) r (by omega) (by omega) hslotRa
  have hslotS01 : read64 mcall1 (sp.toNat - 16) = some v8.toNat :=
    hslotpeel (sp.toNat - 16) v8 (by omega) (by omega) hslotS0
  have hslotS11 : read64 mcall1 (sp.toNat - 24) = some v9.toNat :=
    hslotpeel (sp.toNat - 24) v9 (by omega) (by omega) hslotS1
  have hslotS21 : read64 mcall1 (sp.toNat - 32) = some v18.toNat :=
    hslotpeel (sp.toNat - 32) v18 (by omega) (by omega) hslotS2
  have hframe4 : ∀ R : Register, AbiPreservedNoise R → c4.σ.regs.get? R = gpre R := by
    have keep : ∀ R, AbiPreservedNoise R → BinaryPrefix.firstKeep R = true := by
      intro R
      cases R <;> decide
    exact fun R hR => (segment.reg_frame R (keep R hR)).trans (hgframe R hR)
  have hcodemcall1 : Eval_exprLoaded mcall1 :=
    loaded_eval_expr_agreeP ment mcall1
      (fun k hk => hAgMcall1 k (by rcases hBE.codeStk with h | h <;> omega)) hcode
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 := hsretL
  -- WAVE 47i: the LEFT child's entry-ground bundle at `mcall1` (kit moves 1+2+3).
  have hGroundM1 : EvalGround mcall1 SL A sp sret aExpr.toNat (.binary op el er) :=
    hGmt47.transport_offstack hBE.tableStk hBE.spSLhi
      (hGmt47.stack_bytes_extend
        ((memExtends_writeMap8 ment (sp.toNat - 40) (sdData_val v19)).trans
          (memExtends_writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg))))
      (fun a ha => (hAgMcall1 a ha).symm)
  have hpayL1 : read64 mcall1 (aExpr.toNat + 16) = some aLOp.toNat := by
    rw [evalGround_ast_read64_agree hGmt47 hBE.spSLhi
      (fun a ha => (hAgMcall1 a ha).symm) (off := 16) (by simp [exprReadFields])]
    exact hpayL
  have hGroundL : EvalGround mcall1 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aLOp.toNat el :=
    hGroundM1.child_params (fun lo hi hin => exprIn_binary_left hin aLOp.toNat hpayL1)
      hBE.tableStk hBE.spSLhi (by omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
  refine ⟨4, c4, Nat.le_refl _, segment.steps.toN_of_stepsEq (by exact segment.count), ?_⟩
  refine
    { frame := hgframe
      window :=
        { lo := by rw [hspsub]; have := hBE.sproom; omega
          hi := by rw [hspsub]; have := hBE.spSLhi; omega }
      segment := ⟨bs, segment⟩
      call := ?_ }
  rw [hmem4e]
  exact ⟨hRec.env_valid,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800034f8_ee σ i u (0x800034f8#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),
      hG4, hi4, hpc4, ha0_4, hs1_4, hx11_4, henvReg ▸ hx13_4, hx12_4, hsp_4, ⟨vmi4, hmi4⟩,
      hout4, houtStr, hmem4e, hGroundL.valueWordsTotal
        (by rw [hsub968]; have := hBE.sproom; omega)
        (by rw [hsub968]; have := hBE.sproom; have := hBE.spSLhi; omega),
      hcodemcall1, hviInt1, hviSlot1, hnbs1, hGroundL, hexprL1, hstore1, hstoreSurv1,
      hframe4, ⟨hg8, hg18, ⟨v19, hgx19v⟩, hRec.x20_defined, hRec.x21_defined⟩,
      hslotRa1, hslotS01, hslotS11, hslotS21,
      hBE.lop_ram.1, hBE.lop_ram.2, hBE.lop_win, hBE.lop_stk,
      (by rw [hsub968]; omega), (by rw [hsub968]; omega), (by rw [hsub968]; omega),
      (by omega), hBE.spSLhi, hBE.sp16, (by omega), hSLlo, hBE.SLhiRam, hSLwin,
      hBE.codeStk, hBE.viStk, hBE.tableStk, hBE.arenaStk, hBE.arenaCode,
      hstackBudgetL, hexprBodiesL, hstoreBodiesL⟩


#print axioms blockB_binary_leftStaged

end Vsa.Sim
