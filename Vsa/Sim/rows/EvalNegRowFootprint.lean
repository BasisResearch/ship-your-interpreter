import Vsa.Sim.EvalNegSim3
import Vsa.Sim.UnaryHeadFootprint

/-!
# `EvalNegRowFootprint` — the footprint sibling of the `neg` arm (IH tower, Level 1)

The same execution as `evalNegSim` (`EvalNegSim3.lean`), returning `EvalExitF`
instead of `EvalExitD`.  The node's footprint is derived from the layer:
```
m0   ─ blockB_unary_footprint    ─▸  mret   unaryHeadFoot F  (stack window ∪ child)
mret ─ blockC_neg_footprint      ─▸  mpre   negCellFoot      (three temporaries ∪ box)
mpre ─ blockD_v_rec_footprint    ─▸  exit   inherited
```
For a non-allocating child the node is non-allocating (`noArenaFoot`), and the
`EvalIHF noArenaFoot` supplier `evalNegIHF` closes the arm at that family.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
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
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- The `neg` node's footprint: the head's plus the cell's. -/
def negNodeFoot (F : FootFam) : FootFam := fun SL A sp sret k =>
  unaryHeadFoot F SL A sp k ∨ negCellFoot sp sret k

/-- A non-allocating child makes a non-allocating node. -/
theorem negNodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : negNodeFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (unaryHeadFoot_noArena h k hh)
  · unfold negCellFoot word8 resultSlot at hc
    unfold noArenaFoot stackWin resultSlot
    omega

/-- **`evalNegSimF`** — `evalNegSim` with the node's footprint retained:
`blockA_k ≫ blockB_unary_footprint ≫ blockC_neg_footprint ≫ blockD_v_rec_footprint`. -/
theorem evalNegSimF (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (n : Int)
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem)
    (hIH : EvalIHF F st d env esub st' (.int n))
    (hEvalE : EvalE st d env (.unary .neg esub) st' (.int (wrap64 (-n)))) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv aExpr m0 c ∧
        NegExtras N A SL st esub sp sret aExpr aOperand m0)
      (EvalExitF (negNodeFoot F) g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.int (wrap64 (-n))) sp r sret m0) := by
  intro c ⟨hc, hx⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0 ===
  have hkm0 : read32 m0 aExpr.toNat = some 8 := exprRepr_unary_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, hx13c1⟩ :=
    blockA_k g N A SL φf φc st env (.unary .neg esub) 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl, hnb⟩ := hcl
        have hvicodeD := hc.vicode_stack_disjoint
        have htableD := hc.table_stack_disjoint
        refine ⟨loaded_int_writeMap8 mem a8 dd (by omega) hvi, ?_, ?_⟩
        · exact intSlot_writeMap8 mem a8 dd (by simp only [jumpTableBase]; omega) hsl
        · exact nbsPins_writeMap8 mem a8 dd (by omega) (by omega) hnb)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.envReg⟩⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat (.unary .neg esub) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (unOpTok .neg) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some aOperand.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aOperand.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hpeq : p = aOperand.toNat := by
    have := hpayMent.symm.trans hpayMent'; exact Option.some.inj this
  subst hpeq
  have hOperandReprMent : ExprRepr ment aOperand.toNat esub := hsubReprMent
  have hsp1088N : 1088 ≤ sp.toNat := by
    have := hx.sp_headroom; have := hc.stack_ram.1; omega
  have hspsubN : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsubsretN : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat
      = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088N
  have hgroundChild : EvalGround ment SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub :=
    (hc.mem ▸ hc.ground).child_at
      (fun lo hi hin => exprIn_unary_child hin aOperand.toNat hpayMent')
      hMentM0 ((hc.mem ▸ hc.ground).stack_bytes_extend _hpresM)
      hc.table_stack_disjoint hx.sp_SLhi
      (by omega)
      (by rw [hsubsretN]; have := hx.sp_headroom; have := hc.stack_ram.1; omega)
      (by rw [hsubsretN]; omega)
  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec, with footprint ===
  obtain ⟨c2, hs2, hReturned⟩ :=
    blockB_unary_footprint F g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .neg esub
      (.int n) sp r sret aExpr aEnv aOperand v8 v9 v18 c.σ.sailOutput m0
      hc.env_valid (hc.envset_defined_frame hbridge) hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hpayMent', hOperandReprMent, hgroundChild, hx.expr24,
        hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega), hx.arena_stk, hx.arena_code,
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.unary UnOp.neg esub).stackNeed
                = evalFrame + esub.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            simp only [h1, h2, evalFrame]; omega),
        Expr.bodiesBound_unary hc.expr_bodies,
        hc.store_bodies, _hpresM⟩
  obtain ⟨mcall, hSubR, hCallMemory⟩ := hReturned.result
  have hHeadFoot := hReturned.extra
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hCallMemory.outside
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1  -- discipline: allow(R6-anon-projection-tower) the landed `SubEvalReturn` tower has no named destructurer; same projection as `evalNegSim`
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVintM0 : Value_intLoaded m0 := hc.mem ▸ hc.value_int_code
  have hVintMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hc.vicode_stack_disjoint; omega)).symm) hVintM0
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hMemExtM0mc : MemExtends m0 mcall := hCallMemory.presence
  have hExprMcall : ExprRepr mcall aExpr.toNat (.unary .neg esub) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  -- === block C: post-call neg tail → PreEpilogueVD .int(wrap64 -n), with footprint ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD, hCellFoot⟩ :=
    blockC_neg_footprint (fun R => c1.σ.regs.get? R) g N A SL φf φc
      st.store.frames.size st.store.closures.size
      st' n sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0 c2.σ.mem
      (hc.mem ▸ hc.sret_words)
      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hMemExtM0mc,
        hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_vicode_disjoint_int, hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVintMcall, hx.code_stk, (by have := hx.vicode_stk; omega), hx.vi_arena,
        hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge, rfl⟩
  -- === block D: shared epilogue → EvalExitD, inheriting the composed footprint ===
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (negNodeFoot F SL A sp.toNat sret.toNat)
      g N A SL φfe φce st' (.int (wrap64 (-n))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := evalE_store_mono hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' (.int (wrap64 (-n))) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

/-- **`negRowF`** — the `neg` arm from `EvalEntry` at a non-allocating child: the
node is non-allocating (`EvalExitF noArenaFoot`). -/
theorem negRowF
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (n : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hIH : EvalIHF noArenaFoot st d env esub st' (.int n))
    (hEvalE : EvalE st d env (.unary .neg esub) st' (.int (wrap64 (-n)))) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv aExpr m0)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.int (wrap64 (-n))) sp r sret m0) := by
  intro c hc
  obtain ⟨aOperand, hx⟩ := hc.unaryExtras
  obtain ⟨c', hs, hExitF⟩ :=
    evalNegSimF noArenaFoot g N A SL φf φc st st' d env esub n sp r sret aEnv aExpr
      aOperand m0 hIH hEvalE c ⟨hc, hx⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hx.sp_headroom; omega
  exact ⟨c', hs, hExitF.result, hExitF.extra.mono (negNodeFoot_noArena hsproom)⟩

/-- **The `EvalIHF noArenaFoot` supplier for the `neg` arm**: a non-allocating
child derivation yields a non-allocating parent. -/
theorem evalNegIHF (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (n : Int)
    (hE : EvalE st d env esub st' (.int n))
    (hIH : EvalIHF noArenaFoot st d env esub st' (.int n)) :
    EvalIHF noArenaFoot st d env (.unary .neg esub) st' (.int (wrap64 (-n))) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    negRowF g N A SL φf φc st st' d env esub n sp r sret aEnv aExpr m0 hIH
      (.neg st d env esub st' n hE))

#print axioms negNodeFoot_noArena
#print axioms evalNegSimF
#print axioms negRowF
#print axioms evalNegIHF

end Vsa.Sim
