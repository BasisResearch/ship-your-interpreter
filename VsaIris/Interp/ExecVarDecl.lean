import VsaIris.Interp.ExecVar
import VsaIris.Interp.ExecChild

/-!
`var x = e;` and `var x;` on one core each. The declaration tail (`env_define`, epilogue) is the
mode-generic rule `VarTail`, with the total (`varTail`) and partial (`varTailP`) instances; the
initializer is a `ChildCall`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The declaration tail from the parked `env_define` staging at `0x800040f0`, in one mode:
persistent context `Hyp`, world regime `ρ`, continuation `K`. -/
def VarTail (N : NativeAddrs) (inp : Nat) (Wp : MachWP (GF := GF) (vsaModel live))
    (Φ : Nat × String → IProp GF) (Hyp : IProp GF) (ρ : Regime) (K : IProp GF) (st : St)
    (d env : Nat) (x : String) (eo : Option Expr) (v : Value)
    (aRet s ret v8 v9 v18 v19 : BitVec 64) (R0 : Nat → BitVec 64) : Prop :=
  ∀ (aS aE w0 w1 w2 : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (P : Nat → Prop) (m : Mem)
    (pn pi : Nat),
    StackGeom s (execNeed (.varDecl x eo) d) → ret.toNat % 4 = 0 → VarNode m P aS x eo pn pi →
    (∀ k, P k → ReadOK k) → R 2 = execSP s → R 8 = aS → R 19 = aE →
    KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R → ExecSaved Mt s ret v8 v9 v18 v19 →
    ldv .ld Mt (s.toNat - 176 + 104) = w0 → ldv .ld Mt (s.toNat - 176 + 112) = w1 →
    ldv .ld Mt (s.toNat - 176 + 120) = w2 →
    □ Hyp ∗ codeRes ∗ roOn P m ∗ □ frameAt env aE.toNat ∗ □ valOf N v w0 w1 w2 ∗
      ms 0x800040f0#64 R (InExt (s.toNat - 176, 176)) Mt ∗
      stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp ρ st d ∗ K ⊢ Wp.W Φ

theorem varTail_rule (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N) {Φ : Nat × String → IProp GF}
    {k : Nat} {st : St} {d env : Nat} {x : String} {eo : Option Expr} {v : Value}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 : Nat → BitVec 64} :
    VarTail N inp (twpW (vsaModel live)) Φ emp (.counted (k + defineCost st.store env x))
      (execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k)
        ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19)
      st d env x eo v aRet s ret v8 v9 v18 v19 R0 := by
  intro aS aE w0 w1 w2 R Mt P m pn pi hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iintro ⟨#-, #Hcode, #Hro, #Hfb, #Hv, Hms, Hst, Hslot, Hw, HK⟩
  ihave Hed := hed
  iapply varTail hlive (twpW _) (N := N) (inp := inp) (k := k) (st := st) (env := env) (v := v)
    hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iframe Hed Hcode Hro Hfb Hv Hms Hst Hslot Hw HK

theorem varTailP_rule (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live) {Core : IProp GF}
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core)
    (hed : ⊢ envDefineSpec (GF := GF) (wpW (vsaModel live)) N) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {x : String} {eo : Option Expr} {v : Value}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 : Nat → BitVec 64} :
    VarTail N inp (wpW (vsaModel live)) Φ Newlib.binImg .uncounted
      iprop(execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
          ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19 ∧
        (iprop(abortAt Core s (execNeed (.varDecl x eo) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))
      st d env x eo v aRet s ret v8 v9 v18 v19 R0 := by
  intro aS aE w0 w1 w2 R Mt P m pn pi hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iintro ⟨#Himg, #Hcode, #Hro, #Hfb, #Hv, Hms, Hst, Hslot, Hw, HK⟩
  ihave Hed := hed
  iapply varTailP hlive HN hcl hcore (N := N) (inp := inp) (st := st) (env := env) (v := v)
    hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iframe Hed Hcode Himg Hro Hfb Hv Hms Hst Hslot Hw HK

/-- A tail whose continuation carries a pure side condition. -/
theorem VarTail.of_pure {N : NativeAddrs} {inp : Nat} {Wp : MachWP (GF := GF) (vsaModel live)}
    {Φ : Nat × String → IProp GF} {Hyp : IProp GF} {ρ : Regime} {K : IProp GF} {st : St}
    {d env : Nat} {x : String} {eo : Option Expr} {v : Value}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 : Nat → BitVec 64} {φ : Prop}
    (h : φ → VarTail N inp Wp Φ Hyp ρ K st d env x eo v aRet s ret v8 v9 v18 v19 R0) :
    VarTail N inp Wp Φ Hyp ρ iprop(⌜φ⌝ ∗ K) st d env x eo v aRet s ret v8 v9 v18 v19 R0 := by
  intro aS aE w0 w1 w2 R Mt P m pn pi hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iintro ⟨#Hyp, Hcode, Hro, #Hfb, #Hv, Hms, Hst, Hslot, Hw, %hφ, HK⟩
  iapply h hφ aS aE w0 w1 w2 R Mt P m pn pi hsg hal hn hgeo h2 h8 h19 hk hsv hw0 hw1 hw2
  iframe Hyp Hcode Hro Hfb Hv Hms Hst Hslot Hw HK

/-- The partial continuation at the declaration's final state, keeping the abort branch. -/
theorem execKP_and {N : NativeAddrs} {inp : Nat} {Φ : Nat × String → IProp GF} {st st' : St}
    {d env : Nat} {sm : Stmt} {status : Status} {aRet s : BitVec 64} {R : Nat → BitVec 64}
    {ret v8 v9 v18 v19 : BitVec 64} {A : IProp GF} (hE : ExecS st d env sm st' status) :
    ((∀ (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
          st' d sm status aRet s R ret v8 v9 v18 v19) ∧ A) ⊢
      iprop(execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
        st' d sm status aRet s R ret v8 v9 v18 v19 ∧ A) := by
  iintro HK
  isplit
  · iapply execKP_of hE $$ HK
  · iapply and_elim_r $$ HK

/-- `var x = e` in every mode. -/
theorem varInitCore (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {x : String} {e : Expr}
    (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (Hc Ht : IProp GF)
    (ρin ρout : Regime) (Kin : IProp GF) (Kfin : St → Value → IProp GF)
    (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64)
    (hcall : ChildCall N vsaLayoutP vsaRoomB inp Wp Φ Hc ρin ρout st d env e s
      (execNeed (.varDecl x (some e)) d) (slot24 aRet.toNat) Kin Kfin)
    (htail : ∀ st' v, VarTail N inp Wp Φ Ht ρout (Kfin st' v) st' d env x (some e) v aRet s ret
      v8 v9 v18 v19 R) :
    □ Hc ∗ □ Ht ∗ execDispPre N vsaLayoutP vsaRoomB inp ρin st d env (.varDecl x (some e)) aS aE
      aRet s R Mt ret v8 v9 v18 v19 ∗ Kin ⊢ Wp.W Φ := by
  unfold execDispPre
  iintro ⟨#Hc, #Ht, ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pn, pi, hn⟩ := varNode_of hrepr hgeo
  obtain ⟨hpe, hpi0⟩ := hn.initRepr e rfl
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 104) hf.stack hfg.sf (execNeed_varDecl x e d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 104#64).toNat = s.toNat - 176 + 104 := g.slot
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(□ Hc ∗ □ Ht ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.varDecl x (some e)) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp ρin st d ∗ Kin))
  rotate_left
  · iframe Hdv Hms Hc Ht Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine VarArm_run1I (aI := BitVec.ofNat 64 pi) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.init hpi0 ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hc, #Ht, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩

  iapply hcall 0x800040ec _ (jalx_800040ec live (fun p hp => hlive _ (interp_code_800040ec p hp)))
    interp_code_800040ec (by decide) (slot := execSP s + 104#64) (aC := BitVec.ofNat 64 pi)
    (aE := aE) (sF := execSP s) (f := 176) (m := execNeed (.varDecl x (some e)) d - 176)
    (execSP_eq s).symm g.child g.fits g.below (by omega) hf.stack.le g.slotGeom hbb
  iframe Hc Hcode Hfb Hms Hst Hw Hslot HK
  isplitl []
  · ipureintro
    subst hR0
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hn.initNat]; iapply astEG_of_view hpe hn.node.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st' %v %hkeep1 #Hv1 Hms Hst Hw Hslot HK
  have hk1 : KeepRegs calleeSaved R (upd R1 1 (BitVec.ofNat 64 (0x800040ec + 4))) := by
    subst hR0
    intro y hy
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ix_keep [hkeep1]
  have hsub : ∀ y ∈ [20, 21, 22, 23, 24, 25, 26, 27], y ∈ calleeSaved := by decide

  iapply htail st' v aS aE w0 w1 w2 (upd R1 1 (BitVec.ofNat 64 (0x800040ec + 4)))
    (slotWrite Mt1 (execSP s + 104#64).toNat w0 w1 w2) P m pn pi
    hf.stack hf.ral hn hgeo ((hk1 2 (by decide)).trans hf.regs.sp)
    ((hk1 8 (by decide)).trans hf.regs.s0) ((hk1 19 (by decide)).trans hf.regs.s3)
    (fun y hy => hk1 y (hsub y hy))
    (by have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff)
    (by rw [← g1]; try ix_fwd)
    (by rw [show s.toNat - 176 + 112 = (execSP s + 104#64).toNat + 8 by omega]; try ix_fwd)
    (by rw [show s.toNat - 176 + 120 = (execSP s + 104#64).toNat + 16 by omega]; try ix_fwd)
  iframe Ht Hcode Hro Hfb Hv1 Hms Hst Hslot Hw HK

/-- `var x;` in every mode. -/
theorem varNullCore (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {x : String}
    (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (Ht : IProp GF)
    (ρ : Regime) (K : IProp GF)
    (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64)
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N Wp p)
    (htail : VarTail N inp Wp Φ Ht ρ K st d env x none .null aRet s ret v8 v9 v18 v19 R) :
    □ Ht ∗ execDispPre N vsaLayoutP vsaRoomB inp ρ st d env (.varDecl x none) aS aE
      aRet s R Mt ret v8 v9 v18 v19 ∗ K ⊢ Wp.W Φ := by
  unfold execDispPre
  iintro ⟨#Ht, ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pn, pi, hn⟩ := varNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g1 : (execSP s + 104#64).toNat = s.toNat - 176 + 104 := hoff 104 (by decide)
  have hslg : SlotGeom (execSP s + 104#64) := by
    have := hfg.lo; have := hfg.hi; have := hfg.al
    refine ⟨?_, ?_, ?_⟩ <;> rw [g1] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(□ Ht ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.varDecl x none) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp ρ st d ∗ K))
  rotate_left
  · iframe Hdv Hms Ht Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine VarArm_run1N hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo hn.node.hi hn.node.off
    hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    (by rw [hn.init, hn.initNone rfl]) ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Ht, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩

  ihave Hvn := hvn $$ %(execSP s + 104#64)
  unfold valueNullSpec
  iapply ms_callHelperSlot Wp (i := 0x80004300)
    (jalx_80004300 live (fun p hp => hlive _ (interp_code_80004300 p hp)))
    interp_code_80004300 (by decide) (a := execSP s + 104#64) (R := R0) (Mt := Mt1)
    (S := InExt (s.toNat - 176, 176)) (v := .null)
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; rw [g1] at hb; omega) hslg
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; subst hR0; ix_reg
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms

  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(□ Ht ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗ valOf N .null w0 w1 w2 ∗
      stackScratch (execSP s) (execNeed (.varDecl x none) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp ρ st d ∗ K))
  rotate_left
  · iframe Hms Ht Hcode Hro Hfb Hv1 Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine VarArm_runJ (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hk1 : KeepRegs calleeSaved R R2 := by
    subst hR2 hR0
    intro y hy
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg)
  have hsub : ∀ y ∈ [20, 21, 22, 23, 24, 25, 26, 27], y ∈ calleeSaved := by decide
  unfold F'
  iintro ⟨⟨#Ht, #Hcode, #Hro, #Hfb, #Hv1, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply htail aS aE w0 w1 w2 R2 Mt2 P m pn pi
    hf.stack hf.ral hn hgeo ((hk1 2 (by decide)).trans hf.regs.sp)
    ((hk1 8 (by decide)).trans hf.regs.s0) ((hk1 19 (by decide)).trans hf.regs.s3)
    (fun y hy => hk1 y (hsub y hy))
    (by have := hfg.lo; rw [hMt2, hMt1]; ix_esaved hf.saved using hoff)
    (by rw [hMt2, ← g1]; try ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 112 = (execSP s + 104#64).toNat + 8 by omega]; try ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 120 = (execSP s + 104#64).toNat + 16 by omega]; try ix_fwd)
  iframe Ht Hcode Hro Hfb Hv1 Hms Hst Hslot Hw HK

theorem varInitT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {x : String} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env e st' v n D)
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env
        (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩ .normal
        (n + defineCost st'.store env x) (.varInit st d env x e st' v n D) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  rw [show k + (n + defineCost st'.store env x) = k + defineCost st'.store env x + n by omega]
  iapply varInitCore hlive (twpW _) Φ emp emp _ _ _
    (fun st'' v'' => iprop(⌜st'' = st' ∧ v'' = v⌝ ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k)
        ⟨st'.store.define env x v, st'.out⟩ d (.varDecl x (some e)) .normal aRet s R ret v8 v9 v18
        v19))
    aS aE aRet s R Mt ret v8 v9 v18 v19 (childCallT (k := k + defineCost st'.store env x) D he)
    (fun st'' v'' => VarTail.of_pure fun h => by
      obtain ⟨rfl, rfl⟩ := h; exact varTail_rule hlive hed)
  iframe Hpre
  isplitl []
  · iapply (intuitionistically_emp (PROP := IProp GF)).2
    ipureintro; trivial
  isplitl []
  · iapply (intuitionistically_emp (PROP := IProp GF)).2
    ipureintro; trivial
  iframe HK
  ipureintro; exact ⟨rfl, rfl⟩

theorem varInitP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {Core : IProp GF} (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live)
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core)
    (hed : ⊢ envDefineSpec (GF := GF) (wpW (vsaModel live)) N)
    {st : St} {d env : Nat} {x : String} {e : Expr} :
    errCtx inp ∗ evalSpecsP (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core st d env
        (.varDecl x (some e)) := by
  iintro ⟨#Herr, #IH⟩
  ihave #Himg := errCtx_img inp $$ Herr
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  iapply varInitCore hlive (wpW _) Φ _ _ _ _ _ _ aS aE aRet s R Mt ret v8 v9 v18 v19
    (childCallP (Core := Core) fun st' v h => execKP_and (ExecS.varInit st d env x e st' v h))
    (fun st' v => varTailP_rule hlive HN hcl hcore hed)
  iframe IH Himg Hpre HK

theorem varNullT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {x : String}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p)
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env
        (.varDecl x none) ⟨st.store.define env x .null, st.out⟩ .normal
        (defineCost st.store env x) (.varNull st d env x) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  iapply varNullCore hlive (twpW _) Φ emp _ _ aS aE aRet s R Mt ret v8 v9 v18 v19 hvn
    (varTail_rule hlive hed)
  iframe Hpre HK
  iapply (intuitionistically_emp (PROP := IProp GF)).2
  ipureintro; trivial

theorem varNullP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {Core : IProp GF} (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live)
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core) {st : St} {d env : Nat} {x : String}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p)
    (hed : ⊢ envDefineSpec (GF := GF) (wpW (vsaModel live)) N) :
    errCtx inp ⊢
      execDispP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core st d env
        (.varDecl x none) := by
  iintro #Herr
  ihave #Himg := errCtx_img inp $$ Herr
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  ihave HK := execKP_and (ExecS.varNull st d env x) $$ HK
  iapply varNullCore hlive (wpW _) Φ _ _ _ aS aE aRet s R Mt ret v8 v9 v18 v19 hvn
    (varTailP_rule hlive HN hcl hcore hed)
  iframe Himg Hpre HK

end

end VsaIris.Interp
