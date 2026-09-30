import VsaIris.Interp.BinPrelude

/-!
Mode-specific entry and child-call steps of an `eval_expr` arm.

* `evalEntryT` / `evalEntryP`: unfold the total / partial spec, carve the 1088-byte frame and
  hand the arm to a tail at `evalEntryPC` (`EvalEntry` facts, `ExitK`, `AbortK`).
* `ArmAt.callEvalT` / `ArmAt.callEvalP`: a recursive `eval_expr` call on a child expression from
  an arm frame; the child's value representation joins the frame's continuation.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- Facts at the entry of an `eval_expr` activation for expression `e` at `aX`. -/
structure EvalEntry (s ret sret aE aX inp : BitVec 64) (rv : Nat → BitVec 64) (n : Nat) (e : Expr)
    (m : Mem) (P : Nat → Prop) : Prop where
  geo : ArmGeo s ret sret n
  regs : EvalRegs rv sret inp aX aE s
  repr : ExprReprWithin m P aX.toNat e
  ok : ∀ k, P k → ReadOK k
  bb : e.bodiesBound perCallBudget = true

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The frame of an arm at entry. -/
abbrev entryF (P : Nat → Prop) (m : Mem) (env : Nat) (aE s : BitVec 64) (n : Nat)
    (sret : BitVec 64) (Wd K : IProp GF) : IProp GF :=
  evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat) Wd K

/-- The caller continuation of a partial `eval_expr` spec. -/
abbrev evalKP (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF)
    (st : St) (d env : Nat) (e : Expr) (sret s ret : BitVec 64) (rv : Nat → BitVec 64)
    (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env e st' v⌝ ∗
      evalPost N L Room inp .uncounted st' d e v sret s rv) -∗ (wpW (vsaModel live)).W Φ) ∧
    (abortAt Core s (evalNeed e d) ∗ slot24 sret.toNat -∗ (wpW (vsaModel live)).W Φ))

/-- The caller continuation of a total `eval_expr` spec. -/
abbrev evalKT (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp k : Nat) (st' : St) (d : Nat)
    (e : Expr) (v : Value) (sret s ret : BitVec 64) (rv : Nat → BitVec 64)
    (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st' d e v sret s rv -∗
    (twpW (vsaModel live)).W Φ)

theorem evalKT_exit {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp k : Nat} {st' : St}
    {d : Nat} {e : Expr} {v : Value} {sret s ret : BitVec 64} {rv : Nat → BitVec 64}
    {Φ : Nat × String → IProp GF} :
    ExitK (twpW (vsaModel live)) Φ N s ret sret rv (evalNeed e d) v
      (world N L Room inp (.counted k) st' d) (evalKT (live := live) N L Room inp k st' d e v sret s ret rv Φ) := by
  intro R' hkeep
  iintro ⟨Hpc, Hra, Hregs, Hst, Hval, Hw, Hk⟩
  iapply Hk $$ Hpc Hra
  unfold evalPost
  iexists R'
  iframe Hregs Hst Hval Hw
  ipureintro; exact hkeep

theorem evalKP_exit {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st st' : St} {d env : Nat} {e : Expr} {v : Value} {sret s ret : BitVec 64}
    {rv : Nat → BitVec 64} {Φ : Nat × String → IProp GF} (X : IProp GF)
    (hE : EvalE st d env e st' v) :
    ExitK (wpW (vsaModel live)) Φ N s ret sret rv (evalNeed e d) v
      (world N L Room inp .uncounted st' d)
      iprop(evalKP (live := live) N L Room inp Core st d env e sret s ret rv Φ ∗ X) := by
  intro R' hkeep
  iintro ⟨Hpc, Hra, Hregs, Hst, Hval, Hw, Hk, -⟩
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists st', v
  isplitl []
  · ipureintro; exact hE
  unfold evalPost
  iexists R'
  iframe Hregs Hst Hval Hw
  ipureintro; exact hkeep

theorem evalKP_abort {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {e : Expr} {sret s ret : BitVec 64} {rv : Nat → BitVec 64}
    {Φ : Nat × String → IProp GF} (X : IProp GF) (hX : X ⊢ □ errCtx inp) :
    AbortK (wpW (vsaModel live)) Φ inp Core s sret (evalNeed e d)
      iprop(evalKP (live := live) N L Room inp Core st d env e sret s ret rv Φ ∗ X) := by
  unfold AbortK
  iintro ⟨Hk, HX⟩
  ihave #HE := hX $$ HX
  iframe HE
  iapply and_elim_r $$ Hk

theorem evalEntryT (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st' : St} {d env : Nat} {e : Expr} {v : Value} {n : Nat}
    (D : EvalECost st d env e st' v n)
    (tail : ∀ (k : Nat) (Φ : Nat × String → IProp GF) (sret aE aX s ret : BitVec 64)
      (rv : Nat → BitVec 64) (P : Nat → Prop) (m Mt : Mem),
      EvalEntry s ret sret aE aX (BitVec.ofNat 64 inp) rv (evalNeed e d) e m P →
      ArmAt (twpW (vsaModel live)) Φ
        (entryF P m env aE s (evalNeed e d) sret (world N L Room inp (.counted (k + n)) st d)
          (evalKT (live := live) N L Room inp k st' d e v sret s ret rv Φ))
        evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D := by
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hneed : 1088 ≤ evalNeed e d := by
    have := Expr.stackNeed_ge e; unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hsF : s - 1088#64 = evalSP s := evalSP_eq s
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  iapply tail k Φ sret aE aX s ret rv P m Mt0
    ⟨⟨hsf, by omega, hs2, hs3, hsg, hneed, hal, hslg⟩, hregs, hrepr, hgeo, hbb⟩
  iframe Hms; unfold entryF evalArmF; iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk

theorem evalEntryP (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {e : Expr}
    (tail : ∀ (Φ : Nat × String → IProp GF) (sret aE aX s ret : BitVec 64)
      (rv : Nat → BitVec 64) (P : Nat → Prop) (m Mt : Mem),
      EvalEntry s ret sret aE aX (BitVec.ofNat 64 inp) rv (evalNeed e d) e m P →
      ArmAt (wpW (vsaModel live)) Φ
        (entryF P m env aE s (evalNeed e d) sret (world N L Room inp .uncounted st d)
          iprop(evalKP (live := live) N L Room inp Core st d env e sret s ret rv Φ ∗
            evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp))
        evalEntryPC (upd rv 1 ret) (InExt (s.toNat - 1088, 1088)) Mt) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env e := by
  iintro ⟨#IH, #HE⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hneed : 1088 ≤ evalNeed e d := by
    have := Expr.stackNeed_ge e; unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hsF : s - 1088#64 = evalSP s := evalSP_eq s
  have hsf : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  iapply tail Φ sret aE aX s ret rv P m Mt0
    ⟨⟨hsf, by omega, hs2, hs3, hsg, hneed, hal, hslg⟩, hregs, hrepr, hgeo, hbb⟩
  iframe Hms; unfold entryF evalArmF; iframe Hcode Hro Hfb Hst Hslot Hw Hk IH; iexact HE

/-- A pure fact read off the frame's continuation. -/
theorem ArmAt.pureK {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {φ : Prop} {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hK : K ⊢ K ∗ ⌜φ⌝) (h : φ → ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) pc R S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd K) pc R S Mt := by
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, HK⟩, Hms⟩
  ihave ⟨HK, %hφ⟩ := hK $$ HK
  iapply h hφ
  iframe Hms; unfold evalArmF; iframe Hc Hr Hf Hs Ho Hw HK

theorem valOf_tagK (N : NativeAddrs) {K : IProp GF} (v : Value) (w0 w1 w2 : BitVec 64) :
    iprop(K ∗ □ valOf N v w0 w1 w2) ⊢
      iprop(K ∗ □ valOf N v w0 w1 w2) ∗ ⌜w0.toNat % 2 ^ 32 = valTag v⌝ := by
  iintro ⟨HK, #Hv⟩
  ihave %ht := valOf_tag N v w0 w1 w2 $$ Hv
  iframe HK Hv; ipureintro; exact ht

/-- A child's kind tag, read off its value representation in the frame's continuation. -/
theorem ArmAt.valTag {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat} {Out Wd K : IProp GF}
    {N : NativeAddrs} {v : Value} {w0 w1 w2 : BitVec 64} {pc : BitVec 64} {R : Nat → BitVec 64}
    {S : Nat → Prop} {Mt : Mem}
    (h : w0.toNat % 2 ^ 32 = valTag v → ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd
      iprop(K ∗ □ valOf N v w0 w1 w2)) pc R S Mt) :
    ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd iprop(K ∗ □ valOf N v w0 w1 w2)) pc R S Mt :=
  ArmAt.pureK (valOf_tagK N v w0 w1 w2) h

/-- A total recursive `eval_expr` call on child `e` (represented at `aC`) with result slot at
frame offset `o`; the child's value representation joins the continuation. -/
theorem ArmAt.callEvalT (J : JalAt evalEntryPC) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st' : St} {d env : Nat} {e : Expr} {v : Value} {nc : Nat}
    (Dc : EvalECost st d env e st' v nc)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v nc Dc)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {aE s ret sret : BitVec 64} {n k : Nat}
    {Out K : IProp GF} {R : Nat → BitVec 64} {Mt : Mem} {aC o : Nat}
    (g : ArmGeo s ret sret n) (hle : evalNeed e d + 1088 ≤ n) (ho : o + 24 ≤ 1088)
    (ho8 : o % 8 = 0) (hbb : e.bodiesBound perCallBudget = true)
    (hrepr : ExprReprWithin m P aC e) (hok : ∀ k, P k → ReadOK k) (haC : aC < 2 ^ 64)
    (hregs : EvalRegs R (evalSP s + BitVec.ofNat 64 o) (BitVec.ofNat 64 inp) (BitVec.ofNat 64 aC)
      aE (evalSP s))
    (hk : ∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64), KeepRegs calleeSaved R R' →
      ArmAt (twpW (vsaModel live)) Φ
        (evalArmF P m env aE (evalSP s) (n - 1088) Out (world N L Room inp (.counted k) st' d)
          iprop(K ∗ □ valOf N v w0 w1 w2))
        (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4)))
        (InExt (s.toNat - 1088, 1088)) (slotWrite Mt (evalSP s + BitVec.ofNat 64 o).toNat w0 w1 w2)) :
    ArmAt (twpW (vsaModel live)) Φ
      (evalArmF P m env aE (evalSP s) (n - 1088) Out (world N L Room inp (.counted (k + nc)) st d) K)
      (BitVec.ofNat 64 J.i) R (InExt (s.toNat - 1088, 1088)) Mt := by
  have gc := evalCallGeom (o := o) g.sg hle ho ho8
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Ho, Hw, HK⟩, Hms⟩
  ihave Hc := hc
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (J.exec live hlive) J.mem J.al
    Dc (k := k) (slot := evalSP s + BitVec.ofNat 64 o) (aC := BitVec.ofNat 64 aC) (aE := aE)
    (s := evalSP s) (m := n - 1088) gc.child gc.fits gc.below gc.slotGeom hbb
  iframe Hc Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨hregs, fun b hb => ?_⟩
    have g1 := gc.slot; have g2 := gc.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro
    rw [show (BitVec.ofNat 64 aC).toNat = aC by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haC]]
    iapply astEG_of_view hrepr hok $$ Hro
  iintro %R' %w0 %w1 %w2 %hkeep #Hv Hms Hst Hw
  iapply hk R' w0 w1 w2 hkeep
  iframe Hms; unfold evalArmF; iframe Hcode Hro Hfb Hst Ho Hw HK Hv

/-- A partial recursive `eval_expr` call on child `e`, through the recursive hypothesis in the
arm's continuation. -/
theorem ArmAt.callEvalP (J : JalAt evalEntryPC) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st0 st : St} {d env : Nat} {e0 e : Expr} {sret s ret : BitVec 64} {rv : Nat → BitVec 64}
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {aE : BitVec 64}
    {Out X : IProp GF} {R : Nat → BitVec 64} {Mt : Mem} {aC o : Nat}
    (hOut : Out ⊢ slot24 sret.toNat) (hX : X ⊢ □ evalSpecsP (vsaModel live) N L Room inp Core)
    (g : ArmGeo s ret sret (evalNeed e0 d)) (hle : evalNeed e d + 1088 ≤ evalNeed e0 d)
    (ho : o + 24 ≤ 1088) (ho8 : o % 8 = 0) (hbb : e.bodiesBound perCallBudget = true)
    (hrepr : ExprReprWithin m P aC e) (hok : ∀ k, P k → ReadOK k) (haC : aC < 2 ^ 64)
    (hregs : EvalRegs R (evalSP s + BitVec.ofNat 64 o) (BitVec.ofNat 64 inp) (BitVec.ofNat 64 aC)
      aE (evalSP s))
    (hk : ∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (st' : St) (v : Value),
      EvalE st d env e st' v → KeepRegs calleeSaved R R' →
      ArmAt (wpW (vsaModel live)) Φ
        (evalArmF P m env aE (evalSP s) (evalNeed e0 d - 1088) Out
          (world N L Room inp .uncounted st' d)
          iprop(evalKP (live := live) N L Room inp Core st0 d env e0 sret s ret rv Φ ∗
            (X ∗ □ valOf N v w0 w1 w2)))
        (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4)))
        (InExt (s.toNat - 1088, 1088)) (slotWrite Mt (evalSP s + BitVec.ofNat 64 o).toNat w0 w1 w2)) :
    ArmAt (wpW (vsaModel live)) Φ
      (evalArmF P m env aE (evalSP s) (evalNeed e0 d - 1088) Out
        (world N L Room inp .uncounted st d)
        iprop(evalKP (live := live) N L Room inp Core st0 d env e0 sret s ret rv Φ ∗ X))
      (BitVec.ofNat 64 J.i) R (InExt (s.toNat - 1088, 1088)) Mt := by
  have gc := evalCallGeom (o := o) g.sg hle ho ho8
  have hneed := g.need
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Ho, Hw, Hk, HX⟩, Hms⟩
  ihave #IH := hX $$ HX
  ihave Hc := evalSpecsP_at Core st d env e $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (J.exec live hlive) J.mem J.al
    (Core := Core) (st := st) (d := d) (env := env) (e := e)
    (slot := evalSP s + BitVec.ofNat 64 o) (aC := BitVec.ofNat 64 aC) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed e0 d - 1088) (n0 := evalNeed e0 d) (Out := Out)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st0 d env e0 st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d e0 v sret s rv) -∗
          (wpW (vsaModel live)).W Φ)) hOut
    gc.child gc.fits gc.below (by omega) g.sg.le gc.slotGeom hbb
  iframe Hc Hcode Hfb Hms Hst Hw Ho Hk
  isplitl []
  · ipureintro
    refine ⟨hregs, fun b hb => ?_⟩
    have g1 := gc.slot; have g2 := gc.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro
    rw [show (BitVec.ofNat 64 aC).toNat = aC by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haC]]
    iapply astEG_of_view hrepr hok $$ Hro
  iintro %R' %w0 %w1 %w2 %st' %v %hE %hkeep #Hv Hms Hst Hw Ho Hk
  iapply hk R' w0 w1 w2 st' v hE hkeep
  iframe Hms; unfold evalArmF; iframe Hcode Hro Hfb Hst Ho Hw Hk HX Hv

end

end VsaIris.Interp
