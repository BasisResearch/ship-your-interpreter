import VsaIris.Interp.BinPreludeT

/-!
The partial (abort-aware) binary prelude: `binPreludeP` runs both children through the
recursive `evalSpecsP` hypothesis and hands the operator tail its `ExitK` for every
semantically produced value and its `AbortK`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The tail's view of the partial prelude: the operands' derivations, the state at the
dispatch, the exit for every value the operator semantics produces, and the abort. -/
abbrev BinTailP (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF)
    (st : St) (d env : Nat) (op : BinOp) (l r : Expr) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (sret aE aX s ret : BitVec 64) (rv R : Nat → BitVec 64)
    (P : Nat → Prop) (m Mt : Mem) (w0 w1 w2 u0 u1 u2 : BitVec 64) (st1 st2 : St) (lv rv' : Value)
    (K : IProp GF),
    EvalE st d env l st1 lv → EvalE st1 d env r st2 rv' →
    ArmGeo s ret sret (evalNeed (.binary op l r) d) → BinOpNode m P aX (binOpTok op) →
    BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 →
    (∀ v, binOpSem st2.store op lv rv' = some v →
      ExitK (wpW (vsaModel live)) Φ N s ret sret rv (evalNeed (.binary op l r) d) v
        (world N L Room inp .uncounted st2 d) K) →
    AbortK (wpW (vsaModel live)) Φ inp Core s sret (evalNeed (.binary op l r) d) K →
    BinTail (wpW (vsaModel live)) Φ N
      (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
        (world N L Room inp .uncounted st2 d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2

theorem BinTail.armP {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s sret : BitVec 64} {n : Nat}
    {Wd KP IH E : IProp GF} {R : Nat → BitVec 64} {Mt : Mem} {lv rv' : Value}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : BinTail Wp Φ N (binArmF N P m env aE s n sret Wd iprop(KP ∗ E)) R s Mt lv rv'
      w0 w1 w2 u0 u1 u2) :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat) Wd
      iprop(KP ∗ ((IH ∗ E) ∗ □ valOf N lv w0 w1 w2) ∗ □ valOf N rv' u0 u1 u2)) 0x8000351c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  unfold BinTail at h
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, HK, ⟨⟨-, HE⟩, #Hv1⟩, #Hv2⟩, Hms⟩
  iapply h
  iframe Hms Hv1 Hv2; unfold binArmF evalArmF; iframe Hc Hr Hf Hs Ho Hw HK HE

theorem binPreludeP_R (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st st1 : St} {d env : Nat} {op : BinOp} {l r : Expr} {lv : Value}
    (tail : BinTailP (GF := GF) (live := live) N L Room inp Core st d env op l r)
    (hEl : EvalE st d env l st1 lv)
    {Φ : Nat × String → IProp GF} {sret aE aX s ret : BitVec 64}
    {rv R : Nat → BitVec 64} {P : Nat → Prop} {m Mt : Mem} {w0 w1 w2 : BitVec 64} {aR : Nat}
    (g : ArmGeo s ret sret (evalNeed (.binary op l r) d)) (hn : BinOpNode m P aX (binOpTok op))
    (hR : BinRight m P aX r aR) (hbr : r.bodiesBound perCallBudget = true)
    (b : BinLeft s sret (BitVec.ofNat 64 inp) aE rv R Mt ret aX lv w0 w1 w2) :
    ArmAt (wpW (vsaModel live)) Φ
      (evalArmF P m env aE (evalSP s) (evalNeed (.binary op l r) d - 1088) (slot24 sret.toNat)
        (world N L Room inp .uncounted st1 d)
        iprop(evalKP (live := live) N L Room inp Core st d env (.binary op l r) sret s ret rv Φ ∗
          ((evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp) ∗ □ valOf N lv w0 w1 w2)))
      0x800034fc#64 R (InExt (s.toNat - 1088, 1088)) Mt := by
  have hsf := g.sf; have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al
  have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [b.tl]; exact valTag_lt _
  refine ArmAt.seg (wpW _) hn.view ?_
  refine BinaryAddIntT_run2 (aE := aE) (inp := BitVec.ofNat 64 inp) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) hlive hsf hs' hs2 hs3 hn.lo hn.hi hn.off
    b.r8 b.r2 b.r18 hR.ptr b.ae b.kl b.l1 ?_
  intros
  apply swp_closeM
  intro Mt2 hMt2
  subst hMt2
  refine ArmAt.callEvalP (jal_site% 0x80003518) hlive .rfl (by iintro ⟨⟨#H, -⟩, -⟩; iexact H) g
    (by have := evalNeed_binary_right op l r d; unfold evalFrame at this; omega) (o := 144)
    (by decide) (by decide) hbr hR.repr hR.ok hR.lt
    ⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact b.r2⟩
    fun R2 u0 u1 u2 st2 rv' hEr hkeep2 => ?_
  refine ArmAt.pureK (φ := u0.toNat % 2 ^ 32 = valTag rv') (by
    iintro ⟨Hk, HX, #Hv⟩
    ihave %ht := valOf_tag N rv' u0 u1 u2 $$ Hv
    iframe Hk HX Hv; ipureintro; exact ht) fun htr => ?_
  exact (tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEl hEr g hn
    (binMid_of_left g b (by ix_keep [hkeep2]; exact b.r9) (by ix_keep [hkeep2]) hkeep2 htr)
    (fun _ hv => evalKP_exit _ (EvalE.binary st d env op l r st1 st2 lv rv' _ hEl hEr hv))
    (evalKP_abort _ (by iintro #H; iexact H))).armP

theorem binPreludeP (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {op : BinOp} {l r : Expr}
    (tail : BinTailP (GF := GF) (live := live) N L Room inp Core st d env op l r) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.binary op l r) :=
  evalEntryP hlive fun Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aL, aR, hn, hrl, hR, haL⟩ := binNode_entry ent.repr ent.ok
    have g := ent.geo
    have hregs := ent.regs
    have hbb := ent.bb
    have hoff := g.off
    have hsf := g.sf; have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al
    have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
    have node : BinOpNode m P aX (binOpTok op) := ⟨hn.op, hn.view, hn.lo, hn.hi, hn.off⟩
    have hbl : l.bodiesBound perCallBudget = true := by
      simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.1
    have hbr : r.bodiesBound perCallBudget = true := by
      simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.2
    refine ArmAt.seg (wpW _) hn.view ?_
    unfold evalEntryPC
    refine BinaryAddIntT_run1 hlive g.sf g.lo g.hi g.al hn.lo hn.hi hn.off
      (by ix_reg; exact hregs.a0) (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2)
      (by ix_reg; exact hregs.a3) (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
    intros
    apply swp_closeM
    intro Mt1 hMt1
    have hsv1 : EvalSaved Mt1 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
      subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
    have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by subst hMt1; ix_fwd
    refine ArmAt.callEvalP (jal_site% 0x800034f8) hlive .rfl (by iintro ⟨#H, -⟩; iexact H) g
      (by have := evalNeed_binary_left op l r d; unfold evalFrame at this; omega) (o := 120)
      (by decide) (by decide) hbl hrl ent.ok haL
      ⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.left, by ix_reg; exact hregs.a3,
        by ix_reg⟩ fun R1 w0 w1 w2 st1 lv hEl hkeep1 => ?_
    refine ArmAt.pureK (φ := w0.toNat % 2 ^ 32 = valTag lv) (by
      iintro ⟨Hk, HX, #Hv⟩
      ihave %ht := valOf_tag N lv w0 w1 w2 $$ Hv
      iframe Hk HX Hv; ipureintro; exact ht) fun htl => ?_
    have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [htl]; exact valTag_lt _
    have bl : BinLeft s sret (BitVec.ofNat 64 inp) aE rv (upd R1 1 (BitVec.ofNat 64 (0x800034f8 + 4)))
        (slotWrite Mt1 (s + 18446744073709550528#64 + 120#64).toNat w0 w1 w2) ret aX lv w0 w1 w2 := {
      r2 := by ix_keep [hkeep1]
      r8 := by ix_keep [hkeep1]
      r9 := by ix_keep [hkeep1]
      r18 := by ix_keep [hkeep1]
      hi := fun x hx => by
        simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
      sp := hregs.sp
      saved := by ix_saved hsv1 using hoff
      ae := by ix_fwd; exact hA1
      kl := by ix_fwd
      l0 := by ix_fwd
      l1 := by ix_fwd
      l2 := by ix_fwd
      tl := htl }
    exact binPreludeP_R hlive tail hEl g node hR hbr bl

end

end VsaIris.Interp
