import VsaIris.Interp.ArmEval
import VsaIris.Interp.Case.BinaryAddIntT

/-!
The total binary prelude: entry, left child, right child, up to the operator dispatch.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- Facts at the dispatch of a binary node: operand representations and the left geometry. -/
theorem binNode_entry {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {op : BinOp} {l r : Expr}
    (h : ExprReprWithin m P aX.toNat (.binary op l r)) (hg : ∀ k, P k → ReadOK k) :
    ∃ aL aR : Nat, BinNode m P aX 6 (binOpTok op) (BitVec.ofNat 64 aL) (BitVec.ofNat 64 aR) ∧
      ExprReprWithin m P aL l ∧ BinRight m P aX r aR ∧ aL < 2 ^ 64 := by
  obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := binNode_of_repr h hg
  exact ⟨aL, aR, hn, hrl, ⟨hn.right, hrr, haR, hg⟩, haL⟩

theorem BinTail.arm {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s sret : BitVec 64} {n : Nat}
    {Wd K : IProp GF} {R : Nat → BitVec 64} {Mt : Mem} {lv rv' : Value}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : BinTail Wp Φ N (binArmF N P m env aE s n sret Wd K) R s Mt lv rv' w0 w1 w2 u0 u1 u2) :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat) Wd
      iprop((K ∗ □ valOf N lv w0 w1 w2) ∗ □ valOf N rv' u0 u1 u2)) 0x8000351c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  unfold BinTail at h
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, ⟨HK, #Hv1⟩, #Hv2⟩, Hms⟩
  iapply h
  iframe Hms Hv1 Hv2; unfold binArmF evalArmF; iframe Hc Hr Hf Hs Ho Hw HK

theorem binPreludeT_R (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st1 st2 : St} {d env : Nat} {op : BinOp} {l r : Expr} {lv rv' : Value} {nr : Nat}
    (Dr : EvalECost st1 d env r st2 rv' nr)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    {k : Nat} {Φ : Nat × String → IProp GF} {sret aE aX s ret : BitVec 64}
    {rv R : Nat → BitVec 64} {P : Nat → Prop} {m Mt : Mem} {w0 w1 w2 : BitVec 64} {aR : Nat}
    {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary op l r) d)) (hn : BinOpNode m P aX (binOpTok op))
    (hR : BinRight m P aX r aR) (hbr : r.bodiesBound perCallBudget = true)
    (b : BinLeft s sret (BitVec.ofNat 64 inp) aE rv R Mt ret aX lv w0 w1 w2)
    (tail : ∀ (R' : Nat → BitVec 64) (Mt' : Mem) (u0 u1 u2 : BitVec 64),
      BinMid s sret (BitVec.ofNat 64 inp) rv R' Mt' ret aX lv rv' w0 w1 w2 u0 u1 u2 →
      BinTail (twpW (vsaModel live)) Φ N
        (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
          (world N L Room inp (.counted k) st2 d) K) R' s Mt' lv rv' w0 w1 w2 u0 u1 u2) :
    ArmAt (twpW (vsaModel live)) Φ
      (evalArmF P m env aE (evalSP s) (evalNeed (.binary op l r) d - 1088) (slot24 sret.toNat)
        (world N L Room inp (.counted (k + nr)) st1 d) iprop(K ∗ □ valOf N lv w0 w1 w2))
      0x800034fc#64 R (InExt (s.toNat - 1088, 1088)) Mt := by
  have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [b.tl]; exact valTag_lt _
  have hsf := g.sf; have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al
  refine ArmAt.seg (twpW _) hn.view ?_
  refine BinaryAddIntT_run2 (aE := aE) (inp := BitVec.ofNat 64 inp) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) hlive g.sf g.lo g.hi g.al hn.lo hn.hi hn.off
    b.r8 b.r2 b.r18 hR.ptr b.ae b.kl b.l1 ?_
  intros
  apply swp_closeM
  intro Mt2 hMt2
  subst hMt2
  refine ArmAt.callEvalT (jal_site% 0x80003518) hlive Dr hr g
    (by have := evalNeed_binary_right op l r d; unfold evalFrame at this; omega) (o := 144)
    (by decide) (by decide) hbr hR.repr hR.ok hR.lt
    ⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact b.r2⟩ fun R2 u0 u1 u2 hkeep2 => ?_
  refine ArmAt.valTag fun htr => ?_
  exact (tail _ _ u0 u1 u2
    (binMid_of_left g b (by ix_keep [hkeep2]; exact b.r9) (by ix_keep [hkeep2]) hkeep2 htr)).arm

theorem binPreludeT (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {op : BinOp} {l r : Expr} {lv rv' v : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (Dr : EvalECost st1 d env r st2 rv' nr)
    (D : EvalECost st d env (.binary op l r) st2 v (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    (tail : ∀ (k : Nat) (Φ : Nat × String → IProp GF) (sret aE aX s ret : BitVec 64)
      (rv R : Nat → BitVec 64) (P : Nat → Prop) (m Mt : Mem) (w0 w1 w2 u0 u1 u2 : BitVec 64)
      (K : IProp GF),
      ArmGeo s ret sret (evalNeed (.binary op l r) d) → BinOpNode m P aX (binOpTok op) →
      BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 →
      ExitK (twpW (vsaModel live)) Φ N s ret sret rv (evalNeed (.binary op l r) d) v
        (world N L Room inp (.counted k) st2 d) K →
      BinTail (twpW (vsaModel live)) Φ N
        (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
          (world N L Room inp (.counted k) st2 d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary op l r) st2 v
        (nl + nr) D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt0 ent => by
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
    rw [show k + (nl + nr) = k + nr + nl by omega]
    refine ArmAt.seg (twpW _) hn.view ?_
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
    refine ArmAt.callEvalT (jal_site% 0x800034f8) hlive Dl hl g
      (by have := evalNeed_binary_left op l r d; unfold evalFrame at this; omega) (o := 120)
      (by decide) (by decide) hbl hrl ent.ok haL
      ⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.left, by ix_reg; exact hregs.a3,
        by ix_reg⟩ fun R1 w0 w1 w2 hkeep1 => ?_
    refine ArmAt.valTag fun htl => ?_
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
    exact binPreludeT_R hlive Dr hr g node hR hbr bl
      (fun R' Mt' u0 u1 u2 hm => tail k Φ sret aE aX s ret rv R' P m Mt' w0 w1 w2 u0 u1 u2 _ g node
        hm evalKT_exit)

end

end VsaIris.Interp
