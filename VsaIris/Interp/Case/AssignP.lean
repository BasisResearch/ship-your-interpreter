import VsaIris.Interp.Case.AssignT

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

theorem caseP_Assign {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {x : String} {e : Expr} (HN : NewlibHoles) (hcl : CodeLive live)
    (hroom : ErrRoom (.assign x e) d)
    (hsetS : ⊢ envSetSpec (GF := GF) (wpW (vsaModel live)) N) :
    leafErrCtx inp ∗ evalSpecsP (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) st d env
        (.assign x e) := by
  unfold leafErrCtx
  iintro ⟨⟨#Hb, %jb, #Hj, %hok⟩, #IH⟩
  iapply evalEntryP hlive fun Φ sret aE aX s ret rv P m Mt ent => assignTail (wpW _) hlive hsetS
    ent (ρ' := .uncounted) (Rel := fun st1 v1 => EvalE st d env e st1 v1)
    (Kc := fun _ v1 w0 w1 w2 => iprop(evalKP (live := live) N L Room inp (evalCore N L Room inp)
      st d env (.assign x e) sret s ret rv Φ ∗
      ((evalSpecsP (vsaModel live) N L Room inp (evalCore N L Room inp) ∗ errCtx inp) ∗
        □ valOf N v1 w0 w1 w2)))
    (fun _ _ _ hrc hqc hr hk => ArmAt.callEvalP (jal_site% 0x80003488) hlive .rfl
      (by iintro ⟨#H, -⟩; iexact H) ent.geo
      (by have := evalNeed_assign x e d; unfold evalFrame at this; omega) (by decide) (by decide)
      (by simpa only [Expr.bodiesBound] using ent.bb) hrc ent.ok hqc hr hk)
    (fun _ _ _ _ _ => by iintro ⟨Hk, HX, #Hv⟩; iframe Hk HX Hv)
    (fun st1 v1 store1 hE hset => evalKP_exit _ (EvalE.assign st d env x e st1 v1 store1 hE hset))
    (fun _ _ _ _ => ⟨HN, hcl, hroom, ⟨jb, hok⟩, evalKP_abort _ (by iintro ⟨-, #H⟩; iexact H)⟩)
  iframe IH; unfold errCtx; iframe Hb; iexists jb; iframe Hj; ipureintro; exact hok.ra

end VsaIris.Interp
