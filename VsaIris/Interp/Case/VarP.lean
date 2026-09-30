import VsaIris.Interp.Case.VarT

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

theorem caseP_Var {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {x : String} (HN : NewlibHoles) (hcl : CodeLive live)
    (hroom : ErrRoom (.var x) d)
    (hget : ⊢ envGetSpec (GF := GF) (wpW (vsaModel live)) N) :
    leafErrCtx inp ∗ evalSpecsP (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) st d env
        (.var x) := by
  unfold leafErrCtx
  iintro ⟨⟨#Hb, %jb, #Hj, %hok⟩, #IH⟩
  iapply evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent => varTail (wpW _) hlive hget ent
    (fun v h => evalKP_exit _ (EvalE.var st d env x v h))
    (fun _ => ⟨HN, hcl, hroom, ⟨jb, hok⟩, evalKP_abort _ (by iintro ⟨-, #H⟩; iexact H)⟩)
  iframe IH; unfold errCtx; iframe Hb; iexists jb; iframe Hj; ipureintro; exact hok.ra

end VsaIris.Interp
