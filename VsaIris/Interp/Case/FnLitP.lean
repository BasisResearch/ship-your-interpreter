import VsaIris.Interp.Case.FnLitT

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap VsaIris.Newlib

theorem caseP_FnLit {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) (A : AllocSpecs live)
    {N : NativeAddrs} {inp : Nat}
    (HN : NewlibHoles) (hcl : CodeLive live)
    {st : St} {d env : Nat} {nm : Option String} {ps : List String} {body : List Stmt} :
    leafErrCtx inp ∗
      evalSpecsP (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp (evalCore N vsaLayoutP vsaRoomB inp) ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp
        (evalCore N vsaLayoutP vsaRoomB inp) st d env (.fn nm ps body) := by
  unfold leafErrCtx
  iintro ⟨⟨#Hb, %jb, #Hj, %hok⟩, #IH⟩
  iapply evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent => fnLitTail (wpW _) hlive A ent
    (ρ := .uncounted) (fun store' a h => evalKP_exit _ (EvalE.fn st d env nm ps body store' a h))
    (fun _ => ⟨HN, hcl, errRoom _ _, ⟨jb, hok⟩, evalKP_abort _ (by iintro ⟨-, #H⟩; iexact H)⟩)
  iframe IH; unfold errCtx; iframe Hb; iexists jb; iframe Hj; ipureintro; exact hok.ra

end VsaIris.Interp
