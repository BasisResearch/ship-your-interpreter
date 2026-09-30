import VsaIris.Vsa.BinImg
import VsaIris.Interp.EnvCode
import VsaIris.Vsa.AllocCode

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Sym

def TextOrImpure (p : Nat × BitVec 8) : Prop :=
  (textDom p.1 ∧ textByte p.1 = p.2) ∨ (impureW p.1 ∧ impureByte p.1 = p.2)

instance (p : Nat × BitVec 8) : Decidable (TextOrImpure p) := by
  unfold TextOrImpure; infer_instance

def textOrImpureAll (l : List (Nat × BitVec 8)) : Bool := l.all fun p => decide (TextOrImpure p)

theorem of_textOrImpureAll {l : List (Nat × BitVec 8)} (h : textOrImpureAll l = true) :
    ∀ p ∈ l, TextOrImpure p := by
  intro p hp
  unfold textOrImpureAll at h
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

theorem envText_ok : ∀ p ∈ envText, TextOrImpure p :=
  of_textOrImpureAll (by decide +kernel)

theorem allocText_ok : ∀ p ∈ allocText, TextOrImpure p :=
  of_textOrImpureAll (by decide +kernel)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem textOwn_of_textOrImpure :
    ∀ {l : List (Nat × BitVec 8)}, (∀ p ∈ l, TextOrImpure p) →
      binImg (GF := GF) ∗ impureRO ⊢ textOwn l
  | [], _ => by
    unfold textOwn
    iintro _
    simp only [sepL_nil]
    iempintro
  | p :: l, h => by
    have ih := textOwn_of_textOrImpure (l := l) (fun q hq => h q (.tail _ hq))
    unfold textOwn at ih ⊢
    simp only [sepL_cons]
    iintro #H
    isplitl []
    · unfold binImg impureRO roImg
      icases H with ⟨⟨#Ht, -⟩, #Hi⟩
      rcases h p (.head _) with ⟨hd, hb⟩ | ⟨hd, hb⟩
      · rw [← hb]; iapply Ht $$ %p.1 %hd
      · rw [← hb]; iapply Hi $$ %p.1 %hd
    · iapply ih $$ H

theorem textOwn_envText : binImg (GF := GF) ∗ impureRO ⊢ textOwn envText :=
  textOwn_of_textOrImpure envText_ok

theorem textOwn_allocText : binImg (GF := GF) ∗ impureRO ⊢ textOwn allocText :=
  textOwn_of_textOrImpure allocText_ok

end

end VsaIris.Newlib

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris.Newlib VsaIris.Stdio VsaIris.Sym Vsa.RuntimeRepr Vsa.While

section Code

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def codeX : IProp GF := iprop(binImg ∗ impureRO)

instance : Persistent (codeX (GF := GF)) := by unfold codeX; infer_instance

theorem codeX_binImg : codeX (GF := GF) ⊢ binImg := by
  unfold codeX; iintro ⟨#H, -⟩; iexact H

theorem codeX_envText : codeX (hlc := hlc) (GF := GF) ⊢ textOwn (hlc := hlc) (GF := GF) envText := by
  unfold codeX; exact textOwn_envText (hlc := hlc) (GF := GF)

theorem codeX_allocText : codeX (hlc := hlc) (GF := GF) ⊢ textOwn (hlc := hlc) (GF := GF) allocText := by
  unfold codeX; exact textOwn_allocText (hlc := hlc) (GF := GF)

theorem stdioAt_codeX (P : (Nat → BitVec 8) → Prop) :
    stdioAt (GF := GF) P ∗ binImg ⊢ stdioAt P ∗ codeX := by
  iintro ⟨Hio, #Hb⟩
  ihave ⟨Hio, #Hi⟩ := stdioAt_impure P $$ Hio
  iframe Hio
  unfold codeX
  isplitl []
  · iexact Hb
  · iexact Hi

end Code

section World

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

theorem worldE_codeX (E : IProp GF) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (ρ : Regime) (st : St) (d : Nat) :
    worldE E N L Room inp ρ st d ⊢ worldE E N L Room inp ρ st d ∗ codeX := by
  unfold worldE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
  ihave ⟨Hio, #Hip⟩ := stdioAt_impure _ $$ Hio
  isplitl [Hh Hs Hc Hio Hi]
  · iexists H, B
    iframe Hh Hs Hc Hio Hi
    isplitr
    · ipureintro; exact hB
    · iexact Hb
  · unfold codeX
    isplitl []
    · iexact Hb
    · iexact Hip

theorem world_codeX (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢ world N L Room inp ρ st d ∗ codeX :=
  worldE_codeX _ N L Room inp ρ st d

theorem world_allocText (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢
      world N L Room inp ρ st d ∗ binImg ∗ textOwn allocText := by
  iintro Hw
  ihave ⟨Hw, #Hx⟩ := world_codeX N L Room inp ρ st d $$ Hw
  iframe Hw
  isplitl []
  · iapply codeX_binImg $$ Hx
  · iapply codeX_allocText $$ Hx

end World

end VsaIris.Interp
