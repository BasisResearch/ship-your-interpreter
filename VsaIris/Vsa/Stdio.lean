import VsaIris.MallocRun
import VsaIris.Vsa.ImpureRO
import Vsa.Sim.ExitRuntimeData
import Vsa.Sim.LocaleData
import Vsa.Sim.StderrStream

namespace VsaIris.Stdio

open Iris Iris.BI Iris.Std Iris.ProofMode
open Vsa.MemRepr Vsa.Sim

def InRange (lo hi a : Nat) : Prop := lo ≤ a ∧ a < hi

def stdioFoot (a : Nat) : Prop :=
  InRange 0x8001b520 0x8001b538 a ∨ InRange 0x8001b53c 0x8001b960 a ∨
  InRange 0x8001b970 0x8001b990 a ∨ InRange 0x8001b9b0 0x8001ba08 a ∨
  InRange 0x8001ba0c 0x8001ba18 a ∨ InRange 0x8001ba68 0x8001c168 a

def stderrPtrAddr : Nat := consoleReent + 24

def StdioOKAt (o : Bool) (img : Nat → BitVec 8) : Prop :=
  ∀ m : Mem, (∀ a, stdioFoot a → m[a]? = some (img a)) →
    ConsoleStreamAt o m ∧ ExitRuntimeData m ∧ read64 m stderrPtrAddr = some exitStderr ∧
      LocaleData m ∧ StderrStream m

def StdioOK (img : Nat → BitVec 8) : Prop := ∃ o, StdioOKAt o img

theorem StdioOKAt.ok {o : Bool} {img : Nat → BitVec 8} (h : StdioOKAt o img) : StdioOK img :=
  ⟨o, h⟩

def errnoFoot (a : Nat) : Prop := InRange 0x8001ba08 0x8001ba0c a

instance : DecidablePred errnoFoot := fun a => by unfold errnoFoot InRange; infer_instance

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def errnoOwn : IProp GF := ownSet errnoFoot byteAny

def stdioExcl (a : Nat) : Prop := stdioFoot a ∧ ¬ impureW a

def stdioAt (P : (Nat → BitVec 8) → Prop) : IProp GF :=
  iprop(∃ img, ⌜P img ∧ ImpureImg img⌝ ∗ ownSet stdioExcl (fun a => a ↦ₘ img a) ∗ impureRO)

abbrev stdioOwn : IProp GF := stdioAt StdioOK

def stdioW : IProp GF := iprop(stdioOwn ∗ errnoOwn)

theorem stdioAt_mono {P Q : (Nat → BitVec 8) → Prop} (h : ∀ img, P img → Q img) :
    stdioAt (GF := GF) P ⊢ stdioAt Q := by
  unfold stdioAt
  iintro ⟨%img, %⟨hp, hi⟩, H, #Hr⟩
  iexists img
  iframe H Hr
  ipureintro
  exact ⟨h img hp, hi⟩

theorem stdioAt_impure (P : (Nat → BitVec 8) → Prop) :
    stdioAt (GF := GF) P ⊢ stdioAt P ∗ impureRO := by
  unfold stdioAt
  iintro ⟨%img, %hp, H, #Hr⟩
  isplitl [H]
  · iexists img
    iframe H Hr
    ipureintro
    exact hp
  · iexact Hr

end Own

end VsaIris.Stdio
