import VsaIris.Vsa.Newlib
import VsaIris.Interp.Repr

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Inst
open Vsa.While

def fputsEntry : BitVec 64 := 0x80006500#64
def fputcEntry : BitVec 64 := 0x800062e0#64

def stdoutFile : BitVec 64 := 0x8001bb20#64

def outNeed : Nat := 768

def fnRender (x : String) : String := String.ofList (("<fn " ++ x ++ ">").toList.take 63)

theorem fnRender_eq (x : String) : fnRender x = Vsa.While.fnCatRender x := rfl

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def fprintfOut (fmt arg : BitVec 64) (frag : String) : IProp GF :=
  iprop(⌜fmt = 0x800192c0#64 ∧ frag = intToString arg.toInt⌝ ∨
    (∃ name, ⌜fmt = 0x800192c8#64 ∧ frag = "<fn " ++ name ++ ">"⌝ ∗ strAt arg.toNat name) ∨
    (∃ name, ⌜fmt = 0x800192d8#64 ∧ frag = "<native fn " ++ name ++ ">"⌝ ∗ strAt arg.toNat name))

instance (fmt arg : BitVec 64) (frag : String) : Persistent (fprintfOut (GF := GF) fmt arg frag) := by
  unfold fprintfOut; infer_instance

def outSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (entry : BitVec 64)
    (args : List (BitVec 64)) (R : IProp GF) (s : BitVec 64) (need : Nat) (cs : Nat → BitVec 64)
    (o frag : String) : IProp GF :=
  fnSpecW Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt args ∗ R ∗ stdioW ∗ consoleOwn o ∗
      callFrame s need calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗ stdioW ∗ consoleOwn (o ++ frag) ∗
      callFrame s need calleeSaved cs))

def snprintfFnSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf name : BitVec 64) (x : String) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [buf, 64#64, 0x800192c8#64, name] ∗ blockOwn buf.toNat 64 ∗
      strAt name.toNat x ∗ stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (fnRender x)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

def snprintfIntSpec (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf i : BitVec 64) (cs : Nat → BitVec 64) : IProp GF :=
  fnSpecW Wp snprintfEntry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt [buf, 64#64, 0x800192c0#64, i] ∗ blockOwn buf.toNat 64 ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))
    (fun _ => iprop(clobbered argRegs ∗
      (∃ img, ownImg (InExt (buf.toNat, 64)) img ∗ ⌜CStrImg img buf.toNat (intToString i.toInt)⌝) ∗
      stdioOwn ∗ callFrame s snprintfNeed calleeSaved cs))

end Specs

structure OutHoles : Prop where

theorem OutHoles.proved : OutHoles := ⟨⟩

end VsaIris.Newlib
