import VsaIris.Interp.SpecStringify
import VsaIris.Interp.HeapCall

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.RuntimeRepr

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

structure HeapStr (H : List (Nat × Nat)) (q : BitVec 64) (x : String) : Prop where
  live : (q.toNat, x.toList.length + 1) ∈ H
  align : q.toNat % 16 = 0

def strlenHeapSpec (Wp : MachWP (GF := GF) M) (q : BitVec 64) (x : String) (ρ : Regime)
    (H : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp strlenPC callerSaved (fun rv => rv 10 = q)
    iprop(binImg ∗ ⌜HeapStr H q x⌝ ∗ strOwn q.toNat x ∗ heapRes vsaLayoutP vsaRoomB ρ H)
    (fun rv' => iprop(⌜rv' 10 = BitVec.ofNat 64 x.length⌝ ∗ strOwn q.toNat x ∗
      heapRes vsaLayoutP vsaRoomB ρ H))

def strcpyHeapSpec (Wp : MachWP (GF := GF) M) (d q : BitVec 64) (y : String) (ρ : Regime)
    (H : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp strcpyPC callerSaved (fun rv => rv 10 = d ∧ rv 11 = q)
    iprop(binImg ∗ ⌜HeapStr H q y ∧ RamWin d.toNat (y.toList.length + 1) ∧ htifLo + 16 ≤ d.toNat⌝ ∗
      blockOwn d.toNat (y.toList.length + 1) ∗ strOwn q.toNat y ∗
      heapRes vsaLayoutP vsaRoomB ρ H)
    (fun _ => iprop((∃ img, ownImg (InExt (d.toNat, y.toList.length + 1)) img ∗
        ⌜CStrImg img d.toNat y⌝) ∗ strOwn q.toNat y ∗ heapRes vsaLayoutP vsaRoomB ρ H))

def helperSpecA (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (clob : List Nat)
    (pins : (Nat → BitVec 64) → Prop) (Pre : IProp GF)
    (Post : (Nat → BitVec 64) → IProp GF) (A : IProp GF) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecAbort Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜pins rv⌝ ∗ codeRes ∗ Pre))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ clob → rv' x = rv x⌝ ∗ Post rv'))
    A)

def stringifyPre (p s : BitVec 64) (v : Value) (st : Store) (ρ : Regime)
    (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  iprop(valAt N p.toNat v ∗
    ⌜SlotGeom p ∧ vsaChg ((strRender st v).toList.length + 1) c⌝ ∗ dispRes st v ∗ binImg ∗
    heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗ stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed)

def stringifyPost (p s : BitVec 64) (v : Value) (st : Store) (ρ : Regime)
    (H : List (Nat × Nat)) (o : String) (q : BitVec 64) : IProp GF :=
  iprop(valAt N p.toNat v ∗ strOwn q.toNat (strRender st v) ∗
    ⌜FreshBlock vsaLayoutP H q.toNat ((strRender st v).toList.length + 1) ∧ q.toNat % 16 = 0⌝ ∗
    heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, (strRender st v).toList.length + 1) :: H) ∗
    stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed)

def stringifySpecT (Wp : MachWP (GF := GF) M) (p s : BitVec 64) (v : Value) (st : Store)
    (k : Nat) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  helperSpec M Wp stringifyPC callerSaved (fun rv => rv 10 = p ∧ rv 2 = s)
    (stringifyPre N p s v st (.counted k) H c o)
    (fun rv' => stringifyPost N p s v st (.counted k) H o (rv' 10))

def stringifySpecP (Wp : MachWP (GF := GF) M) (inp : Nat) (p s : BitVec 64) (v : Value)
    (st : Store) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  helperSpecA M Wp stringifyPC callerSaved (fun rv => rv 10 = p ∧ rv 2 = s)
    (stringifyPre N p s v st ρ H c o)
    (fun rv' => stringifyPost N p s v st ρ H o (rv' 10))
    iprop(abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗ slot24 p.toNat)

def CatDispSupply : Prop :=
  ∀ (s : Store) (B : List (Nat × Nat)) (ca p : Nat),
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ storeRepr N s B ∗ dispRes s (.closure ca)

end Specs

end VsaIris.Interp
