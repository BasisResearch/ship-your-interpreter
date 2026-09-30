import VsaIris.Interp.SpecValue
import VsaIris.Interp.HeapCall

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.RuntimeRepr

def closName (st : Store) : Value → Option String
  | .closure ca => (st.closures[ca]?).bind ClosureData.name
  | _ => none

def strRender (st : Store) (v : Value) : String :=
  match closName st v with
  | some x => fnRender x
  | none => v.catDisplay st

theorem strRender_eq (st : Store) (v : Value) : strRender st v = v.catDisplay st := by
  unfold strRender closName
  cases v with
  | closure ca =>
    cases h : st.closures[ca]? with
    | none => simp [Value.catDisplay, h]
    | some cd =>
      cases hn : cd.name <;> simp [Value.catDisplay, h, hn, fnRender_eq]
  | _ => rfl

def stringifyNeed : Nat := 112 + snprintfNeed

abbrev strcpyPC : BitVec 64 := 0x80006dc4#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

def strOwn (q : Nat) (x : String) : IProp GF :=
  iprop(∃ img, ownImg (InExt (q, x.toList.length + 1)) img ∗ ⌜CStrImg img q x⌝)

def memcpySpecOwned (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (n : Nat) (img : Nat → BitVec 8), fnSpecW Wp memcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ htifLo + 16 ≤ dst.toNat ∧
        RamWin src.toNat n⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗
      clobbered argClob ∗ blockOwn dst.toNat n ∗ ownImg (InExt (src.toNat, n)) img ∗ binImg))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      ownImg (InExt (dst.toNat, n)) (fun a => img (a - dst.toNat + src.toNat)) ∗
      ownImg (InExt (src.toNat, n)) img)))

def strcpySpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (dst src : BitVec 64) (x : String) (n : Nat), fnSpecW Wp strcpyPC
    (fun r => iprop(⌜r.toNat % 4 = 0 ∧ RamWin dst.toNat n ∧ x.toList.length + 1 ≤ n ∧
        htifLo + 16 ≤ dst.toNat⌝ ∗
      (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗ clobbered (12 :: argClob) ∗ blockOwn dst.toNat n ∗
      strAt src.toNat x))
    (fun _ => iprop((10 : Nat) ↦ᵣ dst ∗ clobbered retClob ∗
      (∃ img, ownImg (InExt (dst.toNat, n)) img ∗ ⌜CStrImg img dst.toNat x⌝))))

def stringifySpec (Wp : MachWP (GF := GF) M) (inp : Nat) (p s : BitVec 64) (v : Value)
    (st : Store) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat) (o : String) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecAbort Wp stringifyPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜rv 10 = p ∧ rv 2 = s⌝ ∗ codeRes ∗
      valAt N p.toNat v ∗
      ⌜SlotGeom p ∧ vsaChg ((strRender st v).toList.length + 1) c⌝ ∗ dispRes st v ∗ binImg ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗ stdioOwn ∗ consoleOwn o ∗
      stackAt s stringifyNeed))
    (fun _ => iprop(∃ (rv' : Nat → BitVec 64) (q : BitVec 64), regFile rv' ∗
      ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗ ⌜rv' 10 = q⌝ ∗
      valAt N p.toNat v ∗ strOwn q.toNat (strRender st v) ∗
      ⌜FreshBlock vsaLayoutP H q.toNat ((strRender st v).toList.length + 1) ∧ q.toNat % 16 = 0⌝ ∗
      heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, (strRender st v).toList.length + 1) :: H) ∗
      stdioOwn ∗ consoleOwn o ∗ stackAt s stringifyNeed))
    (iprop(⌜ρ = .uncounted⌝ ∗ abortRes N vsaLayoutP vsaRoomB inp s stringifyNeed ∗
      slot24 p.toNat)))

end Specs

end VsaIris.Interp
