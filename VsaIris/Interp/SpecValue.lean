import VsaIris.Interp.SpecEval
import VsaIris.Interp.Abort
import VsaIris.Vsa.NewlibOut
import VsaIris.Vsa.RuntimeError
import VsaIris.Interp.Bridge

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

abbrev valueBoolPC : BitVec 64 := 0x800027f8#64
abbrev valueStrPC : BitVec 64 := 0x8000281c#64
abbrev valueTruthyPC : BitVec 64 := 0x8000282c#64
abbrev valueEqualPC : BitVec 64 := 0x8000285c#64
abbrev valuePrintPC : BitVec 64 := 0x800028fc#64
abbrev nativeAssertPC : BitVec 64 := 0x80002df4#64
abbrev nativePrintPC : BitVec 64 := 0x80002ed4#64
abbrev nativePrintlnPC : BitVec 64 := 0x80002f7c#64
abbrev stringifyPC : BitVec 64 := 0x80002fc0#64

abbrev strcmpPCV : BitVec 64 := 0x80006ea0#64

abbrev callerSaved : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

def printNeed : Nat := fprintfNeed
def nativePrintNeed : Nat := 80 + printNeed
def nativePrintlnNeed : Nat := 48 + nativePrintNeed

def nativeAssertNeed : Nat := 80 + Newlib.RtErr.rtErrNeed

def NativeInj (N : NativeAddrs) : Prop := ∀ f g, N.addr f = N.addr g → f = g

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

structure ArgsGeom (a : BitVec 64) (n : Nat) : Prop where
  al : a.toNat % 8 = 0
  lo : Vsa.Sim.tohostAddr + 16 ≤ a.toNat
  hi : a.toNat + 24 * n ≤ 0x100000000

def valsAt (N : NativeAddrs) (a : Nat) (vs : List Value) : IProp GF :=
  sepL vs.zipIdx (fun p => valAt N (a + 24 * p.2) p.1)

def dispRes (st : Store) : Value → IProp GF
  | .closure ca => iprop(∃ (cd : ClosureData) (p q : Nat) (img : Nat → BitVec 8) (P : Nat → Prop)
      (m : Mem), ⌜st.closures[ca]? = some cd ∧ imgLE img p 8 = q ∧
        (∀ k, InExt (p, 16) k → ReadOK k) ∧ ExprReprWithin m P q (.fn cd.name cd.params cd.body) ∧
        (∀ k, P k → ReadOK k) ∧ SharedWin P⌝ ∗
      closAt ca p ∗ roImg (InExt (p, 16)) img ∗ roOn P m)
  | _ => iprop(emp)

instance (st : Store) (v : Value) : Persistent (dispRes (GF := GF) st v) := by
  cases v <;> unfold dispRes <;> infer_instance

def dispResL (st : Store) (vs : List Value) : IProp GF := sepL vs (dispRes st)

instance (st : Store) (vs : List Value) : Persistent (dispResL (GF := GF) st vs) := by
  unfold dispResL; infer_instance

abbrev stackAt (s : BitVec 64) (n : Nat) : IProp GF :=
  iprop(stackScratch s n ∗ ⌜StackGeom s n⌝)

end Defs

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

def strcmpSpecV (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String),
    helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(binImg ∗ strAt p.toNat x ∗ strAt q.toNat y)
      (fun rv' => iprop(⌜rv' 10 = 0#64 ↔ x = y⌝)))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcmpSpecV M Wp) := by
  unfold strcmpSpecV; infer_instance

def valueBoolSpec (Wp : MachWP (GF := GF) M) (p b : BitVec 64) : IProp GF :=
  helperSpec M Wp valueBoolPC [11, 15] (fun rv => rv 10 = p ∧ rv 11 = b)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat (.bool (b != 0#64)))

def valueStrSpec (Wp : MachWP (GF := GF) M) (p q : BitVec 64) (x : String) : IProp GF :=
  helperSpec M Wp valueStrPC [15] (fun rv => rv 10 = p ∧ rv 11 = q)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p ∧ q.toNat ≠ 0⌝ ∗ strAt q.toNat x)
    (fun _ => valAt N p.toNat (.str x))

def valueTruthySpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) (v : Value) : IProp GF :=
  helperSpec M Wp valueTruthyPC [10, 14, 15] (fun rv => rv 10 = p)
    iprop(valAt N p.toNat v ∗ ⌜SlotGeom p⌝)
    (fun rv' => iprop(valAt N p.toNat v ∗ ⌜rv' 10 = if v.truthy then 1#64 else 0#64⌝))

def valueEqualSpec (Wp : MachWP (GF := GF) M) (pa pb s : BitVec 64) (a b : Value) (st : Store)
    (B : List (Nat × Nat)) : IProp GF :=
  helperSpec M Wp valueEqualPC callerSaved (fun rv => rv 10 = pa ∧ rv 11 = pb ∧ rv 2 = s)
    iprop(valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ ⌜SlotGeom pa ∧ SlotGeom pb ∧ NativeInj N⌝ ∗
      storeRepr N st B ∗ stackAt s 16 ∗ strcmpSpecV M Wp ∗ binImg)
    (fun rv' => iprop(valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ storeRepr N st B ∗ stackAt s 16 ∗
      ⌜rv' 10 = if Value.equal a b then 1#64 else 0#64⌝))

def valuePrintSpec (Wp : MachWP (GF := GF) M) (p s : BitVec 64) (v : Value) (st : Store)
    (o : String) : IProp GF :=
  helperSpec M Wp valuePrintPC callerSaved
    (fun rv => rv 10 = p ∧ rv 11 = stdoutFile ∧ rv 2 = s)
    iprop(valAt N p.toNat v ∗ ⌜SlotGeom p⌝ ∗ dispRes st v ∗ binImg ∗ stdioW ∗ consoleOwn o ∗
      stackAt s printNeed)
    (fun _ => iprop(valAt N p.toNat v ∗ stdioW ∗ consoleOwn (o ++ v.display st) ∗
      stackAt s printNeed))

def nativePrintSpec (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64) (vs : List Value)
    (st : Store) (o : String) : IProp GF :=
  helperSpec M Wp nativePrintPC callerSaved
    (fun rv => rv 10 = sret ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧ rv 2 = s)
    iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ binImg ∗ stdioW ∗ consoleOwn o ∗
      stackAt s nativePrintNeed)
    (fun _ => iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioW ∗
      consoleOwn (o ++ printArgs st vs) ∗ stackAt s nativePrintNeed))

def nativePrintlnSpec (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64) (vs : List Value)
    (st : Store) (o : String) : IProp GF :=
  helperSpec M Wp nativePrintlnPC callerSaved
    (fun rv => rv 10 = sret ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧ rv 2 = s)
    iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ binImg ∗ stdioW ∗ consoleOwn o ∗
      stackAt s nativePrintlnNeed)
    (fun _ => iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ stdioW ∗
      consoleOwn (o ++ printArgs st vs ++ "\n") ∗ stackAt s nativePrintlnNeed))

def AssertOk (vs : List Value) : Prop := ∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy = true

def nativeAssertSpec (Wp : MachWP (GF := GF) M) (L : DlLayout) (Room : RoomPred)
    (sret inp args s line : BitVec 64) (vs : List Value) (ρ : Regime) (st : St) (d : Nat)
    (jb : Nat → BitVec 8) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecAbort Wp nativeAssertPC
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗
      ⌜rv 10 = sret ∧ rv 11 = inp ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧
        rv 14 = line ∧ rv 2 = s⌝ ∗ codeRes ∗ slot24 sret.toNat ∗
      ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31 ∧ Newlib.RtErr.InpGeom inp ∧
        (jbWord inp.toNat jb 0).toNat % 4 = 0⌝ ∗
      valsAt N args.toNat vs ∗ binImg ∗ jmpRO inp.toNat jb ∗ world N L Room inp.toNat ρ st d ∗
      stackAt s nativeAssertNeed))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
      ⌜∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy = true⌝ ∗ valAt N sret.toNat .null ∗
      valsAt N args.toNat vs ∗ world N L Room inp.toNat ρ st d ∗ stackAt s nativeAssertNeed))
    iprop(⌜¬ AssertOk vs⌝ ∗ abortRes N L Room inp.toNat s nativeAssertNeed ∗ slot24 sret.toNat ∗
      valsAt N args.toNat vs))

end Specs

end VsaIris.Interp
