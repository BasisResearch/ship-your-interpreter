import VsaIris.Interp.Code
import VsaIris.Interp.Repr
import VsaIris.Interp.Need
import VsaIris.Stack
import Vsa.While.Cost

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section Regs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

abbrev fRegs : List Nat :=
  [2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

abbrev calleeSaved : List Nat := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def regFile (rv : Nat → BitVec 64) : IProp GF := sepL fRegs (fun r => r ↦ᵣ rv r)

def KeepRegs (keep : List Nat) (rv rv' : Nat → BitVec 64) : Prop := ∀ x ∈ keep, rv' x = rv x

def codeRes : IProp GF := roOwn roR interpText

instance : Persistent (codeRes (GF := GF)) := by unfold codeRes; infer_instance

end Regs

structure StackGeom (s : BitVec 64) (n : Nat) : Prop where
  le : n ≤ s.toNat
  lo : Vsa.Sim.LayoutInstance.stackSL.lo ≤ s.toNat - n
  hi : s.toNat ≤ Vsa.Sim.LayoutInstance.stackSL.hi
  al : s.toNat % 16 = 0
  top : s.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame

structure SlotGeom (a : BitVec 64) : Prop where
  al : a.toNat % 8 = 0
  lo : Vsa.Sim.tohostAddr + 16 ≤ a.toNat
  hi : a.toNat + 24 ≤ 0x100000000

structure EvalRegs (rv : Nat → BitVec 64) (sret inp aX aE s : BitVec 64) : Prop where
  a0 : rv 10 = sret
  a1 : rv 11 = inp
  a2 : rv 12 = aX
  a3 : rv 13 = aE
  sp : rv 2 = s

structure ExecRegs (rv : Nat → BitVec 64) (inp aS aE aRet s : BitVec 64) : Prop where
  a0 : rv 10 = inp
  a1 : rv 11 = aS
  a2 : rv 12 = aE
  a3 : rv 13 = aRet
  sp : rv 2 = s

def statusCode : Status → BitVec 64
  | .normal => 0#64
  | .brk => 1#64
  | .cont => 2#64
  | .ret _ => 3#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

def astSG (a : Nat) (s : Stmt) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜StmtReprWithin m P a s ∧ ∀ k, P k → ReadOK k⌝ ∗ roOn P m)

def statusRet (N : NativeAddrs) (aRet : Nat) : Status → IProp GF
  | .ret v => valAt N aRet v
  | _ => slot24 aRet

omit I in
theorem statusRet_normal [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .normal = slot24 a := rfl

variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

def evalEntryPC : BitVec 64 := 0x80003164#64
def execEntryPC : BitVec 64 := 0x80003fe0#64

def evalPre (ρ : Regime) (st : St) (d env : Nat) (e : Expr) (sret aE aX s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(regFile rv ∗ ⌜EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s⌝ ∗ codeRes ∗
    □ astEG aX.toNat e ∗ □ frameAt env aE.toNat ∗
    stackScratch s (evalNeed e d) ∗ ⌜StackGeom s (evalNeed e d)⌝ ∗
    slot24 sret.toNat ∗ ⌜SlotGeom sret⌝ ∗ ⌜e.bodiesBound perCallBudget = true⌝ ∗
    world N L Room inp ρ st d)

def evalPost (ρ : Regime) (st' : St) (d : Nat) (e : Expr) (v : Value) (sret s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(∃ rv', regFile rv' ∗ ⌜KeepRegs calleeSaved rv rv'⌝ ∗
    stackScratch s (evalNeed e d) ∗ valAt N sret.toNat v ∗ world N L Room inp ρ st' d)

def evalSpecT_body (st : St) (d env : Nat) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_D : EvalECost st d env e st' v n) : IProp GF :=
  iprop(∀ (k : Nat) (sret aE aX s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecW (twpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp (.counted (k + n)) st d env e sret aE aX s rv))
      (fun _ => evalPost N L Room inp (.counted k) st' d e v sret s rv))

def evalSpecP_body (Core : IProp GF) (st : St) (d env : Nat) (e : Expr) : IProp GF :=
  iprop(∀ (sret aE aX s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecAbort (wpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp .uncounted st d env e sret aE aX s rv))
      (fun _ => iprop(∃ st' v, ⌜EvalE st d env e st' v⌝ ∗
        evalPost N L Room inp .uncounted st' d e v sret s rv))
      iprop(abortAt Core s (evalNeed e d) ∗ slot24 sret.toNat))

def evalSpecsP (Core : IProp GF) : IProp GF :=
  iprop(□ ▷ ∀ st d env e, evalSpecP_body M N L Room inp Core st d env e)

instance (Core : IProp GF) : Persistent (evalSpecsP (GF := GF) M N L Room inp Core) := by
  unfold evalSpecsP; infer_instance

def execPre (ρ : Regime) (st : St) (d env : Nat) (sm : Stmt) (aS aE aRet s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(regFile rv ∗ ⌜ExecRegs rv (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗ codeRes ∗
    □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
    stackScratch s (execNeed sm d) ∗ ⌜StackGeom s (execNeed sm d)⌝ ∗
    slot24 aRet.toNat ∗ ⌜SlotGeom aRet⌝ ∗ ⌜sm.bodiesBound perCallBudget = true⌝ ∗
    world N L Room inp ρ st d)

def execPost (ρ : Regime) (st' : St) (d : Nat) (sm : Stmt) (status : Status)
    (aRet s : BitVec 64) (rv : Nat → BitVec 64) : IProp GF :=
  iprop(∃ rv', regFile rv' ∗ ⌜KeepRegs calleeSaved rv rv' ∧ rv' 10 = statusCode status⌝ ∗
    stackScratch s (execNeed sm d) ∗ statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d)

def execSpecT_body (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (_D : ExecSCost st d env sm st' status n) : IProp GF :=
  iprop(∀ (k : Nat) (aS aE aRet s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecW (twpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp (.counted (k + n)) st d env sm aS aE aRet s rv))
      (fun _ => execPost N L Room inp (.counted k) st' d sm status aRet s rv))

def execSpecP_body (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) : IProp GF :=
  iprop(∀ (aS aE aRet s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecAbort (wpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp .uncounted st d env sm aS aE aRet s rv))
      (fun _ => iprop(∃ st' status, ⌜ExecS st d env sm st' status⌝ ∗
        execPost N L Room inp .uncounted st' d sm status aRet s rv))
      iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat))

def execSpecsP (Core : IProp GF) : IProp GF :=
  iprop(□ ▷ ∀ st d env sm, execSpecP_body M N L Room inp Core st d env sm)

instance (Core : IProp GF) : Persistent (execSpecsP (GF := GF) M N L Room inp Core) := by
  unfold execSpecsP; infer_instance

def helperSpec (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (clob : List Nat)
    (pins : (Nat → BitVec 64) → Prop) (Pre : IProp GF)
    (Post : (Nat → BitVec 64) → IProp GF) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecW Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜pins rv⌝ ∗ codeRes ∗ Pre))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ clob → rv' x = rv x⌝ ∗ Post rv')))

def valueIntSpec (Wp : MachWP (GF := GF) M) (p n : BitVec 64) : IProp GF :=
  helperSpec M Wp 0x8000280c#64 [15] (fun rv => rv 10 = p ∧ rv 11 = n)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat (.int n.toInt))

def valueNullSpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) : IProp GF :=
  helperSpec M Wp 0x800027ec#64 [] (fun rv => rv 10 = p)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat .null)

end Specs

end VsaIris.Interp
