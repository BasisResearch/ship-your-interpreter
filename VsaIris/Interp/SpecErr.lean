import VsaIris.Interp.SpecValue
import VsaIris.Interp.Arm

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

abbrev valueKindNamePC : BitVec 64 := 0x800029c8#64

def kindNamePtr : Value → BitVec 64
  | .null => 0x80019018#64
  | .bool _ => 0x800192e8#64
  | .int _ => 0x800192f0#64
  | .str _ => 0x80018ea0#64
  | .closure _ => 0x800192f8#64
  | .native _ => 0x80019308#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

def valueKindNameSpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) (Mt : Mem) (v : Value) : IProp GF :=
  helperSpec M Wp valueKindNamePC [10, 14, 15] (fun rv => rv 10 = p)
    iprop(ownSet (InExt (p.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      ⌜SlotGeom p ∧ (imgW (imgM Mt) p.toNat).toNat % 2 ^ 32 = valTag v⌝)
    (fun rv' => iprop(ownSet (InExt (p.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      ⌜rv' 10 = kindNamePtr v⌝))

structure StrcmpSign (res : BitVec 64) (x y : String) : Prop where
  eq : res = 0#64 ↔ x = y
  lt : res.toInt < 0 ↔ x < y
  gt : 0 < res.toInt ↔ y < x

def strcmpOrdSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String),
    helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(binImg ∗ strAt p.toNat x ∗ strAt q.toNat y)
      (fun rv' => iprop(⌜StrcmpSign (rv' 10) x y⌝)))

theorem strcmpOrdSpec_at {Wp : MachWP (GF := GF) M} (p q : BitVec 64) (x y : String) :
    strcmpOrdSpec M Wp ⊢ helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(binImg ∗ strAt p.toNat x ∗ strAt q.toNat y) (fun rv' => iprop(⌜StrcmpSign (rv' 10) x y⌝)) := by
  unfold strcmpOrdSpec
  iintro #H
  iapply H

def errCtx (inp : Nat) : IProp GF :=
  iprop(binImg ∗ ∃ jb, jmpRO inp jb ∗ ⌜(jbWord inp jb 0).toNat % 4 = 0⌝)

instance (inp : Nat) : Persistent (errCtx (GF := GF) inp) := by
  unfold errCtx; infer_instance

theorem errCtx_img (inp : Nat) : errCtx (GF := GF) inp ⊢ binImg := by
  unfold errCtx; iintro ⟨#H, -⟩; iexact H

abbrev runSp : BitVec 64 :=
  BitVec.ofNat 64 (Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame)

theorem runSp_toNat :
    runSp.toNat = Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame := by
  decide

theorem runTop_eq : Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame =
    0x87fffc50 := by decide

variable (L : DlLayout) (Room : RoomPred) (inp : Nat)

def CoreOK (Core : IProp GF) : Prop :=
  ∀ (sc : BitVec 64) (nc : Nat), nc ≤ sc.toNat → 0x87800000 ≤ sc.toNat - nc →
    sc.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame →
    abortCore N L Room inp sc nc ⊢ Core

structure ErrEnv (live : Nat → Prop) (Core : IProp GF) : Prop where
  newlib : NewlibHoles
  code : CodeLive live
  inpGeom : RtErr.InpGeom (BitVec.ofNat 64 inp)
  inpLt : inp < 2 ^ 64
  core : CoreOK N L Room inp Core

theorem coreOK_top : CoreOK (GF := GF) N L Room inp
    (abortCore N L Room inp runSp (runSp.toNat - 0x87800000)) := fun sc nc _ h2 h3 =>
  abortCore_mono N L Room inp (by decide) (by decide) (by rw [runSp_toNat, runTop_eq]; omega)
    (by rw [runSp_toNat]; exact h3) (by decide)

end Specs

end VsaIris.Interp
