import VsaIris.Interp.ExecArm

/-!
Statement specs from regime-generic arm cores: a deterministic arm proved for every regime
gives both the total spec (`execDispT_of`, at `.counted k`) and the partial spec
(`execDispP_of`, at `.uncounted`, instantiating the continuation's `ExecS` witness).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- A total statement spec whose arm is proved for every regime and continuation. -/
theorem execDispT_of {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {sm : Stmt} {status : Status} (D : ExecSCost st d env sm st status 0)
    (core : ∀ (Φ : Nat × String → IProp GF) (ρ : Regime) (aS aE aRet s : BitVec 64)
      (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64),
      execDispPre N L Room inp ρ st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
        execDispK (vsaModel live) N L Room inp (twpW _) Φ ρ st d sm status aRet s R ret v8 v9 v18
          v19 ⊢ (twpW (vsaModel live)).W Φ) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env sm st status 0 D := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  iapply core Φ (.counted k) aS aE aRet s R Mt ret v8 v9 v18 v19
  iframe Hpre HK

/-- A partial statement spec for a deterministic arm proved for every regime and continuation. -/
theorem execDispP_of {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt} {status : Status}
    (hE : ExecS st d env sm st status)
    (core : ∀ (Φ : Nat × String → IProp GF) (ρ : Regime) (aS aE aRet s : BitVec 64)
      (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64),
      execDispPre N L Room inp ρ st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
        execDispK (vsaModel live) N L Room inp (wpW _) Φ ρ st d sm status aRet s R ret v8 v9 v18
          v19 ⊢ (wpW (vsaModel live)).W Φ) :
    ⊢ execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env sm := by
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  ihave HK := and_elim_l $$ HK
  ihave HK := HK $$ %st %status %hE
  iapply core Φ .uncounted aS aE aRet s R Mt ret v8 v9 v18 v19
  iframe Hpre HK

end

end VsaIris.Interp
