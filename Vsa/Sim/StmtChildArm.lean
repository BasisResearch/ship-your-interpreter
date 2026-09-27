import Vsa.Sim.TruthyCopy
import Vsa.Sim.rows.InitSomeReturnReady
import Vsa.Sim.ExecRetEpilogue

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

def LoopFrame (SL : StackLayout) (A : Arena) (sp aRet : BitVec 64) (m m' : Mem) : Prop :=
  MemExtends m m' ∧
  ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ m'[a]? = m[a]?

namespace LoopFrame

theorem trans {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {m m' m'' : Mem}
    (h1 : LoopFrame SL A sp aRet m m') (h2 : LoopFrame SL A sp aRet m' m'') :
    LoopFrame SL A sp aRet m m'' := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro a hstk hA
  rcases h2.2 a hstk hA with hr | heq
  · exact Or.inl hr
  · rcases h1.2 a hstk hA with hr' | heq'
    · exact Or.inl hr'
    · exact Or.inr (heq.trans heq')

end LoopFrame

end Vsa.Sim
