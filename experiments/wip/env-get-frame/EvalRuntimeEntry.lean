import EvalVarProduct
import RuntimeEntryCore
import Vsa.Sim.StrCmpSeam

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

namespace EnvGetReflected

/-- The variable's name and query ownership come from its represented AST. -/
theorem eval_var_owned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value} {d fa : Nat}
    {sp dst ret aExpr aEnv : BitVec 64} {m0 : Mem} {c : Config}
    (entry : EvalRuntimeEntry g N A SL phiF phiC alloc exts shared st d fa (.var query)
      sp ret dst aEnv aExpr m0 c)
    (hget : st.store.get? fa query = some v) :
    ∃ after, Steps c after ∧
      VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 after := by
  obtain ⟨p, hp, hs⟩ : ∃ p, read64 c.σ.mem (aExpr.toNat + 8) = some p ∧
      CStringWithin c.σ.mem shared p query := by
    cases entry.ast with | var _ _ hp _ hs => exact ⟨_, hp, hs⟩
  have hptr : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ hp)]
  have hquery : SharedCString c.σ.mem shared (BitVec.ofNat 64 p).toNat query := by
    rw [hptr]
    exact ⟨hs.1, hs.2⟩
  exact eval_var_return entry.entry
    (entry.runtime.lookup hquery (Vsa.Sim.FixedRodataLoaded.maskPinned entry.entry.ground.eval_call.image.rodata)) hget
    (by rw [hptr]; exact hp) entry.runtime.arenaStack

/-- All product-clause facts follow from the same owned-entry execution. -/
theorem eval_var_product
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value} {d fa : Nat}
    {sp dst ret aExpr aEnv : BitVec 64} {m0 : Mem} {c : Config}
    (entry : EvalRuntimeEntry g N A SL phiF phiC alloc exts shared st d fa (.var query)
      sp ret dst aEnv aExpr m0 c)
    (hget : st.store.get? fa query = some v) :
    ∃ after, Steps c after ∧
      VarProductResult g N A SL phiF phiC shared st v sp ret dst m0 after := by
  obtain ⟨after, hs, hr⟩ := eval_var_owned entry hget
  exact ⟨after, hs, hr.product entry.runtime.geometry⟩

/-- Shared read support survives the variable's writes to its stack slots. -/
theorem VarEvalResult.shared_agree
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {st : Vsa.While.St} {v : Vsa.While.Value} {sp ret dst : BitVec 64}
    {m0 : Mem} {c : Config}
    (h : VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 c)
    (hsp : sp.toNat ≤ SL.hi) (hslot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi) :
    ∀ k, shared k → c.σ.mem[k]? = m0[k]? := by
  obtain ⟨exts, runtime⟩ := h.runtime
  intro k hk
  have hb := runtime.geometry.stack k hk
  exact h.memory.agree k (by omega) (by omega)

#print axioms eval_var_owned
#print axioms eval_var_product
#print axioms VarEvalResult.shared_agree

end EnvGetReflected
end Vsa.Sim
