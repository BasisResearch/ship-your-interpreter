import EvalVarEntryReturn
import Vsa.Sim.OwnedPayloadClause
import Vsa.Sim.LeafFootprint

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- A represented owned value supplies the tag-indexed ownership clause. -/
theorem OwnedSlot.of_owned {m : Mem} {shared : Nat → Prop} {N : NativeAddrs}
    {phiC : Vsa.While.Addr → Nat} {a : Nat} {v : Vsa.While.Value}
    (hv : ValueRepr m N phiC a v) (ho : ValueOwned m shared a v) :
    OwnedSlot m shared a := by
  cases v
  case str s =>
    obtain ⟨p, hp, hs⟩ := ho
    exact fun _ _ _ => ⟨p, s, hp, hs⟩
  case native f =>
    obtain ⟨p, hp, hs⟩ := ho
    exact fun _ _ _ => ⟨p, nativeName f, hp, hs⟩
  all_goals exact OwnedSlot.of_payloadFree hv trivial

namespace EnvGetReflected

/-- The product clause facts at the same evaluator return. -/
structure VarProductResult
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (shared : Nat → Prop)
    (st : Vsa.While.St) (v : Vsa.While.Value) (sp ret dst : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  exit : EvalExitD g N A SL phiF phiC st.store.frames.size st.store.closures.size
    st v sp ret dst m0 c
  footprint : MemFootprint (noArenaFoot SL A sp.toNat dst.toNat) m0 c.σ.mem
  covered : ValuePayloadCovered (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) c.σ.mem dst.toNat v
  owned : OwnedSlot c.σ.mem shared dst.toNat

theorem VarEvalResult.product
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {st : Vsa.While.St} {v : Vsa.While.Value} {sp ret dst : BitVec 64}
    {m0 : Mem} {c : Config}
    (h : VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 c)
    (geometry : SharedReadGeom shared SL) :
    VarProductResult g N A SL phiF phiC shared st v sp ret dst m0 c :=
  { exit := h.returned.exit
    footprint := MemFootprint.of_leafMemPin A h.memory
    covered := h.owned.covered (fun k hk hin => by have := geometry.stack k hk; omega)
    owned := OwnedSlot.of_owned h.value.repr h.owned }

#print axioms OwnedSlot.of_owned
#print axioms VarEvalResult.product

end EnvGetReflected
end Vsa.Sim
