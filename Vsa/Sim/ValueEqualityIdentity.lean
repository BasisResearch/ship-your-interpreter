import Vsa.RuntimeRepr
import Vsa.Sim.StoreInvariant

/-! Address identity for the two values passed to `value_equal`. -/

namespace Vsa.Sim

open Vsa.RuntimeRepr Vsa.While Vsa.MemRepr

/-- The pointer comparisons used by `value_equal` reflect source identity.
Closure bounds and `StoreRepr` supply the closure field. The native field
requires validity of the compared native addresses. Other value kinds do not
require address injectivity. -/
structure ValueEqualityIdentity (N : NativeAddrs) (phiC : Addr → Nat)
    (left right : Value) : Prop where
  closure : ∀ a b, left = .closure a → right = .closure b →
    phiC a = phiC b → a = b
  native : ∀ f h, left = .native f → right = .native h →
    N.addr f = N.addr h → f = h

/-- Global injectivity supplies the operand-local contract for legacy callers. -/
theorem ValueEqualityIdentity.of_injective
    {N : NativeAddrs} {phiC : Addr → Nat} {left right : Value}
    (hc : ∀ a b, phiC a = phiC b → a = b)
    (hn : ∀ f h, N.addr f = N.addr h → f = h) :
    ValueEqualityIdentity N phiC left right where
  closure a b _ _ := hc a b
  native f h _ _ := hn f h

/-- Allocated-prefix injectivity suffices when both operand references are
bounded by the reached store. Native identity remains an explicit input. -/
theorem ValueEqualityIdentity.of_store
    {m : Mem} {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {s : Store} {left right : Value}
    (hs : StoreRepr m N A phiF phiC s)
    (hl : ValueClosuresBounded s.closures.size left)
    (hr : ValueClosuresBounded s.closures.size right)
    (hn : ∀ f h, left = .native f → right = .native h →
      N.addr f = N.addr h → f = h) :
    ValueEqualityIdentity N phiC left right where
  closure a b ha hb hab := by
    subst left; subst right
    exact hs.φc_inj a b hl hr hab
  native := hn

end Vsa.Sim
