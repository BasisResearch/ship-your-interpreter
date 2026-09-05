import Vsa.Sim.rows.ErrorRouting

/-!
# Faithful error-route bundle compatibility

The former `ErrSiteLinks` record assigned a fixed physical error PC to every
semantic error constructor, including propagation constructors. Trace fuzzing
refuted that interface: propagation constructors reuse a child's `ErrHalts`
result, while only executable leaves own a machine route. Binary failures also
select their site by cause.

This module now exposes the old class-oriented names only as aliases for the
faithful leaf-only interface in `ErrorRouting`. It contains no 42-route table.
-/

open Vsa.Machine (Config)
open Vsa.While

namespace Vsa.Sim

/- Retired constant-config compatibility surface.
/-- Compatibility name for the faithful leaf-only route bundle. -/
abbrev ErrSiteLinks := ErrLeafLinks

/-- Compatibility spelling of the faithful leaf-only family assembly. -/
theorem errFamilyClosed_ofClasses (L : Vsa.Refine.Layout) (S : ErrShared)
    (H : ErrSiteLinks S)
    (hBadClosure : ∀ (c : Config) (st : Vsa.While.St) (d : Nat) (a : Addr)
      (vs : List Value), st.store.closures[a]? = none → ErrHalts c)
    (hTopAbrupt : ∀ (p : Program) (c : Config), InterpRunAbruptPath p c) :
    Vsa.Sim.InterpSimBundle.ErrFamily L :=
  errFamilyClosed_ofLinks L S H hBadClosure hTopAbrupt

#print axioms errFamilyClosed_ofClasses
-/

end Vsa.Sim
