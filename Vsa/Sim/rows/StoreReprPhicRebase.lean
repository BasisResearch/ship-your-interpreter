import Vsa.RuntimeRepr
import Vsa.Sim.StoreInvariant
import Vsa.Sim.InterpEntry

/-!
# `StoreReprPhicRebase` — the φc-entry rebase `StoreRepr … φc → StoreRepr … φc'`

The `.fn` (EX_FN) arm grows the closures array by one (`allocClosure`), so its
`FnArmGeom.hArm` run is OFF-DIAGONAL: it enters at the pre-alloc closures map `φc`
and exits at the widened map `φc'`.  The diagonal seam (`fnArmGeom_hArm_of_seam`)
only produces `Triple (EvalEntry … φc' …) (PreEpilogueV … φc' …)`, so closing the
off-diagonal `FnArmGeom.hArm` needs the entry rebase
`StoreRepr … φc st.store → StoreRepr … φc' st.store` — the closures-side analog of
the φf-rebase in the frame-allocating arms (`CallClosureEnvNewMarshal`).

## The honest side-condition

`StoreRepr … φc s` does NOT by itself constrain the closure *addresses stored in
frame values* to be `< s.closures.size` (a frame binding may be `.closure ca` for
an arbitrary `ca`).  So the fully-general `storeRepr_phic_mono` is FALSE: a value
`.closure ca` with `ca ≥ s.closures.size` reads `φc ca` under `φc` and `φc' ca`
under `φc'`, and `PhiExtends φc φc' s.closures.size` says NOTHING about those
indices — the two `ValueRepr`s can disagree.

The genuine invariant of a well-formed spec store is that every closure reference
is in-bounds (it was returned by an earlier `allocClosure`).  We name it as the
named-field predicate `StoreClosuresBounded` (CLAUDE.md — named structure, never an
anonymous tower) and prove `storeRepr_phic_mono` under it.  `ValueRepr` mentions
`φc` ONLY in the `.closure ca` case, and `PhiExtends` pins `φc' ca = φc ca` for
`ca < s.closures.size`, so the bounded refs rebase verbatim; every other `StoreRepr`
field references `φc` only at indices `< s.closures.size`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Sim

