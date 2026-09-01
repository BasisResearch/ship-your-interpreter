import Vsa.RuntimeRepr
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

namespace Vsa.Sim

/-- A closure reference bound on a spec value: if `v` is `.closure ca`, then
`ca < size`.  (Every other variant carries no closure index.) -/
def ValueClosuresBounded (size : Nat) : Value → Prop
  | .closure ca => ca < size
  | _ => True

/-- **`StoreClosuresBounded s`** — every closure address stored in any frame
binding of `s` is `< s.closures.size` (it was returned by an earlier
`allocClosure`).  This is the well-formedness invariant that makes the closures
map monotone on the store's *own* references, so a `PhiExtends`-widening of `φc`
leaves `StoreRepr` intact.  Named-field structure per CLAUDE.md. -/
structure StoreClosuresBounded (s : Store) : Prop where
  bounded : ∀ fa, (h : fa < s.frames.size) →
    ∀ i, (hi : i < s.frames[fa].vars.length) →
      ValueClosuresBounded s.closures.size (s.frames[fa].vars[i].2)

/-- `ValueRepr` rebases under `PhiExtends` on the bounded closure references:
if the value's closure refs are `< size` and `φc'` agrees with `φc` below `size`,
then `ValueRepr … φc … v ↔`-carries to `ValueRepr … φc' … v`.  Only the `.closure`
case touches `φc`; the equality `φc' ca = φc ca` (from `PhiExtends`, `ca < size`)
makes the two representations defeq after rewriting. -/
theorem valueRepr_phic_mono
    {m : Mem} {N : NativeAddrs} {φc φc' : Addr → Nat} {size : Nat} {a : Nat} {v : Value}
    (hb : ValueClosuresBounded size v)
    (hpe : PhiExtends φc φc' size)
    (hv : ValueRepr m N φc a v) :
    ValueRepr m N φc' a v := by
  cases v with
  | null => exact hv
  | bool b => exact hv
  | int n => exact hv
  | str s => exact hv
  | native f => exact hv
  | closure ca =>
    -- `hb : ca < size`, so `φc' ca = φc ca`; rewrite the two closure reads.
    have hca : ca < size := hb
    have heq : φc' ca = φc ca := hpe ca hca
    obtain ⟨hkind, hread, hnz⟩ := hv
    refine ⟨hkind, ?_, ?_⟩
    · rw [heq]; exact hread
    · rw [heq]; exact hnz

/-- `FrameRepr` rebases under `PhiExtends`: the frame's `φc`-uses are exactly the
per-binding `ValueRepr … φc …`, each on a bounded closure ref, so each rebases via
`valueRepr_phic_mono`.  (`FrameRepr`'s other clauses — count/cap/names/parent — do
not mention `φc`.) -/
theorem frameRepr_phic_mono
    {m : Mem} {N : NativeAddrs} {φf φc φc' : Addr → Nat} {size : Nat} {e : Nat} {f : Frame}
    (hb : ∀ i, (hi : i < f.vars.length) → ValueClosuresBounded size (f.vars[i].2))
    (hpe : PhiExtends φc φc' size)
    (hf : FrameRepr m N φf φc e f) :
    FrameRepr m N φf φc' e f := by
  obtain ⟨hcount, hcap, ⟨pn, pv, hpn, hpv, hbind⟩, hparent⟩ := hf
  refine ⟨hcount, hcap, ⟨pn, pv, hpn, hpv, ?_⟩, hparent⟩
  intro i hi
  obtain ⟨hname, hval⟩ := hbind i hi
  exact ⟨hname, valueRepr_phic_mono (hb i hi) hpe hval⟩

/-- **`storeRepr_phic_mono`** — the φc-entry rebase.  Given the closures-in-bounds
invariant `StoreClosuresBounded s` and `PhiExtends φc φc' s.closures.size`, the store
representation is monotone in the closures map: `StoreRepr … φc s → StoreRepr … φc' s`.

The proof rebases each `StoreRepr` field.  `frames` goes through `frameRepr_phic_mono`
(the frame values are bounded by `StoreClosuresBounded`).  `closures`,
`φc_inj`, `closures_arena` reference `φc` only at indices `ca < s.closures.size`, where
`PhiExtends` gives `φc' ca = φc ca`, so they rebase verbatim.  `ClosureRepr` and the
`φf`-fields carry no `φc`. -/
theorem storeRepr_phic_mono
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc φc' : Addr → Nat} {s : Store}
    (hcb : StoreClosuresBounded s)
    (hpe : PhiExtends φc φc' s.closures.size)
    (hr : StoreRepr m N A φf φc s) :
    StoreRepr m N A φf φc' s where
  frames fa hfa :=
    frameRepr_phic_mono (hcb.bounded fa hfa) hpe (hr.frames fa hfa)
  closures ca hca := by
    -- `ClosureRepr` uses `φf` only, but the ARGUMENT is `φc ca`; rewrite `φc' ca = φc ca`.
    have heq : φc' ca = φc ca := hpe ca hca
    rw [heq]; exact hr.closures ca hca
  φf_inj := hr.φf_inj
  φc_inj a b ha hb hab := by
    -- rewrite both `φc' _ = φc _` (both indices `< size`), then use `hr.φc_inj`.
    have hea : φc' a = φc a := hpe a ha
    have heb : φc' b = φc b := hpe b hb
    rw [hea, heb] at hab
    exact hr.φc_inj a b ha hb hab
  frames_arena := hr.frames_arena
  closures_arena ca hca := by
    have heq : φc' ca = φc ca := hpe ca hca
    rw [heq]; exact hr.closures_arena ca hca

#print axioms valueRepr_phic_mono
#print axioms frameRepr_phic_mono
#print axioms storeRepr_phic_mono

end Vsa.Sim
