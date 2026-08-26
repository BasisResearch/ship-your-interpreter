import Vsa.Sim.Regions

/-!
# `GeomFacts` — a projected-record geometry discharge (M6 interface)

The Layer-4 simulation cases (`EvalEntry`/`ExecEntry` and their per-arm blocks)
each carry a heterogeneous bundle of *geometry residuals*: alignment, RAM/HTIF
bounds, and stack-window disjointness for the several fixed objects a case
touches (the function's own **code** region, the **AST node** it dispatches on,
the callee **code** regions, the caller-provided **buffer** (sret/retslot), the
dispatch **jump-table slot**), all measured against the C-stack scribble window
`[SL.lo, sp)`.

Every such residual is one of a *finite* set of shapes (the taxonomy below).
This module bundles the shapes into ONE projected record `GeomFacts`, so that:

* a case takes ONE `GeomFacts` hypothesis instead of ~15 loose geometry fields,
* every geometry residual becomes an O(1) field projection (`geom`), NO search,
* M6 derives ONE `GeomFacts` from the concrete `Layout` (`geomFacts_of_layout`)
  and hands it to every case.

This generalizes `Vsa.Sim.Regions.FixedMap` (which bundles the *block* geometry
of a freshly-written window) and follows the `ImageDischarge`/`ImageStaticsLoaded`
pattern ("ALL static-data hypotheses discharge from one predicate") extended from
the static bytes to ALL the geometry.

## The geometry-atom taxonomy (the finite recurring shapes)

Every geometry residual in the landed `EvalEntry`/`ExecEntry`/block bundles is an
instance of one of these, for some object region `obj = (lo, len)` and the
case's `SL`/`sp`:

| # | shape                                    | example fields                                   |
|---|------------------------------------------|--------------------------------------------------|
| A | `obj.lo % 8 = 0`  (align8)               | `expr_align`, `stmt_align`, `sret_align`         |
| B | RAM bounds `0x8..0 ≤ lo ∧ hi ≤ 0x1..0`   | `expr_ram`, `stmt_ram`, `sret_ram`, `stack_ram`  |
| C | above HTIF `tohostAddr+16 ≤ lo`          | `expr_win`, `stmt_win`, `sret_win`, `stack_win`  |
| D | disjoint from stack `[SL.lo, sp)`        | `expr_stack_disjoint`, `stmt_stack_disjoint`,    |
|   |   (`hi ≤ SL.lo ∨ sp ≤ lo`)               | `sret_stack_disjoint`, `code_stack_disjoint`,    |
|   |                                          | `vicode_stack_disjoint`, `table_stack_disjoint`  |
| E | disjoint object↔object                   | `sret_vicode_disjoint`, `sret_evalcode_disjoint` |
|   |   (`RDisjoint a b`)                       |                                                  |

Atoms A–D are the vast bulk (three per touched object: align, ram-window, stack).
`FixedMap` already packages A/B/C/E-against-a-fixed-region; `GeomFacts` adds the
D-against-the-live-stack-window orientation the cases actually carry (the stack is
`[SL.lo, sp)`, not a static region), and a *per-object* `ObjGeom` sub-record so a
case with N touched objects is N `ObjGeom`s + the stack facts, each an O(1) proj.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no search in `geom`.
-/

open Vsa Vsa.Alloc Vsa.MemRepr

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ObjGeom` — the geometry of ONE fixed object relative to the stack window

`ObjGeom obj SL sp` bundles the four recurring atoms (A–D) for a single object
region `obj = (lo, len)` touched by a case whose stack scribble is `[SL.lo, sp)`:
8-byte alignment, RAM containment, above-HTIF, and disjointness from the stack
window.  A case carries ONE `ObjGeom` per fixed object it loads/stores. -/
structure ObjGeom (obj : Region) (SL : StackLayout) (sp : Nat) : Prop where
  /-- (A) 8-byte alignment of the object base. -/
  align8 : obj.1 % 8 = 0
  /-- (B) The object lies in RAM `[0x80000000, 0x100000000)`. -/
  in_ram : RSub obj ramRegion
  /-- (C) The object is above the HTIF `tohost` window. -/
  above_tohost : tohostAddr + 16 ≤ obj.1
  /-- (D) The object is disjoint from the C-stack scribble window `[SL.lo, sp)`. -/
  stack_disjoint : obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1

/-! ### O(1) projections of `ObjGeom` (the `geom`-shaped exports)

Each is the exact residual shape a load/store site or a survival lemma consumes.
They are plain field projections (plus a trivial `omega`/`decide` massage where
the site wants `ramLo`/`ramHi` spelt as literals), so `geom` never searches. -/

/-- Alignment atom (A), field form. -/
theorem ObjGeom.align {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 % 8 = 0 := h.align8

/-- RAM lower bound (B): `0x80000000 ≤ obj.lo`. -/
theorem ObjGeom.ram_lo {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : 0x80000000 ≤ obj.1 := by
  have := h.in_ram; simp only [RSub, ramRegion, ramLo, ramHi] at this; omega

/-- RAM upper bound (B): `obj.lo + obj.len ≤ 0x100000000`. -/
theorem ObjGeom.ram_hi {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 + obj.2 ≤ 0x100000000 := by
  have := h.in_ram; simp only [RSub, ramRegion, ramLo, ramHi] at this; omega

/-- RAM bounds (B) as the conjunction the entry fields state. -/
theorem ObjGeom.ram {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : 0x80000000 ≤ obj.1 ∧ obj.1 + obj.2 ≤ 0x100000000 :=
  ⟨h.ram_lo, h.ram_hi⟩

/-- Above-HTIF atom (C), field form. -/
theorem ObjGeom.win {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : tohostAddr + 16 ≤ obj.1 := h.above_tohost

/-- Stack-disjointness atom (D), field form. -/
theorem ObjGeom.disj_stack {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1 := h.stack_disjoint

/-! ## `GeomFacts` — the whole-case geometry bundle

The stack-window itself (`[SL.lo, sp)`) carries the same B/C atoms (it is written
by the prologue spills), plus the `code ↔ stack` D-atom.  `GeomFacts` bundles:

* the stack-region facts (`stack_ram`, `stack_win`),
* the function's own `code ↔ stack` disjointness,
* and is *extended* per case by the `ObjGeom`s of the objects it touches.

A case's precondition becomes `GeomFacts code SL sp` + one `ObjGeom` per object;
M6 supplies all of them from the concrete `Layout`.  (The `code` region here is a
parameter: the codebase pins each function's own `[funcLo, funcHi)`, and there is
no single global text extent — see `Regions.FixedMap`'s header.) -/
structure GeomFacts (code : Region) (SL : StackLayout) (sp : Nat) : Prop where
  /-- The stack region is in RAM `[0x80000000, 0x100000000)`. -/
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  /-- The stack region is above the HTIF `tohost` window. -/
  stack_win : tohostAddr + 16 ≤ SL.lo
  /-- The function's code region is disjoint from the stack scribble `[SL.lo, sp)`. -/
  code_stack_disjoint : sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo

/-! ### O(1) projections of `GeomFacts`. -/

theorem GeomFacts.stackRam {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 := h.stack_ram

theorem GeomFacts.stackWin {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : tohostAddr + 16 ≤ SL.lo := h.stack_win

theorem GeomFacts.codeStk {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo :=
  h.code_stack_disjoint

/-! ## `LayoutGeomPred` + `geomFacts_of_layout` — the M6 derivation

M6 instantiates the abstract `Vsa.Refine.Layout` with concrete constants; the
concrete layout pins every region's `lo/len`.  `LayoutGeomPred` is the
`ImageStaticsLoaded`-style single predicate over those constants from which the
whole `GeomFacts` (and each `ObjGeom`) is derived by projection — mirroring
`imageStatics_*` deriving every static byte-pin from one `ImageStaticsLoaded`.

We state it region-generically (over the same `code`/`SL`/`sp` a case carries):
the predicate is literally the conjunction of the record's atoms, so
`geomFacts_of_layout` is a repackaging (the interesting content is that M6 proves
`LayoutGeomPred` ONCE from the numeric layout, then every case projects). -/
structure LayoutGeomPred (code : Region) (SL : StackLayout) (sp : Nat) : Prop where
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  code_stack_disjoint : sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo

/-- **The M6 interface.**  One `LayoutGeomPred` (proved once from the concrete
`Layout`) yields the `GeomFacts` every case projects.  Structurally trivial by
design — the point is that the *derivation site* is single (rule 6), not that the
repackaging is deep. -/
theorem geomFacts_of_layout {code : Region} {SL : StackLayout} {sp : Nat}
    (h : LayoutGeomPred code SL sp) : GeomFacts code SL sp :=
  ⟨h.stack_ram, h.stack_win, h.code_stack_disjoint⟩

/-- Companion: derive an `ObjGeom` from the raw atoms M6's layout pins for one
object (the per-object analog of `geomFacts_of_layout`).  A case's block helper
takes `ObjGeom obj SL sp` and projects; M6 builds it here from the numeric
layout facts.  Stated so `simp only [RSub, ramRegion]; omega` closes the `in_ram`
side from plain `lo`/`hi` bounds. -/
theorem objGeom_of_bounds {obj : Region} {SL : StackLayout} {sp : Nat}
    (halign : obj.1 % 8 = 0)
    (hlo : 0x80000000 ≤ obj.1) (hhi : obj.1 + obj.2 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ obj.1)
    (hstk : obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1) :
    ObjGeom obj SL sp :=
  ⟨halign, by simp only [RSub, ramRegion, ramLo, ramHi]; omega, hwin, hstk⟩

/-! ## `StackDisjoint` — the D-atom alone, for below-HTIF objects

The dispatch **jump table** is a `.rodata` object that sits BELOW the HTIF
window (`0x80019fb8 < tohostAddr`), so it does NOT satisfy the `above_tohost`
atom and is not a full `ObjGeom`.  But every object — table included — has the
D-atom (disjointness from the C-stack scribble `[SL.lo, sp)`), the only atom the
dispatch's slot-survival reasoning consumes.  `StackDisjoint` is the single-field
projected record for exactly that atom, so a below-HTIF object still discharges
its geometry residual by an O(1) projection. -/
structure StackDisjoint (lo len : Nat) (SL : StackLayout) (sp : Nat) : Prop where
  /-- (D) The `[lo, lo+len)` object is disjoint from the C-stack scribble
  window `[SL.lo, sp)`. -/
  stack_disjoint : lo + len ≤ SL.lo ∨ sp ≤ lo

/-- The D-atom projection.  Stated over `Nat` endpoints (not a `Region` pair) so
the projection type is *already* the site's residual shape — no `.1`/`.2` whnf,
so the discharge is a truly O(1) `exact`. -/
theorem StackDisjoint.disj {lo len : Nat} {SL : StackLayout} {sp : Nat}
    (h : StackDisjoint lo len SL sp) : lo + len ≤ SL.lo ∨ sp ≤ lo := h.stack_disjoint

/-- An `ObjGeom` (full A–D bundle) contains the D-atom, so it forgets to a
`StackDisjoint` — the two share the geometry vocabulary. -/
theorem ObjGeom.toStackDisjoint {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : StackDisjoint obj.1 obj.2 SL sp := ⟨h.stack_disjoint⟩

/-! ## Bridge to `Regions.FixedMap`

A case that already has a `FixedMap block code stack` (the freshly-written-block
bundle) can read an `ObjGeom` for the block off it, given the stack region is the
`[SL.lo, sp)` window (`stack = (SL.lo, sp - SL.lo)`).  This lets the block-writing
specs and the entry-geometry cases share ONE geometry vocabulary. -/
theorem ObjGeom.of_fixedMap {block code : Region} {SL : StackLayout} {sp : Nat}
    (h : FixedMap block code (SL.lo, sp - SL.lo)) (hsp : SL.lo ≤ sp) :
    ObjGeom block SL sp := by
  refine ⟨h.aligned, h.in_ram, h.above_tohost, ?_⟩
  have := h.stack_disjoint
  simp only [RDisjoint] at this
  omega

/-! ## `geom` — the O(1) discharge tactic

`geom` closes a geometry residual by field projection from an `ObjGeom`/`GeomFacts`
in context.  It is a thin ordered `first` over the projection lemmas — each branch
is a single `exact`/`apply` of a projection (no backtracking search, no `simp`
set, no `omega` fallback that could scan): the residual shape uniquely selects the
branch.  The `assumption`-fed hypothesis is the record; the projection picks the
field.

We keep it deliberately small and *non-searchy*: it tries the exact projection
lemmas in order and stops at the first that unifies.  A residual that is not one
of the taxonomy shapes falls through (the caller then discharges it explicitly),
so `geom` never silently does expensive work. -/
macro "geom" : tactic =>
  `(tactic|
    first
    | exact StackDisjoint.disj (by assumption)
    | exact ObjGeom.align (by assumption)
    | exact ObjGeom.win (by assumption)
    | exact ObjGeom.disj_stack (by assumption)
    | exact ObjGeom.ram_lo (by assumption)
    | exact ObjGeom.ram_hi (by assumption)
    | exact ObjGeom.ram (by assumption)
    | exact GeomFacts.stackWin (by assumption)
    | exact GeomFacts.stackRam (by assumption)
    | exact GeomFacts.codeStk (by assumption))

/-! ## `#print axioms` sanity examples

Each must depend only on `{propext, Classical.choice, Quot.sound}` — no
`sorry`/`axiom`/`native_decide`/`bv_decide`. -/

section Sanity

example (obj : Region) (SL : StackLayout) (sp : Nat) (h : ObjGeom obj SL sp) :
    obj.1 % 8 = 0 := by geom

example (obj : Region) (SL : StackLayout) (sp : Nat) (h : ObjGeom obj SL sp) :
    tohostAddr + 16 ≤ obj.1 := by geom

example (obj : Region) (SL : StackLayout) (sp : Nat) (h : ObjGeom obj SL sp) :
    obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1 := by geom

example (obj : Region) (SL : StackLayout) (sp : Nat) (h : ObjGeom obj SL sp) :
    0x80000000 ≤ obj.1 := by geom

example (code : Region) (SL : StackLayout) (sp : Nat) (h : GeomFacts code SL sp) :
    tohostAddr + 16 ≤ SL.lo := by geom

example (code : Region) (SL : StackLayout) (sp : Nat) (h : GeomFacts code SL sp) :
    sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo := by geom

example {code : Region} {SL : StackLayout} {sp : Nat} (h : LayoutGeomPred code SL sp) :
    GeomFacts code SL sp := geomFacts_of_layout h

example (lo len : Nat) (SL : StackLayout) (sp : Nat) (h : StackDisjoint lo len SL sp) :
    lo + len ≤ SL.lo ∨ sp ≤ lo := by geom

end Sanity

#print axioms ObjGeom.ram_lo
#print axioms ObjGeom.of_fixedMap
#print axioms geomFacts_of_layout
#print axioms objGeom_of_bounds

end Vsa.Sim
