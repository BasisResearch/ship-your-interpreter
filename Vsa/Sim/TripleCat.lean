import Vsa.Triple

/-!
# `TripleCat` — the `Triple` consequence calculus, made first-class

`Vsa.Logic.Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'` is a **profunctor** over
the entailment preorder on `Config → Prop`: contravariant in the precondition,
covariant in the postcondition.  The consequence rule (`Triple.conseq`) IS the
profunctor's `dimap`.

This file makes that structure first-class WITHOUT any typeclass / category-theory
machinery (instance search is elaboration-hostile and gate-banned in spirit; the repo
is no-Mathlib).  The categorical structure is the SPEC; the implementation is plain
`def`s, one-field `structure`s, and directional lemmas.

## What is true for the ACTUAL `Triple` definition

`Triple P Q` is a **`Prop`**.  Consequently every "categorical law" that would be an
*equation between morphisms* in a category of data holds here **definitionally, by
proof irrelevance**: any two proofs of the same `Triple P Q` are equal.  So

* seq associativity  (`(a.seq b).seq c` vs `a.seq (b.seq c)`),
* dimap–seq interchange  (`dimap f g (a.seq b)` vs `(dimap f id a).seq (dimap id g b)`),
* dimap composition  (`dimap f g (dimap f' g' t)` vs `dimap (f'.trans f) (g.trans g') t`),
* dimap identity  (`dimap Ent.refl Ent.refl t` vs `t`)

are all `Eq.refl`-provable at `Prop` level (recorded below as `_law` lemmas, `@[simp]`).
The *useful* content is therefore not rewriting between equal proofs — it is the
**directional constructor** `Triple.dimap`, which lets an adapter be written as a single
`dimap` application instead of a hand-rolled `conseq`, and `PredIso`, which collapses an
adapter PAIR (`X_of_Y` + `Y_of_X`) into one iso with `transportPre`/`transportPost`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.Machine (Config)

namespace Vsa.Logic

/-! ## 1. Entailment: the preorder the profunctor acts over -/

/-- Entailment of configuration predicates: `P` entails `Q` when every `P`-config is a
`Q`-config.  This is exactly the shape of `Triple.conseq`'s side conditions
(`∀ c, P' c → P c` / `∀ c, Q c → Q' c`). -/
def Ent (P Q : Config → Prop) : Prop := ∀ c, P c → Q c

namespace Ent

/-- Reflexivity of entailment (the identity morphism of the preorder). -/
@[refl] theorem refl (P : Config → Prop) : Ent P P := fun _ h => h

/-- Transitivity of entailment (composition in the preorder). -/
theorem trans {P Q R : Config → Prop} (h₁ : Ent P Q) (h₂ : Ent Q R) : Ent P R :=
  fun c hc => h₂ c (h₁ c hc)

end Ent

/-- Composition notation for entailment (`P ⊢ₑ Q`).  Kept ASCII-adjacent and local. -/
scoped infixr:25 " ⊢ₑ " => Ent

namespace Triple

/-! ## 2. `Triple.dimap` — the canonical profunctor action (a thin `conseq` wrapper)

`conseq`'s argument order is `(triple) (pre) (post)`; `dimap` puts the two entailments
first (profunctor `dimap : (a' → a) → (b → b') → f a b → f a' b'`) so an adapter reads
`dimap hEntry hExit theCore`. -/

/-- The profunctor action: pull back the precondition along `pre : Ent P' P`, push
forward the postcondition along `post : Ent Q Q'`.  Definitionally `Triple.conseq` with
the entailments reassociated. -/
theorem dimap {P P' Q Q' : Config → Prop}
    (pre : Ent P' P) (post : Ent Q Q') (t : Triple P Q) : Triple P' Q' :=
  Triple.conseq t pre post

/-- Contravariant-only action (strengthen the precondition). -/
theorem lmap {P P' Q : Config → Prop} (pre : Ent P' P) (t : Triple P Q) : Triple P' Q :=
  dimap pre (Ent.refl Q) t

/-- Covariant-only action (weaken the postcondition). -/
theorem rmap {P Q Q' : Config → Prop} (post : Ent Q Q') (t : Triple P Q) : Triple P Q' :=
  dimap (Ent.refl P) post t

/-! ## 3. The profunctor / category laws — all `rfl` at `Prop` level (proof irrelevance)

Each is stated as an equation of proofs and closed by `Subsingleton.elim` (the two
sides inhabit the SAME `Triple _ _`, a `Prop`).  They are the machine-checked witnesses
that the calculus really is a profunctor; `@[simp]` normalises a compound adapter toward
its collapsed single-`dimap` form. -/

/-- `dimap` of identities is the identity (profunctor unit law). -/
@[simp] theorem dimap_id {P Q : Config → Prop} (t : Triple P Q) :
    dimap (Ent.refl P) (Ent.refl Q) t = t := Subsingleton.elim _ _

/-- `dimap` composition (profunctor functoriality): nested `dimap`s collapse to one along
the composed entailments.  This is the law that turns `dimap … (dimap … core)` towers
into a single application. -/
@[simp] theorem dimap_dimap {P P' P'' Q Q' Q'' : Config → Prop}
    (f' : Ent P' P) (g' : Ent Q Q') (f : Ent P'' P') (g : Ent Q' Q'')
    (t : Triple P Q) :
    dimap f g (dimap f' g' t) = dimap (Ent.trans f f') (Ent.trans g' g) t :=
  Subsingleton.elim _ _

/-- Sequencing is associative. -/
@[simp] theorem seq_assoc {P Q R S : Config → Prop}
    (a : Triple P Q) (b : Triple Q R) (c : Triple R S) :
    (a.seq b).seq c = a.seq (b.seq c) := Subsingleton.elim _ _

/-- dimap–seq interchange: a `dimap` around a `seq` splits into a `lmap` on the left
factor and an `rmap` on the right (the middle predicate `Q` is untouched).  This is the
law used to normalise `dimap f g (a ≫ b)`. -/
@[simp] theorem dimap_seq {P P' Q R R' : Config → Prop}
    (f : Ent P' P) (g : Ent R R') (a : Triple P Q) (b : Triple Q R) :
    dimap f g (a.seq b) = (lmap f a).seq (rmap g b) := Subsingleton.elim _ _

/-- `seq` respects `dimap` on the outside factors (a convenience corollary of
`dimap_seq`, kept as a directional builder). -/
theorem seq_dimap {P P' Q R R' : Config → Prop}
    (f : Ent P' P) (g : Ent R R') (a : Triple P Q) (b : Triple Q R) :
    Triple P' R' := dimap f g (a.seq b)

end Triple

/-! ## 4. `PredIso` — an adapter PAIR collapsed to one iso

Every `X_of_Y` + `Y_of_X` adapter pair in the codebase (e.g.
`armPostGeomV_of_ltResid` / `ltResid_of_armPostGeomV`) is exactly an isomorphism of
predicates.  `PredIso P Q` bundles the two entailments; `transportPre`/`transportPost`
apply it to a `Triple` (as `dimap`s), and it composes/inverts. -/

/-- An isomorphism of configuration predicates: mutually-entailing `P` and `Q`. -/
structure PredIso (P Q : Config → Prop) : Prop where
  to  : Ent P Q
  inv : Ent Q P

namespace PredIso

/-- The identity iso. -/
@[refl] theorem refl (P : Config → Prop) : PredIso P P := ⟨Ent.refl P, Ent.refl P⟩

/-- Swap the two directions. -/
theorem symm {P Q : Config → Prop} (h : PredIso P Q) : PredIso Q P := ⟨h.inv, h.to⟩

/-- Compose two isos. -/
theorem trans {P Q R : Config → Prop} (h₁ : PredIso P Q) (h₂ : PredIso Q R) :
    PredIso P R := ⟨Ent.trans h₁.to h₂.to, Ent.trans h₂.inv h₁.inv⟩

/-- Transport a triple's PRECONDITION along an iso: `Triple P R → Triple Q R` (uses the
`inv` direction, since `dimap` is contravariant in the precondition). -/
theorem transportPre {P Q R : Config → Prop} (h : PredIso P Q)
    (t : Triple P R) : Triple Q R := Triple.lmap h.inv t

/-- Transport a triple's POSTCONDITION along an iso: `Triple R P → Triple R Q` (uses the
`to` direction, covariant in the postcondition). -/
theorem transportPost {P Q R : Config → Prop} (h : PredIso P Q)
    (t : Triple R P) : Triple R Q := Triple.rmap h.to t

/-- Rewrite a predicate under an iso, as a plain implication (the `to` field, named). -/
theorem mp {P Q : Config → Prop} (h : PredIso P Q) : ∀ c, P c → Q c := h.to

/-- ... and the reverse. -/
theorem mpr {P Q : Config → Prop} (h : PredIso P Q) : ∀ c, Q c → P c := h.inv

end PredIso

end Vsa.Logic
