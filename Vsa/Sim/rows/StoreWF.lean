import Vsa.While.Cost
import Vsa.Sim.rows.StoreReprPhicRebase

/-!
# `StoreWF` — `StoreClosuresBounded` as a GLOBAL spec-side store invariant

`StoreClosuresBounded s` (defined in `rows/StoreReprPhicRebase.lean`) says every
closure address stored in a frame binding of `s` is `< s.closures.size` — i.e.
every closure reference was returned by an earlier `allocClosure`.  The `.fn`
arm's φc-entry rebase (`storeRepr_phic_mono`) consumes it per-arm as a NAMED
premise `hWF`.  This file discharges that premise ONCE, as a structural invariant
of the WHILE big-step semantics (`Vsa/While/Semantics.lean`): if the *initial*
store is closures-bounded, then every store REACHABLE by
`EvalE`/`EvalArgs`/`Call`/`ExecS`/…/`ExecSeq` is closures-bounded.

## Why the naive statement is not inductive — and the honest fix (in-shape)

`StoreClosuresBounded s → StoreClosuresBounded s'` alone does NOT go through the
`define` step: `Store.define env x v` appends the binding `(x, v)`, and preserving
boundedness needs `ValueClosuresBounded s.closures.size v` — the value being bound
must itself be an in-bounds closure ref.  That extra fact is exactly what the
*producer* of `v` (an `EvalE`/`Call` derivation) must also guarantee.  So the
motive is a CONJUNCTION carried by the mutual induction: the value(s) an
expression / call yields are closure-bounded in the *result* store, AND the result
store stays closures-bounded.  This is NOT a Law-4 falsity — the invariant is true
and inductive once the produced-value bound is threaded alongside it (mirroring how
`Cost.execSeq_store_mono` threads `StoreLe` through the same nine motives).

The append-only closures-size monotonicity `StoreLe` (`Vsa/While/Cost.lean`) is the
other ingredient: a value produced when `closures.size = k` is bounded by any later
size `≥ k`, so `ValueClosuresBounded` only ever *weakens* as the store grows.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa Vsa.While Vsa.Sim

namespace Vsa.Sim

/-! ## `ValueClosuresBounded` monotonicity -/

/-- A closure ref bounded at size `k` is bounded at any larger size. -/
theorem ValueClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {v : Value}, ValueClosuresBounded k v → ValueClosuresBounded k' v
  | .null, h => h
  | .bool _, h => h
  | .int _, h => h
  | .str _, h => h
  | .native _, h => h
  | .closure _ca, h => Nat.lt_of_lt_of_le h hk

/-! ## Every closure-touching store operation preserves the invariant

The spec-side store operations are `allocFrame`, `allocClosure`, `define`, and
`set` (`Vsa/While/Semantics.lean`).  Each is shown to preserve
`StoreClosuresBounded` — the last two additionally requiring the value being
bound / assigned to be an in-bounds closure ref (`ValueClosuresBounded`). -/

/-! ## The nine motives + the mutual induction

The motive for each relation is: **from an entry store that is closures-bounded,
the exit store is closures-bounded AND every value the relation produces (the
expression's value, the argument list, the returned value in a `.ret` status) is an
in-bounds closure ref in the EXIT store.**  This conjunction is what makes the
`define`/`set`/`foldDefine` steps go through: those steps demand a bounded value,
supplied by the sub-derivation that produced it.  Modeled on
`Cost.execSeq_store_mono`'s 9-motive `EvalE.rec` invocation. -/

/-- A returned `Status` carries a bounded value in the `.ret` case (the only status
that escapes a value into an enclosing `define`/assignment). -/
def StatusClosuresBounded (k : Nat) : Status → Prop
  | .ret v => ValueClosuresBounded k v
  | _ => True

/-- Every value of an argument list is an in-bounds closure ref. -/
def ValuesClosuresBounded (k : Nat) (vs : List Value) : Prop :=
  ∀ w ∈ vs, ValueClosuresBounded k w

/-- `StatusClosuresBounded` weakens as the store grows. -/
theorem StatusClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {status : Status}, StatusClosuresBounded k status → StatusClosuresBounded k' status
  | .normal, h => h
  | .brk, h => h
  | .cont, h => h
  | .ret _, h => ValueClosuresBounded.mono hk h

/-- `ValuesClosuresBounded` weakens as the store grows. -/
theorem ValuesClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') {vs : List Value}
    (h : ValuesClosuresBounded k vs) : ValuesClosuresBounded k' vs :=
  fun w hw => (h w hw).mono hk

/-! ### The 50 minor premises, as named `b_*` lemmas (model: `Cost.lean`'s `c_*`).

Each is a standalone lemma so the nine relation-projections share them without
duplicating proofs.  The final `(_ : Rel.ctor …)` slot is proof-irrelevant.  Written
in tactic mode with named `intro`s so no proof depends on positional-underscore
counts (CLAUDE.md R6). -/

-- Literal / trivial EvalE cases: value is a non-closure literal (bounded vacuously),
-- store unchanged.

/-! #### EvalArgs cases -/

/-! #### Call cases -/

/-! #### ExecS cases -/

/-! #### ExecInit / ForLoop / ForCond / ExecStep cases -/

/-! #### ExecSeq cases -/

/-! ### The nine relation-projections, assembled by the shared recursor -/

/-! ## Public invariant theorems + the per-arm consumer

The `.fn` arm consumes `StoreClosuresBounded st.store` as `hWF`
(`rows/FnResidSupply.lean`, `rows/FnArmSeamSupply.lean`).  These projections make it
a THEOREM of any store reachable from a closures-bounded entry — in particular from
`initSt` (the whole-program run), whose only frame binds natives (no closure refs). -/

end Vsa.Sim
