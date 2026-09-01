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

/-- `StoreClosuresBounded` weakened along the append-only ordering: if `s` is
bounded and its closures array only grew to reach `s'`'s size, `s` is still bounded
at the larger size.  (Pure size-weakening of the per-binding refs; the frames are
`s`'s own.) -/
theorem StoreClosuresBounded.atSize {s : Store} {k : Nat}
    (hcb : StoreClosuresBounded s) (hk : s.closures.size ≤ k) :
    ∀ fa, (h : fa < s.frames.size) →
      ∀ i, (hi : i < s.frames[fa].vars.length) →
        ValueClosuresBounded k (s.frames[fa].vars[i].2) :=
  fun fa h i hi => (hcb.bounded fa h i hi).mono hk

/-- **Per-frame boundedness**, the pointwise content of `StoreClosuresBounded`:
every value in `f.vars` is an in-bounds closure ref at size `k`.  Introduced so
the store-op preservation proofs reason at the frame level (avoiding the
dependent-`getElem` rewrite that fails when the length proof mentions the frame). -/
def FrameClosuresBounded (k : Nat) (f : Frame) : Prop :=
  ∀ i, (hi : i < f.vars.length) → ValueClosuresBounded k (f.vars[i].2)

/-- `StoreClosuresBounded s ↔ every frame is `FrameClosuresBounded` at
`s.closures.size`. -/
theorem storeClosuresBounded_iff_frames {s : Store} :
    StoreClosuresBounded s ↔
      ∀ fa, (h : fa < s.frames.size) →
        FrameClosuresBounded s.closures.size (s.frames[fa]) :=
  ⟨fun hcb fa h => hcb.bounded fa h, fun h => ⟨h⟩⟩

/-- Transport per-frame boundedness across a frame equality (the clean way to move
a `getElem_push`/`getElem_modify` frame equation past the dependent length proof:
generalize the frame together with its length witness, then `subst`). -/
theorem FrameClosuresBounded.of_eq {k : Nat} {f g : Frame}
    (hfg : f = g) (hg : FrameClosuresBounded k g) : FrameClosuresBounded k f := by
  subst hfg; exact hg

/-- Membership form: any value in a bounded frame's bindings is bounded. -/
theorem FrameClosuresBounded.of_mem {k : Nat} {f : Frame} (hf : FrameClosuresBounded k f)
    {p : String × Value} (hp : p ∈ f.vars) : ValueClosuresBounded k p.2 := by
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  rw [← hpi]; exact hf i hi

/-- A value found by `Store.lookup` in a closures-bounded store is bounded: it is the
`.2` of some binding of a reachable frame, and `StoreClosuresBounded` bounds every
such binding.  (Gas-recursion over the parent chain.) -/
theorem StoreClosuresBounded.lookup_bounded {s : Store}
    (hcb : StoreClosuresBounded s) :
    ∀ (gas : Nat) (a : Addr) (x : String) (v : Value),
      s.lookup gas a x = some v → ValueClosuresBounded s.closures.size v := by
  intro gas
  induction gas with
  | zero => intro a x v h; exact absurd h (by simp [Store.lookup])
  | succ gas ih =>
    intro a x v h
    unfold Store.lookup at h
    cases hfa : s.frames[a]? with
    | none => rw [hfa] at h; exact absurd h (by simp)
    | some f =>
      rw [hfa] at h; simp only [bind, Option.bind] at h
      cases hfind : f.vars.find? (·.1 == x) with
      | none =>
        rw [hfind] at h; simp only at h
        cases hp : f.parent with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some pa => rw [hp] at h; exact ih pa x v h
      | some pr =>
        rw [hfind] at h
        -- `some (_, v)` matched; the found pair `pr` is a member of `f.vars`.
        obtain ⟨pn, pv⟩ := pr
        simp only at h; injection h with h; subst h
        have hmem : (pn, pv) ∈ f.vars := List.mem_of_find?_eq_some hfind
        -- frame `a` is reachable (`s.frames[a]? = some f`), hence bounded.
        obtain ⟨hain, hfget⟩ := Array.getElem?_eq_some_iff.mp hfa
        have hfb : FrameClosuresBounded s.closures.size f :=
          FrameClosuresBounded.of_eq hfget.symm (hcb.bounded a hain)
        exact hfb.of_mem hmem

/-- `get?` form of `lookup_bounded` (the `EvalE.var` rule's lookup). -/
theorem StoreClosuresBounded.get?_bounded {s : Store} {a : Addr} {x : String} {v : Value}
    (hcb : StoreClosuresBounded s) (h : s.get? a x = some v) :
    ValueClosuresBounded s.closures.size v :=
  hcb.lookup_bounded _ a x v h

/-! ## Every closure-touching store operation preserves the invariant

The spec-side store operations are `allocFrame`, `allocClosure`, `define`, and
`set` (`Vsa/While/Semantics.lean`).  Each is shown to preserve
`StoreClosuresBounded` — the last two additionally requiring the value being
bound / assigned to be an in-bounds closure ref (`ValueClosuresBounded`). -/

/-- `allocFrame` preserves boundedness: it pushes an EMPTY frame (no bindings) and
leaves the closures array untouched. -/
theorem StoreClosuresBounded.allocFrame {s s' : Store} {p : Option Addr} {a : Addr}
    (h : s.allocFrame p = (s', a)) (hcb : StoreClosuresBounded s) :
    StoreClosuresBounded s' := by
  have hs' : s' = { s with frames := s.frames.push ⟨p, []⟩ } := by
    have := congrArg Prod.fst h; simpa [Store.allocFrame] using this.symm
  subst hs'
  rw [storeClosuresBounded_iff_frames]
  intro fa hfa
  show FrameClosuresBounded s.closures.size _
  by_cases hlt : fa < s.frames.size
  · -- old frame: the pushed array agrees with `s.frames` below its size.
    exact FrameClosuresBounded.of_eq (Array.getElem_push_lt hlt)
      (fun i hi => hcb.bounded fa hlt i hi)
  · -- new frame: `fa = s.frames.size` (from `hfa`); the frame is the empty `⟨p,[]⟩`.
    have hfasz : fa = s.frames.size := by
      have : fa < s.frames.size + 1 := by
        rw [← Array.size_push (xs := s.frames) (v := ⟨p, []⟩)]; exact hfa
      omega
    subst hfasz
    exact FrameClosuresBounded.of_eq (g := ⟨p, []⟩) Array.getElem_push_eq
      (fun i hi => absurd hi (by simp))

/-- `allocClosure` preserves boundedness AND makes the whole store bounded at the
NEW (larger) size: it pushes a closure — frames unchanged — and grows
`closures.size` by one, so every pre-existing ref (bounded at the old size) is a
fortiori bounded at the new size (`ValueClosuresBounded.mono`). -/
theorem StoreClosuresBounded.allocClosure {s s' : Store} {c : ClosureData} {a : Addr}
    (h : s.allocClosure c = (s', a)) (hcb : StoreClosuresBounded s) :
    StoreClosuresBounded s' := by
  have hs' : s' = { s with closures := s.closures.push c } := by
    have := congrArg Prod.fst h; simpa [Store.allocClosure] using this.symm
  subst hs'
  rw [storeClosuresBounded_iff_frames]
  intro fa hfa
  -- frames are `s.frames`; closures grew by one, so the size-bound weakens.
  have hsz : s.closures.size ≤ (s.closures.push c).size := by
    rw [Array.size_push]; omega
  show FrameClosuresBounded (s.closures.push c).size _
  exact fun i hi => (hcb.bounded fa hfa i hi).mono hsz

/-- The value written by `Store.define` on a bound frame is bounded, provided the
bound value `v` is bounded and every existing value in the frame is bounded.  This
is the frame-local content of the `define` preservation: `defineFrame` either
overwrites the matching key with `v` (still bounded) or appends `(x, v)` (bounded);
every other slot is an old value (bounded by hypothesis). -/
theorem frameClosuresBounded_defineVars {k : Nat} {f : Frame} {x : String} {v : Value}
    (hf : FrameClosuresBounded k f) (hv : ValueClosuresBounded k v) :
    FrameClosuresBounded k
      { f with vars :=
        if f.vars.any (·.1 == x) then
          f.vars.map fun p => if p.1 == x then (x, v) else p
        else f.vars ++ [(x, v)] } := by
  show ∀ i, (hi : i < (if f.vars.any (·.1 == x) then
        f.vars.map fun p => if p.1 == x then (x, v) else p
      else f.vars ++ [(x, v)]).length) →
      ValueClosuresBounded k ((if f.vars.any (·.1 == x) then
        f.vars.map fun p => if p.1 == x then (x, v) else p
      else f.vars ++ [(x, v)])[i].2)
  by_cases hany : f.vars.any (·.1 == x)
  · rw [if_pos hany]
    -- mapped list: same length; each entry is either the old `.2` or `v`.
    intro i hi
    rw [List.length_map] at hi
    have hget : (f.vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [List.length_map]; exact hi)
        = (fun p => if p.1 == x then (x, v) else p) (f.vars[i]) := List.getElem_map _
    -- align the length-proof form and rewrite
    have : ((f.vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [List.length_map]; exact hi)).2
        = ((fun p => if p.1 == x then (x, v) else p) (f.vars[i])).2 := by rw [hget]
    rw [this]
    show ValueClosuresBounded k (if (f.vars[i]).1 == x then (x, v) else f.vars[i]).2
    by_cases hpi : (f.vars[i]).1 == x
    · rw [if_pos hpi]; exact hv
    · rw [if_neg hpi]; exact hf i hi
  · rw [if_neg hany]
    -- appended list: index either into the old vars or the singleton `[(x,v)]`.
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < f.vars.length
    · have hget : (f.vars ++ [(x, v)])[i]'(by rw [List.length_append, List.length_singleton]; omega)
          = f.vars[i] := List.getElem_append_left hlt
      have : ((f.vars ++ [(x, v)])[i]'(by rw [List.length_append, List.length_singleton]; omega)).2
          = (f.vars[i]).2 := by rw [hget]
      rw [this]; exact hf i hlt
    · -- i = f.vars.length: the appended `(x, v)`.
      have hie : i = f.vars.length := by omega
      subst hie
      have hget : (f.vars ++ [(x, v)])[f.vars.length]'(by rw [List.length_append, List.length_singleton]; omega)
          = (x, v) := by
        rw [List.getElem_append_right (by omega)]
        simp
      have : ((f.vars ++ [(x, v)])[f.vars.length]'(by rw [List.length_append, List.length_singleton]; omega)).2
          = v := by rw [hget]
      rw [this]; exact hv

/-- `define` preserves boundedness, given the bound value is an in-bounds closure
ref: it modifies the target frame's bindings via `defineFrame` (overwrite-or-append)
and leaves the closures array untouched. -/
theorem StoreClosuresBounded.define {s : Store} {a : Addr} {x : String} {v : Value}
    (hcb : StoreClosuresBounded s)
    (hv : ValueClosuresBounded s.closures.size v) :
    StoreClosuresBounded (s.define a x v) := by
  rw [storeClosuresBounded_iff_frames]
  intro fa hfa
  -- closures unchanged; frames modified only at `a`.
  have hcl : (s.define a x v).closures.size = s.closures.size := (define_size s a x v).2
  rw [hcl]
  have hfa' : fa < s.frames.size := (define_size s a x v).1 ▸ hfa
  by_cases hfaa : fa = a
  · subst hfaa
    -- touched frame: `defineFrame` of the pre frame.
    have heq : (s.define fa x v).frames[fa]'hfa
        = { s.frames[fa]'hfa' with vars :=
            if (s.frames[fa]'hfa').vars.any (·.1 == x) then
              (s.frames[fa]'hfa').vars.map fun p => if p.1 == x then (x, v) else p
            else (s.frames[fa]'hfa').vars ++ [(x, v)] } := by
      show (s.frames.modify fa fun f =>
          { f with vars := _ })[fa]'hfa = _
      rw [Array.getElem_modify]; rw [if_pos rfl]
    refine FrameClosuresBounded.of_eq heq ?_
    exact frameClosuresBounded_defineVars (fun i hi => hcb.bounded fa hfa' i hi) hv
  · -- other frame: unchanged.
    have heq : (s.define a x v).frames[fa]'hfa = s.frames[fa]'hfa' := by
      show (s.frames.modify a fun f => { f with vars := _ })[fa]'hfa = _
      rw [Array.getElem_modify]; rw [if_neg (fun h => hfaa h.symm)]
    exact FrameClosuresBounded.of_eq heq (fun i hi => hcb.bounded fa hfa' i hi)

/-- `set` (chain-walking assignment) preserves boundedness given the assigned value
is an in-bounds closure ref.  `set` rewrites at most one `vars` slot in place and
never touches the closures array (`set_preserves_size`), so the argument is the same
overwrite-preservation as `define` — but `set` is defined by gas recursion over the
parent chain, so we induct on the gas. -/
theorem StoreClosuresBounded.set {s s' : Store} {g : Nat} {a : Addr} {x : String} {v : Value}
    (hset : s.set g a x v = some s')
    (hcb : StoreClosuresBounded s)
    (hv : ValueClosuresBounded s.closures.size v) :
    StoreClosuresBounded s' := by
  induction g generalizing s a with
  | zero => exact absurd hset (by simp [Store.set])
  | succ g ih =>
    unfold Store.set at hset
    cases hfa : s.frames[a]? with
    | none => rw [hfa] at hset; exact absurd hset (by simp)
    | some f =>
      rw [hfa] at hset; simp only [bind, Option.bind] at hset
      by_cases hany : f.vars.any (·.1 == x)
      · rw [if_pos hany] at hset
        injection hset with hset; subst hset
        -- s' = s with frame `a` overwritten (matching-key map). Closures untouched.
        rw [storeClosuresBounded_iff_frames]
        intro fa hfa2
        have hcleq : ({ s with frames := s.frames.modify a fun f =>
            { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } } : Store).closures.size
            = s.closures.size := rfl
        rw [hcleq]
        have hfa2' : fa < s.frames.size := by
          have : fa < (s.frames.modify a _).size := hfa2
          rwa [Array.size_modify] at this
        by_cases hfaa : fa = a
        · subst hfaa
          have heq : ({ s with frames := s.frames.modify fa fun f =>
              { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } } : Store).frames[fa]'hfa2
              = { s.frames[fa]'hfa2' with vars :=
                  (s.frames[fa]'hfa2').vars.map fun p => if p.1 == x then (x, v) else p } := by
            show (s.frames.modify fa fun f => { f with vars := _ })[fa]'hfa2 = _
            rw [Array.getElem_modify]; rw [if_pos rfl]
          refine FrameClosuresBounded.of_eq heq ?_
          -- overwrite: same as the `any`-branch of defineVars.
          intro i hi
          rw [List.length_map] at hi
          have hget : ((s.frames[fa]'hfa2').vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [List.length_map]; exact hi)
              = (fun p => if p.1 == x then (x, v) else p) ((s.frames[fa]'hfa2').vars[i]) := List.getElem_map _
          have : (((s.frames[fa]'hfa2').vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [List.length_map]; exact hi)).2
              = ((fun p => if p.1 == x then (x, v) else p) ((s.frames[fa]'hfa2').vars[i])).2 := by rw [hget]
          rw [this]
          show ValueClosuresBounded s.closures.size (if ((s.frames[fa]'hfa2').vars[i]).1 == x then (x, v) else (s.frames[fa]'hfa2').vars[i]).2
          by_cases hpi : ((s.frames[fa]'hfa2').vars[i]).1 == x
          · rw [if_pos hpi]; exact hv
          · rw [if_neg hpi]; exact hcb.bounded fa hfa2' i hi
        · have heq : ({ s with frames := s.frames.modify a fun f =>
              { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } } : Store).frames[fa]'hfa2
              = s.frames[fa]'hfa2' := by
            show (s.frames.modify a fun f => { f with vars := _ })[fa]'hfa2 = _
            rw [Array.getElem_modify]; rw [if_neg (fun h => hfaa h.symm)]
          exact FrameClosuresBounded.of_eq heq (fun i hi => hcb.bounded fa hfa2' i hi)
      · rw [if_neg hany] at hset
        cases hp : f.parent with
        | none => rw [hp] at hset; exact absurd hset (by simp)
        | some p =>
          rw [hp] at hset
          change s.set g p x v = some s' at hset
          exact ih hset hcb hv

/-- Folding `define` over a list of bindings preserves boundedness, given every
bound value is an in-bounds closure ref.  The fold threads the store, but `define`
never changes `closures.size`, so the size — hence every value's bound — is constant
across the whole fold.  This is exactly `Call.closure`'s parameter-binding fold. -/
theorem StoreClosuresBounded.foldDefine {frame : Addr} :
    ∀ (l : List (String × Value)) {s : Store}
      (hcb : StoreClosuresBounded s)
      (hvs : ∀ p ∈ l, ValueClosuresBounded s.closures.size p.2),
      StoreClosuresBounded (l.foldl (fun s (x, v) => s.define frame x v) s)
  | [], _, hcb, _ => hcb
  | (x, v) :: rest, s, hcb, hvs => by
    simp only [List.foldl_cons]
    have hvhead : ValueClosuresBounded s.closures.size v := hvs (x, v) (by simp)
    have hcb' : StoreClosuresBounded (s.define frame x v) := hcb.define hvhead
    have hcleq : (s.define frame x v).closures.size = s.closures.size := (define_size s frame x v).2
    refine StoreClosuresBounded.foldDefine rest hcb' ?_
    intro p hp
    rw [hcleq]
    exact hvs p (by simp [hp])

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

private def P1 st d a e st' v (_ : EvalE st d a e st' v) : Prop :=
  StoreClosuresBounded st.store →
    StoreClosuresBounded st'.store ∧ ValueClosuresBounded st'.store.closures.size v
private def P2 st d a es st' vs (_ : EvalArgs st d a es st' vs) : Prop :=
  StoreClosuresBounded st.store →
    StoreClosuresBounded st'.store ∧ ValuesClosuresBounded st'.store.closures.size vs
private def P3 st d fv vs st' v (_ : Call st d fv vs st' v) : Prop :=
  StoreClosuresBounded st.store → ValuesClosuresBounded st.store.closures.size vs →
    StoreClosuresBounded st'.store ∧ ValueClosuresBounded st'.store.closures.size v
private def P4 st d a s st' status (_ : ExecS st d a s st' status) : Prop :=
  StoreClosuresBounded st.store →
    StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status
private def P5 st d a init st' (_ : ExecInit st d a init st') : Prop :=
  StoreClosuresBounded st.store → StoreClosuresBounded st'.store
private def P6 st d a cnd step b st' status (_ : ForLoop st d a cnd step b st' status) : Prop :=
  StoreClosuresBounded st.store →
    StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status
private def P7 st d a cnd st' (_ : ForCond st d a cnd st') : Prop :=
  StoreClosuresBounded st.store → StoreClosuresBounded st'.store
private def P8 st d a step st' (_ : ExecStep st d a step st') : Prop :=
  StoreClosuresBounded st.store → StoreClosuresBounded st'.store
private def P9 st d a ss st' status (_ : ExecSeq st d a ss st' status) : Prop :=
  StoreClosuresBounded st.store →
    StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status

/-- Closures-size monotonicity extracted from `StoreLe` (`Cost`), specialised to a
single relation whose store-mono is already proved.  Used to weaken a produced
value's bound from an earlier store to a later one. -/
theorem closures_size_le_of_storeLe {a b : Store} (h : StoreLe a b) :
    a.closures.size ≤ b.closures.size := h.2

/-! ### The 50 minor premises, as named `b_*` lemmas (model: `Cost.lean`'s `c_*`).

Each is a standalone lemma so the nine relation-projections share them without
duplicating proofs.  The final `(_ : Rel.ctor …)` slot is proof-irrelevant.  Written
in tactic mode with named `intro`s so no proof depends on positional-underscore
counts (CLAUDE.md R6). -/

-- Literal / trivial EvalE cases: value is a non-closure literal (bounded vacuously),
-- store unchanged.
private theorem b_int : ∀ st d env n, P1 st d env (.int n) st (.int n) (.int ..) :=
  fun _ _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_str : ∀ st d env s, P1 st d env (.str s) st (.str s) (.str ..) :=
  fun _ _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_bool : ∀ st d env b, P1 st d env (.bool b) st (.bool b) (.bool ..) :=
  fun _ _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_null : ∀ st d env, P1 st d env .null st .null (.null ..) :=
  fun _ _ _ hcb => ⟨hcb, trivial⟩

/-- Weaken a value bound along a `StoreLe` (later store, larger closures array). -/
private theorem vcbWeaken {a b : Store} {v : Value} (hab : StoreLe a b)
    (hv : ValueClosuresBounded a.closures.size v) :
    ValueClosuresBounded b.closures.size v :=
  hv.mono (closures_size_le_of_storeLe hab)

private theorem b_var : ∀ st d env x v (hv : st.store.get? env x = some v),
    P1 st d env (.var x) st v (.var st d env x v hv) := by
  intro st d env x v hv hcb
  exact ⟨hcb, hcb.get?_bounded hv⟩
private theorem b_assign : ∀ st d env x e st' v store''
    (he : EvalE st d env e st' v) (hs : st'.store.set? env x v = some store''),
    P1 st d env e st' v he →
    P1 st d env (.assign x e) ⟨store'', st'.out⟩ v (.assign st d env x e st' v store'' he hs) := by
  intro st d env x e st' v store'' he hs ih hcb
  obtain ⟨hcb', hv⟩ := ih hcb
  -- set? preserves closures.size; the assigned value `v` is bounded (from `ih`).
  obtain ⟨-, hcleq⟩ := set_preserves_size _ st'.store env x v store'' hs
  have hcb'' : StoreClosuresBounded store'' := hcb'.set hs hv
  refine ⟨hcb'', ?_⟩
  show ValueClosuresBounded store''.closures.size v
  rw [hcleq]; exact hv
private theorem b_bin : ∀ st d env op l r st' st'' lv rv v
    (hl : EvalE st d env l st' lv) (hr : EvalE st' d env r st'' rv)
    (hop : binOpSem st''.store op lv rv = some v),
    P1 st d env l st' lv hl → P1 st' d env r st'' rv hr →
    P1 st d env (.binary op l r) st'' v (.binary st d env op l r st' st'' lv rv v hl hr hop) := by
  intro st d env op l r st' st'' lv rv v hl hr hop ihl ihr hcb
  obtain ⟨hcbl, _⟩ := ihl hcb
  obtain ⟨hcbr, _⟩ := ihr hcbl
  -- the binop result `v` is a fresh int/bool/str (never a closure): bounded vacuously.
  refine ⟨hcbr, ?_⟩
  -- `binOpSem` produces only `.int`/`.bool`/`.str` (no `.closure`).
  cases v with
  | closure ca =>
    -- impossible: `binOpSem` never returns a closure. Refute from `hop`.
    exact absurd hop (by
      cases op <;> cases lv <;> cases rv <;> simp_all [binOpSem])
  | _ => trivial
private theorem b_ort : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true),
    P1 st d env l st' lv hl →
    P1 st d env (.logical .or l r) st' (.bool true) (.orTrue st d env l r st' lv hl ht) := by
  intro st d env l r st' lv hl ht ih hcb
  obtain ⟨hcbl, _⟩ := ih hcb
  exact ⟨hcbl, trivial⟩
private theorem b_orf : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false) (hr : EvalE st' d env r st'' rv),
    P1 st d env l st' lv hl → P1 st' d env r st'' rv hr →
    P1 st d env (.logical .or l r) st'' (.bool rv.truthy) (.orFalse st d env l r st' st'' lv rv hl hf hr) := by
  intro st d env l r st' st'' lv rv hl hf hr ihl ihr hcb
  obtain ⟨hcbl, _⟩ := ihl hcb
  obtain ⟨hcbr, _⟩ := ihr hcbl
  exact ⟨hcbr, trivial⟩
private theorem b_anf : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false),
    P1 st d env l st' lv hl →
    P1 st d env (.logical .and l r) st' (.bool false) (.andFalse st d env l r st' lv hl hf) := by
  intro st d env l r st' lv hl hf ih hcb
  obtain ⟨hcbl, _⟩ := ih hcb
  exact ⟨hcbl, trivial⟩
private theorem b_ant : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true) (hr : EvalE st' d env r st'' rv),
    P1 st d env l st' lv hl → P1 st' d env r st'' rv hr →
    P1 st d env (.logical .and l r) st'' (.bool rv.truthy) (.andTrue st d env l r st' st'' lv rv hl ht hr) := by
  intro st d env l r st' st'' lv rv hl ht hr ihl ihr hcb
  obtain ⟨hcbl, _⟩ := ihl hcb
  obtain ⟨hcbr, _⟩ := ihr hcbl
  exact ⟨hcbr, trivial⟩
private theorem b_neg : ∀ st d env e st' n (he : EvalE st d env e st' (.int n)),
    P1 st d env e st' (.int n) he →
    P1 st d env (.unary .neg e) st' (.int (wrap64 (-n))) (.neg st d env e st' n he) := by
  intro st d env e st' n he ih hcb
  obtain ⟨hcb', _⟩ := ih hcb
  exact ⟨hcb', trivial⟩
private theorem b_not : ∀ st d env e st' v (he : EvalE st d env e st' v),
    P1 st d env e st' v he →
    P1 st d env (.unary .not e) st' (.bool (!v.truthy)) (.not st d env e st' v he) := by
  intro st d env e st' v he ih hcb
  obtain ⟨hcb', _⟩ := ih hcb
  exact ⟨hcb', trivial⟩
private theorem b_call : ∀ st d env f args st' st'' st''' fv vs v
    (hf : EvalE st d env f st' fv) (ha : EvalArgs st' d env args st'' vs)
    (hc : Call st'' d fv vs st''' v),
    P1 st d env f st' fv hf → P2 st' d env args st'' vs ha → P3 st'' d fv vs st''' v hc →
    P1 st d env (.call f args) st''' v (.call st d env f args st' st'' st''' fv vs v hf ha hc) := by
  intro st d env f args st' st'' st''' fv vs v hf ha hc ihf iha ihc hcb
  obtain ⟨hcbf, _⟩ := ihf hcb
  obtain ⟨hcba, hvs⟩ := iha hcbf
  exact ihc hcba hvs
private theorem b_fn : ∀ st d env name params body store' a
    (hc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)),
    P1 st d env (.fn name params body) ⟨store', st.out⟩ (.closure a)
      (.fn st d env name params body store' a hc) := by
  intro st d env name params body store' a hc hcb
  -- the returned value is `.closure a` where `a = st.store.closures.size` and the
  -- new store has `closures.size = a + 1`, so `a < size'`.
  have hcb' : StoreClosuresBounded store' := hcb.allocClosure hc
  have ha : a = st.store.closures.size := by
    have := congrArg Prod.snd hc; simpa [Store.allocClosure] using this.symm
  have hsz : store'.closures = st.store.closures.push ⟨env, name, params, body⟩ := by
    have := congrArg Prod.fst hc; simpa [Store.allocClosure] using congrArg Store.closures this.symm
  subst ha
  refine ⟨hcb', ?_⟩
  show ValueClosuresBounded store'.closures.size (.closure st.store.closures.size)
  show st.store.closures.size < store'.closures.size
  have hstep : store'.closures.size = st.store.closures.size + 1 := by rw [hsz, Array.size_push]
  omega

/-! #### EvalArgs cases -/

private theorem b_anil : ∀ st d env, P2 st d env [] st [] (.nil ..) :=
  fun _ _ _ hcb => ⟨hcb, fun _ hw => absurd hw (by simp)⟩
private theorem b_acons : ∀ st d env e es st' st'' v vs
    (he : EvalE st d env e st' v) (hes : EvalArgs st' d env es st'' vs),
    P1 st d env e st' v he → P2 st' d env es st'' vs hes →
    P2 st d env (e :: es) st'' (v :: vs) (.cons st d env e es st' st'' v vs he hes) := by
  intro st d env e es st' st'' v vs he hes ihe ihes hcb
  obtain ⟨hcbe, hv⟩ := ihe hcb
  obtain ⟨hcbes, hvs⟩ := ihes hcbe
  refine ⟨hcbes, ?_⟩
  -- head value `v` bounded at `st'`, weaken to `st''` (store grew across `es`).
  intro w hw
  rcases List.mem_cons.mp hw with hwv | hwvs
  · subst hwv; exact vcbWeaken (evalArgs_store_mono hes) hv
  · exact hvs w hwvs

/-! #### Call cases -/

private theorem b_clo : ∀ st d a cd vs store' frame st' status v
    (hc : st.store.closures[a]? = some cd) (hlen : vs.length = cd.params.length)
    (hd : d < maxCallDepth) (hf : st.store.allocFrame (some cd.env) = (store', frame))
    (hst : ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status)
    (hstat : status = .normal ∧ v = .null ∨ status = .ret v),
    P9 ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status hst →
    P3 st d (.closure a) vs st' v
      (.closure st d a cd vs store' frame st' status v hc hlen hd hf hst hstat) := by
  intro st d a cd vs store' frame st' status v hc hlen hd hf hst hstat ihb hcb hvs
  -- Step 1: allocFrame preserves WF and closures.size.
  have hcbAF : StoreClosuresBounded store' := hcb.allocFrame hf
  have hstore' : store' = { st.store with frames := st.store.frames.push ⟨some cd.env, []⟩ } := by
    have := congrArg Prod.fst hf; simpa [Store.allocFrame] using this.symm
  have hAFsz : store'.closures.size = st.store.closures.size := by rw [hstore']
  -- Step 2: the param-bind fold preserves WF (each `vs` value bounded at store'.size).
  have hvs' : ∀ p ∈ cd.params.zip vs, ValueClosuresBounded store'.closures.size p.2 := by
    intro p hp
    rw [hAFsz]
    -- `p.2` is a member of `vs` (it is the snd of a zipped pair).
    have : p.2 ∈ vs := by
      have := List.of_mem_zip hp
      exact this.2
    exact hvs p.2 this
  have hcbFold : StoreClosuresBounded
      ((cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store') :=
    hcbAF.foldDefine _ hvs'
  -- Step 3: run the body; the exit store is WF and the status is bounded.
  obtain ⟨hcbBody, hstatB⟩ := ihb hcbFold
  refine ⟨hcbBody, ?_⟩
  -- Step 4: the returned value `v` is bounded at the exit store.
  rcases hstat with ⟨-, hvnull⟩ | hret
  · subst hvnull; trivial
  · -- status = .ret v, so `StatusClosuresBounded … status = ValueClosuresBounded … v`.
    have : StatusClosuresBounded st'.store.closures.size (.ret v) := hret ▸ hstatB
    exact this
private theorem b_pr : ∀ st d vs,
    P3 st d (.native .print) vs ⟨st.store, st.out ++ printArgs st.store vs⟩ .null (.print ..) :=
  fun _ _ _ hcb _ => ⟨hcb, trivial⟩
private theorem b_prl : ∀ st d vs,
    P3 st d (.native .println) vs ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null
      (.println ..) :=
  fun _ _ _ hcb _ => ⟨hcb, trivial⟩
private theorem b_as : ∀ st d vs v m (hvs : vs = [v] ∨ vs = [v, m]) (ht : v.truthy = true),
    P3 st d (.native .assert) vs st .null (.assertOk st d vs v m hvs ht) :=
  fun _ _ _ _ _ _ _ hcb _ => ⟨hcb, trivial⟩

/-! #### ExecS cases -/

private theorem b_sexpr : ∀ st d env e st' v (he : EvalE st d env e st' v),
    P1 st d env e st' v he → P4 st d env (.expr e) st' .normal (.expr st d env e st' v he) := by
  intro st d env e st' v he ih hcb
  obtain ⟨hcb', _⟩ := ih hcb
  exact ⟨hcb', trivial⟩
private theorem b_svi : ∀ st d env x e st' v (he : EvalE st d env e st' v),
    P1 st d env e st' v he →
    P4 st d env (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩ .normal
      (.varInit st d env x e st' v he) := by
  intro st d env x e st' v he ih hcb
  obtain ⟨hcb', hv⟩ := ih hcb
  -- define with the evaluated value (bounded by `ih`): preserves WF, closures.size const.
  exact ⟨hcb'.define hv, trivial⟩
private theorem b_svn : ∀ st d env x,
    P4 st d env (.varDecl x none) ⟨st.store.define env x .null, st.out⟩ .normal (.varNull ..) := by
  intro st d env x hcb
  -- define with `.null` (vacuously bounded).
  exact ⟨hcb.define trivial, trivial⟩
private theorem b_sblk : ∀ st d env ss store' inner st' status
    (hf : st.store.allocFrame (some env) = (store', inner))
    (hseq : ExecSeq ⟨store', st.out⟩ d inner ss st' status),
    P9 ⟨store', st.out⟩ d inner ss st' status hseq →
    P4 st d env (.block ss) st' status (.block st d env ss store' inner st' status hf hseq) := by
  intro st d env ss store' inner st' status hf hseq ih hcb
  exact ih (hcb.allocFrame hf)
private theorem b_sift : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hs : ExecS st' d env t st'' status),
    P1 st d env c st' v hc → P4 st' d env t st'' status hs →
    P4 st d env (.ifStmt c t e) st'' status (.ifTrue st d env c t e st' st'' v status hc ht hs) := by
  intro st d env c t e st' st'' v status hc ht hs ihc iht hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact iht hcbc
private theorem b_siff : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (hf : v.truthy = false) (hs : ExecS st' d env e st'' status),
    P1 st d env c st' v hc → P4 st' d env e st'' status hs →
    P4 st d env (.ifStmt c t (some e)) st'' status (.ifFalse st d env c t e st' st'' v status hc hf hs) := by
  intro st d env c t e st' st'' v status hc hf hs ihc ihe hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact ihe hcbc
private theorem b_sifn : ∀ st d env c t st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    P1 st d env c st' v hc →
    P4 st d env (.ifStmt c t none) st' .normal (.ifNone st d env c t st' v hc hf) := by
  intro st d env c t st' v hc hf ihc hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact ⟨hcbc, trivial⟩
private theorem b_swf : ∀ st d env c b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    P1 st d env c st' v hc →
    P4 st d env (.whileStmt c b) st' .normal (.whileFalse st d env c b st' v hc hf) := by
  intro st d env c b st' v hc hf ihc hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact ⟨hcbc, trivial⟩
private theorem b_swb : ∀ st d env c b st' st'' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' .brk),
    P1 st d env c st' v hc → P4 st' d env b st'' .brk hb →
    P4 st d env (.whileStmt c b) st'' .normal (.whileBreak st d env c b st' st'' v hc ht hb) := by
  intro st d env c b st' st'' v hc ht hb ihc ihb hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  obtain ⟨hcbb, _⟩ := ihb hcbc
  exact ⟨hcbb, trivial⟩
private theorem b_swr : ∀ st d env c b st' st'' v rv
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' (.ret rv)),
    P1 st d env c st' v hc → P4 st' d env b st'' (.ret rv) hb →
    P4 st d env (.whileStmt c b) st'' (.ret rv) (.whileRet st d env c b st' st'' v rv hc ht hb) := by
  intro st d env c b st' st'' v rv hc ht hb ihc ihb hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact ihb hcbc
private theorem b_swl : ∀ st d env c b st' st'' st''' v status status'
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont)
    (hr : ExecS st'' d env (.whileStmt c b) st''' status'),
    P1 st d env c st' v hc → P4 st' d env b st'' status hb →
    P4 st'' d env (.whileStmt c b) st''' status' hr →
    P4 st d env (.whileStmt c b) st''' status'
      (.whileLoop st d env c b st' st'' st''' v status status' hc ht hb hstat hr) := by
  intro st d env c b st' st'' st''' v status status' hc ht hb hstat hr ihc ihb ihr hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  obtain ⟨hcbb, _⟩ := ihb hcbc
  exact ihr hcbb
private theorem b_sfor : ∀ st d env init cnd step b store' outer st' st'' status
    (hf : st.store.allocFrame (some env) = (store', outer))
    (hi : ExecInit ⟨store', st.out⟩ d outer init st')
    (hl : ForLoop st' d outer cnd step b st'' status),
    P5 ⟨store', st.out⟩ d outer init st' hi → P6 st' d outer cnd step b st'' status hl →
    P4 st d env (.forStmt init cnd step b) st'' status
      (.forStart st d env init cnd step b store' outer st' st'' status hf hi hl) := by
  intro st d env init cnd step b store' outer st' st'' status hf hi hl ihi ihl hcb
  have hcbi := ihi (hcb.allocFrame hf)
  exact ihl hcbi
private theorem b_sret : ∀ st d env e st' v (he : EvalE st d env e st' v),
    P1 st d env e st' v he → P4 st d env (.ret (some e)) st' (.ret v) (.ret st d env e st' v he) := by
  intro st d env e st' v he ih hcb
  obtain ⟨hcb', hv⟩ := ih hcb
  -- status is `.ret v`; `StatusClosuresBounded … (.ret v) = ValueClosuresBounded … v`.
  exact ⟨hcb', hv⟩
private theorem b_srn : ∀ st d env, P4 st d env (.ret none) st (.ret .null) (.retNull ..) :=
  fun _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_sbrk : ∀ st d env, P4 st d env .brk st .brk (.brk ..) :=
  fun _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_scont : ∀ st d env, P4 st d env .cont st .cont (.cont ..) :=
  fun _ _ _ hcb => ⟨hcb, trivial⟩

/-! #### ExecInit / ForLoop / ForCond / ExecStep cases -/

private theorem b_inone : ∀ st d env, P5 st d env none st (.none ..) :=
  fun _ _ _ hcb => hcb
private theorem b_isome : ∀ st d env s st' status (hs : ExecS st d env s st' status),
    P4 st d env s st' status hs →
    P5 st d env (some s) st' (.some st d env s st' status hs) := by
  intro st d env s st' status hs ih hcb
  exact (ih hcb).1
private theorem b_lcf : ∀ st d env c step b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    P1 st d env c st' v hc →
    P6 st d env (some c) step b st' .normal (.condFalse st d env c step b st' v hc hf) := by
  intro st d env c step b st' v hc hf ihc hcb
  obtain ⟨hcbc, _⟩ := ihc hcb
  exact ⟨hcbc, trivial⟩
private theorem b_lbb : ∀ st d env cnd step b st' st''
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' .brk),
    P7 st d env cnd st' hcond → P4 st' d env b st'' .brk hb →
    P6 st d env cnd step b st'' .normal (.bodyBreak st d env cnd step b st' st'' hcond hb) := by
  intro st d env cnd step b st' st'' hcond hb ihc ihb hcb
  have hcbc := ihc hcb
  obtain ⟨hcbb, _⟩ := ihb hcbc
  exact ⟨hcbb, trivial⟩
private theorem b_lbr : ∀ st d env cnd step b st' st'' rv
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' (.ret rv)),
    P7 st d env cnd st' hcond → P4 st' d env b st'' (.ret rv) hb →
    P6 st d env cnd step b st'' (.ret rv) (.bodyRet st d env cnd step b st' st'' rv hcond hb) := by
  intro st d env cnd step b st' st'' rv hcond hb ihc ihb hcb
  have hcbc := ihc hcb
  exact ihb hcbc
private theorem b_lloop : ∀ st d env cnd step b st' st'' st''' st'''' status status'
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont) (hs : ExecStep st'' d env step st''')
    (hr : ForLoop st''' d env cnd step b st'''' status'),
    P7 st d env cnd st' hcond → P4 st' d env b st'' status hb →
    P8 st'' d env step st''' hs → P6 st''' d env cnd step b st'''' status' hr →
    P6 st d env cnd step b st'''' status'
      (.loop st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr) := by
  intro st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr ihc ihb ihs ihr hcb
  have hcbc := ihc hcb
  obtain ⟨hcbb, _⟩ := ihb hcbc
  have hcbs := ihs hcbb
  exact ihr hcbs
private theorem b_cnone : ∀ st d env, P7 st d env none st (.none ..) :=
  fun _ _ _ hcb => hcb
private theorem b_csome : ∀ st d env c st' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true),
    P1 st d env c st' v hc → P7 st d env (some c) st' (.some st d env c st' v hc ht) := by
  intro st d env c st' v hc ht ihc hcb
  exact (ihc hcb).1
private theorem b_stnone : ∀ st d env, P8 st d env none st (.none ..) :=
  fun _ _ _ hcb => hcb
private theorem b_stsome : ∀ st d env e st' v (he : EvalE st d env e st' v),
    P1 st d env e st' v he → P8 st d env (some e) st' (.some st d env e st' v he) := by
  intro st d env e st' v he ih hcb
  exact (ih hcb).1

/-! #### ExecSeq cases -/

private theorem b_qnil : ∀ st d env, P9 st d env [] st .normal (.nil ..) :=
  fun _ _ _ hcb => ⟨hcb, trivial⟩
private theorem b_qcn : ∀ st d env s ss st' st'' status
    (hs : ExecS st d env s st' .normal) (hss : ExecSeq st' d env ss st'' status),
    P4 st d env s st' .normal hs → P9 st' d env ss st'' status hss →
    P9 st d env (s :: ss) st'' status (.consNormal st d env s ss st' st'' status hs hss) := by
  intro st d env s ss st' st'' status hs hss ihs ihss hcb
  obtain ⟨hcbs, _⟩ := ihs hcb
  exact ihss hcbs
private theorem b_qca : ∀ st d env s ss st' status
    (hs : ExecS st d env s st' status) (hne : status ≠ .normal),
    P4 st d env s st' status hs →
    P9 st d env (s :: ss) st' status (.consAbrupt st d env s ss st' status hs hne) := by
  intro st d env s ss st' status hs hne ihs hcb
  exact ihs hcb

/-! ### The nine relation-projections, assembled by the shared recursor -/

/-- **The global store closures-boundedness invariant, packaged as a named-field
structure** (CLAUDE.md — never an anonymous ∧-tower; the R6 rule forbids the
`.2.2.…` positional navigation the raw 9-tuple would force on every consumer).  One
field per WHILE relation: from a closures-bounded entry store, the exit store is
closures-bounded, and every value the relation produces is an in-bounds closure ref
in the exit store (`onCall` additionally requires its argument values bounded on
entry — they were produced by the calling `EvalArgs`). -/
structure StoreWFClosure : Prop where
  onEvalE : ∀ {st d a e st' v}, EvalE st d a e st' v →
    StoreClosuresBounded st.store →
      StoreClosuresBounded st'.store ∧ ValueClosuresBounded st'.store.closures.size v
  onEvalArgs : ∀ {st d a es st' vs}, EvalArgs st d a es st' vs →
    StoreClosuresBounded st.store →
      StoreClosuresBounded st'.store ∧ ValuesClosuresBounded st'.store.closures.size vs
  onCall : ∀ {st d fv vs st' v}, Call st d fv vs st' v →
    StoreClosuresBounded st.store → ValuesClosuresBounded st.store.closures.size vs →
      StoreClosuresBounded st'.store ∧ ValueClosuresBounded st'.store.closures.size v
  onExecS : ∀ {st d a s st' status}, ExecS st d a s st' status →
    StoreClosuresBounded st.store →
      StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status
  onExecInit : ∀ {st d a init st'}, ExecInit st d a init st' →
    StoreClosuresBounded st.store → StoreClosuresBounded st'.store
  onForLoop : ∀ {st d a cnd step b st' status}, ForLoop st d a cnd step b st' status →
    StoreClosuresBounded st.store →
      StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status
  onForCond : ∀ {st d a cnd st'}, ForCond st d a cnd st' →
    StoreClosuresBounded st.store → StoreClosuresBounded st'.store
  onExecStep : ∀ {st d a step st'}, ExecStep st d a step st' →
    StoreClosuresBounded st.store → StoreClosuresBounded st'.store
  onExecSeq : ∀ {st d a ss st' status}, ExecSeq st d a ss st' status →
    StoreClosuresBounded st.store →
      StoreClosuresBounded st'.store ∧ StatusClosuresBounded st'.store.closures.size status

/-- **The global store closures-boundedness invariant, for all nine relations.**
Proved by the auto-generated mutual recursor with the nine `P*` motives and the 50
shared `b_*` minor premises (model: `Cost.execSeq_store_mono`). -/
theorem storeClosuresBounded_mutual : StoreWFClosure :=
  ⟨@fun st d a e st' v h => EvalE.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a es st' vs h => EvalArgs.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d fv vs st' v h => Call.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a s st' status h => ExecS.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a init st' h => ExecInit.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a cnd step b st' status h => ForLoop.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a cnd st' h => ForCond.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a step st' h => ExecStep.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h,
   @fun st d a ss st' status h => ExecSeq.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3) (motive_4 := P4) (motive_5 := P5) (motive_6 := P6) (motive_7 := P7) (motive_8 := P8) (motive_9 := P9) b_int b_str b_bool b_null b_var b_assign b_bin b_ort b_orf b_anf b_ant b_neg b_not b_call b_fn b_anil b_acons b_clo b_pr b_prl b_as b_sexpr b_svi b_svn b_sblk b_sift b_siff b_sifn b_swf b_swb b_swr b_swl b_sfor b_sret b_srn b_sbrk b_scont b_inone b_isome b_lcf b_lbb b_lbr b_lloop b_cnone b_csome b_stnone b_stsome b_qnil b_qcn b_qca h⟩

/-! ## Public invariant theorems + the per-arm consumer

The `.fn` arm consumes `StoreClosuresBounded st.store` as `hWF`
(`rows/FnResidSupply.lean`, `rows/FnArmSeamSupply.lean`).  These projections make it
a THEOREM of any store reachable from a closures-bounded entry — in particular from
`initSt` (the whole-program run), whose only frame binds natives (no closure refs). -/

/-- **The invariant, projected to expression evaluation.**  Every store reachable by
`EvalE` from a closures-bounded store is closures-bounded. -/
theorem evalE_storeClosuresBounded {st d a e st' v}
    (h : EvalE st d a e st' v) (hcb : StoreClosuresBounded st.store) :
    StoreClosuresBounded st'.store :=
  (storeClosuresBounded_mutual.onEvalE h hcb).1

/-- **The invariant, projected to statement sequences** — the `Call.closure` body
form and the whole-program `BigStep` form. -/
theorem execSeq_storeClosuresBounded {st d a ss st' status}
    (h : ExecSeq st d a ss st' status) (hcb : StoreClosuresBounded st.store) :
    StoreClosuresBounded st'.store :=
  (storeClosuresBounded_mutual.onExecSeq h hcb).1

/-- **The invariant, projected to statement execution.** -/
theorem execS_storeClosuresBounded {st d a s st' status}
    (h : ExecS st d a s st' status) (hcb : StoreClosuresBounded st.store) :
    StoreClosuresBounded st'.store :=
  (storeClosuresBounded_mutual.onExecS h hcb).1

/-- The initial store is closures-bounded: its single global frame binds only the
three natives (`print`/`println`/`assert`), none of which is a `.closure`, and its
closures array is empty. -/
theorem storeClosuresBounded_initSt : StoreClosuresBounded initSt.store := by
  refine ⟨?_⟩
  intro fa hfa i hi
  -- the only frame is #0; its three bindings are all `.native`.
  have hfa0 : fa = 0 := by
    have : fa < 1 := by simpa [initSt] using hfa
    omega
  subst hfa0
  -- the frame-0 value at index `i` is a member of the concrete native binding list,
  -- and every value there is `.native` (never `.closure`), so it is bounded.
  have hmem : (initSt.store.frames[0]).vars[i] ∈ (initSt.store.frames[0]).vars :=
    List.getElem_mem hi
  -- every binding value in the initial global frame is a native (never a closure).
  have hall : ∀ p ∈ (initSt.store.frames[0]).vars, ∃ f, p.2 = Value.native f := by
    intro p hp
    have hp3 : p = ("print", Value.native .print) ∨ p = ("println", Value.native .println)
        ∨ p = ("assert", Value.native .assert) := by
      simpa [initSt] using hp
    rcases hp3 with h | h | h <;> exact ⟨_, by rw [h]⟩
  obtain ⟨f, hf⟩ := hall _ hmem
  rw [hf]; trivial

/-- **`storeClosuresBounded_invariant`** — the closures-in-bounds invariant holds at
the end of any whole-program statement-sequence run from `initSt` (or from any
closures-bounded entry).  This DISCHARGES the per-arm `hWF` premise once and for all:
the `.fn` arm fires at a store reached by evaluating the program so far, which is
`EvalE`/`ExecSeq`-reachable from `initSt`. -/
theorem storeClosuresBounded_invariant {d a ss st' status}
    (h : ExecSeq initSt d a ss st' status) : StoreClosuresBounded st'.store :=
  execSeq_storeClosuresBounded h storeClosuresBounded_initSt

#print axioms storeClosuresBounded_mutual
#print axioms evalE_storeClosuresBounded
#print axioms execSeq_storeClosuresBounded
#print axioms storeClosuresBounded_initSt
#print axioms storeClosuresBounded_invariant

end Vsa.Sim
