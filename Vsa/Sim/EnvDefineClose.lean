import Vsa.Sim.HeapOps

/-!
# `EnvDefineClose` — the `env_define` grow-path ledger algebra (L5, brick 1)

`EnvDefSpec.lean`'s "Remaining" note staged the append/grow path as blocked on
"no landed realloc spec". That blocker is GONE: `Vsa/Sim/ReallocSpec.lean`
(Wave-A/B integration) supplies `ReallocOps` — the parameterized grow/null
contracts over one allocator invariant `AInv` and private footprint
`privFoot` — and `Vsa/Sim/HeapOps.lean` packages malloc + realloc onto that
one ledger.

This file lands the first brick of the close: the **grow-path ledger algebra**
the machine's grow block (`0x80002b90..0x80002bc0`: `cap' = if cap == 0 then 8
else 2*cap`; `realloc(names, cap'*8)`; `realloc(vals, cap'*24)`) consumes:

* `mem_erase_mono` / `pairwise_erase` / `mem_erase_of_pairwise` — the
  `List.erase` algebra over a pairwise-`ExtDisjoint`, positive-sized extent
  ledger (a set-like ledger: duplicates are ruled out by self-disjointness);
* `realloc_grow2_arena` — two sequential SUCCESSFUL grows over ONE ledger:
  the composed extent list (`Grow2Exts`) is again a `HeapArena` — live,
  in-arena, pairwise disjoint — from the two results' disjointness clauses
  and the entry arena. The `AInv` re-establishment at the composed list is
  the grow BLOCK's obligation (it is abstract in `HeapOps`), taken as an
  explicit hypothesis at the call site;
* `heapPublicFrame_trans` — two sequential public-memory frames compose over
  the concatenation of their excepted extents (the four-extent frame of the
  two-call footprint).

Remaining bricks (per `experiments/exponentiation-plan.md` L5, each its own
workstream): the grow BLOCK's machine decode (a `#derive_case` chain through
`0x80002b90..0x80002bc0` feeding two `ReallocOps.grow` Triples through the
L4 `callStep` seam), the append path (strlen/malloc/memcpy), and the scan-loop
+ path-dispatch assembly into the top-level
`env_define_spec : Triple env_define_pre env_define_post` that unblocks the
`Call.closure`/`assign`/`varDecl` callers.

Timing witness (2026-08-26): pure Prop/list algebra — no reflection, no
machine decode; see the commit gate for the build time.
-/

open LeanRV64DExecutable Vsa
open Vsa.RuntimeRepr (Arena)
open Vsa.Alloc (StackLayout ExtDisjoint)

namespace Vsa.Sim

/-! ## `List.erase` algebra over a set-like extent ledger -/

/-- `ExtDisjoint` is symmetric (an interval-order atom). -/
theorem extDisjoint_symm {a b : Extent} (h : ExtDisjoint a b) : ExtDisjoint b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Every entry of an erased list is an entry of the original. -/
theorem mem_erase_mono {l : List Extent} {a e : Extent}
    (h : e ∈ l.erase a) : e ∈ l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons b r ih =>
    by_cases hb : (b == a) = true
    · simp only [List.erase, hb] at h
      exact List.mem_cons_of_mem _ h
    · simp only [List.erase, hb, if_false] at h
      rcases List.mem_cons.mp h with h' | h'
      · have : e ∈ b :: r := by rw [← h']; exact List.mem_cons_self
        exact this
      · exact List.mem_cons_of_mem _ (ih h')

/-- Erasing an element preserves pairwise disjointness. -/
theorem pairwise_erase {l : List Extent} {a : Extent}
    (h : l.Pairwise ExtDisjoint) : (l.erase a).Pairwise ExtDisjoint := by
  induction l with
  | nil => exact h
  | cons b r ih =>
    cases h with
    | cons hhead htail =>
      by_cases hb : (b == a) = true
      · simp only [List.erase, hb]; exact htail
      · simp only [List.erase, hb, if_false]
        exact List.Pairwise.cons (fun x hx => hhead x (mem_erase_mono hx)) (ih htail)

/-- In a pairwise-disjoint, positive-sized ledger, erasing `a` really removes
`a`: every survivor is an original member DIFFERENT from `a`. (Positivity +
self-disjointness make the ledger set-like — a duplicate `a` would need
`ExtDisjoint a a`, i.e. `a.1 + a.2 ≤ a.1`, contradicting `0 < a.2`.) -/
theorem mem_erase_of_pairwise {l : List Extent} {a e : Extent}
    (hpw : l.Pairwise ExtDisjoint) (hpos : ∀ x ∈ l, 0 < x.2)
    (h : e ∈ l.erase a) : e ∈ l ∧ e ≠ a := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons b r ih =>
    cases hpw with
    | cons hhead htail =>
      by_cases hb : (b == a) = true
      · simp only [List.erase, hb] at h
        refine ⟨List.mem_cons_of_mem _ h, ?_⟩
        by_cases he : e = a
        · exfalso
          rw [he] at h
          have hd : ExtDisjoint b a := hhead a h
          simp only [beq_iff_eq] at hb
          rw [hb] at hd
          have hposa := hpos a (List.mem_cons_of_mem _ h)
          rcases hd with hd | hd
          · omega
          · omega
        · exact he
      · simp only [List.erase, hb, if_false] at h
        rcases List.mem_cons.mp h with h' | h'
        · refine ⟨?_, ?_⟩
          · rw [← h']; exact List.mem_cons_self
          · intro hea
            rw [h'] at hea
            exact hb ((beq_iff_eq (a := b) (b := a)).mpr hea)
        · have ih' := ih htail (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) h'
          exact ⟨List.mem_cons_of_mem _ ih'.1, ih'.2⟩

/-! ## Two sequential grows: the composed ledger -/

/-- The extent list after growing `(p1, n1)` to `(p1', n1')` and then
`(p2, n2)` to `(p2', n2')`. -/
def Grow2Exts (exts : List Extent) (p1 n1 p1' n1' p2 n2 p2' n2' : Nat) :
    List Extent :=
  (p2', n2') :: (p1', n1') :: (exts.erase (p1, n1)).erase (p2, n2)

/-- **The grow-path ledger merge.** From an entry `HeapArena`, the SUCCESS
branches of two sequential `ReallocGrowResult`s (grow `(p1,n1)→(p1',n1')`,
then `(p2,n2)→(p2',n2')` at the intermediate state), the composed extent
list `Grow2Exts` is again a `HeapArena`: both new extents are live and
in-arena, the survivors keep their facts, and pairwise disjointness holds —
the second result's disjointness clause covers the new-new pair and the
second-generation survivors, the first's covers the first-generation
survivors. The `AInv` re-establishment at the composed list is the grow
BLOCK's own obligation (`AInv` is abstract in `HeapOps`), discharged against
the concrete machine block when it is decoded. -/
theorem realloc_grow2_arena (A : Arena) {exts : List Extent}
    {p1 n1 p1' n1' p2 n2 p2' n2' : Nat}
    (harena : HeapArena A exts)
    (hn1' : 0 < n1') (hn2' : 0 < n2')
    (hc1 : A.contains p1' n1') (hc2 : A.contains p2' n2')
    (hd1 : ∀ e ∈ exts, e ≠ (p1, n1) → ExtDisjoint (p1', n1') e)
    (hd2 : ∀ e ∈ (p1', n1') :: exts.erase (p1, n1),
      ExtDisjoint (p2', n2') e) :
    HeapArena A (Grow2Exts exts p1 n1 p1' n1' p2 n2 p2' n2') := by
  obtain ⟨hlive, hpw⟩ := harena
  constructor
  · intro e he
    rcases List.mem_cons.mp he with h' | h'
    · subst h'; exact ⟨hn2', hc2⟩
    · rcases List.mem_cons.mp h' with h'' | h''
      · subst h''; exact ⟨hn1', hc1⟩
      · exact hlive e (mem_erase_mono (mem_erase_mono h''))
  · refine List.Pairwise.cons (fun x hx => ?_) ?_
    · rcases List.mem_cons.mp hx with h' | h'
      · subst h'; exact hd2 _ (List.mem_cons_self)
      · exact hd2 _ (List.mem_cons_of_mem _ (mem_erase_mono h'))
    · refine List.Pairwise.cons (fun x hx => ?_) ?_
      · have hx1 : x ∈ exts.erase (p1, n1) := mem_erase_mono hx
        have hposE : ∀ y ∈ exts, 0 < y.2 := fun y hy => (hlive y hy).1
        have hne := (mem_erase_of_pairwise hpw hposE hx1).2
        exact hd1 x (mem_erase_mono hx1) hne
      · exact pairwise_erase (pairwise_erase hpw)

/-! ## Sequential public-memory frames compose -/

/-- Two sequential public frames compose over the concatenation of their
excepted extents: a byte outside the union was untouched by either call. -/
theorem heapPublicFrame_trans {privFoot : Nat → Prop} {SL : StackLayout}
    {sp : BitVec 64} {m0 m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    {excepts1 excepts2 : List Extent}
    (h1 : HeapPublicFrame privFoot SL sp excepts1 m0 m1)
    (h2 : HeapPublicFrame privFoot SL sp excepts2 m1 m2) :
    HeapPublicFrame privFoot SL sp (excepts1 ++ excepts2) m0 m2 := by
  intro a hnpriv hnstk hexc
  have hexc2 : ∀ e ∈ excepts2, a < e.1 ∨ e.1 + e.2 ≤ a :=
    fun e he => hexc e (List.mem_append.mpr (Or.inr he))
  have hexc1 : ∀ e ∈ excepts1, a < e.1 ∨ e.1 + e.2 ≤ a :=
    fun e he => hexc e (List.mem_append.mpr (Or.inl he))
  exact (h2 a hnpriv hnstk hexc2).trans (h1 a hnpriv hnstk hexc1)

#print axioms realloc_grow2_arena
#print axioms heapPublicFrame_trans

end Vsa.Sim
