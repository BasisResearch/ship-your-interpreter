import Vsa.Sim.AllocOff

/-!
# `AllocCapacity` — physical chunk accounting and the arena capacity theorem

`PROOF_CLOSURE_PLAN.md` task 2 asks to "derive initial stack/body bounds and
allocator capacity from a source resource bound over every finite execution
prefix", accounting for "physical chunk overhead and fragmentation: a 32-byte
request occupies 48 bytes".

Nothing in the development bounded the live set before this module.  `HeapArena`
says each live extent lies inside the arena and that they are pairwise disjoint,
but says nothing about their TOTAL, so `MallocContract.nonNull_of_bounded` — the
field that collapses `malloc`'s NULL branch — was an assumption with no capacity
content behind it at all.

Two things land here.

* `physSize` is the physical cost of a request: an 8-byte header rounded up to
  the 16-byte alignment, so `physSize 32 = 48` exactly as the plan records.
  `physTotal` sums it over a ledger.  This is INTERNAL fragmentation only — the
  bytes a chunk wastes on its own header and padding.  External fragmentation,
  the free space that exists but is not contiguous, is not modelled here.
* `extents_total_le` is the capacity theorem: pairwise-disjoint extents inside
  `[A.lo, A.hi)` have total size at most `A.hi - A.lo`.  It is proved by strong
  induction on the ledger, splitting the tail around the head extent into the
  part that ends below it and the part that starts above it — the two halves are
  bounded by the sub-arenas `[lo, e.1)` and `[e.1 + e.2, hi)`.  This is what
  makes an arena-capacity statement non-vacuous: a ledger that fits is a real
  constraint on the live set, not a restatement of disjointness.

`ResourceBound` then states the source-side obligation in one named record, and
`arena_has_room` derives from it that the arena holds enough BYTES for the next
request beyond everything currently live.

That is a necessary condition for `nonNull_of_bounded`, not a sufficient one,
and the difference is worth stating plainly rather than leaving in a reader's
way.  A total-byte bound does not exhibit a PLACEMENT: an arena can have ample
free bytes and still no contiguous run of `n` of them, which is exactly external
fragmentation.  Turning `arena_has_room` into `malloc` actually succeeding needs
the allocator's own placement argument — dlmalloc's bin structure, coalescing and
top-chunk behaviour — which is behind `MallocContract` and is not something a
call site or a source-level bound can supply.  What this module removes is the
weaker gap: before it, `nonNull_of_bounded` had no capacity content at all, and
the live set was unbounded.
-/

namespace Vsa.Sim

open Vsa.RuntimeRepr Vsa.Alloc Vsa.Sim.RuntimeOwnership

/-! ## 1. Physical chunk size -/

/-- The physical bytes a request of `n` occupies: an 8-byte chunk header, rounded
up to the allocator's 16-byte alignment. -/
def physSize (n : Nat) : Nat := 16 * ((n + 8 + 15) / 16)

/-- The plan's recorded figure: a 32-byte request occupies 48 bytes. -/
theorem physSize_32 : physSize 32 = 48 := by decide

theorem physSize_ge (n : Nat) : n ≤ physSize n := by
  unfold physSize; omega

theorem physSize_mono {m n : Nat} (h : m ≤ n) : physSize m ≤ physSize n := by
  unfold physSize; omega

/-- The physical cost of a whole ledger. -/
def physTotal (exts : List Extent) : Nat := (exts.map (fun e => physSize e.2)).sum

theorem physTotal_nil : physTotal [] = 0 := rfl

theorem physTotal_cons (e : Extent) (l : List Extent) :
    physTotal (e :: l) = physSize e.2 + physTotal l := rfl

/-! ## 2. The capacity theorem -/

/-- Splitting a list by a decidable predicate splits its sum. -/
private theorem sum_filter_split (p : Extent → Bool) (l : List Extent) :
    ((l.filter p).map Prod.snd).sum + ((l.filter (fun e => !p e)).map Prod.snd).sum
      = (l.map Prod.snd).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : p a with
    | true => simp [h]; omega
    | false => simp [h]; omega

private theorem length_filter_le (p : Extent → Bool) (l : List Extent) :
    (l.filter p).length ≤ l.length :=
  List.Sublist.length_le List.filter_sublist

/-- **The capacity theorem.**  Pairwise-disjoint extents inside `[lo, hi)` have
total size at most `hi - lo`.  Strong induction on the ledger: the tail splits
around the head into the extents that end below it and those that start above
it, bounded by `[lo, e.1)` and `[e.1 + e.2, hi)` respectively. -/
private theorem extents_total_aux :
    ∀ (k : Nat) (l : List Extent) (lo hi : Nat), l.length ≤ k →
      (∀ e ∈ l, lo ≤ e.1 ∧ e.1 + e.2 ≤ hi) → l.Pairwise ExtDisjoint →
      (l.map Prod.snd).sum ≤ hi - lo := by
  intro k
  induction k with
  | zero =>
    intro l lo hi hk _ _
    cases l with
    | nil => simp
    | cons a t => simp at hk
  | succ k ih =>
    intro l lo hi hk hin hp
    cases l with
    | nil => simp
    | cons e t =>
      have hpc := List.pairwise_cons.mp hp
      have hem := hin e (List.mem_cons_self)
      -- the tail splits around `e`
      let below : Extent → Bool := fun f => decide (f.1 + f.2 ≤ e.1)
      have hsplit := sum_filter_split below t
      have hlenB : (t.filter below).length ≤ k := by
        have := length_filter_le below t; simp at hk; omega
      have hlenA : (t.filter (fun f => !below f)).length ≤ k := by
        have := length_filter_le (fun f => !below f) t; simp at hk; omega
      -- extents below `e` live in `[lo, e.1)`
      have hB : ∀ f ∈ t.filter below, lo ≤ f.1 ∧ f.1 + f.2 ≤ e.1 := by
        intro f hf
        have hmem := (List.mem_filter.mp hf).1
        have hpred : below f = true := (List.mem_filter.mp hf).2
        exact ⟨(hin f (List.mem_cons_of_mem _ hmem)).1, by simpa [below] using hpred⟩
      -- extents not below `e` are disjoint from it, so they start at `e.1 + e.2`
      have hA : ∀ f ∈ t.filter (fun f => !below f),
          e.1 + e.2 ≤ f.1 ∧ f.1 + f.2 ≤ hi := by
        intro f hf
        have hmem := (List.mem_filter.mp hf).1
        have hpred : (!below f) = true := (List.mem_filter.mp hf).2
        have hnb : ¬ (f.1 + f.2 ≤ e.1) := by simpa [below] using hpred
        have hd := hpc.1 f hmem
        change e.1 + e.2 ≤ f.1 ∨ f.1 + f.2 ≤ e.1 at hd
        exact ⟨by omega, (hin f (List.mem_cons_of_mem _ hmem)).2⟩
      have hpB : (t.filter below).Pairwise ExtDisjoint :=
        List.Pairwise.sublist List.filter_sublist hpc.2
      have hpA : (t.filter (fun f => !below f)).Pairwise ExtDisjoint :=
        List.Pairwise.sublist List.filter_sublist hpc.2
      have rB := ih (t.filter below) lo e.1 hlenB hB hpB
      have rA := ih (t.filter (fun f => !below f)) (e.1 + e.2) hi hlenA hA hpA
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Pairwise-disjoint live extents fit inside the arena. -/
theorem extents_total_le {A : Arena} {exts : List Extent} (h : HeapArena A exts) :
    (exts.map Prod.snd).sum ≤ A.hi - A.lo :=
  extents_total_aux exts.length exts A.lo A.hi (Nat.le_refl _)
    (fun e he => (h.1 e he).2) h.2

/-! ## 3. The source resource bound -/

/-- **The source-side resource bound**, as one named record: over every finite
execution prefix the interpreter's live set stays within a physical budget, and
every individual request stays within the allocator's static ceiling.  Supplier:
a source-level accounting of the program's allocation behaviour (environment
records, their arrays, copied binding names, closure records, string payloads)
against the arena sized by the linker script. -/
structure ResourceBound (A : Arena) (maxReq : Nat) (exts : List Extent) : Prop where
  /-- The live ledger's PHYSICAL cost, header and alignment included, leaves room
  in the arena for one more request of the static ceiling. -/
  budget : physTotal exts + physSize maxReq ≤ A.hi - A.lo
  /-- The ledger is a genuine live set of the arena. -/
  arena : HeapArena A exts

/-- Logical size never exceeds physical size, extent by extent. -/
theorem sum_le_physTotal (exts : List Extent) :
    (exts.map Prod.snd).sum ≤ physTotal exts := by
  induction exts with
  | nil => exact Nat.le_refl 0
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, physTotal_cons]
    have := physSize_ge a.2
    omega

/-- **The arena holds enough bytes for the next request.**  From the source
bound, at least `physSize n` bytes remain beyond everything currently live, for
any request within the static ceiling.  This is the capacity content
`MallocContract.nonNull_of_bounded` asserts without proof, but it is a NECESSARY
condition only: it does not exhibit a contiguous placement for those bytes, so
external fragmentation and the allocator's placement strategy remain behind
`MallocContract`. -/
theorem arena_has_room {A : Arena} {maxReq : Nat} {exts : List Extent}
    (h : ResourceBound A maxReq exts) {n : Nat} (hn : n ≤ maxReq) :
    (exts.map Prod.snd).sum + physSize n ≤ A.hi - A.lo := by
  have h1 := sum_le_physTotal exts
  have h2 := physSize_mono hn
  have h3 := h.budget
  omega

/-- A fresh block entering the ledger keeps the physical accounting exact. -/
theorem physTotal_fresh (p n : Nat) (exts : List Extent) :
    physTotal ((p, n) :: exts) = physSize n + physTotal exts := rfl

/-! ## 4. Carrying the bound along an execution -/

/-- **Room for `k` further requests at the ceiling.**  `ResourceBound` asserts the
budget at ONE point; this is the same statement indexed by how many more
allocations it still covers, which is what an induction along an execution
needs.  A source-level accounting supplies `k` — the number of allocations the
program can still make — and the lemmas below carry it. -/
def ResourceBudget (A : Arena) (maxReq : Nat) (exts : List Extent) (k : Nat) : Prop :=
  physTotal exts + k * physSize maxReq ≤ A.hi - A.lo

/-- A sublist costs no more physically than the list it came from. -/
theorem physTotal_le_of_sublist {l₁ l₂ : List Extent} (h : l₁.Sublist l₂) :
    physTotal l₁ ≤ physTotal l₂ := by
  induction h with
  | slnil => exact Nat.le_refl 0
  | cons a _ ih => simp only [physTotal_cons]; omega
  | cons₂ a _ ih => simp only [physTotal_cons]; omega

/-- Releasing a block never costs more room. -/
theorem physTotal_erase_le (e : Extent) (l : List Extent) :
    physTotal (l.erase e) ≤ physTotal l :=
  physTotal_le_of_sublist List.erase_sublist

/-- **The allocation step.**  One request within the ceiling consumes exactly one
unit of the budget, whatever its size. -/
theorem ResourceBudget.alloc {A : Arena} {maxReq : Nat} {exts : List Extent} {k : Nat}
    (h : ResourceBudget A maxReq exts (k + 1)) {p n : Nat} (hn : n ≤ maxReq) :
    ResourceBudget A maxReq ((p, n) :: exts) k := by
  have hm := physSize_mono hn
  unfold ResourceBudget at h ⊢
  rw [physTotal_fresh]
  have hs : (k + 1) * physSize maxReq = k * physSize maxReq + physSize maxReq :=
    Nat.succ_mul k (physSize maxReq)
  omega

/-- **The release step.**  Freeing never spends budget, and may recover some. -/
theorem ResourceBudget.free {A : Arena} {maxReq : Nat} {exts : List Extent} {k : Nat}
    (h : ResourceBudget A maxReq exts k) (e : Extent) :
    ResourceBudget A maxReq (exts.erase e) k := by
  have := physTotal_erase_le e exts
  unfold ResourceBudget at h ⊢
  omega

/-- A budget with room to spare is a bound at the current point. -/
theorem ResourceBudget.toBound {A : Arena} {maxReq : Nat} {exts : List Extent} {k : Nat}
    (h : ResourceBudget A maxReq exts (k + 1)) (harena : HeapArena A exts) :
    ResourceBound A maxReq exts where
  budget := by
    unfold ResourceBudget at h
    have hs : (k + 1) * physSize maxReq = k * physSize maxReq + physSize maxReq :=
      Nat.succ_mul k (physSize maxReq)
    omega
  arena := harena

/-- The budget is monotone in the count, so a coarser source bound still serves. -/
theorem ResourceBudget.mono {A : Arena} {maxReq : Nat} {exts : List Extent} {j k : Nat}
    (h : ResourceBudget A maxReq exts k) (hjk : j ≤ k) : ResourceBudget A maxReq exts j := by
  have hjm : j * physSize maxReq ≤ k * physSize maxReq :=
    Nat.mul_le_mul_right (physSize maxReq) hjk
  unfold ResourceBudget at h ⊢
  omega

#print axioms physSize_32
#print axioms extents_total_le
#print axioms sum_le_physTotal
#print axioms arena_has_room
#print axioms physTotal_le_of_sublist
#print axioms physTotal_erase_le
#print axioms ResourceBudget.alloc
#print axioms ResourceBudget.free
#print axioms ResourceBudget.toBound
#print axioms ResourceBudget.mono

end Vsa.Sim
