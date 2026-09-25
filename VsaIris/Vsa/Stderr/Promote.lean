import VsaIris.LocalRunO

/-!
# Read-only cells of a printing run, owned instead (lane N3)

`LocalRun.promote` (`StrlenOwned.lean`) for printing runs (`LRO`): a run
that reads the cells `t2` read-only runs with them owned instead, and hands
them back unchanged (a segment never writes outside its owned set). `fprintf`
reads `main`'s `err_msg` through its data view (`strlen_sw` measures a
read-only string) while `main` owns the buffer: `LRO.promote` reconciles the
two.
-/

namespace VsaIris

variable {M : MachineModel} {ro : List (Nat × BitVec 64)} {t1 t2 : List (Nat × BitVec 8)}
  {rs : List Nat} {S : Nat → Prop}

/-- One segment, with the cells `t2` owned instead of read-only. -/
theorem SegFromO.promote (hd : ∀ p ∈ t2, ¬ S p.1) {k : Nat} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} {P : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h : SegFromO M ro (t1 ++ t2) rs S k rv mv P) (ht : ∀ p ∈ t2, mv p.1 = p.2) :
    SegFromO M ro t1 rs (fun a => S a ∨ ∃ p ∈ t2, p.1 = a) k rv mv
      (fun o rv' mv' => P o rv' mv' ∧ ∀ p ∈ t2, mv' p.1 = p.2) := by
  intro σ hok hro hr hm
  have hro' : ROHolds M σ ro (t1 ++ t2) := ⟨hro.1, fun p hp => by
    rcases List.mem_append.1 hp with h1 | h2
    · exact hro.2 p h1
    · rw [hm p.1 (.inr ⟨p, h2, rfl⟩)]; exact ht p h2⟩
  obtain ⟨σ', o, hreach, hok', hregs, hmem, hout, hP⟩ :=
    h σ hok hro' hr (fun a ha => hm a (.inl ha))
  refine ⟨σ', o, hreach, hok', hregs, fun a ha => hmem a (fun h => ha (.inl h)), hout, hP, ?_⟩
  intro p hp
  rw [hmem p.1 (hd p hp), hm p.1 (.inr ⟨p, hp, rfl⟩)]
  exact ht p hp

/-- **Promoting read-only cells of a printing run to owned ones.** -/
theorem LRO.promote {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hd : ∀ p ∈ t2, ¬ S p.1) {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LRO M ro (t1 ++ t2) rs S Q t rv mv) (ht : ∀ p ∈ t2, mv p.1 = p.2) :
    LRO M ro t1 rs (fun a => S a ∨ ∃ p ∈ t2, p.1 = a)
      (fun t rv mv => Q t rv mv ∧ ∀ p ∈ t2, mv p.1 = p.2) t rv mv := by
  refine LRO.ind (X := fun t rv mv => (∀ p ∈ t2, mv p.1 = p.2) →
      LRO M ro t1 rs (fun a => S a ∨ ∃ p ∈ t2, p.1 = a)
        (fun t rv mv => Q t rv mv ∧ ∀ p ∈ t2, mv p.1 = p.2) t rv mv)
    (fun t rv mv hq ht => LRO.done ⟨hq, ht⟩)
    (fun t rv mv k hs ht => LRO.seg k ((hs.promote hd ht).mono fun o rv' mv' ⟨hx, ht'⟩ => hx ht'))
    h ht

end VsaIris
