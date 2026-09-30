import Vsa.Sim.AllocOff
import Vsa.AllocResource

namespace Vsa.Sim

open Vsa.RuntimeRepr Vsa.Alloc Vsa.Sim.RuntimeOwnership

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

      let below : Extent → Bool := fun f => decide (f.1 + f.2 ≤ e.1)
      have hsplit := sum_filter_split below t
      have hlenB : (t.filter below).length ≤ k := by
        have := length_filter_le below t; simp at hk; omega
      have hlenA : (t.filter (fun f => !below f)).length ≤ k := by
        have := length_filter_le (fun f => !below f) t; simp at hk; omega

      have hB : ∀ f ∈ t.filter below, lo ≤ f.1 ∧ f.1 + f.2 ≤ e.1 := by
        intro f hf
        have hmem := (List.mem_filter.mp hf).1
        have hpred : below f = true := (List.mem_filter.mp hf).2
        exact ⟨(hin f (List.mem_cons_of_mem _ hmem)).1, by simpa [below] using hpred⟩

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

theorem physTotal_fresh (p n : Nat) (exts : List Extent) :
    physTotal ((p, n) :: exts) = physSize n + physTotal exts := rfl

theorem ResourceBudget.alloc {A : Arena} {maxReq : Nat} {exts : List Extent} {k : Nat}
    (h : ResourceBudget A maxReq exts (k + 1)) {p n : Nat} (hn : n ≤ maxReq) :
    ResourceBudget A maxReq ((p, n) :: exts) k := by
  have hm := physSize_mono hn
  unfold ResourceBudget at h ⊢
  rw [physTotal_fresh]
  have hs : (k + 1) * physSize maxReq = k * physSize maxReq + physSize maxReq :=
    Nat.succ_mul k (physSize maxReq)
  omega

end Vsa.Sim
