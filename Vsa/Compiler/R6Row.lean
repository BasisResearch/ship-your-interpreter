import Vsa.Compiler.RTBase

namespace Vsa.Compiler

open Vsa.Sim

/-- First-match value of literal key `n` in a register row `ks`/`vs`. -/
def rowVal (n : Nat) : List Nat → List (BitVec 64) → BitVec 64
  | k :: ks, v :: vs => if n = k then v else rowVal n ks vs
  | _, _ => 0

/-- A register row: every literal key in `ks` holds its paired value in `L`. Keys are a closed
literal list (so membership and disjointness are decided by `decide`); values are opaque. -/
def Models (L : GRegs) : List Nat → List (BitVec 64) → Prop
  | k :: ks, v :: vs => Has L k v ∧ Models L ks vs
  | _, _ => True

theorem Models.nil (L : GRegs) : Models L [] [] := trivial

theorem Models.cons {L : GRegs} {k : Nat} {v : BitVec 64} {ks : List Nat} {vs : List (BitVec 64)}
    (h : Has L k v) (hm : Models L ks vs) : Models L (k :: ks) (v :: vs) := ⟨h, hm⟩

theorem Models.get {L : GRegs} : ∀ {ks : List Nat} {vs : List (BitVec 64)} {n : Nat},
    Models L ks vs → n ∈ ks → ks.length = vs.length → Has L n (rowVal n ks vs)
  | [], _, _, _, hn, _ => by simp at hn
  | _ :: _, [], _, _, _, hl => by simp at hl
  | k :: ks, v :: vs, n, ⟨h, hm⟩, hn, hl => by
    simp only [rowVal]
    split
    · next e => subst e; exact h
    · next e =>
      exact Models.get hm (by simpa [e] using hn) (by simpa using hl)

/-- Frame rule: a Keep set disjoint from the row's keys preserves the row. -/
theorem Keep.models {S : List Nat} {L L' : GRegs} (hk : Keep S L L') {ks : List Nat}
    (hd : ∀ k ∈ ks, k ∉ S) : ∀ {vs : List (BitVec 64)}, Models L ks vs → Models L' ks vs := by
  induction ks with
  | nil => intro vs _; cases vs <;> trivial
  | cons k ks ih =>
    intro vs hm
    cases vs with
    | nil => trivial
    | cons v vs =>
      exact ⟨hk.has (hd k (List.mem_cons_self ..)) hm.1,
        ih (fun j hj => hd j (List.mem_cons_of_mem _ hj)) hm.2⟩

/-- Frame rule for one register write off the row's keys (a `reg_simp` rewrite, side goal by `decide`). -/
theorem models_gset {L : GRegs} {rd : Nat} {w : BitVec 64} {ks : List Nat} (hd : ∀ k ∈ ks, k ≠ rd) :
    ∀ {vs : List (BitVec 64)}, Models (gset L rd w) ks vs ↔ Models L ks vs := by
  induction ks with
  | nil => intro vs; cases vs <;> exact Iff.rfl
  | cons k ks ih =>
    intro vs
    cases vs with
    | nil => exact Iff.rfl
    | cons v vs =>
      have hk : k ≠ rd := hd k (List.mem_cons_self ..)
      have hh : Has (gset L rd w) k v ↔ Has L k v := by
        unfold Has; rw [lookupG_set, if_neg hk]
      exact and_congr hh (ih (fun j hj => hd j (List.mem_cons_of_mem _ hj)))

/-- The rewriting kit `wp_simp` consumes: key membership, key values, and row lookup. -/
theorem Models.wp {L : GRegs} {ks : List Nat} {vs : List (BitVec 64)} (hm : Models L ks vs)
    (hl : ks.length = vs.length := by rfl) :
    (∀ n, n ∈ ks → n ≠ 0 → n ∈ keysG L) ∧ (∀ n, n ∈ ks → srcVal n L = rowVal n ks vs) ∧
      (∀ n k ks' (v : BitVec 64) vs', rowVal n (k :: ks') (v :: vs') = if n = k then v else rowVal n ks' vs') :=
  ⟨fun _ hn h0 => has_mem (hm.get hn hl) h0, fun _ hn => srcVal_of_has (hm.get hn hl), fun _ _ _ _ _ => rfl⟩


end Vsa.Compiler
