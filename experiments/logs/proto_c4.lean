import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- General: foldl-insert over a list L makes every element of L present with v,
-- and preserves keys not in L. Prove membership for k ∈ L.
theorem foldl_insert_mem (v : BitVec 8) (L : List Nat) (m : ExtHashMap Nat (BitVec 8)) :
    ∀ k, k ∈ L → (L.foldl (fun m k => m.insert k v) m)[k]? = some v := by
  induction L generalizing m with
  | nil => intro k hk; exact absurd hk (by simp)
  | cons x xs ih =>
    intro k hk
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with h | h
    · subst h
      -- after inserting x, later inserts of xs don't remove x; but x may be
      -- reinserted. Either way x present. Use: if x ∉ xs then ih gives... hmm.
      by_cases hx : x ∈ xs
      · exact ih (m.insert x v) k hx |>.trans (by rw [h] at hx ⊢; rfl) |>.symm ▸ (ih (m.insert x v) x hx)
      · sorry
    · exact ih (m.insert x v) k h
