import VsaIris.Vsa.ReallocDec

/-!
# Word copies

`_realloc_r` copies the old payload word by word, forwards: its unrolled
copies and `memmove`'s forward loops all store word `i` of the source at word
`i` of the destination in order. `copyW m d s j` is the memory after the
first `j` such copies; `copyW_spec` gives its contents when the destination
does not start above the source or lies wholly above it.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Eight present bytes make a doubleword. -/
theorem read64_of_present {m : Mem} {a : Nat} (h : ∀ k, k < 8 → (m[a + k]?).isSome) :
    ∃ v, read64 m a = some v := by
  obtain ⟨b0, e0⟩ := Option.isSome_iff_exists.1 (h 0 (by omega))
  obtain ⟨b1, e1⟩ := Option.isSome_iff_exists.1 (h 1 (by omega))
  obtain ⟨b2, e2⟩ := Option.isSome_iff_exists.1 (h 2 (by omega))
  obtain ⟨b3, e3⟩ := Option.isSome_iff_exists.1 (h 3 (by omega))
  obtain ⟨b4, e4⟩ := Option.isSome_iff_exists.1 (h 4 (by omega))
  obtain ⟨b5, e5⟩ := Option.isSome_iff_exists.1 (h 5 (by omega))
  obtain ⟨b6, e6⟩ := Option.isSome_iff_exists.1 (h 6 (by omega))
  obtain ⟨b7, e7⟩ := Option.isSome_iff_exists.1 (h 7 (by omega))
  simp only [Nat.add_zero] at e0
  simp only [read64, readLE, Nat.add_assoc, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  exact ⟨_, rfl⟩

/-- Two doublewords with one value have the same bytes. -/
theorem bytes_of_read64_eq2 {m m' : Mem} {a b v : Nat} (h : read64 m a = some v)
    (h' : read64 m' b = some v) : ∀ k, k < 8 → m'[b + k]? = m[a + k]? := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hv⟩ := read64_bytes m a v h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hv'⟩ := read64_bytes m' b v h'
  have l0 := b0.isLt; have l1 := b1.isLt; have l2 := b2.isLt; have l3 := b3.isLt
  have l4 := b4.isLt; have l5 := b5.isLt; have l6 := b6.isLt; have l7 := b7.isLt
  have k0 := c0.isLt; have k1 := c1.isLt; have k2 := c2.isLt; have k3 := c3.isLt
  have k4 := c4.isLt; have k5 := c5.isLt; have k6 := c6.isLt; have k7 := c7.isLt
  have q0 : c0 = b0 := BitVec.eq_of_toNat_eq (by omega)
  have q1 : c1 = b1 := BitVec.eq_of_toNat_eq (by omega)
  have q2 : c2 = b2 := BitVec.eq_of_toNat_eq (by omega)
  have q3 : c3 = b3 := BitVec.eq_of_toNat_eq (by omega)
  have q4 : c4 = b4 := BitVec.eq_of_toNat_eq (by omega)
  have q5 : c5 = b5 := BitVec.eq_of_toNat_eq (by omega)
  have q6 : c6 = b6 := BitVec.eq_of_toNat_eq (by omega)
  have q7 : c7 = b7 := BitVec.eq_of_toNat_eq (by omega)
  intro k hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simpa [e0, f0] using congrArg some q0
  · rw [e1, f1, q1]
  · rw [e2, f2, q2]
  · rw [e3, f3, q3]
  · rw [e4, f4, q4]
  · rw [e5, f5, q5]
  · rw [e6, f6, q6]
  · rw [e7, f7, q7]
  · omega

/-- The memory after copying `j` words from `s` to `d`, forwards. -/
def copyW (m : Mem) (d s : Nat) : Nat → Mem
  | 0 => m
  | j + 1 => writeLog (copyW m d s j) [(d + 8 * j, 8, ldv .ld (copyW m d s j) (s + 8 * j))]

theorem copyW_zero (m : Mem) (d s : Nat) : copyW m d s 0 = m := rfl

theorem copyW_succ (m : Mem) (d s j : Nat) :
    copyW m d s (j + 1) =
      writeLog (copyW m d s j) [(d + 8 * j, 8, ldv .ld (copyW m d s j) (s + 8 * j))] := rfl

/-- Bytes outside the destination are kept. -/
theorem copyW_out {m : Mem} {d s a : Nat} :
    ∀ {j : Nat}, (a < d ∨ d + 8 * j ≤ a) → (copyW m d s j)[a]? = m[a]?
  | 0, _ => rfl
  | j + 1, h => by
    have ho : OutL [(d + 8 * j, 8, ldv .ld (copyW m d s j) (s + 8 * j))] a := ⟨by simp only; omega, trivial⟩
    rw [copyW_succ, writeLog_out _ _ _ ho]
    exact copyW_out (by omega)

/-- Presence is kept. -/
theorem copyW_present {m : Mem} {d s a : Nat} :
    ∀ {j : Nat}, (m[a]?).isSome → ((copyW m d s j)[a]?).isSome
  | 0, h => h
  | _ + 1, h => writeLog_present _ _ _ (copyW_present h)

/-- **A forward word copy**: with the destination not above the source, or
wholly above it, each copied byte reads as the source's. -/
theorem copyW_spec {m : Mem} {d s : Nat} :
    ∀ {j : Nat}, (d ≤ s ∨ s + 8 * j ≤ d) → (∀ i, i < 8 * j → (m[s + i]?).isSome) →
      ∀ i, i < 8 * j → (copyW m d s j)[d + i]? = m[s + i]?
  | 0, _, _, i, hi => by omega
  | j + 1, hov, hp, i, hi => by
    have IH := copyW_spec (m := m) (d := d) (s := s) (j := j) (by omega)
      (fun i hi => hp i (by omega))
    by_cases hlo : i < 8 * j
    · have ho : OutL [(d + 8 * j, 8, ldv .ld (copyW m d s j) (s + 8 * j))] (d + i) :=
        ⟨by simp only; omega, trivial⟩
      rw [copyW_succ, writeLog_out _ _ _ ho]
      exact IH i hlo
    · -- the `j`-th word: the source word, still intact
      have hsrc : ∀ k, k < 8 → (copyW m d s j)[s + 8 * j + k]? = m[s + 8 * j + k]? :=
        fun k hk => copyW_out (by omega)
      obtain ⟨v, hv⟩ := read64_of_present (m := copyW m d s j) (a := s + 8 * j) fun k hk => by
        rw [hsrc k hk, show s + 8 * j + k = s + (8 * j + k) by omega]; exact hp _ (by omega)
      have hvlt := Vsa.Sim.read64_lt _ _ _ hv
      have hld : ldv .ld (copyW m d s j) (s + 8 * j) = BitVec.ofNat 64 v :=
        ldv_ld (by rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt])
      have hw : read64 (copyW m d s (j + 1)) (d + 8 * j) = some v := by
        rw [copyW_succ, hld, read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
      have := bytes_of_read64_eq2 hv hw (i - 8 * j) (by omega)
      rw [show d + 8 * j + (i - 8 * j) = d + i by omega] at this
      rw [this, hsrc _ (by omega), show s + 8 * j + (i - 8 * j) = s + i by omega]

end VsaIris.VsaHeap
