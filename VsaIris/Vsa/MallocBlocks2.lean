import VsaIris.Vsa.MallocBlocks

/-!
# `_malloc_r`'s block walk: the loops

The bin loop within a block (`bw_bins`), the check of the bins below the
scan's start and the clearing of an exhausted block's bit (`bw_clear`), the
search for the next set bit (`bw_next`, `bw_find`), and the walk over the
blocks (`bw_walk`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `x & 3` is `x mod 4`. -/
theorem and3_toNat (x : BitVec 64) : (x &&& 3#64).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and, show (3#64 : BitVec 64).toNat = 2 ^ 2 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The state of a block's scan: the walk's invariant, the scan's start bin
`start` in `a7` (its block's bit in `a0`, its header in `t5`), `31` in `t3`,
and the search may start at `start`. -/
structure BWBlock (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb start : Nat) (R : Nat → BitVec 64) : Prop where
  bw : BW C Mt brkv chunks bins nb R
  a7 : (R 17).toNat = start
  a0 : (R 10).toNat = 2 ^ (start / 4)
  t5 : (R 30).toNat = binAt start
  t3 : (R 28).toNat = 31
  sf : ScanFrom chunks bins nb start
  s1 : 1 < start
  sn : start < numBins

theorem BWBlock.keep {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb start : Nat} {R R' : Nat → BitVec 64}
    (B : BWBlock C Mt brkv chunks bins nb start R)
    (h : ∀ x, x ≠ 6 → x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 15 → x ≠ 31 → R' x = R x) :
    BWBlock C Mt brkv chunks bins nb start R' where
  bw := ⟨B.bw.frame.of_regs (h 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (h 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (h 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (h 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    B.bw.heap, B.bw.nbok, B.bw.nb31, B.bw.b1,
    by rw [h 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.bw.a4,
    by rw [h 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.bw.a6,
    by rw [h 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.bw.t4,
    by rw [h 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.bw.s0⟩
  a7 := by rw [h 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.a7
  a0 := by rw [h 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.a0
  t5 := by rw [h 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.t5
  t3 := by rw [h 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact B.t3
  sf := B.sf
  s1 := B.s1
  sn := B.sn

theorem getLast_cons_rev (b : Nat) (l : List Nat) :
    (b :: l).getLast? = some (l.reverse.head?.getD b) := by
  rw [List.getLast?_eq_head?_reverse, List.reverse_cons]
  cases h : l.reverse with
  | nil => simp
  | cons x xs => simp

/-- The end of a block's scan: `t6` at the next block. -/
abbrev bend (start : Nat) : Nat := 4 * (start / 4 + 1)

/-- **The bin loop** (`0x800049c8` for bin `k`): scan bin `k` (`bw_member`);
exhausted, it is empty, and the scan moves to bin `k + 1`, or leaves the block
at `0x80004e48` with all of `[start, bend start)` empty. -/
theorem bw_bins {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb start : Nat}
    (hblk : ∀ R', BWBlock C Mt brkv chunks bins nb start R' → (R' 31).toNat = bend start →
      (∀ j, start ≤ j → j < bend start → bins j = []) → AW C.live C.S C.Q 0x80004e48#64 R' Mt) :
    ∀ n k (R : Nat → BitVec 64), bend start - k = n → start ≤ k → k < bend start →
      BWBlock C Mt brkv chunks bins nb start R → (R 6).toNat = binAt k → (R 31).toNat = k →
      (R 13).toNat = (bins k).reverse.head?.getD (binAt k) →
      (∀ j, start ≤ j → j < k → bins j = []) → AW C.live C.S C.Q 0x800049c8#64 R Mt := by
  intro n
  induction n with
  | zero => intro k R hn h1 h2; omega
  | succ n ih =>
    intro k R hn hsk hkb B h6 h31 h13 hprev
    unfold bend at hn hkb hblk
    have HH := B.bw.heap.heap.heap.heap
    have hsn := B.sn; have hs1 := B.s1
    have hkn : k < numBins := by unfold numBins at hsn ⊢; omega
    refine bw_member O B.bw (by omega) hkn h6 B.t3 ?_ (bins k).reverse [] R (by simp) (by simp [AllSmall])
      (fun _ _ _ _ _ => rfl) h13
    intro R' hsm hkp h13'
    have hemp : bins k = [] := scanFrom_empty HH B.sf B.s1 hsk hkn hsm
    have hk31 : (R' 31).toNat = k := by rw [hkp 31 (by decide) (by decide) (by decide) (by decide)]; exact h31
    have hk6 : (R' 6).toNat = binAt k := by rw [hkp 6 (by decide) (by decide) (by decide) (by decide)]; exact h6
    have hgk := binAt_geo k hkn
    refine st_80004cfc O.live ?_
    refine st_80004d00 O.live ?_
    refine st_80004d04 O.live ?_
    sx_norm
    have hk1 : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R' 31 + 1#64))).toNat = k + 1 := by
      have := sx32_add_toNat (x := R' 31) (k := 1) (by rw [hk31]; unfold numBins at hkn; omega)
      rw [hk31] at this; exact this
    have hB' : ∀ R'' : Nat → BitVec 64, (∀ x, x ≠ 6 → x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 15 →
        x ≠ 31 → R'' x = R' x) → BWBlock C Mt brkv chunks bins nb start R'' := fun R'' h =>
      B.keep fun x h6 h11 h12 h13 h15 h31 => (h x h6 h11 h12 h13 h15 h31).trans
        (hkp x h11 h12 h13 h15)
    refine st_80004d08 O.live (fun hz => ?_) (fun hnz => ?_)
    · -- the block's end
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz
      have hz' := congrArg BitVec.toNat hz
      rw [show (3#64 : BitVec 64) = (3#64 : BitVec 64) from rfl, and3_toNat, hk1] at hz'
      simp at hz'
      refine hblk _ (hB' _ fun x h6 h11 h12 h13 h15 h31 => by
        simp only [upd_apply, h6, h15, h31, ite_false]) (by
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hk1]; omega) ?_
      intro j hj1 hj2
      by_cases hjk : j = k
      · subst hjk; exact hemp
      · exact hprev j hj1 (by omega)
    · -- the next bin
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hnz
      have hnz' : (k + 1) % 4 ≠ 0 := by
        intro h0; apply hnz; apply BitVec.eq_of_toNat_eq
        rw [and3_toNat, hk1]; simp; omega
      have hk1n : k + 1 < numBins := by unfold numBins at hkn ⊢; omega
      have hgk1 := binAt_geo (k + 1) hk1n
      have hring := (binList_iff_ring.1 (HH.bins_list (k + 1) (by omega) hk1n)).1
      obtain ⟨l, hl⟩ : ∃ l, (binAt (k + 1) :: bins (k + 1)).getLast? = some l := ⟨_, List.getLast?_cons⟩
      have hbk := ring_bk_head hring hl
      have hbklt := Vsa.Sim.read64_lt _ _ _ hbk
      have hE : (R' 6 + 16#64 + 24#64).toNat = binAt (k + 1) + 24 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, hk6]; unfold binAt avAddr at hgk ⊢
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      refine st_80004d0c O.live ?_ ?_ ?_
      · sx_norm; rw [hE]; unfold LdOK Vsa.Sim.tohostAddr; omega
      · sx_norm; rw [hE]; exact O.bin_link hk1n (.inr rfl)
      sx_norm
      rw [hE, ldv_at hbk _ rfl]
      refine st_80004d10 O.live ?_
      refine ih (k + 1) _ (by unfold bend; omega) (by omega) (by unfold bend; omega)
        (hB' _ fun x h6 h11 h12 h13 h15 h31 => by
          simp only [upd_apply, h6, h13, h15, h31, ite_false]) ?_ ?_ ?_ ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [BitVec.toNat_add, hk6]; unfold binAt avAddr at hgk ⊢
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      · exact hk1
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbklt]
        rw [getLast_cons_rev] at hl; cases hl; rfl
      · intro j hj1 hj2
        by_cases hjk : j = k
        · subst hjk; exact hemp
        · exact hprev j hj1 (by omega)

end VsaIris.VsaHeap
