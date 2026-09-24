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

/-- The walk's invariant depends only on `sp`, `s0`-`s3`, `a4`, `a6` and `t4`. -/
theorem BW.of_eq {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {nb : Nat} {R R' : Nat → BitVec 64} (W : BW C Mt brkv chunks bins nb R)
    (h2 : R' 2 = R 2) (h8 : R' 8 = R 8) (h9 : R' 9 = R 9) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19)
    (h14 : R' 14 = R 14) (h16 : R' 16 = R 16) (h29 : R' 29 = R 29) :
    BW C Mt brkv chunks bins nb R' :=
  ⟨W.frame.of_regs h2 h9 h18 h19, W.heap, W.nbok, W.nb31, W.b1, by rw [h14]; exact W.a4,
    by rw [h16]; exact W.a6, by rw [h29]; exact W.t4, by rw [h8]; exact W.s0⟩

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

theorem clr_keep {x m : BitVec 64} {b : Nat} (hm : m.toNat = 2 ^ b) (t : Nat)
    (ht : t ≠ b) (h : x.toNat / 2 ^ t % 2 = 1) :
    ((m ^^^ 18446744073709551615#64) &&& x).toNat / 2 ^ t % 2 = 1 := by
  have hx : x.toNat.testBit t = true := by rw [Nat.testBit_eq_decide_div_mod_eq]; simpa using h
  have htl : t < 64 := by
    refine Classical.byContradiction fun hc => ?_
    have : x.toNat < 2 ^ t := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt this] at h; simp at h
  have : ((m ^^^ 18446744073709551615#64) &&& x).toNat.testBit t = true := by
    rw [BitVec.toNat_and, BitVec.toNat_xor, hm, Nat.testBit_and, Nat.testBit_xor, hx,
      Nat.testBit_two_pow]
    simp only [show (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.testBit_two_pow_sub_one]
    simp [htl, Ne.symm ht]
  rw [Nat.testBit_eq_decide_div_mod_eq] at this
  simpa using this

theorem clr_le {x m : BitVec 64} : ((m ^^^ 18446744073709551615#64) &&& x).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

/-- The state at the next-block search (`0x80004e64`): the walk's invariant,
block `b`'s bit in `a0`, the bitmap `bb` (as in memory) in `a5`, the next
block's first bin in `t6`, and `31` in `t3`. -/
structure BWNext (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb b bb : Nat) (R : Nat → BitVec 64) : Prop where
  bw : BW C Mt brkv chunks bins nb R
  a0 : (R 10).toNat = 2 ^ b
  a5 : (R 15).toNat = bb
  t6 : (R 31).toNat = 4 * (b + 1)
  t3 : (R 28).toNat = 31
  bbr : read64 Mt binblocksAddr = some bb
  lo : binIndex nb < 4 * (b + 1)
  bl : b < 32

/-- **An exhausted block** (`0x80004e48`): the bins below the scan's start
are checked; all empty, the block's bit is cleared (`0x80004e54`). -/
theorem bw_clear {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb start : Nat} (hs4 : 4 ≤ start) (hsn : start < numBins)
    (hlo : binIndex nb < bend start)
    (hnext : ∀ R' Mt' bb', BWNext C Mt' brkv chunks bins nb (start / 4) bb' R' →
      AW C.live C.S C.Q 0x80004e64#64 R' Mt') :
    ∀ n i (R : Nat → BitVec 64), i - 4 * (start / 4) = n → 4 * (start / 4) ≤ i → i ≤ start →
      BW C Mt brkv chunks bins nb R → (R 17).toNat = i → (R 30).toNat = binAt i →
      (R 10).toNat = 2 ^ (start / 4) → (R 31).toNat = bend start → (R 28).toNat = 31 →
      (∀ j, i ≤ j → j < bend start → bins j = []) → AW C.live C.S C.Q 0x80004e48#64 R Mt := by
  intro n
  unfold bend at hlo
  induction n with
  | zero =>
    -- the block's first bin: clear the bit
    intro i R hn hi1 hi2 W h17 h30 h10 h31 h28 hemp
    unfold bend at h31 hemp
    have HH := W.heap.heap.heap.heap
    have hi : i = 4 * (start / 4) := by omega
    subst hi
    obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.1 HH.binblocks_present
    have hbbl := W.heap.heap.bb_lt bb hbb
    have ha6 := W.a6
    have hsplo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hsplo
    have hbbA : binblocksAddr = 2147593496 := rfl
    rw [← upd_self_eq ha6]
    refine st_80004e48 O.live ?_
    refine st_80004e4c O.live ?_
    refine st_80004e50 O.live (fun hc => absurd ?_ hc) (fun _ => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [show (sign_extend (m := 64) (0x003#12) : BitVec 64) = 3#64 from rfl, and3_toNat, h17]; simp
    refine st_80004e54 O.live (by sx_norm; decide) (by sx_norm; exact O.glob (by decide) (by decide)) ?_
    sx_norm
    rw [hbbA] at hbb
    simp (disch := decide) only [ldv_at hbb]
    refine st_80004e58 O.live ?_
    refine st_80004e5c O.live ?_
    refine st_80004e60 O.live (by sx_norm; decide) (by sx_norm; exact O.glob (by decide) (by decide)) ?_
    sx_norm
    have hbv : (BitVec.ofNat 64 bb).toNat = bb := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle := clr_le (x := BitVec.ofNat 64 bb) (m := R 10)
    rw [hbv] at hle
    have hoB := W.heap.off_stack (a := 2147593496) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    unfold mHead at hoB
    have hMH : MHeap C (writeLog Mt [(2147593496, 8, (R 10 ^^^ 18446744073709551615#64) &&&
        BitVec.ofNat 64 bb)]) brkv chunks bins := by
      refine ⟨W.heap.heap.clearBlock (b := start / 4) ?_ (by rw [hbbA]; exact read64_store_hit _ _ _)
        ?_ (by omega) ?_, pres_store W.heap.pres, W.heap.disj,
        frame_store (fun b h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩))) W.heap.frame⟩
      · intro i hi1 hi hib
        exact hemp i (by omega) (by omega)
      · intro bb0 hbb0 t ht hbit
        rw [hbbA, hbb] at hbb0; cases hbb0
        have := clr_keep (x := BitVec.ofNat 64 bb) h10 t ht (by rw [hbv]; exact hbit)
        exact this
      · intro a ha hna
        rw [hbbA] at hna
        exact writeLog_out _ _ _ (by simp only [OutL, and_true]; omega)
    refine hnext _ _ (((R 10 ^^^ 18446744073709551615#64) &&& BitVec.ofNat 64 bb).toNat)
      ⟨⟨(W.frame.store (by omega)).of_regs ?_ ?_ ?_ ?_, hMH, W.nbok, W.nb31, W.b1,
      ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by unfold numBins at hsn; omega⟩ <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact W.a4
    · exact W.t4
    · exact W.s0
    · exact h10
    · exact h31
    · exact h28
    · rw [hbbA]; exact read64_store_hit _ _ _
    · exact hlo
  | succ n ih =>
    intro i R hn hi1 hi2 W h17 h30 h10 h31 h28 hemp
    have HH := W.heap.heap.heap.heap
    have ha6 := W.a6
    have hi1n : i - 1 < numBins := by unfold numBins at hsn ⊢; omega
    have hg := binAt_geo (i - 1) hi1n
    have hring := (binList_iff_ring.1 (HH.bins_list (i - 1) (by omega) hi1n)).1
    obtain ⟨f, hf⟩ : ∃ f, (bins (i - 1) ++ [binAt (i - 1)]).head? = some f := by
      rcases bins (i - 1) with _ | ⟨z, zs⟩ <;> simp
    have hfd := ring_fd_head hring hf
    have hflt := Vsa.Sim.read64_lt _ _ _ hfd
    have hi4 : i % 4 ≠ 0 := by omega
    refine st_80004e48 O.live ?_
    refine st_80004e4c O.live ?_
    refine st_80004e50 O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
    rotate_left
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      intro he; apply hi4
      have := congrArg BitVec.toNat he
      rw [show (sign_extend (m := 64) (0x003#12) : BitVec 64) = 3#64 from rfl, and3_toNat, h17] at this
      simpa using this
    have hE : (R 30 + 18446744073709551600#64 + 16#64).toNat = binAt (i - 1) + 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, h30]; unfold binAt avAddr
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      unfold binAt avAddr at hg; omega
    refine st_80004e3c O.live ?_ ?_ ?_
    · sx_norm; rw [hE]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · sx_norm; rw [hE]; exact O.bin_link hi1n (.inl rfl)
    sx_norm
    rw [hE, ldv_at hfd _ rfl]
    refine st_80004e40 O.live ?_
    sx_norm
    have hE30 : (R 30 + 18446744073709551600#64).toNat = binAt (i - 1) := by
      rw [BitVec.toNat_add, h30]; unfold binAt avAddr
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      unfold binAt avAddr at hg; omega
    have h17' : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 17 + 18446744073709551615#64))).toNat
        = i - 1 := by
      have e : R 17 + 18446744073709551615#64 = R 17 - 1#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_sub, h17]; simp; omega
      rw [e]
      have hs : (R 17 - 1#64).toNat = i - 1 := by rw [BitVec.toNat_sub, h17]; simp; omega
      rw [toNat_sx32_small _ (by rw [hs]; unfold numBins at hi1n; omega), hs]
    refine st_80004e44 O.live (fun hne => ?_) (fun heq => ?_)
    · -- a lower bin holds chunks: keep the bit
      obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.1 HH.binblocks_present
      have hbbl := W.heap.heap.bb_lt bb hbb
      have hbbA : binblocksAddr = 2147593496 := rfl
      rw [← upd_self_eq ha6]
      refine st_80005060 O.live (by sx_norm; decide) (by sx_norm; exact O.glob (by decide) (by decide)) ?_
      sx_norm
      rw [hbbA] at hbb
      simp (disch := decide) only [ldv_at hbb]
      refine st_80005064 O.live ?_
      rw [← hbbA] at hbb
      refine hnext _ _ bb ⟨W.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, hbb, hlo,
        by unfold numBins at hsn; omega⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact ha6.symm
      · exact h10
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · exact h31
      · exact h28
    · -- empty too: on down
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at heq
      have hfb : f = binAt (i - 1) := by
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hflt, hE30] at this; exact this
      have hemp1 : bins (i - 1) = [] := by
        rcases h : bins (i - 1) with _ | ⟨z, zs⟩
        · rfl
        · exfalso
          rw [h] at hf; simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hf
          subst hf
          exact (binList_iff_ring.1 (HH.bins_list (i - 1) (by omega) hi1n)).2 z
            (by rw [h]; exact List.mem_cons_self) hfb
      refine ih (i - 1) _ (by omega) (by omega) (by omega)
        (W.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact h17'
      · exact hE30
      · exact h10
      · unfold bend; exact h31
      · exact h28
      · intro j hj1 hj2
        by_cases hj : j = i - 1
        · subst hj; exact hemp1
        · exact hemp j (by omega) hj2

theorem bit_test {m x : BitVec 64} {c : Nat} (hm : m.toNat = 2 ^ c) :
    m &&& x = 0#64 ↔ x.toNat / 2 ^ c % 2 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun y : BitVec 64 => y.toNat.testBit c) h
    simp only [BitVec.toNat_and, hm, Nat.testBit_and, Nat.testBit_two_pow_self, Bool.true_and] at h1
    have : (0#64 : BitVec 64).toNat.testBit c = false := by simp
    rw [this, Nat.testBit_eq_decide_div_mod_eq] at h1
    simp at h1; omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hm]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : c = i
    · subst hi; rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    · simp [hi]

/-- A bitmap at least `2 ^ c` has a set bit at or above `c`. -/
theorem exists_set_bit {bb c : Nat} (h : 2 ^ c ≤ bb) (hlt : bb < 2 ^ 32) :
    ∃ t, c ≤ t ∧ t < 32 ∧ bb / 2 ^ t % 2 = 1 := by
  have hb0 : bb ≠ 0 := by have := Nat.one_le_two_pow (n := c); omega
  refine ⟨bb.log2, ?_, ?_, ?_⟩
  · exact (Nat.le_log2 hb0).2 h
  · exact (Nat.log2_lt hb0).2 hlt
  · have h1 := Nat.log2_self_le hb0
    have h2 := Nat.lt_log2_self (n := bb)
    have : bb / 2 ^ bb.log2 = 1 := by
      have hp : 0 < 2 ^ bb.log2 := Nat.two_pow_pos _
      rw [Nat.pow_succ] at h2
      refine Nat.eq_of_le_of_lt_succ (Nat.le_div_iff_mul_le hp |>.2 (by omega)) ?_
      exact (Nat.div_lt_iff_lt_mul hp).2 (by omega)
    rw [this]

/-- The next-block search's continuation: the scan of block `c`, whose bit is
set, from its first bin. -/
abbrev BWBlockAt (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb b bb : Nat) : Prop :=
  ∀ (R' : Nat → BitVec 64) c, BW C Mt brkv chunks bins nb R' → b < c → c < 32 →
    bb / 2 ^ c % 2 = 1 → (R' 17).toNat = 4 * c → (R' 10).toNat = 2 ^ c → (R' 28).toNat = 31 →
    AW C.live C.S C.Q 0x800049a8#64 R' Mt

/-- The inner search (`0x80004e78`): bit `c` of the bitmap is clear; try the
next one. -/
theorem bw_next_loop {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb b bb t : Nat} (ht : bb / 2 ^ t % 2 = 1) (ht32 : t < 32)
    (hblk : BWBlockAt C Mt brkv chunks bins nb b bb) :
    ∀ d c (R : Nat → BitVec 64), t - c = d → b < c → c < t → BW C Mt brkv chunks bins nb R →
      (R 10).toNat = 2 ^ c → (R 31).toNat = 4 * c → (R 15).toNat = bb → (R 28).toNat = 31 →
      AW C.live C.S C.Q 0x80004e78#64 R Mt := by
  intro d
  induction d with
  | zero => intro c R h1 h2 h3; omega
  | succ d ih =>
    intro c R hd hbc hct W h10 h31 h15 h28
    refine st_80004e78 O.live ?_
    refine st_80004e7c O.live ?_
    refine st_80004e80 O.live ?_
    sx_norm
    have h10' : (R 10 <<< 1).toNat = 2 ^ (c + 1) := by
      rw [BitVec.toNat_shiftLeft, h10, Nat.shiftLeft_eq, Nat.pow_succ]
      have : 2 ^ c * 2 < 2 ^ 64 := by
        rw [← Nat.pow_succ]; exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have h31' : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 31 + 4#64))).toNat = 4 * (c + 1) := by
      rw [sx32_add_toNat (x := R 31) (k := 4) (by rw [h31]; omega), h31]; omega
    have hbt := bit_test (x := R 15) h10'
    rw [h15] at hbt
    refine st_80004e84 O.live (fun hz => ?_) (fun hnz => ?_)
    · -- bit `c + 1` clear: on
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz
      have hc1 : bb / 2 ^ (c + 1) % 2 = 0 := hbt.1 hz
      have hct' : c + 1 < t := by
        refine Nat.lt_of_le_of_ne hct ?_
        intro he; rw [he] at hc1; omega
      exact ih (c + 1) _ (by omega) (by omega) hct' (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h31')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h28)
    · -- bit `c + 1` set: its block
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hnz
      have hc1 : bb / 2 ^ (c + 1) % 2 = 1 := by
        have := mt hbt.2 hnz; omega
      refine st_80004e88 O.live ?_
      refine st_80004e8c O.live ?_
      exact hblk _ (c + 1) (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl) (by omega) (by omega) hc1
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; sx_norm; exact h31')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h28)

/-- **The next block** (`0x80004e64`): no set bit above block `b` sends the
walk to the top; otherwise the next set bit's block is scanned. -/
theorem bw_next {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb b bb : Nat}
    (N : BWNext C Mt brkv chunks bins nb b bb R)
    (htop : ∀ R', BW C Mt brkv chunks bins nb R' → AW C.live C.S C.Q 0x80004a2c#64 R' Mt)
    (hblk : BWBlockAt C Mt brkv chunks bins nb b bb) :
    AW C.live C.S C.Q 0x80004e64#64 R Mt := by
  have hbl := N.bl
  have hbb32 := N.bw.heap.heap.bb_lt bb N.bbr
  refine st_80004e64 O.live ?_
  refine st_80004e68 O.live ?_
  sx_norm
  have h10' : (R 10 <<< 1).toNat = 2 ^ (b + 1) := by
    rw [BitVec.toNat_shiftLeft, N.a0, Nat.shiftLeft_eq, Nat.pow_succ]
    have : 2 ^ b * 2 < 2 ^ 64 := by
      rw [← Nat.pow_succ]; exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have h1 : (R 10 <<< 1 + 18446744073709551615#64).toNat = 2 ^ (b + 1) - 1 := by
    rw [BitVec.toNat_add, h10']
    have := Nat.one_le_two_pow (n := b + 1)
    have : 2 ^ (b + 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) (by omega)
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  refine st_80004e6c O.live (fun hle => ?_) (fun hgt => ?_)
  · -- no set bit above: the top
    exact htop _ (N.bw.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, N.a5, h1] at hgt
    have hge : 2 ^ (b + 1) ≤ bb := by have := Nat.one_le_two_pow (n := b + 1); omega
    obtain ⟨t, ht1, ht2, ht3⟩ := exists_set_bit hge hbb32
    refine st_80004e70 O.live ?_
    sx_norm
    have hbt := bit_test (x := R 15) h10'
    rw [N.a5] at hbt
    refine st_80004e74 O.live (fun hnz => ?_) (fun hz => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hnz
      have hc1 : bb / 2 ^ (b + 1) % 2 = 1 := by have := mt hbt.2 hnz; omega
      refine st_80004e88 O.live ?_
      refine st_80004e8c O.live ?_
      exact hblk _ (b + 1) (N.bw.of_eq rfl rfl rfl rfl rfl rfl rfl rfl) (by omega) (by omega) hc1
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; sx_norm; exact N.t6)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.t3)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at hz
      have hc1 : bb / 2 ^ (b + 1) % 2 = 0 := hbt.1 hz
      have hbt' : b + 1 < t := by
        refine Nat.lt_of_le_of_ne ht1 ?_
        intro he; rw [← he] at ht3; omega
      exact bw_next_loop O ht3 ht2 hblk _ (b + 1) _ rfl (by omega) hbt'
        (N.bw.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.t6)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.a5)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.t3)

/-- **A block's scan** (`0x800049a8`): bin `start`'s header in `t5`/`t1`, its
last member in `a3`, then the bin loop from `start`. -/
theorem bw_block {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb start : Nat}
    (W : BW C Mt brkv chunks bins nb R) (h17 : (R 17).toNat = start)
    (h10 : (R 10).toNat = 2 ^ (start / 4)) (h28 : (R 28).toNat = 31)
    (hsf : ScanFrom chunks bins nb start) (hs1 : 1 < start) (hsn : start < numBins)
    (hblk : ∀ R', BWBlock C Mt brkv chunks bins nb start R' → (R' 31).toNat = bend start →
      (∀ j, start ≤ j → j < bend start → bins j = []) → AW C.live C.S C.Q 0x80004e48#64 R' Mt) :
    AW C.live C.S C.Q 0x800049a8#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  have ha6 := W.a6
  have hg := binAt_geo start hsn
  have hring := (binList_iff_ring.1 (HH.bins_list start (by omega) hsn)).1
  obtain ⟨l, hl⟩ : ∃ l, (binAt start :: bins start).getLast? = some l := ⟨_, List.getLast?_cons⟩
  have hbk := ring_bk_head hring hl
  have hbklt := Vsa.Sim.read64_lt _ _ _ hbk
  refine st_800049a8 O.live ?_
  refine st_800049ac O.live ?_
  refine st_800049b0 O.live ?_
  refine st_800049b4 O.live ?_
  refine st_800049b8 O.live ?_
  refine st_800049bc O.live ?_
  sx_norm
  have hT : (R 16 + ((BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 17 <<< 1 + 2#64))) <<< 3 +
      18446744073709551600#64)).toNat = binAt start := by
    have h1 : (R 17 <<< 1).toNat = 2 * start := by
      rw [BitVec.toNat_shiftLeft, h17, Nat.shiftLeft_eq]; unfold numBins at hsn; omega
    have h2 := sx32_add_toNat (x := R 17 <<< 1) (k := 2) (by rw [h1]; unfold numBins at hsn; omega)
    rw [h1] at h2
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, h2, ha6, Nat.shiftLeft_eq]
    unfold binAt avAddr; unfold numBins at hsn
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have hE : (R 16 + ((BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 17 <<< 1 + 2#64))) <<< 3 +
      18446744073709551600#64) + 24#64).toNat = binAt start + 24 := by
    rw [BitVec.toNat_add, hT]; unfold binAt avAddr at hg ⊢
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  refine st_800049c0 O.live ?_ ?_ ?_
  · sx_norm; rw [hE]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hE]; exact O.bin_link hsn (.inr rfl)
  sx_norm
  rw [hE, ldv_at hbk _ rfl]
  refine st_800049c4 O.live ?_
  refine bw_bins O hblk _ start _ rfl (Nat.le_refl _) (by unfold bend; omega)
    ⟨W.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, hsf, hs1, hsn⟩ ?_ ?_ ?_
    (fun j h1 h2 => absurd h2 (by omega)) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact h17
  · exact h10
  · exact hT
  · exact h28
  · exact hT
  · simp; exact h17
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbklt]
    rw [getLast_cons_rev] at hl; cases hl; rfl

/-- **A block from its scan to its clearing**: the scan (`bw_block`) finds
nothing, so the block's bins below the start are checked and its bit
possibly cleared (`bw_clear`) before the next-block search. -/
theorem bw_scan {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb start : Nat}
    (W : BW C Mt brkv chunks bins nb R) (h17 : (R 17).toNat = start)
    (h10 : (R 10).toNat = 2 ^ (start / 4)) (h28 : (R 28).toNat = 31)
    (hsf : ScanFrom chunks bins nb start) (hs4 : 4 ≤ start) (hsn : start < numBins)
    (hnext : ∀ R' Mt' bb', BWNext C Mt' brkv chunks bins nb (start / 4) bb' R' →
      AW C.live C.S C.Q 0x80004e64#64 R' Mt') :
    AW C.live C.S C.Q 0x800049a8#64 R Mt :=
  bw_block O W h17 h10 h28 hsf (by omega) hsn fun R' B h31 hemp => by
    have hlo : binIndex nb < start := by
      rcases hsf with h | ⟨x, sz, hx, _, _⟩
      · exact h
      · rw [hemp start (Nat.le_refl _) (by unfold bend; omega)] at hx; cases hx
    exact bw_clear O hs4 hsn (by unfold bend; omega) hnext _ start R' rfl (by omega) (Nat.le_refl _)
      B.bw B.a7 B.t5 B.a0 h31 B.t3 hemp

/-- The walk's exit to the top (`0x80004a2c`), from any memory. -/
abbrev BWTop (C : MCtx) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat) (nb : Nat) : Prop :=
  ∀ R' Mt', BW C Mt' brkv chunks bins nb R' → AW C.live C.S C.Q 0x80004a2c#64 R' Mt'

/-- **The walk over the blocks** (`0x80004e64` after block `b`): an induction
over the blocks left. -/
theorem bw_walk {C : MCtx} (O : MOK C) {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb : Nat} (htop : BWTop C brkv chunks bins nb) :
    ∀ n b Mt bb (R : Nat → BitVec 64), 32 - b ≤ n → BWNext C Mt brkv chunks bins nb b bb R →
      AW C.live C.S C.Q 0x80004e64#64 R Mt := by
  intro n
  induction n with
  | zero => intro b Mt bb R hn N; have := N.bl; omega
  | succ n ih =>
    intro b Mt bb R hn N
    refine bw_next O N (htop · Mt) fun R' c W hbc hc32 _ h17 h10 h28 => ?_
    have hlo := N.lo
    have hc4 : 4 * c / 4 = c := by omega
    refine bw_scan O W h17 (by rw [hc4]; exact h10) h28 (.inl (by omega)) (by omega)
      (by unfold numBins; omega) fun R'' Mt'' bb'' N'' => ?_
    rw [hc4] at N''
    exact ih c Mt'' bb'' R'' (by omega) N''

/-- **A found block** (`0x800049a4`): `t3 = 31`, then the walk from `start`. -/
theorem bw_found {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb start : Nat}
    (htop : BWTop C brkv chunks bins nb)
    (W : BW C Mt brkv chunks bins nb R) (h17 : (R 17).toNat = start)
    (h10 : (R 10).toNat = 2 ^ (start / 4))
    (hsf : ScanFrom chunks bins nb start) (hs4 : 4 ≤ start) (hsn : start < numBins) :
    AW C.live C.S C.Q 0x800049a4#64 R Mt := by
  refine st_800049a4 O.live ?_
  refine bw_scan O (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl) h17 h10 (by sx_norm) hsf hs4 hsn
    fun R' Mt' bb' N => bw_walk O htop _ _ Mt' bb' R' (Nat.le_refl _) N

/-- The initial search's loop (`0x80004994`): block `c`'s bit is clear; try
the next. -/
theorem bw_find_loop {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb bb t : Nat} (htop : BWTop C brkv chunks bins nb)
    (ht : bb / 2 ^ t % 2 = 1) (ht32 : t < 32) :
    ∀ d c (R : Nat → BitVec 64), t - c = d → c < t → BW C Mt brkv chunks bins nb R →
      (R 10).toNat = 2 ^ c → (R 17).toNat = 4 * c → (R 11).toNat = bb → binIndex nb < 4 * c →
      AW C.live C.S C.Q 0x80004994#64 R Mt := by
  intro d
  induction d with
  | zero => intro c R h1 h2; omega
  | succ d ih =>
    intro c R hd hct W h10 h17 h11 hlo
    refine st_80004994 O.live ?_
    refine st_80004998 O.live ?_
    refine st_8000499c O.live ?_
    sx_norm
    have h10' : (R 10 <<< 1).toNat = 2 ^ (c + 1) := by
      rw [BitVec.toNat_shiftLeft, h10, Nat.shiftLeft_eq, Nat.pow_succ]
      have : 2 ^ c * 2 < 2 ^ 64 := by
        rw [← Nat.pow_succ]; exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have h17' : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 17 + 4#64))).toNat = 4 * (c + 1) := by
      have := sx32_add_toNat (x := R 17) (k := 4) (by rw [h17]; omega)
      rw [h17] at this; rw [this]; omega
    have hbt := bit_test (x := R 11) h10'
    rw [h11] at hbt
    refine st_800049a0 O.live (fun hz => ?_) (fun hnz => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz
      have hc1 := hbt.1 hz
      have hct' : c + 1 < t := by
        refine Nat.lt_of_le_of_ne (by omega) ?_
        intro he; rw [he] at hc1; omega
      exact ih (c + 1) _ (by omega) hct' (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h11) (by omega)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hnz
      exact bw_found O htop (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
            rw [h10', show 4 * (c + 1) / 4 = c + 1 by omega])
        (.inl (by omega)) (by omega) (by unfold numBins; omega)

theorem binIndex_ge4 {nb : Nat} (h : 32 ≤ nb) : 4 ≤ binIndex nb := by
  unfold binIndex
  repeat (first | omega | split)

/-- The search's start is at or above the request's bin. -/
theorem scanFrom_ge {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb idx : Nat}
    (HH : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) (hsf : ScanFrom chunks bins nb idx)
    (h1 : 1 < idx) (hidx : idx < numBins) : binIndex nb ≤ idx := by
  rcases hsf with h | ⟨y, sy, hy, hfy, hly⟩
  · omega
  · obtain ⟨c, hc, hca, _, hbi⟩ := HH.bin_free idx y (by omega) hidx hy
    have := HH.chunk_eq hc hfy hca
    subst this
    rw [← hbi h1]
    exact binIndex_mono hly

/-- `_malloc_r`'s exit to the top, for the walk: `top_path`, `extend_top`. -/
theorem bwTop {C : MCtx} (O : MOK C) {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb : Nat} : BWTop C brkv chunks bins nb := fun R' _ W =>
  top_path O W.frame W.heap (idx := (R' 17).toNat) ⟨W.a4, rfl, W.a6⟩ W.s0 W.nbok W.nb31
    fun hsm _ F4 G4 T4 h84 => extend_top O F4 W.heap G4 T4 h84 W.nbok W.nb31 hsm

/-- **The block walk** (`0x80004978`): the first block at or above the
request's with its bit set, then the walk (`bw_found`, `bw_find_loop`). -/
theorem bw_find {C : MCtx} (O : MOK C) :
    ∀ R' Mt brkv' chunks' bins' nb idx bb, MFrame C R' Mt →
      MHeap C Mt brkv' chunks' bins' → bins' 1 = [] → ScanFrom chunks' bins' nb idx →
      NbOK C.n nb → nb < 2 ^ 31 → idx < numBins → 1 < idx → LRRegs nb idx R' →
      (R' 29).toNat = binAt 1 → R' 8 = reentV → read64 Mt binblocksAddr = some bb →
      2 ^ (idx / 4) ≤ bb → (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
      AW C.live C.S C.Q 0x80004978#64 R' Mt := by
  intro R Mt brkv chunks bins nb idx bb F Hp hb1 hsf hnb hnb31 hidx hidx1 G h29 h8 hbb hle h11 h10
  have HH := Hp.heap.heap.heap
  have W : BW C Mt brkv chunks bins nb R := ⟨F, Hp, hnb, hnb31, hb1, G.a4, G.a6, h29, h8⟩
  have hge := scanFrom_ge HH hsf hidx1 hidx
  have h4 := binIndex_ge4 hnb.lo
  have hbbl := Hp.heap.bb_lt bb hbb
  have h17 := G.a7
  have hbt := bit_test (x := R 11) h10
  rw [h11] at hbt
  refine st_80004978 O.live ?_
  refine st_8000497c O.live (fun hnz => ?_) (fun hz => ?_)
  · exact bw_found O (bwTop O) (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10) hsf (by omega) hidx
  · simp only [upd_apply, ite_true, ne_eq, Decidable.not_not] at hz
    have hc0 := hbt.1 hz
    have hemp : bins idx = [] := by
      refine Classical.byContradiction fun hne => ?_
      have := HH.binblocks bb hbb idx hidx1 hidx hne; omega
    have hlo : binIndex nb < idx := by
      rcases hsf with h | ⟨x, _, hx, _, _⟩
      · exact h
      · rw [hemp] at hx; cases hx
    have hle' : 2 ^ (idx / 4 + 1) ≤ bb := by
      have hp : 0 < 2 ^ (idx / 4) := Nat.two_pow_pos _
      have h1 : 1 ≤ bb / 2 ^ (idx / 4) := (Nat.le_div_iff_mul_le hp).2 (by omega)
      have h2 : 2 ≤ bb / 2 ^ (idx / 4) := by omega
      have := (Nat.le_div_iff_mul_le hp).1 h2
      rw [Nat.pow_succ]; omega
    refine st_80004980 O.live ?_
    refine st_80004984 O.live ?_
    refine st_80004988 O.live ?_
    refine st_8000498c O.live ?_
    sx_norm
    have h10' : (R 10 <<< 1).toNat = 2 ^ (idx / 4 + 1) := by
      rw [BitVec.toNat_shiftLeft, h10, Nat.shiftLeft_eq, Nat.pow_succ]
      have : 2 ^ (idx / 4) * 2 < 2 ^ 64 := by
        rw [← Nat.pow_succ]; exact Nat.pow_lt_pow_right (by omega) (by unfold numBins at hidx; omega)
      omega
    have h17' : (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        ((R 17 &&& 18446744073709551612#64) + 4#64))).toNat = 4 * (idx / 4 + 1) := by
      have hm : (R 17 &&& 18446744073709551612#64).toNat = 4 * (idx / 4) := by
        rw [toNat_and_m4, h17]; omega
      have := sx32_add_toNat (x := R 17 &&& 18446744073709551612#64) (k := 4)
        (by rw [hm]; unfold numBins at hidx; omega)
      rw [hm] at this; rw [this]; omega
    have hbt' := bit_test (x := R 11) h10'
    rw [h11] at hbt'
    refine st_80004990 O.live (fun hnz => ?_) (fun hz => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq] at hnz
      have hc1 : bb / 2 ^ (idx / 4 + 1) % 2 = 1 := by have := mt hbt'.2 hnz; omega
      have hc32 : idx / 4 + 1 < 32 := by
        refine Classical.byContradiction fun hc => ?_
        have : bb / 2 ^ (idx / 4 + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hbbl
          (Nat.pow_le_pow_right (by omega) (by omega)))
        omega
      exact bw_found O (bwTop O) (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
            rw [h10', show 4 * (idx / 4 + 1) / 4 = idx / 4 + 1 by omega])
        (.inl (by omega)) (by omega) (by unfold numBins; omega)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq,
        Decidable.not_not] at hz
      have hc1 := hbt'.1 hz
      obtain ⟨t, ht1, ht2, ht3⟩ := exists_set_bit hle' hbbl
      have hlt : idx / 4 + 1 < t := by
        refine Nat.lt_of_le_of_ne ht1 ?_
        intro he; rw [← he] at ht3; omega
      exact bw_find_loop O (bwTop O) ht3 ht2 _ (idx / 4 + 1) _ rfl hlt
        (W.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17')
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h11) (by omega)

/-- **`_malloc_r` from its entry, on every path.** `malloc_paths` with its
last join, the block walk (`bw_find`), discharged. -/
theorem malloc_all {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : MEntry C R) (Hp : MHeap C C.Mt0 brkv chunks bins) :
    AW C.live C.S C.Q 0x800047a8#64 R C.Mt0 :=
  malloc_paths O E Hp (bw_find O)

end VsaIris.VsaHeap
