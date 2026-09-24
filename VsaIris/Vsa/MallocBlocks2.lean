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

end VsaIris.VsaHeap
