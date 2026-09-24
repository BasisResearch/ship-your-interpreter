import VsaIris.Vsa.MallocRebin

/-!
# Re-binning a large last remainder

A last remainder of more than 511 bytes that is smaller than the request goes
to its large bin (`0x80004c70`), which is kept sorted by size:

* `lbin_idx`: the six-way cascade computing `binIndex sz` and the address of
  the bin's `fd` word;
* the bin is empty: set its block bit and make the remainder its only member;
* otherwise walk the bin from its first member while the member is larger,
  and link the remainder in before the first one that is not.

The heap edit is `PHeapAt.moveBinAt`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A sign-extended 32-bit sum that fits is the sum. -/
theorem sx32_add_toNat {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (x + BitVec.ofNat 64 k))).toNat = x.toNat + k := by
  have hs : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [toNat_sx32_small _ (by rw [hs]; omega), hs]

/-- The registers the large-bin cascade leaves at `0x80004c94`: the offset of
bin `binIndex sz`'s `fd` word from `__malloc_av_` in `a0`, the index in `a2`;
everything else but `a3` kept. -/
structure LBinIdx (sz : Nat) (R R' : Nat → BitVec 64) : Prop where
  a0 : (R' 10).toNat = 16 * binIndex sz + 16
  a2 : (R' 12).toNat = binIndex sz
  keep : ∀ x, x ≠ 10 → x ≠ 12 → x ≠ 13 → R' x = R x

/-- The cascade's `fd` offset: `sext32 ((y << 1) + K) << 3`. -/
theorem cascade_off {x : BitVec 64} {y K : Nat} (hx : x.toNat = y) (h : 2 * y + K < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (x <<< 1 + BitVec.ofNat 64 K)) <<< 3).toNat =
      (2 * y + K) * 8 := by
  have h1 : (x <<< 1).toNat = 2 * y := by
    rw [BitVec.toNat_shiftLeft, hx, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_shiftLeft, sx32_add_toNat (by rw [h1]; omega), h1, Nat.shiftLeft_eq]
  omega

theorem binIndex_large {sz : Nat} (h : 512 ≤ sz) : 57 ≤ binIndex sz ∧ binIndex sz ≤ 126 := by
  unfold binIndex
  repeat' split
  all_goals omega

/-- `binIndex` is monotone. -/
theorem binIndex_mono {a b : Nat} (h : a ≤ b) : binIndex a ≤ binIndex b := by
  unfold binIndex
  repeat' split
  all_goals omega

/-- **Where the block search may start.** Every nonempty bin from `idx` up
holds a chunk of at least `nb` bytes: either `idx` is above the request's own
bin (so, by `binIndex_mono`, every chunk from there up is larger), or bin `idx`
has such a chunk. The search clears the bit of a block it exhausted, which
keeps `HeapAt.binblocks` only because of this. -/
def ScanFrom (chunks : List Chunk) (bins : Nat → List Nat) (nb idx : Nat) : Prop :=
  binIndex nb < idx ∨ ∃ x sz, x ∈ bins idx ∧ FreeAt chunks x sz ∧ nb ≤ sz

/-- **The large-bin cascade** (`0x80004c70`): from the chunk size in `t1`,
`binIndex sz` and its bin's `fd` offset. -/
theorem lbin_idx {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {sz : Nat}
    (h6 : (R 6).toNat = sz) (hlo : 512 ≤ sz) (hhi : sz < 2 ^ 31)
    (hk : ∀ R', LBinIdx sz R R' → AW C.live C.S C.Q 0x80004c94#64 R' Mt) :
    AW C.live C.S C.Q 0x80004c70#64 R Mt := by
  have hbi := binIndex_large hlo
  refine st_80004c70 O.live ?_
  refine st_80004c74 O.live ?_
  sx_norm
  have hx : (R 6 >>> 9).toNat = sz / 512 := by
    rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
  refine st_80004c78 O.live (fun h4 => ?_) (fun h4 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h4
  · -- `sz / 512 ≤ 4`: bins 57 to 64
    have h4' : sz / 512 ≤ 4 := by simpa using h4
    sx_run [8] O.live at 0x80004c94
    have hy : (R 6 >>> 6).toNat = sz / 64 := by
      rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
    have hb : binIndex sz = 56 + sz / 64 := by
      unfold binIndex; rw [if_neg (by omega), if_pos h4']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]
  -- `sz / 512 > 4`
  have h4' : ¬ sz / 512 ≤ 4 := by simpa using h4
  refine st_80004c7c O.live ?_
  refine st_80004c80 O.live (fun h20 => ?_) (fun h20 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h20
  rotate_left
  · -- `sz / 512 ≤ 20`: bins 92 to 111
    have h20' : sz / 512 ≤ 20 := by sx_norm; omega
    sx_run [8] O.live at 0x80004c94
    have hy : (R 6 >>> 9).toNat = sz / 512 := by
      rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
    have hb : binIndex sz = 91 + sz / 512 := by
      unfold binIndex; rw [if_neg (by omega), if_neg h4', if_pos h20']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]
  have h20' : 20 < sz / 512 := by sx_norm; omega
  refine st_80004f1c O.live ?_
  refine st_80004f20 O.live (fun h84 => ?_) (fun h84 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h84
  rotate_left
  · -- `sz / 512 ≤ 84`: bins 111 to 120
    have h84' : sz / 512 ≤ 84 := by sx_norm; omega
    sx_run [8] O.live at 0x80004c94
    have hy : (R 6 >>> 12).toNat = sz / 4096 := by
      rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
    have hb : binIndex sz = 110 + sz / 4096 := by
      unfold binIndex; rw [if_neg (by omega), if_neg h4', if_neg (by omega), if_pos h84']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]
  have h84' : 84 < sz / 512 := by sx_norm; omega
  refine st_80004fa0 O.live ?_
  refine st_80004fa4 O.live (fun h340 => ?_) (fun h340 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h340
  rotate_left
  · -- `sz / 512 ≤ 340`: bins 120 to 124
    have h340' : sz / 512 ≤ 340 := by sx_norm; omega
    sx_run [8] O.live at 0x80004c94
    have hy : (R 6 >>> 15).toNat = sz / 32768 := by
      rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
    have hb : binIndex sz = 119 + sz / 32768 := by
      unfold binIndex; rw [if_neg (by omega), if_neg h4', if_neg (by omega), if_neg (by omega), if_pos h340']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]
  have h340' : 340 < sz / 512 := by sx_norm; omega
  refine st_80005024 O.live ?_
  refine st_80005028 O.live (fun h1364 => ?_) (fun h1364 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h1364
  rotate_left
  · -- `sz / 512 ≤ 1364`: bins 124 to 126
    have h1364' : sz / 512 ≤ 1364 := by sx_norm; omega
    sx_run [8] O.live at 0x80004c94
    have hy : (R 6 >>> 18).toNat = sz / 262144 := by
      rw [BitVec.toNat_ushiftRight, h6, Nat.shiftRight_eq_div_pow]
    have hb : binIndex sz = 124 + sz / 262144 := by
      unfold binIndex; rw [if_neg (by omega), if_neg h4', if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h1364']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]
  -- the last bin, 126
  have h1364' : 1364 < sz / 512 := by sx_norm; omega
  sx_run [8] O.live at 0x80004c94
  have hb : binIndex sz = 126 := by
    unfold binIndex; rw [if_neg (by omega), if_neg h4', if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hb]; rfl
  · rw [hb]; rfl
  · intro x h10 h12 h13; simp only [upd_apply, h10, h12, h13, ite_false]

/-- **The heap after a re-binning into bin `j` between `pred` and `succ`.**
The machine's four link stores (`v`'s `bk` and `fd`, `pred`'s `fd`, `succ`'s
`bk`) over a memory `M0` that differs from the detached heap `Mt'` at most on
the bitmap, holding `bb'` with bin `j`'s block bit set. -/
theorem rebin_at_heap {C : MCtx} {Mt Mt' M0 : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {v sz j pred succ bb bb' : Nat} {pre' post' : List Nat}
    (Hp : MHeap C Mt brkv chunks bins) (D : MDetach C Mt Mt' bins 1 v) (hfree : FreeAt chunks v sz)
    (hj0 : 1 < j) (hj : j < numBins) (hidx : binIndex sz = j)
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hbb : read64 Mt binblocksAddr = some bb)
    (hM0 : ∀ a : Nat, ¬ (binblocksAddr ≤ a ∧ a < binblocksAddr + 8) → M0[a]? = Mt'[a]?)
    (hP0 : ∀ a : Nat, (Mt'[a]?).isSome → (M0[a]?).isSome)
    (hbb0 : read64 M0 binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : bb' / 2 ^ (j / 4) % 2 = 1) (hbbkeep : ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    {w0 w1 w2 : BitVec 64} (h0 : w0.toNat = pred) (h1 : w1.toNat = succ) (h2 : w2.toNat = v) :
    MHeap C (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)])
      brkv chunks (updBins (updBins bins 1 []) j (pre' ++ v :: post')) := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hbnd := HH.walk.chunk_bounds _ hfree
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  simp only at hbnd hv16
  unfold heapStart at hbnd
  have hgj := binAt_geo j hj
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  have hvmem : v ∈ bins 1 := by rw [D.bin]; exact List.mem_cons_self
  have hvJ : v ∉ bins j := fun hc => by
    have := HH.bin_unique (by omega) hj (by decide) (by unfold numBins; decide) hc hvmem; omega
  -- the insertion point's nodes
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hpos]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  have hloc : ∀ x, (x = binAt j ∨ x ∈ bins j) →
      x % 16 = 0 ∧ x ≠ v ∧ (x = binAt j ∨ (0x8001c170 ≤ x ∧ x + 32 ≤ C.top0)) ∧
        ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (x + k) := by
    intro x hx
    obtain ⟨hx16, hxn⟩ := HH.node (by omega) hj hx
    refine ⟨hx16, ?_, ?_, B.node_foot (by omega) hj hx⟩
    · rcases hx with rfl | h
      · unfold binAt avAddr at hgj ⊢; omega
      · exact fun he => hvJ (he ▸ h)
    · rcases hxn with h | ⟨cx, hcx, rfl, _, _⟩
      · exact .inl h
      · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
  obtain ⟨hp16, hpv, hploc, hpf⟩ := hloc pred hpm
  obtain ⟨hs16, hsv, hsloc, hsf⟩ := hloc succ hsm
  unfold binAt avAddr at hgj hg1 hploc hsloc
  have hbbA : binblocksAddr = 2147593496 := rfl
  have hb1 : binAt 1 = 2147593504 := rfl
  have e1 : fdOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) (binAt 1) =
      some (binAt 1) := by
    show read64 _ (binAt 1 + 16) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega), read64_keep fun k hk => hM0 _ (by rw [hbbA, hb1]; omega)]
    exact D.fd
  have e2 : bkOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) (binAt 1) =
      some (binAt 1) := by
    show read64 _ (binAt 1 + 24) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega), read64_keep fun k hk => hM0 _ (by rw [hbbA, hb1]; omega)]
    exact D.bk
  have e3 : fdOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) v =
      some succ := by
    show read64 _ (v + 16) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_store_hit, h1]
  have e4 : bkOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) v =
      some pred := by
    show read64 _ (v + 24) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_store_hit, h0]
  have e5 : fdOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) pred =
      some v := by
    show read64 _ (pred + 16) = _
    rw [read64_miss _ _ (by omega), read64_store_hit, h2]
  have e6 : bkOf (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)]) succ =
      some v := by
    show read64 _ (succ + 24) = _
    rw [read64_store_hit, h2]
  have e7 : read64 (writeLog (writeLog (writeLog (writeLog M0
      [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)])
      binblocksAddr = some bb' := by
    rw [hbbA]
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega)]
    rw [← hbbA]; exact hbb0
  have hag : ∀ a, vsaFoot C.H a → ¬ MoveAtW 1 v pred succ a →
      (writeLog (writeLog (writeLog (writeLog M0
        [(v + 24, 8, w0)]) [(v + 16, 8, w1)]) [(pred + 16, 8, w2)]) [(succ + 24, 8, w2)])[a]? =
        Mt[a]? := by
    intro a ha hna
    unfold MoveAtW at hna
    rw [hb1, hbbA] at hna
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      try (simp only [OutL, and_true]; omega)
    rw [hM0 a (by rw [hbbA]; omega)]
    exact D.agree a ha (by rw [hb1]; omega)
  have HP := Hp.heap.moveBinAt (i := 1) (j := j) (by decide) (by unfold numBins; decide) (by omega)
    hj (by omega) (by omega) D.bin hfree (fun _ => hidx) hpos hpred hsucc e1 e2 e3 e4 e5 e6 e7
    hbblt hbbset (fun bb0 hbb0 k hk => by rw [hbb] at hbb0; cases hbb0; exact hbbkeep k hk) hag
  refine ⟨HP, fun a ha => ?_, Hp.disj, fun a ha => ?_, Hp.live⟩
  · exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (hP0 a (D.pres a ha)))))
  · have hnf : ¬ vsaFoot C.H a := fun h => ha (.inl h)
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · rw [hM0 a (fun h => hnf (.inl (.inl ⟨by rw [hbbA] at h; omega, by rw [hbbA] at h; omega⟩)))]
      exact D.frame a ha
    all_goals simp only [OutL, and_true]
    · exact out_of_foot hnf (fun k hk => by
        have := (foot_free B hfree rfl).1 (8 + k) (by omega)
        rwa [show v + 16 + (8 + k) = v + 24 + k by omega] at this)
    · exact out_of_foot hnf (fun k hk => (foot_free B hfree rfl).1 k (by omega))
    · exact out_of_foot hnf (fun k hk => by
        have := hpf (16 + k) (by omega) (by omega)
        rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
    · exact out_of_foot hnf (fun k hk => by
        have := hsf (24 + k) (by omega) (by omega)
        rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)

/-- The re-binning continuation: the block search's test, entered with any
heap at the entry break and chunks, the request's registers, `t4 = bin 1`, and
the bitmap in `a1`. -/
abbrev RebinNext (C : MCtx) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb idx : Nat) : Prop :=
  ∀ R'' Mt'' bins'' bb'', MFrame C R'' Mt'' → MHeap C Mt'' brkv chunks bins'' →
    bins'' 1 = [] → (∀ k, k ≠ 1 → ∀ x ∈ bins k, x ∈ bins'' k) →
    LRRegs nb idx R'' → (R'' 29).toNat = binAt 1 → R'' 8 = reentV →
    read64 Mt'' binblocksAddr = some bb'' → (R'' 11).toNat = bb'' →
    AW C.live C.S C.Q 0x80004968#64 R'' Mt''

/-- **Link the remainder in** (`0x80004cc0`): with `pred` in `a0` and `succ`
in `a3`, the four link stores, then the block search's test. -/
theorem rebin_link {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' M0 : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {nb idx v sz j pred succ bb bb' : Nat} {pre' post' : List Nat}
    (F : MFrame C R M0) (Hp : MHeap C Mt brkv chunks bins) (D : MDetach C Mt Mt' bins 1 v)
    (hfree : FreeAt chunks v sz) (hj0 : 1 < j) (hj : j < numBins) (hidx : binIndex sz = j)
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hbb : read64 Mt binblocksAddr = some bb)
    (hM0 : ∀ a : Nat, ¬ (binblocksAddr ≤ a ∧ a < binblocksAddr + 8) → M0[a]? = Mt'[a]?)
    (hP0 : ∀ a : Nat, (Mt'[a]?).isSome → (M0[a]?).isSome)
    (hbb0 : read64 M0 binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : bb' / 2 ^ (j / 4) % 2 = 1) (hbbkeep : ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (G : LRRegs nb idx R) (h29 : (R 29).toNat = binAt 1) (h8 : R 8 = reentV)
    (h10 : (R 10).toNat = pred) (h13 : (R 13).toNat = succ) (h15 : (R 15).toNat = v)
    (h11 : (R 11).toNat = bb') (hnext : RebinNext C brkv chunks bins nb idx) :
    AW C.live C.S C.Q 0x80004cc0#64 R M0 := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hbnd := HH.walk.chunk_bounds _ hfree
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  simp only at hbnd hv16
  unfold heapStart at hbnd
  have hgj := binAt_geo j hj
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapEnd at hbrk
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hpos]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  have hloc : ∀ x, (x = binAt j ∨ x ∈ bins j) →
      x % 16 = 0 ∧ (x = binAt j ∨ (0x8001c170 ≤ x ∧ x + 32 ≤ C.top0)) := by
    intro x hx
    obtain ⟨hx16, hxn⟩ := HH.node (by omega) hj hx
    refine ⟨hx16, ?_⟩
    rcases hxn with h | ⟨cx, hcx, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
  obtain ⟨hp16, hploc⟩ := hloc pred hpm
  obtain ⟨hs16, hsloc⟩ := hloc succ hsm
  have hpf := B.node_foot (by omega) hj hpm
  have hsf := B.node_foot (by omega) hj hsm
  have hvf := (foot_free B hfree rfl).1
  simp only at hvf
  unfold binAt avAddr at hgj hploc hsloc
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hoV := Hp.off_stack (fun k hk => hvf k (by omega))
  have hoV' := Hp.off_stack (fun k hk => by
    have := hvf (8 + k) (by omega); rwa [show v + 16 + (8 + k) = v + 24 + k by omega] at this)
  have hoP := Hp.off_stack (a := pred + 16) (fun k hk => by
    have := hpf (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  have hoS := Hp.off_stack (a := succ + 24) (fun k hk => by
    have := hsf (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  unfold mHead at hoV hoV' hoP hoS
  -- `sd a0,24(a5); sd a3,16(a5)`: `v`'s links
  refine st_80004cc0 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => by
      have := hvf (8 + k) (by omega)
      rwa [show v + 16 + (8 + k) = (R 15 + 24#64).toNat + k by sx_addr] at this)
  sx_norm
  rw [show (R 15 + 24#64).toNat = v + 24 by sx_addr]
  refine st_80004cc4 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => by
      have := hvf k (by omega); rwa [show v + 16 + k = (R 15 + 16#64).toNat + k by sx_addr] at this)
  sx_norm
  rw [show (R 15 + 16#64).toNat = v + 16 by sx_addr]
  -- `sd a5,16(a0); sd a5,24(a3)`: `pred`'s `fd`, `succ`'s `bk`
  refine st_80004cc8 O.live ?_ ?_ ?_
  · sx_norm; unfold StOK Vsa.Sim.tohostAddr
    rw [show (R 10 + 16#64).toNat = pred + 16 by sx_addr]; omega
  · sx_norm; rw [show (R 10 + 16#64).toNat = pred + 16 by sx_addr]
    exact O.foot (fun k hk => by
      have := hpf (16 + k) (by omega) (by omega)
      rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  sx_norm
  rw [show (R 10 + 16#64).toNat = pred + 16 by sx_addr]
  refine st_80004ccc O.live ?_ ?_ ?_
  · sx_norm; unfold StOK Vsa.Sim.tohostAddr
    rw [show (R 13 + 24#64).toNat = succ + 24 by sx_addr]; omega
  · sx_norm; rw [show (R 13 + 24#64).toNat = succ + 24 by sx_addr]
    exact O.foot (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  sx_norm
  rw [show (R 13 + 24#64).toNat = succ + 24 by sx_addr]
  refine st_80004cd0 O.live ?_
  have Hp'' := rebin_at_heap Hp D hfree hj0 hj hidx hpos hpred hsucc hbb hM0 hP0 hbb0 hbblt
    hbbset hbbkeep (w0 := R 10) (w1 := R 13) (w2 := R 15) h10 h13 h15
  refine hnext _ _ _ bb' ((((F.store (by omega)).store (by omega)).store (by omega)).store
    (by omega)) Hp'' (by rw [updBins_other _ _ (by omega : (1 : Nat) ≠ j), updBins_same])
    (fun k hk y hy => ?_) G h29 h8 ?_ h11
  · by_cases hkj : k = j
    · subst hkj; rw [updBins_same]; rw [hpos] at hy
      rcases List.mem_append.mp hy with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
    · rw [updBins_other _ _ hkj, updBins_other _ _ hk]; exact hy
  have hbbA : binblocksAddr = 2147593496 := rfl
  rw [hbbA]
  rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
    read64_miss _ _ (by omega)]
  rw [← hbbA]; exact hbb0

/-- The state of the large re-binning around its walk: the detached heap, the
remainder `v` of size `sz` in `a5`, bin `j = binIndex sz`, the bitmap `bb` in
`a1`, and the request's registers. -/
structure RebinL (C : MCtx) (Mt Mt' : Mem) (brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (nb idx v sz j bb : Nat) (R : Nat → BitVec 64) : Prop where
  frame : MFrame C R Mt'
  heap : MHeap C Mt brkv chunks bins
  det : MDetach C Mt Mt' bins 1 v
  free : FreeAt chunks v sz
  large : 511 < sz
  bin_idx : binIndex sz = j
  regs : LRRegs nb idx R
  t4 : (R 29).toNat = binAt 1
  s0 : R 8 = reentV
  a5 : (R 15).toNat = v
  a1 : (R 11).toNat = bb
  bbr : read64 Mt binblocksAddr = some bb

theorem RebinL.upd {C : MCtx} {Mt Mt' : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb idx v sz j bb : Nat} {R : Nat → BitVec 64}
    (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R) {R' : Nat → BitVec 64}
    (h : ∀ x, x ≠ 6 → x ≠ 10 → x ≠ 12 → x ≠ 13 → R' x = R x) :
    RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R' where
  frame := L.frame.of_regs (h 2 (by decide) (by decide) (by decide) (by decide))
    (h 9 (by decide) (by decide) (by decide) (by decide))
    (h 18 (by decide) (by decide) (by decide) (by decide))
    (h 19 (by decide) (by decide) (by decide) (by decide))
  heap := L.heap
  det := L.det
  free := L.free
  large := L.large
  bin_idx := L.bin_idx
  regs := ⟨by rw [h 14 (by decide) (by decide) (by decide) (by decide)]; exact L.regs.a4,
    by rw [h 17 (by decide) (by decide) (by decide) (by decide)]; exact L.regs.a7,
    by rw [h 16 (by decide) (by decide) (by decide) (by decide)]; exact L.regs.a6⟩
  t4 := by rw [h 29 (by decide) (by decide) (by decide) (by decide)]; exact L.t4
  s0 := by rw [h 8 (by decide) (by decide) (by decide) (by decide)]; exact L.s0
  a5 := by rw [h 15 (by decide) (by decide) (by decide) (by decide)]; exact L.a5
  a1 := by rw [h 11 (by decide) (by decide) (by decide) (by decide)]; exact L.a1
  bbr := L.bbr

/-- **The walk's exit** (`0x80004cbc`): `succ` in `a3`; load its `bk`, the
insertion point's `pred`, and link the remainder in. -/
theorem rebinL_exit {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz j bb succ : Nat}
    {pre' post' : List Nat} (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R)
    (hj : j < numBins) (hne : bins j ≠ []) (hpos : bins j = pre' ++ post')
    (hsucc : (post' ++ [binAt j]).head? = some succ) (h13 : (R 13).toNat = succ)
    (hnext : RebinNext C brkv chunks bins nb idx) :
    AW C.live C.S C.Q 0x80004cbc#64 R Mt' := by
  have HH := L.heap.heap.heap.heap
  have B := L.heap.heap.heap
  have hj0 : 1 < j := by have := binIndex_large (sz := sz) (by have := L.large; omega); rw [← L.bin_idx]; omega
  have hgj := binAt_geo j hj
  have hbbl := L.heap.heap.bb_lt bb L.bbr
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre').getLast? = some p := ⟨_, List.getLast?_cons⟩
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hs16, hsnode⟩ := HH.node (by omega) hj hsm
  have hsf := B.node_foot (by omega) hj hsm
  -- `bk succ` is `pred`
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  have hbkS : bkOf Mt succ = some pred := by
    rcases post' with _ | ⟨y, ys⟩
    · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hsucc
      subst hsucc
      rw [hpos, List.append_nil] at hring
      exact ring_bk_head hring hpred
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hsucc
      subst hsucc
      rw [hpos] at hring
      obtain ⟨q, hq⟩ : ∃ q, (ys ++ [binAt j]).head? = some q := by
        rcases ys with _ | ⟨z, zs⟩ <;> simp
      exact (ring_member hring hpred hq).2
  have hbkS' : read64 Mt' (succ + 24) = some pred := by
    rw [L.det.read (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this) ?_]
    · exact hbkS
    · rcases hsnode with rfl | ⟨cx, hcx, rfl, _, _⟩
      · unfold binAt avAddr; unfold binAt avAddr at hgj; omega
      · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; unfold binAt avAddr; omega
  have hsl : succ + 32 ≤ 0x100000000 := by
    rcases hsnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · unfold binAt avAddr at hgj ⊢; omega
    · have := HH.walk.chunk_bounds cx hcx; have := HH.top_le; have := HH.brk_le
      unfold heapEnd at *; omega
  have hsl2 : 0x80000000 ≤ succ := by
    rcases hsnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · unfold binAt avAddr at hgj ⊢; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  have hEs : ((R 13) + sign_extend (m := 64) (0x018#12)).toNat = succ + 24 := by sx_addr
  refine st_80004cbc O.live ?_ ?_ ?_
  · rw [hEs]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEs]; exact O.foot (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  rw [ldv_at hbkS' _ hEs]
  have hpl := Vsa.Sim.read64_lt _ _ _ hbkS'
  have L' := L.upd (R' := upd R 10 (BitVec.ofNat 64 pred)) (fun x h6 h10 h12 h13 => upd_other _ _ h10)
  exact rebin_link O L'.frame L.heap L.det L.free hj0 hj L.bin_idx hpos hpred hsucc L.bbr
    (fun _ _ => rfl) (fun _ h => h) (by rw [L.det.read (fun k hk => .inl (.inl ⟨by
      unfold binblocksAddr avAddr; omega, by unfold binblocksAddr avAddr; omega⟩))
      (by unfold binblocksAddr binAt avAddr; omega)]; exact L.bbr) hbbl
    (HH.binblocks bb L.bbr j hj0 hj hne) (fun k h => h)
    L'.regs L'.t4 L'.s0 (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hpl]) (by rw [upd_other _ _ (by decide)]; exact h13) L'.a5 L'.a1 hnext

/-- A free chunk `cx` at `x` on a bin, seen from the detached heap: its place,
its footprint words (header and links) and its header's read. -/
structure MemberAt (C : MCtx) (Mt' : Mem) (chunks : List Chunk) (x : Nat) (cx : Chunk) : Prop where
  mem : cx ∈ chunks
  addr : cx.addr = x
  free : cx.inuse = false
  al : x % 16 = 0
  lo : 0x8001c170 ≤ x
  hi : x + cx.size ≤ C.top0
  min : 32 ≤ cx.size
  foot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (x + o)
  hdr : ∃ h, read64 Mt' (x + 8) = some h ∧ chunkSize h = cx.size

theorem RebinL.member {C : MCtx} {Mt Mt' : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb idx v sz j bb x : Nat} {R : Nat → BitVec 64}
    (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R) (hj : j < numBins)
    (hx : x ∈ bins j) : ∃ cx, MemberAt C Mt' chunks x cx := by
  have HH := L.heap.heap.heap.heap
  have B := L.heap.heap.heap
  have hj0 : 1 < j := by
    have := binIndex_large (sz := sz) (by have := L.large; omega); rw [← L.bin_idx]; omega
  obtain ⟨cx, hcx, rfl, hf⟩ := HH.member (by omega) hj hx
  have hb := HH.walk.chunk_bounds cx hcx
  unfold heapStart at hb
  have hfoot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (cx.addr + o) := by
    intro o h1 h2
    by_cases ho : o < 16
    · have := foot_header B (.inr ⟨cx, hcx, rfl⟩) (o - 8) (by omega)
      rwa [show cx.addr + 8 + (o - 8) = cx.addr + o by omega] at this
    · exact B.node_foot (by omega) hj (.inr hx) o (by omega) h2
  obtain ⟨⟨h, hr, hs, _⟩, _⟩ := HH.headers hcx
  refine ⟨cx, hcx, rfl, hf, HH.aligned.1 cx hcx, hb.1, hb.2.1, hb.2.2, hfoot, h, ?_, hs⟩
  rw [L.det.read (fun k hk => hfoot (8 + k) (by omega) (by omega) |> fun h' => by
    rwa [show cx.addr + (8 + k) = cx.addr + 8 + k by omega] at h') (by unfold binAt avAddr; omega)]
  exact hr

/-- One test of the sorted walk (`0x80004cb0`): read member `x`'s size; a
larger member is passed (`0x80004ca8`), otherwise `x` is the insertion
point. -/
theorem rebinL_cmp {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz j bb x : Nat}
    {pre rest : List Nat} (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R)
    (hj : j < numBins) (hmem : bins j = pre ++ x :: rest)
    (h13 : (R 13).toNat = x) (h6 : (R 6).toNat = sz) (hnext : RebinNext C brkv chunks bins nb idx)
    (hpass : ∀ R', RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R' → (R' 13).toNat = x →
      R' 10 = R 10 → (R' 6).toNat = sz → AW C.live C.S C.Q 0x80004ca8#64 R' Mt') :
    AW C.live C.S C.Q 0x80004cb0#64 R Mt' := by
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨cx, M⟩ := L.member hj hx
  obtain ⟨h, hr, hs⟩ := M.hdr
  have hlo := M.lo; have hhi := M.hi; have hmin := M.min
  have htle := L.heap.heap.heap.heap.top_le; have hbrk := L.heap.heap.heap.heap.brk_le
  unfold heapEnd at hbrk
  have hEh : ((R 13) + sign_extend (m := 64) (0x008#12)).toNat = x + 8 := by sx_addr
  have hhlt := Vsa.Sim.read64_lt _ _ _ hr
  refine st_80004cb0 O.live ?_ ?_ ?_
  · rw [hEh]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEh]; exact O.foot (fun k hk => by
      have := M.foot (8 + k) (by omega) (by omega)
      rwa [show x + (8 + k) = x + 8 + k by omega] at this)
  rw [ldv_at hr _ hEh]
  refine st_80004cb4 O.live ?_
  have hsz : (BitVec.ofNat 64 h &&& sign_extend (m := 64) (0xffc#12)).toNat = cx.size := by
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt, ← hs]
    rfl
  have L' := L.upd (R' := upd (upd R 12 (BitVec.ofNat 64 h)) 12
    (BitVec.ofNat 64 h &&& sign_extend (m := 64) (0xffc#12)))
    (fun y h6 h10 h12 h13 => by simp only [upd_apply, h12, ite_false])
  refine st_80004cb8 O.live (fun hlt => ?_) (fun hge => ?_)
  · exact hpass _ L' (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h13)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h6)
  · have hne : bins j ≠ [] := by rw [hmem]; simp
    exact rebinL_exit O L' hj hne (pre' := pre) (post' := x :: rest) hmem rfl
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h13) hnext

/-- The walk's step (`0x80004ca8`): move to member `x`'s successor; the
header ends the walk with the remainder last in the bin. -/
theorem rebinL_adv {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz j bb x : Nat}
    {pre rest : List Nat} (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R)
    (hj : j < numBins) (hmem : bins j = pre ++ x :: rest)
    (h13 : (R 13).toNat = x) (h10 : (R 10).toNat = binAt j) (h6 : (R 6).toNat = sz)
    (hnext : RebinNext C brkv chunks bins nb idx)
    (hloop : ∀ y rest', rest = y :: rest' → ∀ R', RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R' →
      (R' 13).toNat = y → (R' 10).toNat = binAt j → (R' 6).toNat = sz →
      AW C.live C.S C.Q 0x80004cb0#64 R' Mt') :
    AW C.live C.S C.Q 0x80004ca8#64 R Mt' := by
  have HH := L.heap.heap.heap.heap
  have hj0 : 1 < j := by
    have := binIndex_large (sz := sz) (by have := L.large; omega); rw [← L.bin_idx]; omega
  have hgj := binAt_geo j hj
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨cx, M⟩ := L.member hj hx
  have hlo := M.lo; have hhi := M.hi; have hmin := M.min
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapEnd at hbrk
  -- `fd x` is the next node
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨nx, hnx⟩ : ∃ q, (rest ++ [binAt j]).head? = some q := by
    rcases rest with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hnx).1
  have hfd' : read64 Mt' (x + 16) = some nx := by
    rw [L.det.read (fun k hk => by
      have := M.foot (16 + k) (by omega) (by omega)
      rwa [show x + (16 + k) = x + 16 + k by omega] at this) (by unfold binAt avAddr; omega)]
    exact hfd
  have hnxlt := Vsa.Sim.read64_lt _ _ _ hfd'
  have hEf : ((R 13) + sign_extend (m := 64) (0x010#12)).toNat = x + 16 := by sx_addr
  refine st_80004ca8 O.live ?_ ?_ ?_
  · rw [hEf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEf]; exact O.foot (fun k hk => by
      have := M.foot (16 + k) (by omega) (by omega)
      rwa [show x + (16 + k) = x + 16 + k by omega] at this)
  rw [ldv_at hfd' _ hEf]
  have L' := L.upd (R' := upd R 13 (BitVec.ofNat 64 nx))
    (fun y h6 h10 h12 h13 => upd_other _ _ h13)
  have hne : bins j ≠ [] := by rw [hmem]; simp
  rcases rest with _ | ⟨y, rest'⟩
  · -- the header: exit with the remainder last
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    refine st_80004cac O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
    · exact rebinL_exit O L' hj hne (pre' := pre ++ [x]) (post' := []) (by rw [hmem]; simp) rfl
        (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt]) hnext
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt]
  · -- the next member
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    have hym : y ∈ bins j := by rw [hmem]; simp
    obtain ⟨cy, My⟩ := L.member hj hym
    have hylo := My.lo
    refine st_80004cac O.live (fun hc => absurd hc ?_) (fun _ => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      intro he
      have := congrArg BitVec.toNat he
      rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt] at this
      unfold binAt avAddr at this hgj; omega
    · exact hloop y rest' rfl _ L' (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnxlt]) (by rw [upd_other _ _ (by decide)]; exact h10)
        (by rw [upd_other _ _ (by decide)]; exact h6)

/-- **The sorted walk** (`0x80004cb0`): at member `x` of bin `j`, with the
members before it passed over. A member larger than the remainder is passed
(`0x80004ca8`, back here or to the exit at the header); the first one that is
not is the insertion point. -/
theorem rebinL_walk {C : MCtx} (O : MOK C) {Mt Mt' : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb idx v sz j bb : Nat} (hj : j < numBins)
    (hnext : RebinNext C brkv chunks bins nb idx) :
    ∀ (rest pre : List Nat) (x : Nat) (R : Nat → BitVec 64),
      RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R → bins j = pre ++ x :: rest →
      (R 13).toNat = x → (R 10).toNat = binAt j → (R 6).toNat = sz →
      AW C.live C.S C.Q 0x80004cb0#64 R Mt' := by
  intro rest
  induction rest with
  | nil =>
    intro pre x R L hmem h13 h10 h6
    refine rebinL_cmp O L hj hmem h13 h6 hnext fun R' L' h13' h10' h6' =>
      rebinL_adv O L' hj hmem h13' (h10'.symm ▸ h10) h6' hnext fun y rest' he => nomatch he
  | cons y rest ih =>
    intro pre x R L hmem h13 h10 h6
    refine rebinL_cmp O L hj hmem h13 h6 hnext fun R' L' h13' h10' h6' =>
      rebinL_adv O L' hj hmem h13' (h10'.symm ▸ h10) h6' hnext fun y' rest' he R'' L'' h13'' h10'' h6'' => ?_
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ih (pre ++ [x]) y R'' L'' (by rw [hmem]; simp) h13'' h10'' h6''
/-- **An empty large bin** (`0x80004e98`): set its block bit and make the
remainder its only member. -/
theorem rebinL_empty {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz j bb : Nat}
    (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz j bb R) (hj : j < numBins)
    (hemp : bins j = []) (h12 : (R 12).toNat = j) (h10 : (R 10).toNat = binAt j)
    (h13 : (R 13).toNat = binAt j) (hnext : RebinNext C brkv chunks bins nb idx) :
    AW C.live C.S C.Q 0x80004e98#64 R Mt' := by
  have HH := L.heap.heap.heap.heap
  have hj0 : 1 < j := by
    have := binIndex_large (sz := sz) (by have := L.large; omega); rw [← L.bin_idx]; omega
  have hgj := binAt_geo j hj
  have hbbl := L.heap.heap.bb_lt bb L.bbr
  have ha6 := L.regs.a6
  refine st_80004e98 O.live ?_
  refine st_80004e9c O.live ?_
  refine st_80004ea0 O.live ?_
  refine st_80004ea4 O.live ?_
  sx_norm
  have hq := sraiw2_toNat h12 (by unfold numBins at hj; omega)
  have hbit := shl_one hq (by unfold numBins at hj; omega)
  have hor : (R 11 ||| 1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
      (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 12)) 2#5)))).toNat = bb ||| 2 ^ (j / 4) := by
    rw [BitVec.toNat_or, L.a1, BitVec.shiftLeft_eq', hbit]
  have hEb : ((R 16) + 8#64).toNat = binblocksAddr := by
    rw [ha6]; rfl
  refine st_80004ea8 O.live (by sx_norm; rw [hEb]; decide)
    (by sx_norm; rw [hEb]; exact O.glob (by decide) (by decide)) ?_
  sx_norm
  refine st_80004eac O.live ?_
  rw [hEb]
  have hFb : binblocksAddr + 8 ≤ C.s.toNat - 96 + 80 ∨ C.s.toNat - 96 + 96 ≤ binblocksAddr := by
    have := L.heap.off_stack (a := binblocksAddr) (fun k hk => .inl (.inl ⟨by
      unfold binblocksAddr avAddr; omega, by unfold binblocksAddr avAddr; omega⟩))
    have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
    unfold mHead at this; omega
  refine rebin_link O (L.frame.store hFb |>.of_regs ?_ ?_ ?_ ?_) L.heap L.det L.free hj0 hj
    L.bin_idx (pre' := []) (post' := []) (by rw [hemp]; rfl) rfl rfl L.bbr
    (fun a ha => writeLog_out _ _ _ (by simp only [OutL, and_true]; omega))
    (fun a h => writeLog_present _ _ _ h) (read64_store_hit _ _ _ |>.trans (by rw [hor]))
    (lor_lt bb _ hbbl (by unfold numBins at hj; omega)) (lor_bit_set bb _)
    (fun k hk => lor_bit_keep bb _ k hk) ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hnext <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact L.regs.a4
  · exact L.regs.a7
  · exact ha6
  · exact L.t4
  · exact L.s0
  · exact h10
  · exact h13
  · exact L.a5
  · exact hor

/-- **The large re-binning** (`0x80004c70`): bin `binIndex sz` by the
cascade, then an empty bin takes the remainder as its only member and a
nonempty one is walked for the insertion point. -/
theorem rebinL {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz bb : Nat}
    (L : RebinL C Mt Mt' brkv chunks bins nb idx v sz (binIndex sz) bb R)
    (h6 : (R 6).toNat = sz) (hnext : RebinNext C brkv chunks bins nb idx) :
    AW C.live C.S C.Q 0x80004c70#64 R Mt' := by
  have HH := L.heap.heap.heap.heap
  have hbi := binIndex_large (sz := sz) (by have := L.large; omega)
  have hj : binIndex sz < numBins := by unfold numBins; omega
  have hgj := binAt_geo (binIndex sz) hj
  have hbnd := HH.walk.chunk_bounds _ L.free
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapEnd at hbrk
  simp only at hbnd
  unfold heapStart at hbnd
  refine lbin_idx O h6 (by have := L.large; omega) (by omega) fun R' I => ?_
  have L' := L.upd (R' := R') fun x h6 h10 h12 h13 => I.keep x h10 h12 h13
  have h6' : (R' 6).toNat = sz := by rw [I.keep 6 (by decide) (by decide) (by decide)]; exact h6
  have ha6 := L'.regs.a6
  -- the bin's first member
  have hring := (binList_iff_ring.1 (HH.bins_list (binIndex sz) (by omega) hj)).1
  obtain ⟨f, hf⟩ : ∃ f, (bins (binIndex sz) ++ [binAt (binIndex sz)]).head? = some f := by
    rcases bins (binIndex sz) with _ | ⟨z, zs⟩ <;> simp
  have hfd := ring_fd_head hring hf
  have hfd' : read64 Mt' (binAt (binIndex sz) + 16) = some f := by
    rw [L.det.read (fun k hk => .inl (.inl ⟨by omega, by omega⟩)) (by unfold binAt avAddr; omega)]
    exact hfd
  have hflt := Vsa.Sim.read64_lt _ _ _ hfd'
  have hEa : (R' 16 + R' 10).toNat = binAt (binIndex sz) + 16 := by
    rw [ha6, BitVec.toNat_add, I.a0]; unfold binAt avAddr; unfold binAt avAddr at hgj
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  refine st_80004c94 O.live ?_
  refine st_80004c98 O.live ?_ ?_ ?_
  · sx_norm; rw [hEa]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEa]; exact O.bin_link hj (.inl rfl)
  sx_norm
  rw [hEa, ldv_at hfd' _ rfl]
  refine st_80004c9c O.live ?_
  sx_norm
  have hEb : (R' 16 + R' 10 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (binIndex sz)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hEa, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold binAt avAddr at hgj ⊢; omega
  rw [hEb]
  have hbl : binAt (binIndex sz) < 2 ^ 64 := by omega
  have L'' := L'.upd (R' := upd (upd (upd R' 10 (R' 16 + R' 10)) 13 (BitVec.ofNat 64 f)) 10
    (BitVec.ofNat 64 (binAt (binIndex sz))))
    (fun y h6 h10 h12 h13 => by simp only [upd_apply, h10, h13, ite_false])
  refine st_80004ca0 O.live (fun hne => ?_) (fun heq => ?_)
  · -- nonempty: walk from the first member
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    have hfne : f ≠ binAt (binIndex sz) := fun he => hne (by rw [he])
    obtain ⟨x, rest, hx⟩ : ∃ x rest, bins (binIndex sz) = x :: rest := by
      rcases h : bins (binIndex sz) with _ | ⟨z, zs⟩
      · rw [h] at hf; simp at hf; exact absurd hf.symm hfne
      · exact ⟨z, zs, rfl⟩
    rw [hx] at hf; simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hf
    subst hf
    exact rebinL_walk O hj hnext rest [] _ _ L'' (by rw [hx]; rfl)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hflt])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbl])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h6')
  · -- empty
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at heq
    have hemp : bins (binIndex sz) = [] := by
      rcases h : bins (binIndex sz) with _ | ⟨z, zs⟩
      · rfl
      · exfalso
        rw [h] at hf hring
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hf
        subst hf
        have := (binList_iff_ring.1 (HH.bins_list (binIndex sz) (by omega) hj)).2 z
          (by rw [h]; exact List.mem_cons_self)
        apply this
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbl,
          Nat.mod_eq_of_lt hflt] at this
        exact this.symm
    have hfb : f = binAt (binIndex sz) := by
      rw [hemp] at hf; simpa using hf.symm
    refine st_80004ca4 O.live ?_
    refine rebinL_empty O L'' hj hemp ?_ ?_ ?_ hnext <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact I.a2
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbl]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hflt, hfb]

end VsaIris.VsaHeap
