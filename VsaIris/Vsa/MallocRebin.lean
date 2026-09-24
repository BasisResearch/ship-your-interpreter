import VsaIris.Vsa.MallocSplit
import VsaIris.Vsa.HeapMoveAt

/-!
# Re-binning a too-small last remainder

`0x8000491c` is reached when the last remainder `v` (already detached from
bin 1, `MDetach`) is smaller than the request. It goes to its own bin: at the
head of small bin `sz / 8` (`rebin_small`), or at its sorted position in a
large bin (`0x80004c70`). Both set the bin's block bit in `binblocks` and
continue at the block search's test (`bb_entry`, `0x80004968`).

The heap edit is `PHeapAt.moveBinAt` (`HeapMoveAt.lean`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem lor_bit_set (bb k : Nat) : (bb ||| 2 ^ k) / 2 ^ k % 2 = 1 := by
  have h := Nat.testBit_two_pow_self (n := k)
  have : (bb ||| 2 ^ k).testBit k = true := by rw [Nat.testBit_or, h, Bool.or_true]
  rw [Nat.testBit_eq_decide_div_mod_eq] at this
  simpa using this

theorem lor_bit_keep (bb k t : Nat) (h : bb / 2 ^ t % 2 = 1) : (bb ||| 2 ^ k) / 2 ^ t % 2 = 1 := by
  have : bb.testBit t = true := by rw [Nat.testBit_eq_decide_div_mod_eq]; simpa using h
  have h2 : (bb ||| 2 ^ k).testBit t = true := by rw [Nat.testBit_or, this, Bool.true_or]
  rw [Nat.testBit_eq_decide_div_mod_eq] at h2
  simpa using h2

theorem lor_lt (bb k : Nat) (h : bb < 2 ^ 32) (hk : k < 32) : bb ||| 2 ^ k < 2 ^ 32 :=
  Nat.or_lt_two_pow h (Nat.pow_lt_pow_right (by omega) hk)

/-- The address of bin `j`'s `fd` word as the code forms it:
`av + (sext32 (2 j + 2) << 3)`. -/
theorem binfd_toNat {x : BitVec 64} {j : Nat} (hx : x.toNat = j) (hj : j < 2 ^ 20) :
    (2147593488#64 + BitVec.signExtend 64 (BitVec.extractLsb 31 0 (x <<< 1 + 2#64)) <<< 3).toNat =
      binAt j + 16 := by
  have h1 : (x <<< 1 + 2#64).toNat = 2 * j + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hx, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have h2 := toNat_sx32_small _ (by rw [h1]; omega)
  rw [h1] at h2
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, h2, Nat.shiftLeft_eq]
  unfold binAt avAddr
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- A byte outside the footprint is outside every footprint range. -/
theorem out_of_foot {H : List (Nat × Nat)} {a b w : Nat} (hnf : ¬ vsaFoot H a)
    (hf : ∀ k, k < w → vsaFoot H (b + k)) : a < b ∨ b + w ≤ a :=
  Classical.byContradiction fun hc => hnf (by
    have := hf (a - b) (by omega)
    rwa [show b + (a - b) = a by omega] at this)

/-- **The heap after the small re-binning.** The machine's five stores (`v`'s
links, the bitmap with the block bit set, bin `j`'s `fd` and the old first
member's `bk`), with the stored words named by their values, leave the heap
with `v` at the head of bin `j = sz / 8` and bin 1 empty. -/
theorem rebin_small_heap {C : MCtx} {Mt Mt' : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {v sz j oldfirst bb : Nat}
    (Hp : MHeap C Mt brkv chunks bins) (D : MDetach C Mt Mt' bins 1 v) (hfree : FreeAt chunks v sz)
    (hsz : sz ≤ 511) (hj : j = sz / 8) (hfirst : (bins j ++ [binAt j]).head? = some oldfirst)
    (hbb : read64 Mt binblocksAddr = some bb)
    {w0 w1 w2 w3 : BitVec 64} (h0 : w0.toNat = oldfirst) (h1 : w1.toNat = binAt j)
    (h2 : w2.toNat = bb ||| 2 ^ (j / 4)) (h3 : w3.toNat = v) :
    MHeap C (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(binblocksAddr, 8, w2)]) [(binAt j + 16, 8, w3)])
      [(oldfirst + 24, 8, w3)]) brkv chunks (updBins (updBins bins 1 []) j (v :: bins j)) := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hbnd := HH.walk.chunk_bounds _ hfree
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  obtain ⟨hsz16, hsz32⟩ := walk_sizes HH.walk _ hfree
  simp only at hbnd hv16 hsz16 hsz32
  unfold heapStart at hbnd
  have hj4 : 4 ≤ j ∧ j < 64 := by omega
  have hjn : j < numBins := by unfold numBins; omega
  have hgj := binAt_geo j hjn
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  have hvmem : v ∈ bins 1 := by rw [D.bin]; exact List.mem_cons_self
  have hvJ : v ∉ bins j := fun hc => by
    have := HH.bin_unique (by omega) hjn (by decide) (by unfold numBins; decide) hc hvmem; omega
  -- the old first member of bin `j`
  have hofm : oldfirst = binAt j ∨ oldfirst ∈ bins j := by
    have := List.mem_of_mem_head? hfirst
    rcases List.mem_append.mp this with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  obtain ⟨ho16, honode⟩ := HH.node (by omega) hjn hofm
  have hoLoc : (oldfirst = binAt j) ∨ (heapStart ≤ oldfirst ∧ oldfirst + 32 ≤ C.top0) := by
    rcases honode with h | ⟨cx, hcx, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hov : oldfirst ≠ v := by
    rcases hofm with rfl | h
    · unfold binAt avAddr; omega
    · exact fun he => hvJ (he ▸ h)
  have hbbl := Hp.heap.bb_lt bb hbb
  unfold binAt avAddr at hgj hg1 ⊢
  unfold binblocksAddr avAddr
  unfold heapStart binAt avAddr at hoLoc
  -- the reads the move needs
  have e1 : fdOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) (binAt 1) = some (binAt 1) := by
    show read64 _ (binAt 1 + 16) = _
    unfold binAt avAddr
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega), read64_miss _ _ (by omega)]
    exact D.fd
  have e2 : bkOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) (binAt 1) = some (binAt 1) := by
    show read64 _ (binAt 1 + 24) = _
    unfold binAt avAddr
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega), read64_miss _ _ (by omega)]
    exact D.bk
  have e3 : fdOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) v = some oldfirst := by
    show read64 _ (v + 16) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_miss _ _ (by omega), read64_store_hit, h0]
  have e4 : bkOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) v = some (binAt j) := by
    show read64 _ (v + 24) = _
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_miss _ _ (by omega),
      read64_store_hit, h1]
  have e5 : fdOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) (binAt j) = some v := by
    show read64 _ (binAt j + 16) = _
    unfold binAt avAddr
    rw [read64_miss _ _ (by omega), read64_store_hit, h3]
  have e6 : bkOf (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) oldfirst = some v := by
    show read64 _ (oldfirst + 24) = _
    rw [read64_store_hit, h3]
  have e7 : read64 (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
      [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)]) binblocksAddr =
      some (bb ||| 2 ^ (j / 4)) := by
    unfold binblocksAddr avAddr
    rw [read64_miss _ _ (by omega), read64_miss _ _ (by omega), read64_store_hit, h2]
  have hag : ∀ a, vsaFoot C.H a → ¬ MoveAtW 1 v (binAt j) oldfirst a →
      (writeLog (writeLog (writeLog (writeLog (writeLog Mt'
        [(v + 16, 8, w0)]) [(v + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
        [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(oldfirst + 24, 8, w3)])[a]? = Mt[a]? := by
    intro a ha hna
    unfold MoveAtW binAt binblocksAddr avAddr at hna
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      try (simp only [OutL, and_true]; omega)
    exact D.agree a ha (by unfold binAt avAddr; omega)
  have HP := Hp.heap.moveBinAt (i := 1) (j := j) (pre' := []) (post' := bins j) (by decide)
    (by unfold numBins; decide) (by omega) hjn (by omega) (by omega) D.bin hfree
    (fun _ => by unfold binIndex; rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; omega) rfl rfl hfirst e1 e2 e3 e4 e5 e6 e7
    (lor_lt bb _ hbbl (by omega)) (lor_bit_set bb _) (fun bb0 hbb0 k hk => by
      rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk) hag
  simp only [List.nil_append] at HP
  refine ⟨HP, fun a ha => ?_, Hp.disj, fun a ha => ?_, Hp.live⟩
  · exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (writeLog_present _ _ _ (D.pres a ha)))))
  · have hnf : ¬ vsaFoot C.H a := fun h => ha (.inl h)
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact D.frame a ha
    all_goals simp only [OutL, and_true]
    · exact out_of_foot hnf (fun k hk => (foot_free B hfree rfl).1 k (by omega))
    · exact out_of_foot hnf (fun k hk => by
        have := (foot_free B hfree rfl).1 (8 + k) (by omega)
        rwa [show v + 16 + (8 + k) = v + 24 + k by omega] at this)
    · exact out_of_foot hnf (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    · exact out_of_foot hnf (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    · exact out_of_foot hnf (fun k hk => by
        have := B.node_foot (x := oldfirst) (by omega) hjn hofm (24 + k) (by omega) (by omega)
        rwa [show oldfirst + (24 + k) = oldfirst + 24 + k by omega] at this)

/-- **Re-bin the last remainder** (`0x8000491c`): a remainder of at most 511
bytes goes to the head of its small bin, and the block search's test follows
with the updated bitmap. A larger one takes the large-bin path (`0x80004c70`). -/
theorem rebin {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz : Nat}
    (F : MFrame C R Mt') (Hp : MHeap C Mt brkv chunks bins) (D : MDetach C Mt Mt' bins 1 v)
    (G : LRRegs nb idx R) (V : LRVictim nb sz v R) (h8 : R 8 = reentV) (hfree : FreeAt chunks v sz)
    (hlarge : 511 < sz → ∀ R' bb, MFrame C R' Mt' → LRRegs nb idx R' → (R' 15).toNat = v →
      (R' 6).toNat = sz → (R' 29).toNat = binAt 1 → R' 8 = reentV →
      read64 Mt binblocksAddr = some bb → (R' 11).toNat = bb →
      AW C.live C.S C.Q 0x80004c70#64 R' Mt')
    (hnext : ∀ R'' Mt'' bins'' bb'', MFrame C R'' Mt'' → MHeap C Mt'' brkv chunks bins'' →
      bins'' 1 = [] → (∀ k, k ≠ 1 → ∀ x ∈ bins k, x ∈ bins'' k) →
      LRRegs nb idx R'' → (R'' 29).toNat = binAt 1 → R'' 8 = reentV →
      read64 Mt'' binblocksAddr = some bb'' → (R'' 11).toNat = bb'' →
      AW C.live C.S C.Q 0x80004968#64 R'' Mt'') :
    AW C.live C.S C.Q 0x8000491c#64 R Mt' := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have ha4 := V.a4; have ha5 := V.a5; have ht1 := V.t1
  have ha6 := G.a6; have ha7 := G.a7
  have hbnd := HH.walk.chunk_bounds _ hfree
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  obtain ⟨hsz16, hsz32⟩ := walk_sizes HH.walk _ hfree
  simp only at hbnd hv16 hsz16 hsz32
  unfold heapStart at hbnd
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapEnd at hbrk
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mt binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbb' : read64 Mt' binblocksAddr = some bb := by
    rw [D.read (fun k hk => .inl (.inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩)) (by unfold binblocksAddr binAt avAddr; omega)]
    exact hbb
  have hbblt := Hp.heap.bb_lt bb hbb
  rw [← upd_self_eq ha6]
  -- `li a3,511; ld a1,8(a6)`: the bitmap
  sx_run [2] O.live
  unfold binblocksAddr avAddr at hbb'
  simp (disch := sx_addr) only [ldv_at hbb']
  have hbbv : (BitVec.ofNat 64 bb).toNat = bb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine st_80004924 O.live (fun hl => ?_) (fun hs => ?_)
  · -- a large remainder
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hl
    refine hlarge (by rw [ht1] at hl; exact hl) _ bb (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
      hbb ?_ <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact ha4
    · exact ha7
    · exact ha5
    · exact ht1
    · exact V.t4
    · exact h8
    · exact hbbv
  · -- a small remainder: the head of bin `sz / 8`
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hs
    rw [ht1] at hs
    have hs' : sz ≤ 511 := by
      have e : (511#64 : BitVec 64).toNat = 511 := rfl
      omega
    have hjn : sz / 8 < numBins := by unfold numBins; omega
    have hgj := binAt_geo (sz / 8) hjn
    -- bin `j`'s first member
    have hringJ := (binList_iff_ring.1 (HH.bins_list (sz / 8) (by omega) hjn)).1
    obtain ⟨oldfirst, hof⟩ : ∃ f, (bins (sz / 8) ++ [binAt (sz / 8)]).head? = some f := by
      rcases h : bins (sz / 8) with _ | ⟨x, xs⟩ <;> simp
    have hfdJ := ring_fd_head hringJ hof
    have hfdJ' : read64 Mt' (binAt (sz / 8) + 16) = some oldfirst := by
      rw [D.read (fun k hk => .inl (.inl ⟨by omega, by omega⟩)) (by unfold binAt avAddr; omega)]
      exact hfdJ
    have hoflt := Vsa.Sim.read64_lt _ _ _ hfdJ
    sx_run [6] O.live at 0x8000493c
    have hj8 : (R 6 >>> 3).toNat = sz / 8 := by
      rw [BitVec.toNat_ushiftRight, ht1, Nat.shiftRight_eq_div_pow]
    have hA3 := binfd_toNat hj8 (by omega)
    have hglo := binAt_geo (sz / 8) hjn
    refine st_8000493c O.live ?_ ?_ ?_
    · sx_norm; rw [hA3]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · sx_norm; rw [hA3]; exact O.bin_link hjn (.inl rfl)
    sx_norm
    rw [hA3, ldv_at hfdJ' _ rfl]
    -- the bit of block `j / 4`
    refine st_80004940 O.live ?_
    refine st_80004944 O.live ?_
    refine st_80004948 O.live ?_
    sx_norm
    have hq := sraiw2_toNat hj8 (by omega)
    have hbit := shl_one hq (by omega)
    refine st_8000494c O.live ?_
    refine st_80004950 O.live ?_
    sx_norm
    have hor : (BitVec.ofNat 64 bb ||| 1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
        (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 6 >>> 3)) 2#5)))).toNat =
        bb ||| 2 ^ (sz / 8 / 4) := by
      rw [BitVec.toNat_or, hbbv, BitVec.shiftLeft_eq', hbit]
    have hvf := (foot_free B hfree rfl).1
    simp only at hvf
    have hA2 : (2147593488#64 + BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 6 >>> 3 <<< 1 + 2#64))
        <<< 3 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (sz / 8)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hA3, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      unfold binAt avAddr at hglo ⊢; omega
    have hofm : oldfirst = binAt (sz / 8) ∨ oldfirst ∈ bins (sz / 8) := by
      have := List.mem_of_mem_head? hof
      rcases List.mem_append.mp this with hm | hm
      · exact .inr hm
      · exact .inl (by simpa using hm)
    have hof16 : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (oldfirst + k) :=
      B.node_foot (by omega) hjn hofm
    obtain ⟨ho16, honode⟩ := HH.node (by omega) hjn hofm
    have holoc : oldfirst = binAt (sz / 8) ∨ (0x8001c170 ≤ oldfirst ∧ oldfirst + 32 ≤ C.top0) := by
      rcases honode with h | ⟨cx, hcx, rfl, _, _⟩
      · exact .inl h
      · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
    -- `sd a0,16(a5); sd a2,24(a5)`: `v`'s links
    refine st_80004954 O.live ?_ ?_ ?_
    · sx_norm; sx_addr
    · sx_norm; exact O.foot (fun k hk => by
        have := hvf k (by omega); rwa [show v + 16 + k = (R 15 + 16#64).toNat + k by sx_addr] at this)
    sx_norm
    rw [show (R 15 + 16#64).toNat = v + 16 by sx_addr]
    refine st_80004958 O.live ?_ ?_ ?_
    · sx_norm; sx_addr
    · sx_norm; exact O.foot (fun k hk => by
        have := hvf (8 + k) (by omega)
        rwa [show v + 16 + (8 + k) = (R 15 + 24#64).toNat + k by sx_addr] at this)
    sx_norm
    rw [show (R 15 + 24#64).toNat = v + 24 by sx_addr, hA2]
    -- `sd a1,8(a6)`: the bitmap
    refine st_8000495c O.live (by sx_norm; decide) (by sx_norm; sx_side) ?_
    sx_norm
    -- `sd a5,0(a3); sd a5,24(a0)`: bin `j`'s `fd` and the old first member's `bk`
    refine st_80004960 O.live ?_ ?_ ?_
    · sx_norm; rw [hA3]; unfold StOK Vsa.Sim.tohostAddr; unfold binAt avAddr at hglo ⊢; omega
    · sx_norm; rw [hA3]; exact O.bin_link hjn (.inl rfl)
    sx_norm
    rw [hA3]
    have hEo : (BitVec.ofNat 64 oldfirst + 24#64).toNat = oldfirst + 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      unfold binAt avAddr at holoc; omega
    refine st_80004964 O.live ?_ ?_ ?_
    · sx_norm; rw [hEo]; unfold StOK Vsa.Sim.tohostAddr; unfold binAt avAddr at holoc; omega
    · sx_norm; rw [hEo]; exact O.foot (fun k hk => by
        have := hof16 (24 + k) (by omega) (by omega)
        rwa [show oldfirst + (24 + k) = oldfirst + 24 + k by omega] at this)
    sx_norm
    rw [hEo]
    have hofflt : binAt (sz / 8) < 2 ^ 64 := by unfold binAt avAddr at hglo ⊢; omega
    have Hp'' := rebin_small_heap Hp D hfree hs' rfl hof hbb
      (w0 := BitVec.ofNat 64 oldfirst) (w1 := BitVec.ofNat 64 (binAt (sz / 8))) (w3 := R 15)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt])
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hofflt]) hor ha5
    have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
    have hoV := Hp.off_stack (fun k hk => hvf k (by omega))
    have hoV' := Hp.off_stack (fun k hk => by
      have := hvf (8 + k) (by omega); rwa [show v + 16 + (8 + k) = v + 24 + k by omega] at this)
    have hoJ := Hp.off_stack (a := binAt (sz / 8) + 16) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    have hoO := Hp.off_stack (a := oldfirst + 24) (fun k hk => by
      have := hof16 (24 + k) (by omega) (by omega)
      rwa [show oldfirst + (24 + k) = oldfirst + 24 + k by omega] at this)
    have hoB := Hp.off_stack (a := 2147593496) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    unfold mHead at hoV hoV' hoJ hoO hoB
    refine hnext _ _ _ (bb ||| 2 ^ (sz / 8 / 4))
      ((((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).store
        (by omega)).of_regs ?_ ?_ ?_ ?_) Hp''
      (by rw [updBins_other _ _ (by omega : (1 : Nat) ≠ sz / 8), updBins_same])
      (fun k hk y hy => by
        by_cases hkj : k = sz / 8
        · subst hkj; rw [updBins_same]; exact List.mem_cons_of_mem _ hy
        · rw [updBins_other _ _ hkj, updBins_other _ _ hk]; exact hy)
      ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact ha4
    · exact ha7
    · exact V.t4
    · exact h8
    · unfold binblocksAddr avAddr
      rw [read64_miss _ _ (by omega), read64_miss _ _ (by unfold binAt avAddr at hglo ⊢; omega),
        read64_store_hit, hor]
    · exact hor

end VsaIris.VsaHeap
