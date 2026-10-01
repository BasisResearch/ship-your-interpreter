import VsaIris.OmegaHint
import VsaIris.Vsa.MallocSplit
import VsaIris.Vsa.HeapMoveAt
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.RegKeep

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


theorem head_node_MallocRebin {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins) {j f : Nat} (hj0 : 0 < j)
    (hj : j < numBins) (hf : (bins j ++ [binAt j]).head? = some f) :
    (f = binAt j ∨ f ∈ bins j) ∧ f % 16 = 0 ∧ (f = binAt j ∨ 0x8001c170 ≤ f ∧ f + 32 ≤ top) ∧
      Rgn (vsaFoot H) (f + 16) 16 := by
  have hm : f = binAt j ∨ f ∈ bins j := by
    rcases List.mem_append.mp (List.mem_of_mem_head? hf) with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  refine ⟨hm, (B.nodeK hj0 hj hm).al, ?_, (B.nodeK hj0 hj hm).links⟩
  rcases (B.heap.node hj0 hj hm).2 with h | ⟨cx, hcx, rfl, _, _⟩
  · exact .inl h
  · have := B.heap.walk.chunk_bounds cx hcx; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩

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
  have B := Hp.heap.heap
  have K := B.chunkK hfree; have FS := B.freeSpan hfree rfl
  open_fields K; simp only at FS K_lo K_hi K_al K_sz32
  have hjn : j < numBins := by unfold numBins; omega
  have hvmem : v ∈ bins 1 := by rw [D.bin]; exact List.mem_cons_self
  have hvJ : v ∉ bins j := fun hc => by
    have := B.heap.bin_unique (by omega) hjn (by decide) (by unfold numBins; decide) hc hvmem; omega
  obtain ⟨hofm, ho16, hoLoc, rO⟩ := head_node_MallocRebin B (by omega) hjn hfirst
  have hbj : binAt j = 2147593488 + 16 * j := rfl
  have hb1 : binAt 1 = 2147593504 := rfl
  have hbbA : binblocksAddr = 2147593496 := rfl
  have hov : oldfirst ≠ v := by
    rcases hofm with rfl | h
    · omega
    · exact fun he => hvJ (he ▸ h)
  have Gl := globRgn C.H
  have e1 : read64 Mt' (binAt 1 + 16) = some (binAt 1) := D.fd
  have e2 : read64 Mt' (binAt 1 + 24) = some (binAt 1) := D.bk
  refine ⟨Hp.heap.moveBinAt (i := 1) (j := j) (pred := binAt j) (pre' := []) (post' := bins j)
    (by decide) (by unfold numBins; decide) (by omega) hjn (by omega) (by omega) D.bin hfree
    (fun _ => by unfold binIndex; rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; omega)
    rfl rfl hfirst ?_ ?_ ?_ ?_ ?_ ?_ ?_ (lor_lt bb _ (Hp.heap.bb_lt bb hbb) (by omega))
    (lor_bit_set bb _) (fun bb0 hbb0 k hk => by
      rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk) fun a ha hna => ?_,
    ?_, Hp.disj, ?_, Hp.live⟩
  · show read64 _ (binAt 1 + 16) = _; rd_log [e1]
  · show read64 _ (binAt 1 + 24) = _; rd_log [e2]
  · show read64 _ (v + 16) = _; rd_log [h0]
  · show read64 _ (v + 24) = _; rd_log [h1]
  · show read64 _ (binAt j + 16) = _; rd_log [h3]
  · show read64 _ (oldfirst + 24) = _; rd_log [h3]
  · rd_log [h2]
  · unfold MoveAtW at hna
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      try (simp only [OutL, and_true]; omega)
    exact D.agree a ha (by omega)
  · exact pres_log _ (pres_log _ (pres_log _ (pres_log _ (pres_log _ D.pres))))
  · simp only [writeLog_nest, List.cons_append, List.nil_append]
    exact frame_log (by log_in) D.frame

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
  have B := Hp.heap.heap
  have K := B.chunkK hfree; have FS := B.freeSpan hfree rfl
  open_fields K; simp only at FS K_lo K_hi K_al K_sz16 K_sz32
  have ha4 := V.a4; have ha5 := V.a5; have ht1 := V.t1
  have ha6 := G.a6; have ha7 := G.a7
  have Gl := globRgn C.H
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mt binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 B.heap.binblocks_present
  have hbb' : read64 Mt' 2147593496 = some bb := by
    rw [D.read (Gl.word (by omega) (by omega)) (by unfold binAt avAddr; omega)]; exact hbb
  have hbblt := Hp.heap.bb_lt bb hbb
  rw [← upd_self_eq ha6]
  rgn_run O.live at 0x80004924
  rgn_ld [hbb']
  have hbbv : (BitVec.ofNat 64 bb).toNat = bb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (step% st 0x80004924) O.live (fun hl => ?_) (fun hs => ?_)
  ·
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hl
    refine hlarge (by rw [ht1] at hl; exact hl) _ bb (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
      hbb ?_ <;> reg_close [ha4, ha7, ha5, ht1, V.t4, h8, hbbv]
  ·
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hs
    rw [ht1] at hs
    have hs' : sz ≤ 511 := by
      have e : (511#64 : BitVec 64).toNat = 511 := rfl
      omega
    have hjn : sz / 8 < numBins := by unfold numBins; omega
    obtain ⟨oldfirst, hof⟩ : ∃ f, (bins (sz / 8) ++ [binAt (sz / 8)]).head? = some f := by
      rcases h : bins (sz / 8) with _ | ⟨x, xs⟩ <;> simp
    obtain ⟨hofm, ho16, holoc, rO⟩ := head_node_MallocRebin B (by omega) hjn hof
    have hbj : binAt (sz / 8) = 2147593488 + 16 * (sz / 8) := rfl
    have hfdJ' : read64 Mt' (binAt (sz / 8) + 16) = some oldfirst := by
      rw [D.read (Gl.word (by omega) (by omega)) (by unfold binAt avAddr; omega)]
      exact ring_fd_head (binList_iff_ring.1 (B.heap.bins_list (sz / 8) (by omega) hjn)).1 hof
    have hoflt := Vsa.Sim.read64_lt _ _ _ hfdJ'
    have hj8 : (R 6 >>> 3).toNat = sz / 8 := by
      rw [BitVec.toNat_ushiftRight, ht1, Nat.shiftRight_eq_div_pow]
    have hA3 := binfd_toNat hj8 (by omega)
    have hY := hA3; simp only [key_toNat_add, BitVec.reduceToNat] at hY
    have hq := sraiw2_toNat hj8 (by omega)
    have hbit := shl_one hq (by omega)
    rgn_step O.live at 0x8000493c
    sx_norm
    rgn_run O.live at 0x80004940
    rgn_ld [hfdJ']
    rgn_step O.live at 0x80004968
    sx_norm
    rw [show (R 15 + 16#64).toNat = v + 16 by rgn_arith, show (R 15 + 24#64).toNat = v + 24 by rgn_arith,
      hA3, show (BitVec.ofNat 64 oldfirst + 24#64).toNat = oldfirst + 24 by rgn_arith]
    have hor : (BitVec.ofNat 64 bb ||| 1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
        (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 6 >>> 3)) 2#5))).toNat).toNat =
        bb ||| 2 ^ (sz / 8 / 4) := by rw [BitVec.toNat_or, hbbv, hbit]
    have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
    have oV := FS.offStack Hp.disj (by omega); have oG := Gl.offStack Hp.disj (by decide)
    have oO := rO.offStack Hp.disj (by decide); unfold mHead at oV oG oO
    have hbbA : binblocksAddr = 2147593496 := rfl
    refine hnext _ _ _ (bb ||| 2 ^ (sz / 8 / 4))
      ((((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).store
        (by omega)).of_regs ?_ ?_ ?_ ?_)
      (rebin_small_heap Hp D hfree hs' rfl hof hbb (by rgn_arith) (by rgn_arith) hor ha5)
      (by rw [updBins_other _ _ (by omega : (1 : Nat) ≠ sz / 8), updBins_same])
      (fun k hk y hy => by
        by_cases hkj : k = sz / 8
        · subst hkj; rw [updBins_same]; exact List.mem_cons_of_mem _ hy
        · rw [updBins_other _ _ hkj, updBins_other _ _ hk]; exact hy)
      ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ <;> reg_try [ha4, ha7, V.t4, h8, hor]
    rd_log [hor]

end VsaIris.VsaHeap
