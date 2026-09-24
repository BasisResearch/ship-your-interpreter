import VsaIris.Vsa.FreePro

/-!
# `_free_r`'s bin insertion

Every path that ends with the released chunk in a bin reaches `0x800073e8`
with the chunk `X` of size `S` in `a4`/`a5`, in use in a virtual heap `M2`
(the heap as if the chunk and its coalesced neighbours were one in-use chunk),
and the actual memory agreeing with `M2` except on the chunk's footer and the
next header, which the machine has already written (`FBin`). The insertion
links `X` in at the head of its small bin, or at its sorted place in its large
bin, and `PHeapAt.release` gives the heap.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The end of a free run's heap work: the heap without the block, its top
no higher, the footprint present, and every byte outside the write window at
its entry value. -/
structure FDone (C : MCtx) (Mt : Mem) : Prop where
  heap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins ∧ top ≤ C.top0
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- The state before the bin insertion: the virtual heap `M2` with `X` an
in-use chunk of size `S` holding no block, between in-use neighbours and below
a top no higher than at entry; the actual memory `Mt` agrees with `M2` but on
`X`'s footer (written, `S`) and the next header (`PREV_INUSE` cleared). -/
structure FBin (C : MCtx) (Mt M2 : Mem) (X S top brkv : Nat) (cs₁ cs₂ : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt M2 C.H top brkv (cs₁ ++ ⟨X, S, true⟩ :: cs₂) bins
  top_le : top ≤ C.top0
  hno : ∀ e ∈ C.H, e.1 ≠ X + 16
  prev : ∀ h0, read64 M2 (X + 8) = some h0 → h0 % 2 = 1
  next : ∀ d ∈ cs₂.head?, d.inuse = true
  not_top : X + S ≠ top
  agree : ∀ w, vsaFoot C.H w → ¬ (X + S ≤ w ∧ w < X + S + 16) → Mt[w]? = M2[w]?
  foot : read64 Mt (X + S) = some S
  nx : ∀ hd, read64 M2 (X + S + 8) = some hd → ∃ hd', read64 Mt (X + S + 8) = some hd' ∧
    chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2 ∧ prevInuse hd' = false
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- A footprint doubleword away from the chunk's footer and next header reads
as in the virtual heap. -/
theorem FBin.read {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {w : Nat}
    (hf : ∀ k, k < 8 → vsaFoot C.H (w + k)) (hw : w + 8 ≤ X + S ∨ X + S + 16 ≤ w) :
    read64 Mt w = read64 M2 w :=
  read64_keep fun k hk => B.agree _ (hf k hk) (by omega)

/-- A read through a store to another doubleword. -/
theorem read64_miss' {Mt : Mem} {a b : Nat} {v : BitVec 64} (h : a + 8 ≤ b ∨ b + 8 ≤ a) :
    read64 (writeLog Mt [(b, 8, v)]) a = read64 Mt a := read64_store_miss Mt v h

/-- **The heap after a small-bin insertion.** The machine's five stores (`X`'s
links, `binblocks` with bin `j`'s block bit, bin `j`'s `fd`, and the old first
member's `bk`) link `X` at the head of bin `j = S / 8`. -/
theorem fb_small_heap {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (hS : S ≤ 511) {j first bb : Nat} (hj : j = S / 8)
    (hfirst : (bins j ++ [binAt j]).head? = some first)
    (hbb : read64 M2 binblocksAddr = some bb)
    {w0 w1 w2 w3 : BitVec 64} (h0 : w0.toNat = first) (h1 : w1.toNat = binAt j)
    (h2 : w2.toNat = bb ||| 2 ^ (j / 4)) (h3 : w3.toNat = X) :
    FDone C (writeLog (writeLog (writeLog (writeLog (writeLog Mt
      [(X + 16, 8, w0)]) [(X + 24, 8, w1)]) [(binblocksAddr, 8, w2)]) [(binAt j + 16, 8, w3)])
      [(first + 24, 8, w3)]) := by
  have Hh := B.heap
  have BB := Hh.heap
  have HH := BB.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hbnd := HH.walk.chunk_bounds _ hX
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hX16 := hal0 _ hX
  obtain ⟨hS16, hS32⟩ := walk_sizes HH.walk _ hX
  simp only at hbnd hX16 hS16 hS32
  unfold heapStart at hbnd
  have hj4 : 4 ≤ j ∧ j < 64 := by omega
  have hjn : j < numBins := by unfold numBins; omega
  have hgj := binAt_geo j hjn
  have hXJ : X ∉ bins j := fun hc => by
    obtain ⟨c, hc, hca, hf⟩ := HH.member (by omega) hjn hc
    have := HH.chunk_eq hc hX hca
    rw [this] at hf; cases hf
  have hofm : first = binAt j ∨ first ∈ bins j := by
    have := List.mem_of_mem_head? hfirst
    rcases List.mem_append.mp this with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  obtain ⟨ho16, honode⟩ := HH.node (by omega) hjn hofm
  have hoLoc : (first = binAt j) ∨ (heapStart ≤ first ∧ first + 32 ≤ top) := by
    rcases honode with h | ⟨cx, hcx, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hoX : first ≠ X := by
    rcases hofm with rfl | h
    · unfold binAt avAddr at hgj ⊢; omega
    · exact fun he => hXJ (he ▸ h)
  have hbbl := Hh.bb_lt bb hbb
  have hbS : X + S ≠ first + 16 :=
    HH.bnd_ne_node hjn honode (HH.end_bnd hX) 16 (by omega) (by omega)
  unfold binAt avAddr at hgj ⊢
  unfold binblocksAddr avAddr
  unfold heapStart binAt avAddr at hoLoc
  -- the final memory's reads
  generalize hMf : writeLog (writeLog (writeLog (writeLog (writeLog Mt
      [(X + 16, 8, w0)]) [(X + 24, 8, w1)]) [(0x8001ad10 + 8, 8, w2)])
      [(0x8001ad10 + 16 * j + 16, 8, w3)]) [(first + 24, 8, w3)] = Mf
  have eV1 : fdOf Mf X = some first := by
    show read64 _ (X + 16) = _
    rw [← hMf, read64_miss' (by omega), read64_miss' (by omega), read64_miss' (by omega),
      read64_miss' (by omega), read64_store_hit, h0]
  have eV2 : bkOf Mf X = some (binAt j) := by
    show read64 _ (X + 24) = _
    rw [← hMf, read64_miss' (by omega), read64_miss' (by omega), read64_miss' (by omega),
      read64_store_hit, h1]
  have eP : fdOf Mf (binAt j) = some X := by
    show read64 _ (binAt j + 16) = _
    unfold binAt avAddr
    rw [← hMf, read64_miss' (by omega), read64_store_hit, h3]
  have eS : bkOf Mf first = some X := by
    show read64 _ (first + 24) = _
    rw [← hMf, read64_store_hit, h3]
  have eB : read64 Mf binblocksAddr = some (bb ||| 2 ^ (j / 4)) := by
    unfold binblocksAddr avAddr
    rw [← hMf, read64_miss' (by omega), read64_miss' (by omega), read64_store_hit, h2]
  have eF : read64 Mf (X + S) = some S := by
    rw [← hMf, read64_miss' (by omega), read64_miss' (by omega), read64_miss' (by omega),
      read64_miss' (by omega), read64_miss' (by omega)]
    exact B.foot
  have eN : ∀ hd, read64 M2 (X + S + 8) = some hd → ∃ hd', read64 Mf (X + S + 8) = some hd' ∧
      chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2 ∧ prevInuse hd' = false := by
    intro hd hr
    obtain ⟨hd', h1', h2', h3', h4'⟩ := B.nx hd hr
    refine ⟨hd', ?_, h2', h3', h4'⟩
    rw [← hMf, read64_miss' (by omega), read64_miss' (by omega), read64_miss' (by omega),
      read64_miss' (by omega), read64_miss' (by omega)]
    exact h1'
  have hag : ∀ w, vsaFoot C.H w → ¬ RelW X S (binAt j) first w → Mf[w]? = M2[w]? := by
    intro w hw hna
    unfold RelW binAt binblocksAddr avAddr at hna
    rw [← hMf, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      try (simp only [OutL, and_true]; omega)
    exact B.agree w hw (by omega)
  have HP := Hh.release B.hno B.prev B.next B.not_top (j := j) (pre' := []) (post' := bins j)
    (by omega) hjn
    (fun _ => by unfold binIndex; rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; omega)
    (fun h => absurd h (by omega)) rfl rfl hfirst eV1 eV2 eP eS eF eN eB
    (lor_lt bb _ hbbl (by omega)) (fun _ => lor_bit_set bb _) (fun bb0 hbb0 k hk => by
      rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk) hag
  simp only [List.nil_append] at HP
  have BP := HP.heap
  have hXf : (⟨X, S, false⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, false⟩ :: cs₂ := by simp
  refine ⟨⟨_, _, _, _, HP, B.top_le⟩, fun a ha => ?_, fun a ha => ?_⟩
  · rw [← hMf]
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (writeLog_present _ _ _ (B.pres a ha)))))
  · have hnf : ¬ vsaFoot C.H a := fun h => ha (.inl h)
    rw [← hMf, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact B.frame a ha
    all_goals simp only [OutL, and_true]
    · exact out_of_foot hnf (fun k hk => (foot_free BP hXf rfl).1 k (by omega))
    · exact out_of_foot hnf (fun k hk => by
        have := (foot_free BP hXf rfl).1 (8 + k) (by omega)
        rwa [show X + 16 + (8 + k) = X + 24 + k by omega] at this)
    · exact out_of_foot hnf (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    · exact out_of_foot hnf (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
    · exact out_of_foot hnf (fun k hk => by
        have := BB.node_foot (x := first) (by omega) hjn hofm (24 + k) (by omega) (by omega)
        rwa [show first + (24 + k) = first + 24 + k by omega] at this)

/-- A footprint range lies wholly below or above the stack window. -/
theorem FBin.off_stack {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {a : Nat}
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) :
    a + 8 ≤ C.s.toNat - mHead ∨ C.s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hk : (if a ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - a) < 8 := by
    split <;> omega
  exact B.disj _ (by split <;> omega) (by unfold mHead at *; split <;> omega) (hf _ hk)

/-- The chunk's interior is footprint of the heap without the block: no live
block lies in it. -/
theorem FBin.foot_chunk {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {a : Nat}
    (h1 : X + 8 ≤ a) (h2 : a < X + S + 8) : vsaFoot C.H a := by
  have HH := B.heap.heap.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hb := HH.walk.chunk_bounds _ hX
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := B.heap.heap.top_room
  simp only at hb
  refine .inr ⟨by omega, by omega, fun e he hin => ?_⟩
  obtain ⟨c, hc, hu, hce, hcs⟩ := HH.exact e he he
  have hcb := HH.walk.chunk_bounds c hc
  unfold InExt at hin
  rcases HH.walk.chunk_sep c hc _ hX with rfl | h3 | h3
  · exact B.hno e he (by simp only at hce; omega)
  · simp only at h3; omega
  · simp only at h3; omega

/-- **The small-bin insertion** (`0x800073f0`): `X` of `S ≤ 511` bytes goes to
the head of bin `S / 8`, whose block bit is set; then the epilogue. -/
theorem fb_small {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) (hS : S ≤ 511)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x800073f0#64 R Mt := by
  have Hh := B.heap
  have BB := Hh.heap
  have HH := BB.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hbnd := HH.walk.chunk_bounds _ hX
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hX16 := hal0 _ hX
  obtain ⟨hS16, hS32⟩ := walk_sizes HH.walk _ hX
  simp only at hbnd hX16 hS16 hS32
  unfold heapStart at hbnd
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapEnd at hbrk
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbb' : read64 Mt binblocksAddr = some bb := by
    rw [B.read (fun k hk => .inl (.inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩)) (by unfold binblocksAddr avAddr; omega)]
    exact hbb
  have hbblt := Hh.bb_lt bb hbb
  have hjn : S / 8 < numBins := by unfold numBins; omega
  have hgj := binAt_geo (S / 8) hjn
  have hringJ := (binList_iff_ring.1 (HH.bins_list (S / 8) (by omega) hjn)).1
  obtain ⟨first, hof⟩ : ∃ f, (bins (S / 8) ++ [binAt (S / 8)]).head? = some f := by
    rcases h : bins (S / 8) with _ | ⟨x, xs⟩ <;> simp
  have hfdJ := ring_fd_head hringJ hof
  have hfdJ' : read64 Mt (binAt (S / 8) + 16) = some first := by
    rw [B.read (fun k hk => .inl (.inl ⟨by omega, by omega⟩)) (by unfold binAt avAddr at hgj ⊢; omega)]
    exact hfdJ
  have hoflt := Vsa.Sim.read64_lt _ _ _ hfdJ
  rw [← upd_self_eq h17]
  refine st_800073f0 O.live ?_
  refine st_800073f4 O.live ?_
  refine st_800073f8 O.live ?_
  refine st_800073fc O.live ?_
  sx_norm
  refine st_80007400 O.live (by sx_norm; decide) (by sx_norm; sx_side) ?_
  sx_norm
  simp (disch := decide) only [ldv_at hbb']
  have hbbv : (BitVec.ofNat 64 bb).toNat = bb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj8 : (R 15 >>> 3).toNat = S / 8 := by
    rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
  have hA3 := binfd_toNat hj8 (by omega)
  refine st_80007404 O.live ?_
  refine st_80007408 O.live ?_ ?_ ?_
  · sx_norm; rw [hA3]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hA3]; exact O.toWOK.bin_link hjn (.inl rfl)
  sx_norm
  rw [hA3, ldv_at hfdJ' _ rfl]
  refine st_8000740c O.live ?_
  refine st_80007410 O.live ?_
  refine st_80007414 O.live ?_
  refine st_80007418 O.live ?_
  refine st_8000741c O.live ?_
  sx_norm
  have hq := sraiw2_toNat hj8 (by omega)
  have hbit := shl_one hq (by omega)
  have hor : (1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
      (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 15 >>> 3)) 2#5))).toNat |||
      BitVec.ofNat 64 bb).toNat = bb ||| 2 ^ (S / 8 / 4) := by
    rw [BitVec.toNat_or, hbbv, hbit, Nat.or_comm]
  have hA2 : (2147593488#64 + BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 15 >>> 3 <<< 1 + 2#64))
      <<< 3 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (S / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hA3, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold binAt avAddr at hgj ⊢; omega
  have hofm : first = binAt (S / 8) ∨ first ∈ bins (S / 8) := by
    have := List.mem_of_mem_head? hof
    rcases List.mem_append.mp this with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  have hof16 : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (first + k) := BB.node_foot (by omega) hjn hofm
  obtain ⟨ho16, honode⟩ := HH.node (by omega) hjn hofm
  have holoc : first = binAt (S / 8) ∨ (0x8001c170 ≤ first ∧ first + 32 ≤ top) := by
    rcases honode with h | ⟨cx, hcx, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
  have hvf : ∀ k, k < 16 → vsaFoot C.H (X + 16 + k) := fun k hk => B.foot_chunk (by omega) (by omega)
  -- `sd a1,16(a4); sd a2,24(a4)`: `X`'s links
  refine st_80007420 O.live ?_ ?_ ?_
  · sx_norm; rw [BitVec.toNat_add, h14]; unfold StOK Vsa.Sim.tohostAddr; simp; omega
  · sx_norm; rw [BitVec.toNat_add, h14]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega)]; exact O.foot (fun k hk => hvf k (by omega))
  sx_norm
  rw [show (R 14 + 16#64).toNat = X + 16 by rw [BitVec.toNat_add, h14]; simp; omega]
  refine st_80007424 O.live ?_ ?_ ?_
  · sx_norm; rw [BitVec.toNat_add, h14]; unfold StOK Vsa.Sim.tohostAddr; simp; omega
  · sx_norm; rw [BitVec.toNat_add, h14]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact O.foot (fun k hk => by have := hvf (8 + k) (by omega); rwa [show X + 16 + (8 + k) = X + 24 + k by omega] at this)
  sx_norm
  rw [show (R 14 + 24#64).toNat = X + 24 by rw [BitVec.toNat_add, h14]; simp; omega, hA2]
  -- `sd a5,8(a7)`: the bitmap
  refine st_80007428 O.live (by sx_norm; decide) (by sx_norm; sx_side) ?_
  sx_norm
  -- `sd a4,0(a3); sd a4,24(a1)`: bin `j`'s `fd` and the old first member's `bk`
  refine st_8000742c O.live ?_ ?_ ?_
  · sx_norm; rw [hA3]; unfold StOK Vsa.Sim.tohostAddr; unfold binAt avAddr at hgj ⊢; omega
  · sx_norm; rw [hA3]; exact O.toWOK.bin_link hjn (.inl rfl)
  sx_norm
  rw [hA3]
  have hEo : (BitVec.ofNat 64 first + 24#64).toNat = first + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    unfold binAt avAddr at holoc; omega
  refine st_80007430 O.live ?_ ?_ ?_
  · sx_norm; rw [hEo]; unfold StOK Vsa.Sim.tohostAddr; unfold binAt avAddr at holoc; omega
  · sx_norm; rw [hEo]; exact O.foot (fun k hk => by
      have := hof16 (24 + k) (by omega) (by omega)
      rwa [show first + (24 + k) = first + 24 + k by omega] at this)
  sx_norm
  rw [hEo]
  have hofflt : binAt (S / 8) < 2 ^ 64 := by unfold binAt avAddr at hgj ⊢; omega
  have D := fb_small_heap B hS rfl hof hbb
    (w0 := BitVec.ofNat 64 first) (w1 := BitVec.ofNat 64 (binAt (S / 8))) (w3 := R 14)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt])
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hofflt]) hor h14
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hoV := B.off_stack (fun k hk => hvf k (by omega))
  have hoV' := B.off_stack (a := X + 24) (fun k hk => by
    have := hvf (8 + k) (by omega); rwa [show X + 16 + (8 + k) = X + 24 + k by omega] at this)
  have hoJ := B.off_stack (a := binAt (S / 8) + 16) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
  have hoO := B.off_stack (a := first + 24) (fun k hk => by
    have := hof16 (24 + k) (by omega) (by omega)
    rwa [show first + (24 + k) = first + 24 + k by omega] at this)
  have hoB := B.off_stack (a := 2147593496) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
  unfold mHead at hoV hoV' hoJ hoO hoB
  have h9 := F.s1; have h18 := F.s2; have h19 := F.s3; have h2 := F.sp
  exact free_epi O ((((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])) D.heap D.pres D.frame

end VsaIris.VsaHeap
