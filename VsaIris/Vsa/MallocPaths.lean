import VsaIris.Vsa.MallocCtx

/-!
# `_malloc_r`'s paths

The join lemmas of a malloc run. Each states the symbolic state at one PC
(named-field invariants, never positional towers) and proves `AW` there, by
running the step table with `sx_run` and handing off to the next join.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A small-request state at `0x800047dc`: the chunk size in `a4`, the bin
index in `a7`, the bin's `fd` offset in `a3`. -/
structure SmallRegs (nb : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = nb / 8
  a3 : (R 13).toNat = 16 * (nb / 8) + 16

/-- The chunk size of a request (`request2size`). -/
structure NbOK (n : BitVec 64) (nb : Nat) : Prop where
  eq : nb = physSize n.toNat

theorem NbOK.al {n : BitVec 64} {nb : Nat} (h : NbOK n nb) : nb % 16 = 0 := by
  rw [h.eq]; unfold physSize; omega

theorem NbOK.lo {n : BitVec 64} {nb : Nat} (h : NbOK n nb) : 32 ≤ nb := by
  rw [h.eq]; unfold physSize; omega

theorem NbOK.fits {n : BitVec 64} {nb : Nat} (h : NbOK n nb) : n.toNat + 8 ≤ nb := by
  rw [h.eq]; unfold physSize; omega

theorem nbOK_small {n : BitVec 64} {nb : Nat} (h : NbOK n nb) (hs : nb ≤ 503) :
    4 ≤ nb / 8 ∧ nb / 8 ≤ 62 ∧ nb / 8 % 2 = 0 ∧ nb = 8 * (nb / 8) := by
  have := h.al; have := h.lo; omega

/-- The registers `_malloc_r` keeps at the last-remainder check `0x800048ec`:
the chunk size in `a4`, the next bin index in `a7`, `__malloc_av_` in `a6`. -/
structure LRRegs (nb idx : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = idx
  a6 : R 16 = 0x8001ad10#64

/-- A doubleword load at an address equal to one with a known `read64`. -/
theorem ldv_eq_of_read {Mt : Mem} {a a' : Nat} {v : BitVec 64} (he : a = a')
    (h : read64 Mt a' = some v.toNat) : ldv .ld Mt a = v := by
  subst he; exact ldv_ld h

/-- A load from a bin header's link word reads the ring's link. -/
theorem bin_link_ld {Mt : Mem} {a a' l : Nat} (he : a = a') (h : read64 Mt a' = some l)
    (hl : l < 2 ^ 64) : ldv .ld Mt a = BitVec.ofNat 64 l :=
  ldv_eq_of_read he (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl])

/-- A 32-bit result that fits, sign-extended, is itself. -/
theorem toNat_sx32_small (x : BitVec 64) (h : x.toNat < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 x)).toNat = x.toNat := by
  have he : (BitVec.extractLsb 31 0 x).toNat = x.toNat := by
    rw [BitVec.extractLsb_toNat]; simp; omega
  have hm : (BitVec.extractLsb 31 0 x).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, he]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, he]
  omega

/-- **`J_small`** (`0x800047dc`): the small-bin check. A nonempty bin `idx`
gives its last chunk (`small_take`). An empty bin `idx` (bin `idx + 1` is
always empty) continues at the last-remainder check with `a7 = idx + 2`. -/
theorem j_small {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : SmallRegs nb R) (hnb : NbOK C.n nb) (hsmall : nb ≤ 503)
    (htake : ∀ pre v, bins (nb / 8) = pre ++ [v] →
      ∀ R', (R' 15).toNat = v → (R' 13).toNat = binAt (nb / 8) + 16 → R' 2 = R 2 → R' 8 = R 8 →
        R' 9 = R 9 → R' 18 = R 18 → R' 19 = R 19 →
        AW C.live C.S C.Q 0x800047f4#64 R' Mt)
    (hLR : ∀ R', LRRegs nb (nb / 8 + 2) R' → R' 2 = R 2 → R' 8 = R 8 →
        R' 9 = R 9 → R' 18 = R 18 → R' 19 = R 19 →
        AW C.live C.S C.Q 0x800048ec#64 R' Mt) :
    AW C.live C.S C.Q 0x800047dc#64 R Mt := by
  have HH := Hp.heap.heap.heap
  obtain ⟨hi4, hi62, hiev, hnbi⟩ := nbOK_small hnb hsmall
  have ha3 := G.a3; have ha4 := G.a4; have ha7 := G.a7
  have hbinI := HH.bins_list (nb / 8) (by omega) (by unfold numBins; omega)
  have hring := (binList_iff_ring.1 hbinI).1
  have hbinJ := HH.bins_list (nb / 8 + 1) (by omega) (by unfold numBins; omega)
  have hringJ := (binList_iff_ring.1 hbinJ).1
  have hemptyJ : bins (nb / 8 + 1) = [] := HH.odd_empty (by omega) (by omega) (by omega)
  rw [hemptyJ] at hringJ
  have hbkJ : bkOf Mt (binAt (nb / 8 + 1)) = some (binAt (nb / 8 + 1)) := (ring_nil_iff.1 hringJ).2
  -- the last node of bin `idx`
  obtain ⟨last, hlast⟩ : ∃ l, (binAt (nb / 8) :: bins (nb / 8)).getLast? = some l := ⟨_, List.getLast?_cons⟩
  have hbk := ring_bk_head hring hlast
  have hlastlt := Vsa.Sim.read64_lt _ _ _ hbk
  refine st_800047dc O.live ?_
  refine st_800047e0 O.live ?_
  refine st_800047e4 O.live ?_
  sx_norm
  have hEA : (2147593488#64 + R 13 + sign_extend (m := 64) (0x008#12)).toNat = binAt (nb / 8) + 24 := by
    unfold binAt avAddr; sx_addr
  have hgeo := binAt_geo (nb / 8) (by unfold numBins; omega)
  refine st_800047e8 O.live ?_ ?_ ?_
  · sx_norm; rw [hEA]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEA]; exact O.bin_link (j := nb / 8) (by unfold numBins; omega) (.inr rfl)
  sx_norm
  have hv : ldv .ld Mt (2147593488#64 + R 13 + 8#64).toNat = BitVec.ofNat 64 last :=
    bin_link_ld (by unfold binAt avAddr; sx_addr) hbk hlastlt
  rw [hv]
  refine st_800047ec O.live ?_
  sx_norm
  have hA2 : (2147593488#64 + R 13 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (nb / 8)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
  have hbinlt : binAt (nb / 8) < 2 ^ 64 := by omega
  refine st_800047f0 O.live (fun heq => ?_) (fun hne => ?_)
  · -- bin `idx` is empty
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at heq
    rw [hA2] at heq
    have hle : last = binAt (nb / 8) := by
      have := congrArg BitVec.toNat heq
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlastlt, Nat.mod_eq_of_lt hbinlt] at this
    -- bin `idx + 1`
    have hgeo1 := binAt_geo (nb / 8 + 1) (by unfold numBins; omega)
    have hEA1 : ((2147593488#64 + R 13) + sign_extend (m := 64) (0x018#12)).toNat =
        binAt (nb / 8 + 1) + 24 := by unfold binAt avAddr; sx_addr
    have hbkJlt := Vsa.Sim.read64_lt _ _ _ hbkJ
    refine st_80004c60 O.live ?_ ?_ ?_
    · sx_norm; rw [hEA1]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · sx_norm; rw [hEA1]; exact O.bin_link (j := nb / 8 + 1) (by unfold numBins; omega) (.inr rfl)
    sx_norm
    have hv1 : ldv .ld Mt ((2147593488#64 + R 13) + 24#64).toNat = BitVec.ofNat 64 (binAt (nb / 8 + 1)) :=
      bin_link_ld (by unfold binAt avAddr; sx_addr) hbkJ hbkJlt
    rw [hv1]
    refine st_80004c64 O.live ?_
    sx_norm
    have hA3 : 2147593488#64 + R 13 = BitVec.ofNat 64 (binAt (nb / 8 + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
    refine st_80004c68 O.live (fun _ => ?_) (fun hne => absurd hA3 hne)
    refine hLR _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact ha4
    · rw [toNat_sx32_small _ (by sx_addr)]; sx_addr
  · -- bin `idx` is not empty: its last chunk
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    rw [hA2] at hne
    have hlne : last ≠ binAt (nb / 8) := fun h => hne (by rw [h])
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hlast
    obtain ⟨pre, hpre⟩ : ∃ pre, bins (nb / 8) = pre ++ [last] := by
      rcases ys with _ | ⟨y, ys'⟩
      · simp at hys; exact absurd hys.1.symm hlne
      · simp only [List.cons_append, List.cons.injEq] at hys
        exact ⟨ys', hys.2⟩
    refine htake pre last hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlastlt]
    · unfold binAt avAddr; sx_addr

/-- A load at an address equal to one with a known doubleword (for `simp` with
`sx_addr` discharging the address). -/
theorem ldv_at {Mt : Mem} {a' x : Nat} (h : read64 Mt a' = some x) :
    ∀ a, a = a' → ldv .ld Mt a = BitVec.ofNat 64 x := by
  intro a he; subst he
  exact ldv_ld (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ h)])

/-- **The small take** (`0x800047f4`): unlink the last chunk `v` of small bin
`idx`, set `PREV_INUSE` after it, unlock, and return `v + 16`. -/
theorem small_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    {pre : List Nat} {v : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (hnb : NbOK C.n nb) (hsmall : nb ≤ 503) (hbin : bins (nb / 8) = pre ++ [v])
    (h15 : (R 15).toNat = v) (h13 : (R 13).toNat = binAt (nb / 8) + 16) :
    AW C.live C.S C.Q 0x800047f4#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  obtain ⟨hi4, hi62, hiev, hnbi⟩ := nbOK_small hnb hsmall
  obtain ⟨cv, hcv, hcva, hcvf, hcvs, _⟩ := HH.small_member (i := nb / 8) (q := v) (by omega) (by omega)
    (by rw [hbin]; simp)
  subst hcva
  have hbnd := HH.walk.chunk_bounds cv hcv
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hcv16 := hal0 cv hcv
  obtain ⟨⟨hv, hvr, hvsz, hvlow⟩, ⟨hd, hdr, hdpi⟩⟩ := HH.headers hcv
  have hring := (binList_iff_ring.1 (HH.bins_list (nb / 8) (by omega) (by unfold numBins; omega))).1
  rw [hbin] at hring
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt (nb / 8) :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  have hsucc : (([] : List Nat) ++ [binAt (nb / 8)]).head? = some (binAt (nb / 8)) := rfl
  obtain ⟨hfdv, hbkv⟩ := ring_member (post := []) hring hpred hsucc
  have hhv := foot_header B (.inr ⟨cv, hcv, rfl⟩)
  have hlv := (foot_free B hcv hcvf).1
  have hbrk := HH.brk_le; have htle := HH.top_le
  have hvlt := Vsa.Sim.read64_lt _ _ _ hvr
  have hpredlt := Vsa.Sim.read64_lt _ _ _ hbkv
  have hbinlt := Vsa.Sim.read64_lt _ _ _ hfdv
  -- ld a4,8(a5): the victim's header
  refine st_800047f4 O.live ?_ ?_ ?_
  · sx_addr
  · exact O.foot_at hhv _ (by sx_addr)
  simp (disch := sx_addr) only [ldv_at hvr]
  -- ld a2,24(a5): its `bk`
  have hbkw : ∀ j, j < 8 → vsaFoot C.H (cv.addr + 24 + j) := fun j hj => by
    have := hlv (8 + j) (by omega); rwa [show cv.addr + 16 + (8 + j) = cv.addr + 24 + j by omega] at this
  refine st_800047f8 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at hbkw _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at (show read64 Mt (cv.addr + 24) = some pred from hbkv)]
  -- ld a1,16(a5): its `fd`
  refine st_800047fc O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at (fun j hj => hlv j (by omega)) _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at (show read64 Mt (cv.addr + 16) = some (binAt (nb / 8)) from hfdv)]
  -- andi a4,a4,-4; add a4,a5,a4: the next chunk
  refine st_80004800 O.live ?_
  refine st_80004804 O.live ?_
  sx_norm
  -- ld a3,8(a4): the next chunk's header
  have hnx := foot_header B (HH.end_bnd hcv)
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  refine st_80004808 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at hnx _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at hdr]
  -- the predecessor and the bin header
  have hpredm : pred = binAt (nb / 8) ∨ pred ∈ bins (nb / 8) := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  obtain ⟨hp16, _⟩ := HH.node (by omega) (by unfold numBins; omega) hpredm
  have hpl : (0x8001ad10 + 16 ≤ pred ∧ pred + 32 ≤ 0x8001b520) ∨ (heapStart ≤ pred ∧ pred + 32 ≤ C.top0) := by
    rcases hpredm with rfl | hm
    · have := binAt_geo (nb / 8) (by unfold numBins; omega); unfold binAt avAddr at *; exact .inl (by omega)
    · obtain ⟨cx, hcx, rfl, _⟩ := HH.member (by omega) (by unfold numBins; omega) hm
      have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hgeo := binAt_geo (nb / 8) (by unfold numBins; omega)
  -- sd a2,24(a1): the bin's `bk` := the predecessor
  refine st_8000480c O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at (fun j hj => by
      have := B.node_foot (x := binAt (nb / 8)) (j := nb / 8) (by omega) (by unfold numBins; omega)
        (.inl rfl) (24 + j) (by omega) (by omega)
      rwa [show binAt (nb / 8) + (24 + j) = binAt (nb / 8) + 24 + j by omega] at this) _ (by sx_addr)
  sx_norm
  rw [show (BitVec.ofNat 64 (binAt (nb / 8)) + 24#64).toNat = binAt (nb / 8) + 24 by sx_addr]
  -- sd a5,8(sp)
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  refine st_80004810 O.live ?_ ?_ ?_
  · sx_norm; rw [hs2]; sx_addr
  · sx_norm; rw [hs2]; exact O.stack (by unfold mHead; sx_addr) (by sx_addr)
  sx_norm
  rw [hs2, show (C.s + 18446744073709551520#64 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
  -- sd a1,16(a2): the predecessor's `fd` := the bin header
  refine st_80004814 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at (fun j hj => by
      have := B.node_foot (j := nb / 8) (by omega) (by unfold numBins; omega) hpredm (16 + j)
        (by omega) (by omega)
      rwa [show pred + (16 + j) = pred + 16 + j by omega] at this) _ (by sx_addr)
  sx_norm
  rw [show (BitVec.ofNat 64 pred + 16#64).toNat = pred + 16 by sx_addr]
  -- ori a3,a3,1; mv a0,s0
  refine st_80004818 O.live ?_
  refine st_8000481c O.live ?_
  sx_norm
  -- sd a3,8(a4): the next header, with `PREV_INUSE`
  refine st_80004820 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at hnx _ (by sx_addr)
  sx_norm
  rw [show (R 15 + (BitVec.ofNat 64 hv &&& 18446744073709551612#64) + 8#64).toNat =
    cv.addr + cv.size + 8 by sx_addr]
  -- the written heap words lie off the stack window
  have hfP : ∀ j, j < 8 → vsaFoot C.H (pred + 16 + j) := fun j hj => by
    have := B.node_foot (j := nb / 8) (by omega) (by unfold numBins; omega) hpredm (16 + j) (by omega) (by omega)
    rwa [show pred + (16 + j) = pred + 16 + j by omega] at this
  have hoffN := Hp.off_stack hnx
  have hoffP := Hp.off_stack hfP
  unfold mHead at hoffN hoffP
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  sx_run [12] O.live at 0x80004830
  -- the bin's `bk` word lies off the stack window too
  have hfB : ∀ j, j < 8 → vsaFoot C.H (binAt (nb / 8) + 24 + j) := fun j hj => by
    have := B.node_foot (x := binAt (nb / 8)) (j := nb / 8) (by omega) (by unfold numBins; omega)
      (.inl rfl) (24 + j) (by omega) (by omega)
    rwa [show binAt (nb / 8) + (24 + j) = binAt (nb / 8) + 24 + j by omega] at this
  have hoffB := Hp.off_stack hfB
  unfold mHead at hoffB
  -- the next chunk (not the top: `v` is free)
  have hnxd : ∃ d ∈ chunks, d.addr = cv.addr + cv.size := by
    rcases HH.end_bnd hcv with he | hd'
    · exfalso
      rw [he, HH.top_header] at hdr
      cases hdr
      rw [hcvf] at hdpi
      have := HH.top_size
      unfold prevInuse at hdpi
      simp only [beq_eq_false_iff_ne, ne_eq] at hdpi
      omega
    · exact hd'
  obtain ⟨d, hdmem, hda⟩ := hnxd
  obtain ⟨hd0, hd0r, _, hd0low⟩ := walk_header HH.walk d hdmem
  rw [hda, hdr] at hd0r
  cases hd0r
  have hdeven : hd % 2 = 0 := by
    rw [hcvf] at hdpi; unfold prevInuse at hdpi
    simp only [beq_eq_false_iff_ne, ne_eq] at hdpi; omega
  have hsz16 := (walk_sizes HH.walk cv hcv).1
  have hnb8 := hnb.fits
  -- read-backs through the four stores
  have hOr : (BitVec.ofNat 64 hd ||| 1#64).toNat = hd + 1 := by
    have := or_one_even (BitVec.ofNat 64 hd) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]; exact hdeven)
    rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at this
    rw [this, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    simp; omega
  have rd_fd : read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(C.s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (pred + 16) = some (binAt (nb / 8)) := by
    rw [read64_store_miss _ _ (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbinlt]
  have rd_bk : read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(C.s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (binAt (nb / 8) + 24) = some pred := by
    unfold binAt avAddr heapStart at *
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_hit, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hpredlt]
  have rd_hd : read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(C.s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (cv.addr + cv.size + 8) =
      some (hd + 1) := by
    rw [read64_store_hit, hOr]
  have rd_frame : ∀ o, o + 8 ≤ 96 → 16 ≤ o → read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(C.s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (C.s.toNat - 96 + o) =
      read64 Mt (C.s.toNat - 96 + o) := by
    intro o ho1 ho2
    unfold binAt avAddr at *
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega)]
  have ha0 : (R 15 + 16#64).toNat = cv.addr + 16 := by rw [BitVec.toNat_add, h15]; sx_addr
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hcv hcvf (n := C.n.toNat) (by omega)
  have hsz : ∀ h0, read64 Mt (cv.addr + cv.size + 8) = some h0 →
      chunkSize (hd + 1) = chunkSize h0 ∧ (hd + 1) % 4 < 2 := by
    intro h0 h0r
    rw [hdr] at h0r; cases h0r
    unfold chunkSize; omega
  have hpi : prevInuse (hd + 1) = true := by unfold prevInuse; simp only [beq_iff_eq]; omega
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hag : ∀ a, vsaFoot C.H a → ¬ TakeW pred (binAt (nb / 8)) (cv.addr + cv.size) a →
      (writeLog (writeLog (writeLog (writeLog Mt
        [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(C.s.toNat - 96 + 8, 8, R 15)])
        [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
        [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)])[a]? = Mt[a]? := by
    intro a ha hna
    unfold TakeW at hna
    have := hns a ha
    unfold binAt avAddr at *
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  have hheap := PHeapAt.take Hp.heap (i := nb / 8) (by omega) (by unfold numBins; omega)
    (pre := pre) (post := []) hbin hcv rfl (n := C.n.toNat) (by omega) hpred hsucc rd_fd rd_bk rd_hd
    hsz hpi hag
  rw [List.append_nil] at hheap
  refine epi_80004830 O ?F (O.fin_ok ?fr ?al ?heap
    (pres_store (pres_store (pres_store (pres_store Hp.pres))))
    (frame_store (win_foot hnx) (frame_store (win_foot hfP)
      (frame_store (win_stack (a := C.s.toNat - 96 + 8) (w := 8) (by unfold mHead; omega) (by omega))
        (frame_store (win_foot hfB) Hp.frame)))))
  case F =>
    refine ⟨?_, by rw [rd_frame 80 (by omega) (by omega)]; exact F.s0,
      by rw [rd_frame 88 (by omega) (by omega)]; exact F.ra, ?_, ?_, ?_⟩ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · exact F.sp
    · exact F.s1
    · exact F.s2
    · exact F.s3
  case fr => simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [ha0]; exact hfr
  case al => simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [ha0]; exact hal16
  case heap =>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [ha0]
    exact ⟨_, _, _, _, hheap, by omega⟩

end VsaIris.VsaHeap
