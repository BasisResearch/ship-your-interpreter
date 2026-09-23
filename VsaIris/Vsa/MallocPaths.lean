import VsaIris.Vsa.MallocGen

/-!
# `_malloc_r`'s paths

The join lemmas of a malloc run. Each states the symbolic state at one PC
(named-field invariants, never positional towers) and proves `AW` there, by
running the step table with `sx_run` and handing off to the next join.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A malloc run's stack frame at a symbolic state: `sp` 96 bytes below the
caller's, the saved `s0` and `ra` in their slots, `s1-s3` untouched. -/
structure MFrame (s r : BitVec 64) (rv0 : Nat → BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  sp : R 2 = s + 18446744073709551520#64
  s0 : read64 Mt (s.toNat - 96 + 80) = some (rv0 8).toNat
  ra : read64 Mt (s.toNat - 96 + 88) = some r.toNat
  s1 : R 9 = rv0 9
  s2 : R 18 = rv0 18
  s3 : R 19 = rv0 19

theorem sp96_toNat {s : BitVec 64} (h : SpOKA s) (d : Nat) (hd : d ≤ 96) :
    (s + 18446744073709551520#64 + BitVec.ofNat 64 d).toNat = s.toNat - 96 + d := by
  have := h.lo; have := h.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at *
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- A frame byte is owned. -/
theorem frame_owned {H : List (Nat × Nat)} {s : BitVec 64} (hsp : SpOKA s) {a : Nat}
    (h1 : s.toNat - 96 ≤ a) (h2 : a < s.toNat) : mS H s a := by
  have := hsp.lo
  unfold allocHeadroom Vsa.Sim.tohostAddr at *
  exact .inl ⟨by simp only [allocHeadroom]; omega, by simp only [allocHeadroom]; omega⟩

/-- A frame doubleword at offset `d` is a well-formed load. -/
theorem frame_ld {s : BitVec 64} (hsp : SpOKA s) {d : Nat} (hd : d + 8 ≤ 96) :
    LdOK (s.toNat - 96 + d) 8 := by
  have := hsp.lo; have := hsp.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at *
  unfold LdOK Vsa.Sim.tohostAddr
  omega

/-- A doubleword load at an address equal to one with a known `read64`. -/
theorem ldv_eq_of_read {Mt : Mem} {a a' : Nat} {v : BitVec 64} (he : a = a')
    (h : read64 Mt a' = some v.toNat) : ldv .ld Mt a = v := by
  subst he; exact ldv_ld h

/-- **The epilogue** `ld ra,88(sp); ld s0,80(sp); addi sp,sp,96; ret` at any of
its copies (the four step lemmas as arguments), then the return. -/
theorem epi_core {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {pc1 pc2 pc3 pc4 : BitVec 64}
    (st1 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, mS H s b) →
      AW live (mS H s) (mQ H n r s saved k) pc2
        (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x058#12)).toNat)) Mt →
      AW live (mS H s) (mQ H n r s saved k) pc1 R Mt)
    (st2 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8, mS H s b) →
      AW live (mS H s) (mQ H n r s saved k) pc3
        (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x050#12)).toNat)) Mt →
      AW live (mS H s) (mQ H n r s saved k) pc2 R Mt)
    (st3 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      AW live (mS H s) (mQ H n r s saved k) pc4
        (upd R 2 ((R 2) + sign_extend (m := 64) (0x060#12))) Mt →
      AW live (mS H s) (mQ H n r s saved k) pc3 R Mt)
    (st4 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, (R 1).toNat % 4 = 0 →
      AW live (mS H s) (mQ H n r s saved k) (R 1) R Mt →
      AW live (mS H s) (mQ H n r s saved k) pc4 R Mt)
    (hsp : SpOKA s) (hsv : saved.map Prod.fst = vsaSaved)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (F : MFrame s r rv0 R Mt)
    (hfresh : FreshBlock vsaLayoutP H (R 10).toNat n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : PHeapAt Mt (((R 10).toNat, n.toNat) :: H) top brkv chunks bins)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top) (hpres : ∀ a, vsaFoot H a → (Mt[a]?).isSome) :
    AW live (mS H s) (mQ H n r s saved k) pc1 R Mt := by
  have hlo := hsp.lo; have hhi := hsp.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  refine st1 (by rw [hs2]; sx_addr) (fun b hb => ?_) ?_
  · have := of_mem_accAddrs hb; rw [hs2] at this
    exact frame_owned hsp (by sx_addr) (by sx_addr)
  refine st2 (by rw [upd_other _ _ (by decide), hs2]; sx_addr) (fun b hb => ?_) ?_
  · have := of_mem_accAddrs hb; rw [upd_other _ _ (by decide), hs2] at this
    exact frame_owned hsp (by sx_addr) (by sx_addr)
  refine st3 ?_
  have hr : ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat = r :=
    ldv_eq_of_read (by rw [hs2]; sx_addr) F.ra
  have hs0 : ldv .ld (Mt) ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
      sign_extend (m := 64) (0x050#12)).toNat = rv0 8 :=
    ldv_eq_of_read (by rw [upd_other _ _ (by decide), hs2]; sx_addr) F.s0
  refine st4 (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hr]; exact hral) ?_
  have hpc : (upd (upd (upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 8
      (ldv .ld Mt ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
        sign_extend (m := 64) (0x050#12)).toNat)) 2
      ((upd (upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 8
        (ldv .ld Mt ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
          sign_extend (m := 64) (0x050#12)).toNat)) 2 + sign_extend (m := 64) (0x060#12))) 1 = r := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
  rw [hpc]
  have hs96 : R 2 + sign_extend (m := 64) (0x060#12) = s := by
    apply BitVec.eq_of_toNat_eq; rw [hs2]; sx_addr
  refine malloc_exit (brkv := brkv) (chunks := chunks) (bins := bins) hsv ?_ ?_ (fun p hp => ?_)
    ?_ ?_ ?_ hcap hpres
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hs96
  · have hk : p.1 ∈ vsaSaved := by rw [← hsv]; exact List.mem_map_of_mem hp
    have hv := hE.saved p hp
    unfold vsaSaved at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h <;> rw [h] at hv ⊢ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> rw [← hv]
    · exact hs0
    · exact F.s1
    · exact F.s2
    · exact F.s3
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hfresh
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hal
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hheap

/-- The epilogue at `0x8000484c`. -/
theorem epi_8000484c {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hlive : AllocLive live) (hsp : SpOKA s) (hsv : saved.map Prod.fst = vsaSaved)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (F : MFrame s r rv0 R Mt)
    (hfresh : FreshBlock vsaLayoutP H (R 10).toNat n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : PHeapAt Mt (((R 10).toNat, n.toNat) :: H) top brkv chunks bins)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top) (hpres : ∀ a, vsaFoot H a → (Mt[a]?).isSome) :
    AW live (mS H s) (mQ H n r s saved k) 0x8000484c#64 R Mt :=
  epi_core (st_8000484c hlive) (st_80004850 hlive) (st_80004854 hlive) (st_80004858 hlive)
    hsp hsv hral hE F hfresh hal hheap hcap hpres

/-- The epilogue at `0x80004830`. -/
theorem epi_80004830 {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hlive : AllocLive live) (hsp : SpOKA s) (hsv : saved.map Prod.fst = vsaSaved)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (F : MFrame s r rv0 R Mt)
    (hfresh : FreshBlock vsaLayoutP H (R 10).toNat n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : PHeapAt Mt (((R 10).toNat, n.toNat) :: H) top brkv chunks bins)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top) (hpres : ∀ a, vsaFoot H a → (Mt[a]?).isSome) :
    AW live (mS H s) (mQ H n r s saved k) 0x80004830#64 R Mt :=
  epi_core (st_80004830 hlive) (st_80004834 hlive) (st_80004838 hlive) (st_8000483c hlive)
    hsp hsv hral hE F hfresh hal hheap hcap hpres

/-- The heap during a malloc run: the page-aligned shape on the tracking
memory, its footprint present, the credits, and the stack window off the
footprint. -/
structure MHeap (H : List (Nat × Nat)) (s : BitVec 64) (kc : Nat) (Mt : Mem) (top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mt H top brkv chunks bins
  pres : ∀ a, vsaFoot H a → (Mt[a]?).isSome
  cap : 2 * kc + extendSlack ≤ heapEnd - top
  disj : ∀ a, stackWin s allocHeadroom a → ¬ vsaFoot H a

/-- An allocator-global doubleword is owned. -/
theorem glob_owned {H : List (Nat × Nat)} {s : BitVec 64} {a : Nat}
    (h1 : 0x8001ad10 ≤ a) (h2 : a + 8 ≤ 0x8001b520) : ∀ b ∈ accAddrs a 8, mS H s b := by
  intro b hb
  have := of_mem_accAddrs hb
  exact .inr (.inl (.inl ⟨by omega, by omega⟩))

/-- A small-request state at `0x800047dc`: the chunk size in `a4`, the bin
index in `a7`, the bin's `fd` offset in `a3`. -/
structure SmallRegs (nb : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = nb / 8
  a3 : (R 13).toNat = 16 * (nb / 8) + 16

/-- The chunk size of a request and its charge. -/
structure NbOK (n : BitVec 64) (c nb : Nat) : Prop where
  al : nb % 16 = 0
  lo : 32 ≤ nb
  fits : n.toNat + 8 ≤ nb
  chg : nb ≤ 2 * c

theorem nbOK_small {n : BitVec 64} {c nb : Nat} (h : NbOK n c nb) (hs : nb ≤ 503) :
    4 ≤ nb / 8 ∧ nb / 8 ≤ 62 ∧ nb / 8 % 2 = 0 ∧ nb = 8 * (nb / 8) := by
  have := h.al; have := h.lo; omega

/-- The registers `_malloc_r` keeps at the last-remainder check `0x800048ec`:
the chunk size in `a4`, the next bin index in `a7`, `__malloc_av_` in `a6`. -/
structure LRRegs (nb idx : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = idx
  a6 : R 16 = 0x8001ad10#64

/-- The bin headers' link words are owned. -/
theorem bin_link_owned {H : List (Nat × Nat)} {s : BitVec 64} {j a : Nat} (hj : j < numBins)
    (ha : a = binAt j + 16 ∨ a = binAt j + 24) : ∀ b ∈ accAddrs a 8, mS H s b := by
  have := binAt_geo j hj
  rcases ha with rfl | rfl <;> exact glob_owned (by omega) (by omega)

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
theorem j_small {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k c : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (hlive : AllocLive live) (hsp : SpOKA s)
    (F : MFrame s r rv0 R Mt) (Hp : MHeap H s (k + c) Mt top brkv chunks bins)
    (G : SmallRegs nb R) (hnb : NbOK n c nb) (hsmall : nb ≤ 503)
    (htake : ∀ pre v, bins (nb / 8) = pre ++ [v] →
      ∀ R', (R' 15).toNat = v → (R' 13).toNat = binAt (nb / 8) + 16 → R' 2 = R 2 → R' 8 = R 8 →
        R' 9 = R 9 → R' 18 = R 18 → R' 19 = R 19 →
        AW live (mS H s) (mQ H n r s saved k) 0x800047f4#64 R' Mt)
    (hLR : ∀ R', LRRegs nb (nb / 8 + 2) R' → R' 2 = R 2 → R' 8 = R 8 →
        R' 9 = R 9 → R' 18 = R 18 → R' 19 = R 19 →
        AW live (mS H s) (mQ H n r s saved k) 0x800048ec#64 R' Mt) :
    AW live (mS H s) (mQ H n r s saved k) 0x800047dc#64 R Mt := by
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
  refine st_800047dc hlive ?_
  refine st_800047e0 hlive ?_
  refine st_800047e4 hlive ?_
  sx_norm
  have hEA : (2147593488#64 + R 13 + sign_extend (m := 64) (0x008#12)).toNat = binAt (nb / 8) + 24 := by
    unfold binAt avAddr; sx_addr
  have hgeo := binAt_geo (nb / 8) (by unfold numBins; omega)
  refine st_800047e8 hlive ?_ ?_ ?_
  · sx_norm; rw [hEA]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEA]; exact bin_link_owned (j := nb / 8) (by unfold numBins; omega) (.inr rfl)
  sx_norm
  have hv : ldv .ld Mt (2147593488#64 + R 13 + 8#64).toNat = BitVec.ofNat 64 last :=
    bin_link_ld (by unfold binAt avAddr; sx_addr) hbk hlastlt
  rw [hv]
  refine st_800047ec hlive ?_
  sx_norm
  have hA2 : (2147593488#64 + R 13 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (nb / 8)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
  have hbinlt : binAt (nb / 8) < 2 ^ 64 := by omega
  refine st_800047f0 hlive (fun heq => ?_) (fun hne => ?_)
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
    refine st_80004c60 hlive ?_ ?_ ?_
    · sx_norm; rw [hEA1]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · sx_norm; rw [hEA1]; exact bin_link_owned (j := nb / 8 + 1) (by unfold numBins; omega) (.inr rfl)
    sx_norm
    have hv1 : ldv .ld Mt ((2147593488#64 + R 13) + 24#64).toNat = BitVec.ofNat 64 (binAt (nb / 8 + 1)) :=
      bin_link_ld (by unfold binAt avAddr; sx_addr) hbkJ hbkJlt
    rw [hv1]
    refine st_80004c64 hlive ?_
    sx_norm
    have hA3 : 2147593488#64 + R 13 = BitVec.ofNat 64 (binAt (nb / 8 + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
    refine st_80004c68 hlive (fun _ => ?_) (fun hne => absurd hA3 hne)
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

/-- A heap doubleword in the footprint is owned. -/
theorem foot_owned {H : List (Nat × Nat)} {s : BitVec 64} {a : Nat}
    (h : ∀ k, k < 8 → vsaFoot H (a + k)) : ∀ b ∈ accAddrs a 8, mS H s b := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact .inr (h j (List.mem_range.mp hj))

/-- A load at an address equal to one with a known doubleword (for `simp` with
`sx_addr` discharging the address). -/
theorem ldv_at {Mt : Mem} {a' x : Nat} (h : read64 Mt a' = some x) :
    ∀ a, a = a' → ldv .ld Mt a = BitVec.ofNat 64 x := by
  intro a he; subst he
  exact ldv_ld (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ h)])

/-- An owned footprint doubleword at an address equal to `a'`. -/
theorem foot_owned_at {H : List (Nat × Nat)} {s : BitVec 64} {a' : Nat}
    (h : ∀ k, k < 8 → vsaFoot H (a' + k)) : ∀ a, a = a' → ∀ b ∈ accAddrs a 8, mS H s b := by
  intro a he; subst he; exact foot_owned h

/-- Frame bytes are owned: the `sx_side` rule for stack accesses. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; have hb' := VsaIris.Sym.of_mem_accAddrs hb; refine VsaIris.VsaHeap.frame_owned ‹VsaIris.VsaHeap.SpOKA _› ?_ ?_ <;> sx_addr))

/-- A footprint doubleword lies wholly below or above the stack window. -/
theorem off_window {H : List (Nat × Nat)} {s : BitVec 64} {a : Nat}
    (hd : ∀ b, stackWin s allocHeadroom b → ¬ vsaFoot H b) (hf : ∀ k, k < 8 → vsaFoot H (a + k)) :
    a + 8 ≤ s.toNat - allocHeadroom ∨ s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hk : (if a ≥ s.toNat - allocHeadroom then 0 else s.toNat - allocHeadroom - a) < 8 := by
    split <;> omega
  refine hd _ ⟨?_, ?_⟩ (hf _ hk)
  · simp only; split <;> omega
  · simp only; unfold allocHeadroom at *; split <;> omega

/-- **The small take** (`0x800047f4`): unlink the last chunk `v` of small bin
`idx`, set `PREV_INUSE` after it, unlock, and return `v + 16`. -/
theorem small_take {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k c : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    {pre : List Nat} {v : Nat}
    (hlive : AllocLive live) (hsp : SpOKA s) (hsv : saved.map Prod.fst = vsaSaved)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (F : MFrame s r rv0 R Mt) (Hp : MHeap H s (k + c) Mt top brkv chunks bins)
    (hnb : NbOK n c nb) (hsmall : nb ≤ 503) (hbin : bins (nb / 8) = pre ++ [v])
    (h15 : (R 15).toNat = v) (h13 : (R 13).toNat = binAt (nb / 8) + 16) :
    AW live (mS H s) (mQ H n r s saved k) 0x800047f4#64 R Mt := by
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
  refine st_800047f4 hlive ?_ ?_ ?_
  · sx_addr
  · exact foot_owned_at hhv _ (by sx_addr)
  simp (disch := sx_addr) only [ldv_at hvr]
  -- ld a2,24(a5): its `bk`
  have hbkw : ∀ j, j < 8 → vsaFoot H (cv.addr + 24 + j) := fun j hj => by
    have := hlv (8 + j) (by omega); rwa [show cv.addr + 16 + (8 + j) = cv.addr + 24 + j by omega] at this
  refine st_800047f8 hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at hbkw _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at (show read64 Mt (cv.addr + 24) = some pred from hbkv)]
  -- ld a1,16(a5): its `fd`
  refine st_800047fc hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at (fun j hj => hlv j (by omega)) _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at (show read64 Mt (cv.addr + 16) = some (binAt (nb / 8)) from hfdv)]
  -- andi a4,a4,-4; add a4,a5,a4: the next chunk
  refine st_80004800 hlive ?_
  refine st_80004804 hlive ?_
  sx_norm
  -- ld a3,8(a4): the next chunk's header
  have hnx := foot_header B (HH.end_bnd hcv)
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  refine st_80004808 hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at hnx _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at hdr]
  -- the predecessor and the bin header
  have hpredm : pred = binAt (nb / 8) ∨ pred ∈ bins (nb / 8) := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  obtain ⟨hp16, _⟩ := HH.node (by omega) (by unfold numBins; omega) hpredm
  have hpl : (0x8001ad10 + 16 ≤ pred ∧ pred + 32 ≤ 0x8001b520) ∨ (heapStart ≤ pred ∧ pred + 32 ≤ top) := by
    rcases hpredm with rfl | hm
    · have := binAt_geo (nb / 8) (by unfold numBins; omega); unfold binAt avAddr at *; exact .inl (by omega)
    · obtain ⟨cx, hcx, rfl, _⟩ := HH.member (by omega) (by unfold numBins; omega) hm
      have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hgeo := binAt_geo (nb / 8) (by unfold numBins; omega)
  -- sd a2,24(a1): the bin's `bk` := the predecessor
  refine st_8000480c hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at (fun j hj => by
      have := B.node_foot (x := binAt (nb / 8)) (j := nb / 8) (by omega) (by unfold numBins; omega)
        (.inl rfl) (24 + j) (by omega) (by omega)
      rwa [show binAt (nb / 8) + (24 + j) = binAt (nb / 8) + 24 + j by omega] at this) _ (by sx_addr)
  sx_norm
  rw [show (BitVec.ofNat 64 (binAt (nb / 8)) + 24#64).toNat = binAt (nb / 8) + 24 by sx_addr]
  -- sd a5,8(sp)
  have hlo := hsp.lo; have hhi := hsp.hi; have hsal := hsp.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  refine st_80004810 hlive ?_ ?_ ?_
  · sx_norm; rw [hs2]; sx_addr
  · sx_norm; intro b hb; have := of_mem_accAddrs hb; rw [hs2] at this
    exact frame_owned hsp (by sx_addr) (by sx_addr)
  sx_norm
  rw [hs2, show (s + 18446744073709551520#64 + 8#64).toNat = s.toNat - 96 + 8 by sx_addr]
  -- sd a1,16(a2): the predecessor's `fd` := the bin header
  refine st_80004814 hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at (fun j hj => by
      have := B.node_foot (j := nb / 8) (by omega) (by unfold numBins; omega) hpredm (16 + j)
        (by omega) (by omega)
      rwa [show pred + (16 + j) = pred + 16 + j by omega] at this) _ (by sx_addr)
  sx_norm
  rw [show (BitVec.ofNat 64 pred + 16#64).toNat = pred + 16 by sx_addr]
  -- ori a3,a3,1; mv a0,s0
  refine st_80004818 hlive ?_
  refine st_8000481c hlive ?_
  sx_norm
  -- sd a3,8(a4): the next header, with `PREV_INUSE`
  refine st_80004820 hlive ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact foot_owned_at hnx _ (by sx_addr)
  sx_norm
  rw [show (R 15 + (BitVec.ofNat 64 hv &&& 18446744073709551612#64) + 8#64).toNat =
    cv.addr + cv.size + 8 by sx_addr]
  -- the written heap words lie off the stack window
  have hoffN := off_window Hp.disj hnx
  have hoffP := off_window Hp.disj (a := pred + 16) fun j hj => by
    have := B.node_foot (j := nb / 8) (by omega) (by unfold numBins; omega) hpredm (16 + j) (by omega) (by omega)
    rwa [show pred + (16 + j) = pred + 16 + j by omega] at this
  unfold allocHeadroom at hoffN hoffP
  have hs2n : (R 2).toNat = s.toNat - 96 := by rw [hs2]; sx_addr
  sx_run [12] hlive at 0x80004830
  -- the bin's `bk` word lies off the stack window too
  have hoffB := off_window Hp.disj (a := binAt (nb / 8) + 24) fun j hj => by
    have := B.node_foot (x := binAt (nb / 8)) (j := nb / 8) (by omega) (by unfold numBins; omega)
      (.inl rfl) (24 + j) (by omega) (by omega)
    rwa [show binAt (nb / 8) + (24 + j) = binAt (nb / 8) + 24 + j by omega] at this
  unfold allocHeadroom at hoffB
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
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (pred + 16) = some (binAt (nb / 8)) := by
    rw [read64_store_miss _ _ (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbinlt]
  have rd_bk : read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (binAt (nb / 8) + 24) = some pred := by
    unfold binAt avAddr heapStart at *
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_hit, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hpredlt]
  have rd_hd : read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (cv.addr + cv.size + 8) =
      some (hd + 1) := by
    rw [read64_store_hit, hOr]
  have rd_frame : ∀ o, o + 8 ≤ 96 → 16 ≤ o → read64 (writeLog (writeLog (writeLog (writeLog Mt
      [(binAt (nb / 8) + 24, 8, BitVec.ofNat 64 pred)]) [(s.toNat - 96 + 8, 8, R 15)])
      [(pred + 16, 8, BitVec.ofNat 64 (binAt (nb / 8)))])
      [(cv.addr + cv.size + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (s.toNat - 96 + o) =
      read64 Mt (s.toNat - 96 + o) := by
    intro o ho1 ho2
    unfold binAt avAddr at *
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega)]
  have hcapk : 2 * k + extendSlack ≤ heapEnd - top := by have := Hp.cap; omega
  have ha0 : (R 15 + 16#64).toNat = cv.addr + 16 := by rw [BitVec.toNat_add, h15]; sx_addr
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hcv hcvf (n := n.toNat) (by omega)
  refine epi_80004830 (brkv := brkv) (chunks := chunks.map (reflag (cv.addr + cv.size) true))
    (bins := updBins bins (nb / 8) pre) hlive hsp hsv hral hE ?F ?fr ?al ?heap hcapk ?pres
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
    have hpost : pre = pre ++ [] := (List.append_nil pre).symm
    refine hpost ▸ PHeapAt.take Hp.heap (i := nb / 8) (by omega) (by unfold numBins; omega)
      (pre := pre) (post := []) hbin hcv rfl (n := n.toNat) (by omega) hpred hsucc rd_fd rd_bk rd_hd
      ?_ ?_ ?_
    · intro h0 h0r
      rw [hdr] at h0r; cases h0r
      unfold chunkSize; omega
    · unfold prevInuse; simp only [beq_iff_eq]; omega
    · intro a ha hna
      unfold TakeW at hna
      have hns : a < s.toNat - 512 ∨ s.toNat ≤ a := by
        refine Classical.byContradiction fun hc => Hp.disj a ?_ ha
        unfold stackWin InExt allocHeadroom; simp only; omega
      unfold binAt avAddr at *
      rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
        simp only [OutL, and_true] <;> omega
  case pres =>
    intro a ha
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (Hp.pres a ha))))

end VsaIris.VsaHeap
