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

/-- **The epilogue at `0x8000484c`**: `ld ra; ld s0; addi sp; ret`, then the
return. -/
theorem epi_8000484c {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k : Nat} {rv0 R : Nat → BitVec 64} {Mt : Mem}
    {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hlive : AllocLive live) (hsp : SpOKA s) (hsv : saved.map Prod.fst = vsaSaved)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (F : MFrame s r rv0 R Mt)
    (hfresh : FreshBlock vsaLayoutP H (R 10).toNat n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : PHeapAt Mt (((R 10).toNat, n.toNat) :: H) top brkv chunks bins)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top) (hpres : ∀ a, vsaFoot H a → (Mt[a]?).isSome) :
    AW live (mS H s) (mQ H n r s saved k) 0x8000484c#64 R Mt := by
  have hlo := hsp.lo; have hhi := hsp.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  refine st_8000484c hlive (by rw [hs2]; sx_addr) (fun b hb => ?_) ?_
  · have := of_mem_accAddrs hb; rw [hs2] at this
    exact frame_owned hsp (by sx_addr) (by sx_addr)
  refine st_80004850 hlive (by rw [upd_other _ _ (by decide), hs2]; sx_addr) (fun b hb => ?_) ?_
  · have := of_mem_accAddrs hb; rw [upd_other _ _ (by decide), hs2] at this
    exact frame_owned hsp (by sx_addr) (by sx_addr)
  refine st_80004854 hlive ?_
  have hr : ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat = r :=
    ldv_eq_of_read (by rw [hs2]; sx_addr) F.ra
  have hs0 : ldv .ld (Mt) ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
      sign_extend (m := 64) (0x050#12)).toNat = rv0 8 :=
    ldv_eq_of_read (by rw [upd_other _ _ (by decide), hs2]; sx_addr) F.s0
  refine st_80004858 hlive (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hr]; exact hral) ?_
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
  refine malloc_exit (brkv := brkv) (chunks := chunks) (bins := bins) hsv ?_ ?_ (fun p hp => ?_) ?_ ?_ ?_ hcap hpres
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
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hfresh
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hal
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hheap

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

end VsaIris.VsaHeap
