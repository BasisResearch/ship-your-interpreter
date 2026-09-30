import VsaIris.Vsa.MallocCtx
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure SmallRegs (nb : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = nb / 8
  a3 : (R 13).toNat = 16 * (nb / 8) + 16

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

structure LRRegs (nb idx : Nat) (R : Nat → BitVec 64) : Prop where
  a4 : (R 14).toNat = nb
  a7 : (R 17).toNat = idx
  a6 : R 16 = 0x8001ad10#64

theorem ldv_eq_of_read {Mt : Mem} {a a' : Nat} {v : BitVec 64} (he : a = a')
    (h : read64 Mt a' = some v.toNat) : ldv .ld Mt a = v := by
  subst he; exact ldv_ld h

theorem bin_link_ld {Mt : Mem} {a a' l : Nat} (he : a = a') (h : read64 Mt a' = some l)
    (hl : l < 2 ^ 64) : ldv .ld Mt a = BitVec.ofNat 64 l :=
  ldv_eq_of_read he (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl])

theorem toNat_sx32_small (x : BitVec 64) (h : x.toNat < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 x)).toNat = x.toNat := by
  have he : (BitVec.extractLsb 31 0 x).toNat = x.toNat := by
    rw [BitVec.extractLsb_toNat]; simp; omega
  have hm : (BitVec.extractLsb 31 0 x).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, he]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, he]
  omega

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
  obtain ⟨last, hlast⟩ : ∃ l, (binAt (nb / 8) :: bins (nb / 8)).getLast? = some l := ⟨_, List.getLast?_cons⟩
  have hbk := ring_bk_head hring hlast
  have hlastlt := Vsa.Sim.read64_lt _ _ _ hbk
  have hb : binAt (nb / 8) = 2147593488 + 16 * (nb / 8) := rfl
  have hbJ : binAt (nb / 8 + 1) = 2147593488 + 16 * (nb / 8 + 1) := rfl
  have Bn := binRgn C.H (j := nb / 8) (by unfold numBins; omega)
  have BnJ := binRgn C.H (j := nb / 8 + 1) (by unfold numBins; omega)
  rgn_step O.live at 0x800047e8
  sx_norm
  rgn_run O.live at 0x800047ec
  rgn_ld [hbk]
  rgn_run O.live at 0x800047f0
  have hA2 : (2147593488#64 + R 13 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (nb / 8)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
  refine (step% st 0x800047f0) O.live (fun heq => ?_) (fun hne => ?_)
  ·
    rgn_run O.live at 0x80004c64
    rgn_ld [hbkJ]
    refine (step% st 0x80004c64) O.live ?_
    sx_norm
    have hA3 : 2147593488#64 + R 13 = BitVec.ofNat 64 (binAt (nb / 8 + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; sx_addr
    refine (step% st 0x80004c68) O.live (fun _ => ?_) (fun hne => absurd hA3 hne)
    refine hLR _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact ha4
    · rw [toNat_sx32_small _ (by sx_addr)]; sx_addr
  ·
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

theorem small_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    {pre : List Nat} {v : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (hnb : NbOK C.n nb) (hsmall : nb ≤ 503) (hbin : bins (nb / 8) = pre ++ [v])
    (h15 : (R 15).toNat = v) (h13 : (R 13).toNat = binAt (nb / 8) + 16) :
    AW C.live C.S C.Q 0x800047f4#64 R Mt := by
  have HH := Hp.heap.heap.heap
  obtain ⟨hi4, hi62, hiev, hnbi⟩ := nbOK_small hnb hsmall
  have hi1 : nb / 8 < numBins := by unfold numBins; omega
  obtain ⟨cv, hcv, hcva, hcvf, hcvs, _⟩ := HH.small_member (i := nb / 8) (q := v) (by omega) (by omega)
    (by rw [hbin]; simp)
  subst hcva
  have hring := (binList_iff_ring.1 (HH.bins_list (nb / 8) (by omega) hi1)).1
  rw [hbin] at hring
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt (nb / 8) :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  have hsucc : (([] : List Nat) ++ [binAt (nb / 8)]).head? = some (binAt (nb / 8)) := rfl
  obtain ⟨hfdv, hbkv⟩ := ring_member (post := []) hring hpred hsucc
  have hpredm : pred = binAt (nb / 8) ∨ pred ∈ bins (nb / 8) := by
    rcases List.mem_cons.mp (List.mem_of_getLast? hpred) with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  have K := Hp.heap.heap.chunkK hcv; have FS := Hp.heap.heap.freeSpan hcv hcvf
  have P := Hp.heap.heap.nodeK (by omega) hi1 hpredm; have Bn := binRgn C.H hi1
  open_fields K; open_fields P
  obtain ⟨hv, hvr, hvsz, hvlow⟩ := K.hdrv; obtain ⟨hd, hdr, hdpi⟩ := K.nhdrv
  have hgeo := binAt_geo (nb / 8) hi1
  have hvlt := Vsa.Sim.read64_lt _ _ _ hvr; have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hszv : (BitVec.ofNat 64 hv &&& 18446744073709551612#64).toNat = cv.size := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]; unfold chunkSize at hvsz; omega
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [F.sp]; sx_addr
  have St := O.stackRgn
  have oN := K_nhdr.offStack Hp.disj (by decide); have oP := P_links.offStack Hp.disj (by decide)
  have oB := Bn.offStack Hp.disj (by decide); unfold mHead at oN oP oB
  rgn_run O.live at 0x80004800
  rgn_ld [hvr, hbkv, hfdv]
  rgn_run O.live at 0x8000480c
  rgn_ld [hdr]
  rgn_run O.live at 0x80004830
  rw [show (BitVec.ofNat 64 (binAt (nb / 8)) + 24#64).toNat = binAt (nb / 8) + 24 by rgn_arith,
    show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith,
    show (BitVec.ofNat 64 pred + 16#64).toNat = pred + 16 by rgn_arith,
    show (R 15 + (BitVec.ofNat 64 hv &&& 18446744073709551612#64) + 8#64).toNat =
      cv.addr + cv.size + 8 by rgn_arith]
  have hdeven : hd % 2 = 0 := by
    rw [hcvf] at hdpi; unfold prevInuse at hdpi
    simp only [beq_eq_false_iff_ne, ne_eq] at hdpi; omega
  have hd4 : hd % 4 < 2 := by
    rcases K_next with he | ⟨d, hdm, hda⟩
    · exfalso; have := HH.top_size; rw [he, HH.top_header] at hdr; cases hdr; omega
    · obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d hdm
      rw [hda, hdr] at hd0r; cases hd0r; exact hd0l
  have hOr : (BitVec.ofNat 64 hd ||| 1#64).toNat = hd + 1 := by
    have := or_one_even (BitVec.ofNat 64 hd) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]; exact hdeven)
    rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at this
    rw [this, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    simp; omega
  have hvP : (BitVec.ofNat 64 pred).toNat = pred := by rw [BitVec.toNat_ofNat]; omega
  have hvB : (BitVec.ofNat 64 (binAt (nb / 8))).toNat = binAt (nb / 8) := by rw [BitVec.toNat_ofNat]; omega
  have hn8 : C.n.toNat + 8 ≤ cv.size := by have := hnb.fits; omega
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hcv hcvf hn8
  refine epi_80004830 O ?F (O.fin_take (v := cv.addr) ?a0 ⟨hfr, hal16,
    ⟨_, brkv, _, updBins bins (nb / 8) (pre ++ []), ?heap, Nat.le_add_right _ _, Hp.live.map_reflag (cv.addr + cv.size)⟩,
    pres_store (pres_store (pres_store (pres_store Hp.pres))), ?frame⟩)
  case a0 => rgn_arith
  case F =>
    exact ((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).of_regs
      rfl rfl rfl rfl
  case frame =>
    simp only [writeLog_nest, List.cons_append, List.nil_append]
    exact frame_log (by log_in) Hp.frame
  case heap =>
    suffices hR : Realises C.H Mt _ (unlinkPermit pred (binAt (nb / 8)) (cv.addr + cv.size) (hd + 1)) by
      exact Hp.heap.take (by omega) hi1 (post := []) hbin hcv rfl hn8 hpred hsucc
        (hd' := hd + 1) hR.reads.1 hR.reads.2.1 hR.reads.2.2.1
        (fun h0 h0r => by rw [hdr] at h0r; cases h0r; unfold chunkSize; omega)
        (by unfold prevInuse; simp only [beq_iff_eq]; omega) hR.agree
    exact Realises.of_log (by wl_win <;> first
        | exact .inl (by unfold TakeW; omega)
        | exact .inr fun hf => by have := offStack_pt Hp.disj hf; omega)
      (by rd_log [hvB, hvP, hOr]) trivial

end VsaIris.VsaHeap
