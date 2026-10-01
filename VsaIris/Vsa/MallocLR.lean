import VsaIris.Vsa.MallocPro
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.MallocGlue2

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem lr_cmp {x y : BitVec 64} {sz nb : Nat} (hx : x.toNat = sz) (hy : y.toNat = nb)
    (hsz : sz < 2 ^ 62) (hnb : nb < 2 ^ 62) :
    ((31#64).toInt < (x - y).toInt ↔ nb + 32 ≤ sz) ∧
      ((0#64).toInt ≤ (x - y).toInt ↔ nb ≤ sz) := by
  have hxy : (x - y).toNat = (sz + (2 ^ 64 - nb)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, hx, hy]; omega
  have hi : (x - y).toInt =
      if 2 * (x - y).toNat < 2 ^ 64 then ((x - y).toNat : Int)
      else ((x - y).toNat : Int) - 2 ^ 64 := BitVec.toInt_eq_toNat_cond _
  rw [hxy] at hi
  have h31 : ((31#64 : BitVec 64)).toInt = (31 : Int) := by decide
  have h0 : ((0#64 : BitVec 64)).toInt = (0 : Int) := by decide
  by_cases hle : nb ≤ sz
  · rw [show (sz + (2 ^ 64 - nb)) % 2 ^ 64 = sz - nb by omega, if_pos (by omega)] at hi
    rw [hi, h31, h0]
    exact ⟨by omega, by omega⟩
  · rw [show (sz + (2 ^ 64 - nb)) % 2 ^ 64 = 2 ^ 64 - (nb - sz) by omega, if_neg (by omega)] at hi
    rw [hi, h31, h0]
    exact ⟨by constructor <;> intro hc <;> omega, by constructor <;> intro hc <;> omega⟩

structure LRVictim (nb sz v : Nat) (R : Nat → BitVec 64) : Prop where
  a5 : (R 15).toNat = v
  t1 : (R 6).toNat = sz
  a3 : R 13 = R 6 - R 14
  a4 : (R 14).toNat = nb
  t4 : (R 29).toNat = binAt 1

structure MDetach (C : MCtx) (Mt Mt' : Mem) (bins : Nat → List Nat) (i v : Nat) : Prop where
  bin : bins i = [v]
  fd : fdOf Mt' (binAt i) = some (binAt i)
  bk : bkOf Mt' (binAt i) = some (binAt i)
  agree : ∀ a, vsaFoot C.H a → ¬ (binAt i + 16 ≤ a ∧ a < binAt i + 32) → Mt'[a]? = Mt[a]?
  pres : ∀ a, vsaFoot C.H a → (Mt'[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt'[a]? = C.Mt0[a]?

theorem lr_check {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb31 : nb < 2 ^ 31)
    (hscan : bins 1 = [] → ∀ R', MFrame C R' Mt → LRRegs nb idx R' → (R' 29).toNat = binAt 1 →
      R' 8 = reentV →
      AW C.live C.S C.Q 0x80004be8#64 R' Mt)
    (hsplit : ∀ v sz, bins 1 = [v] → FreeAt chunks v sz → nb + 32 ≤ sz →
      ∀ R', MFrame C R' Mt → LRRegs nb idx R' → LRVictim nb sz v R' → R' 8 = reentV →
        AW C.live C.S C.Q 0x80004da0#64 R' Mt)
    (hexact : ∀ v sz, FreeAt chunks v sz → nb ≤ sz → sz < nb + 32 →
      ∀ R' Mt', MFrame C R' Mt' → MDetach C Mt Mt' bins 1 v → LRVictim nb sz v R' →
        AW C.live C.S C.Q 0x80004d78#64 R' Mt')
    (hrebin : ∀ v sz, FreeAt chunks v sz → sz < nb →
      ∀ R' Mt', MFrame C R' Mt' → MDetach C Mt Mt' bins 1 v → LRRegs nb idx R' →
        LRVictim nb sz v R' → R' 8 = reentV →
        AW C.live C.S C.Q 0x8000491c#64 R' Mt') :
    AW C.live C.S C.Q 0x800048ec#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have ha4 := G.a4; have ha7 := G.a7
  have ha6 : (R 16).toNat = 2147593488 := by rw [G.a6]; rfl
  have hb1 : binAt 1 = 2147593504 := rfl
  have Bn := binRgn C.H (j := 1) (by decide)
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hbinI := HH.bins_list 1 (by decide) (by unfold numBins; decide)
  have hring := (binList_iff_ring.1 hbinI).1
  have hnev := (binList_iff_ring.1 hbinI).2

  obtain ⟨first, hfd, hfirst⟩ :
      ∃ f, fdOf Mt (binAt 1) = some f ∧ ((bins 1 = [] ∧ f = binAt 1) ∨ bins 1 = [f]) := by
    obtain ⟨l, hl⟩ : ∃ l, bins 1 = l := ⟨_, rfl⟩
    rcases l with _ | ⟨v, vs⟩
    · exact ⟨binAt 1, (ring_nil_iff.1 (hl ▸ hring)).1, .inl ⟨hl, rfl⟩⟩
    · have hlen := HH.remainder
      rw [hl] at hlen
      have hvs : vs = [] := by
        rcases vs with _ | ⟨w, ws⟩
        · rfl
        · simp only [List.length_cons] at hlen; omega
      subst hvs
      exact ⟨v, ring_fd_head (hl ▸ hring) rfl, .inr hl⟩
  have hfirstlt := Vsa.Sim.read64_lt _ _ _ hfd
  rgn_run O.live at 0x800048f0
  rgn_ld [hfd]
  rgn_step O.live at 0x800048f8
  sx_norm
  have ht4 : (2147593504#64 : BitVec 64) = BitVec.ofNat 64 (binAt 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; decide
  refine (step% st 0x800048f8) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc ⊢
  ·
    rw [ht4] at hc
    have hb : bins 1 = [] := by
      rcases hfirst with ⟨h1, _⟩ | h1
      · exact h1
      · exfalso
        have he := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfirstlt,
          Nat.mod_eq_of_lt (by omega)] at he
        exact hnev first (by rw [h1]; exact List.mem_cons_self) he
    refine hscan hb _ (((F.upd (by decide)).upd (by decide)).upd (by decide)) ⟨?_, ?_, ?_⟩ ?_ ?_ <;>
      reg_close [ha4, ha7, G.a6, h8]
  ·
    rw [ht4] at hc
    have hb : bins 1 = [first] := by
      rcases hfirst with ⟨_, rfl⟩ | h1
      · exact absurd rfl hc
      · exact h1
    obtain ⟨sz, hfree⟩ := freeAt_of_member HH (j := 1) (by decide)
      (by unfold numBins; decide) (by rw [hb]; exact List.mem_cons_self)
    have K := Hp.heap.heap.chunkK hfree
    open_fields K
    obtain ⟨hh, hhr, hhsz, hhlow⟩ := K_hdrv
    have hhlt := Vsa.Sim.read64_lt _ _ _ hhr
    rgn_run O.live at 0x80004900
    rgn_ld [hhr]
    rgn_run O.live at 0x8000490c
    have hszv : ((BitVec.ofNat 64 hh) &&& 18446744073709551612#64).toNat = sz := by
      rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt]
      unfold chunkSize at hhsz; omega
    have hnb62 : nb < 2 ^ 62 := by omega
    have hsz62 : sz < 2 ^ 62 := by omega
    have hcmp := lr_cmp (x := (BitVec.ofNat 64 hh) &&& 18446744073709551612#64) (y := R 14)
      hszv ha4 hsz62 hnb62
    refine (step% st 0x8000490c) O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc2 ⊢
    ·
      refine hsplit first sz hb hfree (hcmp.1.1 hc2) _
        (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
        reg_close [ha4, ha7, G.a6, hszv, h8]
    ·
      have hlt32 : sz < nb + 32 := by
        have := hcmp.1
        omega
      rgn_run O.live at 0x80004918
      rw [show (R 16 + 40#64).toNat = binAt 1 + 24 by rgn_arith,
        show (R 16 + 32#64).toNat = binAt 1 + 16 by rgn_arith]
      have hwv : ((2147593504#64 : BitVec 64)).toNat = binAt 1 := rfl
      have hD : MDetach C Mt (writeLog (writeLog Mt [(binAt 1 + 24, 8, 2147593504#64)])
          [(binAt 1 + 16, 8, 2147593504#64)]) bins 1 first :=
        ⟨hb, show read64 _ (binAt 1 + 16) = _ by rd_log [hwv],
          show read64 _ (binAt 1 + 24) = _ by rd_log [hwv], fun a _ hna => by
            rw [writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩,
              writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩],
          pres_store (pres_store Hp.pres),
          by rw [writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) Hp.frame⟩
      refine (step% st 0x80004918) O.live (fun hc3 => ?_) (fun hc3 => ?_) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3
      ·
        refine hexact first sz hfree (hcmp.2.1 hc3) hlt32 _ _
          (((F.of_regs ?_ ?_ ?_ ?_).store (by omega)).store (by omega)) hD
          ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          reg_close [hszv, ha4, hwv]
      ·
        refine hrebin first sz hfree (by have := hcmp.2; omega) _ _
          (((F.of_regs ?_ ?_ ?_ ?_).store (by omega)).store (by omega)) hD
          ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
          reg_close [ha4, ha7, G.a6, hszv, hwv, h8]

theorem MDetach.read {C : MCtx} {Mt Mt' : Mem} {bins : Nat → List Nat} {i v : Nat}
    (D : MDetach C Mt Mt' bins i v) {a : Nat} (hf : ∀ k, k < 8 → vsaFoot C.H (a + k))
    (hoff : a + 8 ≤ binAt i + 16 ∨ binAt i + 32 ≤ a) : read64 Mt' a = read64 Mt a :=
  read64_agreeP (P := fun b => vsaFoot C.H b ∧ ¬ (binAt i + 16 ≤ b ∧ b < binAt i + 32))
    (fun b hb => D.agree b hb.1 hb.2) (fun k hk => ⟨hf k hk, by omega⟩)

theorem lr_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb sz v : Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb)
    (hfree : FreeAt chunks v sz) (hle : nb ≤ sz)
    (F : MFrame C R Mt') (D : MDetach C Mt Mt' bins 1 v) (G : LRVictim nb sz v R) :
    AW C.live C.S C.Q 0x80004d78#64 R Mt' := by
  have HH := Hp.heap.heap.heap
  have K := Hp.heap.heap.chunkK hfree
  open_fields K
  obtain ⟨hd, hdr, hdpi⟩ := K_nhdrv
  have hb1 : binAt 1 = 2147593504 := rfl
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have ha5 := G.a5; have ht1 := G.t1
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [F.sp]; sx_addr
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdr' : read64 Mt' (v + sz + 8) = some hd := (D.read K_nhdr.byte (by omega)).trans hdr
  have oN := K_nhdr.offStack Hp.disj (by decide); unfold mHead at oN
  have St := O.stackRgn
  rgn_run O.live at 0x80004d80
  rgn_ld [hdr']
  rgn_run O.live at 0x8000484c
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith,
    show (R 15 + R 6 + 8#64).toNat = v + sz + 8 by rgn_arith]
  have hdeven : hd % 2 = 0 := by
    unfold prevInuse at hdpi; simp only [beq_eq_false_iff_ne, ne_eq] at hdpi; omega
  have hd4 : hd % 4 < 2 := by
    rcases K_next with he | ⟨d, hdm, hda⟩
    · exfalso; have := HH.top_size; rw [he, HH.top_header] at hdr; cases hdr; omega
    · obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d hdm
      rw [hda, hdr] at hd0r; cases hd0r; exact hd0l
  have hOr : ((BitVec.ofNat 64 hd) ||| 1#64).toNat = hd + 1 := by
    have hoe := or_one_even (BitVec.ofNat 64 hd)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]; exact hdeven)
    rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at hoe
    rw [hoe, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hn8 : C.n.toNat + 8 ≤ sz := by have := hnb.fits; omega
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) hn8
  refine epi_8000484c O ?F (O.fin_take (v := v) ?a0 ⟨hfr, hal16,
    ⟨_, brkv, _, updBins bins 1 ([] ++ []), ?heap, Nat.le_add_right _ _, Hp.live.map_reflag (v + sz)⟩,
    pres_store (pres_store D.pres), ?frame⟩)
  case a0 => rgn_arith
  case F => exact ((F.store (by omega)).store (by omega)).of_regs rfl rfl rfl rfl
  case frame => rw [writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) D.frame
  case heap =>
    refine Hp.heap.take (i := 1) (by decide) (by unfold numBins; decide) (pre := []) (post := [])
      D.bin hfree rfl hn8 (pred := binAt 1) (succ := binAt 1) rfl rfl
      (show read64 _ (binAt 1 + 16) = _ by rd_log; exact D.fd)
      (show read64 _ (binAt 1 + 24) = _ by rd_log; exact D.bk) (hd' := hd + 1) (by rd_log [hOr])
      (fun h0 h0r => by rw [hdr] at h0r; cases h0r; unfold chunkSize; omega)
      (by unfold prevInuse; simp only [beq_iff_eq]; omega) fun a ha hna => ?_
    unfold TakeW at hna; simp only at hna; have := offStack_pt Hp.disj ha
    rw [writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩,
      writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩]
    exact D.agree a ha (by omega)

theorem lr_last {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hscan : bins 1 = [] → ∀ R', MFrame C R' Mt → LRRegs nb idx R' → (R' 29).toNat = binAt 1 →
      R' 8 = reentV →
      AW C.live C.S C.Q 0x80004be8#64 R' Mt)
    (hsplit : ∀ v sz, bins 1 = [v] → FreeAt chunks v sz → nb + 32 ≤ sz →
      ∀ R', MFrame C R' Mt → LRRegs nb idx R' → LRVictim nb sz v R' → R' 8 = reentV →
        AW C.live C.S C.Q 0x80004da0#64 R' Mt)
    (hrebin : ∀ v sz, FreeAt chunks v sz → sz < nb →
      ∀ R' Mt', MFrame C R' Mt' → MDetach C Mt Mt' bins 1 v → LRRegs nb idx R' →
        LRVictim nb sz v R' → R' 8 = reentV →
        AW C.live C.S C.Q 0x8000491c#64 R' Mt') :
    AW C.live C.S C.Q 0x800048ec#64 R Mt :=
  lr_check O F Hp G h8 hnb31 hscan hsplit
    (fun _ _ hfree hle _ _ _ F' D' G' => lr_take O Hp hnb hfree hle F' D' G') hrebin
