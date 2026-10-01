import VsaIris.Vsa.FreePro
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure FDone (C : MCtx) (Mt : Mem) : Prop where
  heap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins ∧ top ≤ C.top0
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

structure FBinCore (C : MCtx) (Mt M2 : Mem) (X S top brkv : Nat) (cs₁ cs₂ : List Chunk)
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

structure FBin (C : MCtx) (Mt M2 : Mem) (X S top brkv : Nat) (cs₁ cs₂ : List Chunk)
    (bins : Nat → List Nat) : Prop extends FBinCore C Mt M2 X S top brkv cs₁ cs₂ bins where
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

theorem FBin.read {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {w : Nat}
    (hf : ∀ k, k < 8 → vsaFoot C.H (w + k)) (hw : w + 8 ≤ X + S ∨ X + S + 16 ≤ w) :
    read64 Mt w = read64 M2 w :=
  read64_keep fun k hk => B.agree _ (hf k hk) (by omega)


theorem foot_of_chunk {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) {X S : Nat}
    (hX : (⟨X, S, true⟩ : Chunk) ∈ chunks) (hno : ∀ e ∈ H, e.1 ≠ X + 16) {a : Nat}
    (h1 : X + 8 ≤ a) (h2 : a < X + S + 8) : vsaFoot H a := by
  have HH := h.heap.heap
  have hb := HH.walk.chunk_bounds _ hX
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := h.heap.top_room
  simp only at hb
  refine .inr ⟨by omega, by omega, fun e he hin => ?_⟩
  obtain ⟨c, hc, hu, hce, hcs⟩ := HH.exact e he he
  have hcb := HH.walk.chunk_bounds c hc
  unfold InExt at hin
  rcases HH.walk.chunk_sep c hc _ hX with rfl | h3 | h3
  · exact hno e he (by simp only at hce; omega)
  · simp only at h3; omega
  · simp only at h3; omega

theorem FBin.foot_chunk {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {a : Nat}
    (h1 : X + 8 ≤ a) (h2 : a < X + S + 8) : vsaFoot C.H a :=
  foot_of_chunk B.heap (by simp) B.hno h1 h2


theorem fb_release {C : MCtx} {Mt M2 Mf : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBinCore C Mt M2 X S top brkv cs₁ cs₂ bins)
    {j pred succ bb' : Nat} {pre' post' : List Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hidx : 1 < j → binIndex S = j) (hj1 : j = 1 → bins 1 = [])
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hV1 : fdOf Mf X = some succ) (hV2 : bkOf Mf X = some pred)
    (hP : fdOf Mf pred = some X) (hSb : bkOf Mf succ = some X)
    (hbbr : read64 Mf binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : 1 < j → bb' / 2 ^ (j / 4) % 2 = 1)
    (hbbkeep : ∀ bb, read64 M2 binblocksAddr = some bb →
      ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (hag : ∀ w, vsaFoot C.H w → ¬ RelW X S pred succ w → Mf[w]? = Mt[w]?)
    (hkeep : ∀ w, X + S ≤ w → w < X + S + 16 → Mf[w]? = Mt[w]?)
    (hpres : ∀ a, vsaFoot C.H a → (Mf[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → Mf[a]? = C.Mt0[a]?) :
    FDone C Mf := by
  have eF : read64 Mf (X + S) = some S := by
    rw [read64_keep (fun k hk => hkeep _ (by omega) (by omega))]; exact B.foot
  have eN : ∀ hd, read64 M2 (X + S + 8) = some hd → ∃ hd', read64 Mf (X + S + 8) = some hd' ∧
      chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2 ∧ prevInuse hd' = false := by
    intro hd hr
    obtain ⟨hd', h1', h2', h3', h4'⟩ := B.nx hd hr
    exact ⟨hd', by rw [read64_keep (fun k hk => hkeep _ (by omega) (by omega))]; exact h1', h2', h3', h4'⟩
  have hag' : ∀ w, vsaFoot C.H w → ¬ RelW X S pred succ w → Mf[w]? = M2[w]? := by
    intro w hw hna
    rw [hag w hw hna]
    exact B.agree w hw (fun h => hna (.inr (.inr (.inr (.inr h)))))
  have HP := B.heap.release B.hno B.prev B.next B.not_top hj0 hj hidx hj1 hpos hpred hsucc
    hV1 hV2 hP hSb eF eN hbbr hbblt hbbset hbbkeep hag'
  exact ⟨⟨_, _, _, _, HP, B.top_le⟩, hpres, hframe⟩

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
  have BB := B.heap.heap
  have HH := BB.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K := BB.chunkK hX; open_fields K
  have hjn : j < numBins := by unfold numBins; omega
  have hgj := binAt_geo j hjn
  have hofm : first = binAt j ∨ first ∈ bins j := by
    have := List.mem_of_mem_head? hfirst
    rcases List.mem_append.mp this with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  have Nf := BB.nodeK (by omega) hjn hofm
  open_fields Nf
  have hoX : first ≠ X := by
    rcases hofm with rfl | h
    · omega
    · intro he; obtain ⟨c, hc, hca, hf⟩ := HH.member (by omega) hjn h
      have := HH.chunk_eq hc hX (hca.trans he)
      rw [this] at hf; cases hf
  have hbS := Nf.bnd _ K.next 16 (by omega) (by omega)
  have rX : Rgn (vsaFoot C.H) (X + 16) 16 := ⟨fun k hk => B.foot_chunk (by omega) (by omega)⟩
  have rG := globRgn C.H
  have hbA : binblocksAddr = 0x8001ad18 := rfl
  simp only at hbS
  refine fb_release B.toFBinCore (j := j) (pre' := []) (post' := bins j) (pred := binAt j) (by omega) hjn
    (fun _ => by unfold binIndex; rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; omega)
    (fun h => absurd h (by omega)) rfl rfl hfirst (by unfold fdOf; rd_log [h0]) (by unfold bkOf; rd_log [h1])
    (by unfold fdOf; rd_log [h3]) (by unfold bkOf; rd_log [h3]) (by rd_log [h2])
    (lor_lt bb _ (B.heap.bb_lt bb hbb) (by omega)) (fun _ => lor_bit_set bb _) (fun bb0 hbb0 k hk => by
      rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk)
    (fun w _ => (by wl_win <;> (unfold RelW; omega) : WinAgree (RelW X S (binAt j) first) _ Mt) w)
    (fun w h1 h2 => (by wl_win <;> omega : WinAgree (fun a => ¬ (X + S ≤ a ∧ a < X + S + 16)) _ Mt) w
      (fun h => h ⟨h1, h2⟩))
    (pres_log _ (pres_log _ (pres_log _ (pres_log _ (pres_log _ B.pres))))) ?_
  simp only [writeLog_nest, List.cons_append, List.nil_append]
  exact frame_log (by log_in) B.frame

theorem fb_small {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) (hS : S ≤ 511)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x800073f0#64 R Mt := by
  have BB := B.heap.heap
  have HH := BB.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K := BB.chunkK hX; open_fields K
  have rG := globRgn C.H
  have rX : Rgn (vsaFoot C.H) (X + 16) 16 := ⟨fun k hk => B.foot_chunk (by omega) (by omega)⟩
  have hbA : binblocksAddr = 2147593496 := rfl
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbb' : read64 Mt binblocksAddr = some bb := by
    rw [B.read (rG.word (by omega) (by omega)) (by omega)]; exact hbb
  have hbblt := B.heap.bb_lt bb hbb
  have hjn : S / 8 < numBins := by unfold numBins; omega
  have hgj := binAt_geo (S / 8) hjn
  obtain ⟨first, hof⟩ : ∃ f, (bins (S / 8) ++ [binAt (S / 8)]).head? = some f := by
    rcases h : bins (S / 8) with _ | ⟨x, xs⟩ <;> simp
  have hfdJ' : read64 Mt (binAt (S / 8) + 16) = some first := by
    rw [B.read (rG.word (by omega) (by omega)) (by omega)]
    exact ring_fd_head (binList_iff_ring.1 (HH.bins_list (S / 8) (by omega) hjn)).1 hof
  have hoflt := Vsa.Sim.read64_lt _ _ _ hfdJ'
  have hofm : first = binAt (S / 8) ∨ first ∈ bins (S / 8) := by
    have := List.mem_of_mem_head? hof
    rcases List.mem_append.mp this with hm | hm
    · exact .inr hm
    · exact .inl (by simpa using hm)
  have Nf := BB.nodeK (by omega) hjn hofm; open_fields Nf
  have hj8 : (R 15 >>> 3).toNat = S / 8 := by
    rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
  have hA3 : 2147593488#64 + BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 15 >>> 3 <<< 1 + 2#64)) <<< 3
      = BitVec.ofNat 64 (binAt (S / 8) + 16) := BitVec.eq_of_toNat_eq (by
    rw [binfd_toNat hj8 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  rw [← upd_self_eq h17]
  rgn_step O.live at 0x80007408
  sx_norm
  rw [hA3]; simp (disch := decide) only [ldv_at hbb']
  rgn_step O.live at 0x8000740c
  rgn_ld [hfdJ']
  rgn_step O.live at 0x80007434
  sx_norm
  rw [show (R 14 + 16#64).toNat = X + 16 by rgn_arith, show (R 14 + 24#64).toNat = X + 24 by rgn_arith,
    show (BitVec.ofNat 64 (binAt (S / 8) + 16)).toNat = binAt (S / 8) + 16 by rgn_arith,
    show (BitVec.ofNat 64 first + 24#64).toNat = first + 24 by rgn_arith]
  have hq := sraiw2_toNat hj8 (by omega)
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have oX := rX.offStack B.disj (by decide); have oG := rG.offStack B.disj (by decide)
  have oF := Nf_links.offStack B.disj (by decide); unfold mHead at oX oG oF
  refine (fun D : FDone C _ => free_epi O ((((((F.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)).of_regs ?_ ?_ ?_ ?_) D.heap D.pres D.frame)
    (fb_small_heap B hS rfl hof hbb (by rgn_arith) (by rgn_arith) (by
      rw [BitVec.toNat_or, shl_one hq (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.or_comm]) h14) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]

end VsaIris.VsaHeap

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem fl_link {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mb M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    {j pred succ bb' : Nat} {pre' post' : List Nat}
    (F : FFrame C R Mb) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (hj0 : 1 < j) (hj : j < numBins) (hidx : binIndex S = j)
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hbbr : read64 Mb binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : bb' / 2 ^ (j / 4) % 2 = 1)
    (hbbkeep : ∀ bb, read64 M2 binblocksAddr = some bb →
      ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (hMb : ∀ w, ¬ (binblocksAddr ≤ w ∧ w < binblocksAddr + 8) → Mb[w]? = Mt[w]?)
    (hMbp : ∀ a, vsaFoot C.H a → (Mb[a]?).isSome)
    (hMbf : ∀ a, ¬ MWin C.H C.s a → Mb[a]? = C.Mt0[a]?)
    (h11 : (R 11).toNat = pred) (h13 : (R 13).toNat = succ) (h14 : (R 14).toNat = X) :
    AW C.live C.S C.Q 0x800074e4#64 R Mb := by
  have BB := B.heap.heap
  have HH := BB.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K := BB.chunkK hX
  have hgj := binAt_geo j hj
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
  have Np := BB.nodeK (by omega) hj hpm; have Ns := BB.nodeK (by omega) hj hsm
  open_fields K; open_fields Np; open_fields Ns
  have hXJ : ∀ y, (y = binAt j ∨ y ∈ bins j) → y ≠ X := by
    rintro y (rfl | hy) he
    · unfold binAt avAddr at hgj he; omega
    · obtain ⟨c, hc, hca, hf⟩ := HH.member (by omega) hj hy
      have := HH.chunk_eq hc hX (hca.trans he)
      rw [this] at hf; cases hf
  have hpX := hXJ pred hpm; have hsX := hXJ succ hsm
  have hbp := Np.bnd _ K.next 16 (by omega) (by omega)
  have hbs := Ns.bnd _ K.next 16 (by omega) (by omega)
  have rX : Rgn (vsaFoot C.H) (X + 16) 16 := ⟨fun k hk => B.foot_chunk (by omega) (by omega)⟩
  have St := O.stackRgn
  have hlo := O.sp.lo; have hhi := O.sp.hi; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 32 := by rw [F.sp]; sx_addr
  have oX := rX.offStack B.disj (by decide); have oP := Np_links.offStack B.disj (by decide)
  have oS := Ns_links.offStack B.disj (by decide); unfold mHead at oX oP oS
  simp only at hbp hbs
  rgn_run O.live at 0x800074f8
  rgn_ld [F.s0, F.ra]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rgn_run O.live at 0
  · sx_norm; exact O.ral
  rw [show (R 14 + 24#64).toNat = X + 24 by rgn_arith, show (R 14 + 16#64).toNat = X + 16 by rgn_arith,
    show (R 11 + 16#64).toNat = pred + 16 by rgn_arith, show (R 13 + 24#64).toNat = succ + 24 by rgn_arith]
  have hW : WinAgree (fun a => (X + 16 ≤ a ∧ a < X + 32) ∨ (pred + 16 ≤ a ∧ a < pred + 24) ∨
      (succ + 24 ≤ a ∧ a < succ + 32)) (writeLog (writeLog (writeLog (writeLog Mb [(X + 24, 8, R 11)])
      [(X + 16, 8, R 13)]) [(pred + 16, 8, R 14)]) [(succ + 24, 8, R 14)]) Mb := by wl_win <;> omega
  have hbA : binblocksAddr = 0x8001ad18 := rfl
  have D := fb_release B.toFBinCore (by omega) hj (fun _ => hidx) (fun h => absurd h (by omega))
    hpos hpred hsucc (by unfold fdOf; rd_log [h13]) (by unfold bkOf; rd_log [h11])
    (by unfold fdOf; rd_log [h14]) (by unfold bkOf; rd_log [h14]) (by rw [hbA]; rd_log [← hbA, hbbr])
    hbblt (fun _ => hbbset) hbbkeep
    (fun w hw hna => (hW w (by unfold RelW at hna; omega)).trans
      (hMb w fun h => hna (.inr (.inr (.inr (.inl h))))))
    (fun w h1 h2 => (hW w (by omega)).trans (hMb w (by unfold binblocksAddr avAddr; omega)))
    (pres_log _ (pres_log _ (pres_log _ (pres_log _ hMbp))))
    (by simp only [writeLog_nest, List.cons_append, List.nil_append]; exact frame_log (by log_in) hMbf)
  refine O.ok _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, D.heap, D.pres, D.frame⟩ <;> carry_close [F.sp, F.s1, F.s2, F.s3]

end VsaIris.VsaHeap
