import VsaIris.Vsa.FreeBin
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.Carry

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure FreeL (C : MCtx) (R : Nat → BitVec 64) (Mt M2 : Mem) (X S top brkv : Nat)
    (cs₁ cs₂ : List Chunk) (bins : Nat → List Nat) (j : Nat) : Prop where
  frame : FFrame C R Mt
  bin : FBin C Mt M2 X S top brkv cs₁ cs₂ bins
  large : 511 < S
  idx : binIndex S = j
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = X
  a5 : (R 15).toNat = S

theorem FreeL.upd {C : MCtx} {R : Nat → BitVec 64} {Mt M2 : Mem} {X S top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j) {R' : Nat → BitVec 64}
    (h : ∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 13 → R' x = R x) :
    FreeL C R' Mt M2 X S top brkv cs₁ cs₂ bins j where
  frame := L.frame.of_regs (keep4 h 2) (keep4 h 9) (keep4 h 18) (keep4 h 19)
  bin := L.bin
  large := L.large
  idx := L.idx
  a7 := (keep4 h 17).trans L.a7
  a4 := by rw [keep4 h 14]; exact L.a4
  a5 := by rw [keep4 h 15]; exact L.a5

theorem FreeL.j_range {C : MCtx} {R : Nat → BitVec 64} {Mt M2 : Mem} {X S top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j) : 1 < j ∧ j < numBins := by
  have := binIndex_large (sz := S) (by have := L.large; omega)
  rw [L.idx] at this; unfold numBins; omega

structure FMember (C : MCtx) (Mt M2 : Mem) (top : Nat) (chunks : List Chunk) (x : Nat)
    (cx : Chunk) : Prop where
  mem : cx ∈ chunks
  addr : cx.addr = x
  free : cx.inuse = false
  al : x % 16 = 0
  lo : 0x8001c170 ≤ x
  hi : x + cx.size ≤ top
  min : 32 ≤ cx.size
  foot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (x + o)
  read : ∀ o, 8 ≤ o → o < 32 → o % 8 = 0 → read64 Mt (x + o) = read64 M2 (x + o)

theorem FBin.member {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {j x : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hx : x ∈ bins j) :
    ∃ cx, FMember C Mt M2 top (cs₁ ++ ⟨X, S, true⟩ :: cs₂) x cx := by
  have BB := B.heap.heap
  have HH := BB.heap
  obtain ⟨cx, hcx, rfl, hf⟩ := HH.member hj0 hj hx
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have Kc := BB.chunkK hcx; have KX := BB.chunkK hX
  have hfoot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (cx.addr + o) := fun o h1 h2 =>
    if ho : o < 16 then Kc.hdr.mem (by omega) (by omega)
    else (BB.nodeK hj0 hj (.inr hx)).links.mem (by omega) (by omega)
  have hxn : cx.addr ≠ X + S := by
    intro he
    have hw := HH.walk
    obtain ⟨_, hnext⟩ := walk_next_of hw
    rcases hnext with ⟨h1, _⟩ | ⟨d, cs₃, h1, h2⟩
    · exact B.not_top (by simp only at h1; exact h1)
    · have hd : d ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by rw [h1]; simp
      have := HH.chunk_eq hcx hd (by rw [he, h2])
      have hdu := B.next d (by rw [h1]; rfl)
      rw [← this, hf] at hdu; cases hdu
  have hal := Kc.al; have hmin := Kc.sz32; have hXal := KX.al; have hS16 := KX.sz16
  simp only at hXal hS16
  refine ⟨cx, hcx, rfl, hf, hal, Kc.lo, Kc.hi, hmin, hfoot, fun o h1 h2 h3 => ?_⟩
  refine B.read (fun k hk => by
    have := hfoot (o + k) (by omega) (by omega)
    rwa [show cx.addr + (o + k) = cx.addr + o + k by omega] at this) ?_
  rcases HH.walk.chunk_sep cx hcx _ hX with he | h4 | h4
  · rw [he] at hf; cases hf
  · simp only at h4; omega
  · simp only at h4; omega

theorem FBin.node_read {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {j y : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hy : y = binAt j ∨ y ∈ bins j) {o : Nat}
    (ho : o = 16 ∨ o = 24) : read64 Mt (y + o) = read64 M2 (y + o) := by
  have hgj := binAt_geo j hj
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hlo := (B.heap.heap.chunkK hX).lo
  rcases hy with rfl | hy
  · exact B.read ((binRgn C.H hj).word (by omega) (by omega)) (.inl (by simp only at hlo; omega))
  · obtain ⟨cx, M⟩ := B.member hj0 hj hy
    rcases ho with rfl | rfl
    · exact M.read 16 (by omega) (by omega) (by omega)
    · exact M.read 24 (by omega) (by omega) (by omega)

theorem fl_exit {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j succ : Nat}
    {pre' post' : List Nat} (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j)
    (hne : bins j ≠ []) (hpos : bins j = pre' ++ post')
    (hsucc : (post' ++ [binAt j]).head? = some succ) (h13 : (R 13).toNat = succ) :
    AW C.live C.S C.Q 0x800074e0#64 R Mt := by
  have B := L.bin
  have BB := B.heap.heap
  have HH := BB.heap
  obtain ⟨hj0, hj⟩ := L.j_range
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre').getLast? = some p := ⟨_, List.getLast?_cons⟩
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  have Ns := BB.nodeK (by omega) hj hsm; open_fields Ns
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  have hbkS : bkOf M2 succ = some pred := by
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
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hbkS' : read64 Mt (succ + 24) = some pred := by
    rw [B.read (Ns_links.word (by omega) (by omega)) (by have := Ns.end_sep HH hX; omega)]
    exact hbkS
  have K := BB.chunkK hX; have K_lo := K.lo; have K_room := K.room; have K_brk := K.brk
  simp only at K_lo
  refine (step% st 0x800074e0) O.live (Ns_links.ldOK (by rgn_arith)) (O.rgn Ns_links (by rgn_arith)) ?_
  rgn_ld [hbkS']
  have hpl := Vsa.Sim.read64_lt _ _ _ hbkS'
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbA : binblocksAddr = 2147593496 := rfl
  have hbb' : read64 Mt binblocksAddr = some bb := by
    rw [B.read ((globRgn C.H).word (by omega) (by omega)) (by omega)]; exact hbb
  have L' := L.upd (R' := upd R 11 (BitVec.ofNat 64 pred)) (fun x h10 h11 h12 h13 => upd_other _ _ h11)
  exact fl_link O L'.frame B hj0 hj L.idx hpos hpred hsucc hbb' (B.heap.bb_lt bb hbb)
    (HH.binblocks bb hbb j hj0 hj hne) (fun bb0 hbb0 k h => by rw [hbb] at hbb0; cases hbb0; exact h)
    (fun _ _ => rfl) B.pres B.frame
    (by carry_close) (by carry_close) L'.a4

theorem fl_cmp {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j x : Nat}
    {pre rest : List Nat} (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j)
    (hmem : bins j = pre ++ x :: rest) (h13 : (R 13).toNat = x)
    (hpass : ∀ R', FreeL C R' Mt M2 X S top brkv cs₁ cs₂ bins j → (R' 13).toNat = x →
      R' 11 = R 11 → AW C.live C.S C.Q 0x800074cc#64 R' Mt) :
    AW C.live C.S C.Q 0x800074d4#64 R Mt := by
  obtain ⟨hj0, hj⟩ := L.j_range
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨cx, M⟩ := L.bin.member (by omega) hj hx
  obtain rfl := M.addr
  have K := L.bin.heap.heap.chunkK M.mem; have K_hi := K.hi; have K_room := K.room; have K_brk := K.brk
  obtain ⟨h, hr, -⟩ := K.hdrv
  have hr' : read64 Mt (cx.addr + 8) = some h := by
    rw [M.read 8 (by omega) (by omega) (by omega)]; exact hr
  refine (step% st 0x800074d4) O.live (K.hdr.ldOK (by rgn_arith)) (O.rgn K.hdr (by rgn_arith)) ?_
  rgn_ld [hr']
  refine (step% st 0x800074d8) O.live ?_
  have L' := L.upd (R' := upd (upd R 12 (BitVec.ofNat 64 h)) 12
    (BitVec.ofNat 64 h &&& sign_extend (m := 64) (0xffc#12)))
    (fun y h10 h11 h12 h13 => by simp only [upd_apply, h12, ite_false])
  refine (step% st 0x800074dc) O.live (fun hlt => ?_) (fun hge => ?_)
  · exact hpass _ L' (by carry_close [h13]) (by carry_close)
  · exact fl_exit O L' (by rw [hmem]; simp) (pre' := pre) (post' := cx.addr :: rest) hmem rfl (by carry_close [h13])

theorem fl_adv {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j x : Nat}
    {pre rest : List Nat} (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j)
    (hmem : bins j = pre ++ x :: rest) (h13 : (R 13).toNat = x) (h11 : (R 11).toNat = binAt j)
    (hloop : ∀ y rest', rest = y :: rest' → ∀ R', FreeL C R' Mt M2 X S top brkv cs₁ cs₂ bins j →
      (R' 13).toNat = y → (R' 11).toNat = binAt j → AW C.live C.S C.Q 0x800074d4#64 R' Mt) :
    AW C.live C.S C.Q 0x800074cc#64 R Mt := by
  obtain ⟨hj0, hj⟩ := L.j_range
  have HH := L.bin.heap.heap.heap
  have hgj := binAt_geo j hj
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨cx, M⟩ := L.bin.member (by omega) hj hx
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapEnd at hbrk
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨nx, hnx⟩ : ∃ q, (rest ++ [binAt j]).head? = some q := by
    rcases rest with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hnx).1
  have hfd' : read64 Mt (x + 16) = some nx := by
    rw [M.read 16 (by omega) (by omega) (by omega)]; exact hfd
  have hnxlt := Vsa.Sim.read64_lt _ _ _ hfd'
  have N := L.bin.heap.heap.nodeK (by omega) hj (.inr hx); open_fields N
  refine (step% st 0x800074cc) O.live (N_links.ldOK (by rgn_arith)) (O.rgn N_links (by rgn_arith)) ?_
  rgn_ld [hfd']
  have L' := L.upd (R' := upd R 13 (BitVec.ofNat 64 nx)) (fun y h10 h11 h12 h13 => upd_other _ _ h13)
  rcases rest with _ | ⟨y, rest'⟩
  · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    refine (step% st 0x800074d0) O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
    · exact fl_exit O L' (by rw [hmem]; simp) (pre' := pre ++ [x]) (post' := []) (by rw [hmem]; simp) rfl
        (by carry_close)
    · exact BitVec.eq_of_toNat_eq (by carry_close [h11])
  · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    have hym : y ∈ bins j := by rw [hmem]; simp
    obtain ⟨cy, My⟩ := L.bin.member (by omega) hj hym
    have hylo := My.lo
    refine (step% st 0x800074d0) O.live (fun hc => absurd hc ?_) (fun _ => ?_)
    · intro he
      have := congrArg BitVec.toNat he
      carry_norm [h11] at this
      unfold binAt avAddr at this hgj; omega
    · exact hloop y rest' rfl _ L' (by carry_close) (by carry_close [h11])

theorem fl_walk {C : MCtx} (O : FOK C) {Mt M2 : Mem} {X S top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat} :
    ∀ (rest pre : List Nat) (x : Nat) (R : Nat → BitVec 64),
      FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j → bins j = pre ++ x :: rest →
      (R 13).toNat = x → (R 11).toNat = binAt j → AW C.live C.S C.Q 0x800074d4#64 R Mt := by
  intro rest
  induction rest with
  | nil =>
    intro pre x R L hmem h13 h11
    refine fl_cmp O L hmem h13 fun R' L' h13' h11' =>
      fl_adv O L' hmem h13' (h11'.symm ▸ h11) fun y rest' he => nomatch he
  | cons y rest ih =>
    intro pre x R L hmem h13 h11
    refine fl_cmp O L hmem h13 fun R' L' h13' h11' =>
      fl_adv O L' hmem h13' (h11'.symm ▸ h11) fun y' rest' he R'' L'' h13'' h11'' => ?_
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ih (pre ++ [x]) y R'' L'' (by rw [hmem]; simp) h13'' h11''

theorem fl_empty {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j) (hemp : bins j = [])
    (h12 : (R 12).toNat = j) (h11 : (R 11).toNat = binAt j) (h13 : (R 13).toNat = binAt j) :
    AW C.live C.S C.Q 0x800075ec#64 R Mt := by
  have B := L.bin
  have HH := B.heap.heap.heap
  obtain ⟨hj0, hj⟩ := L.j_range
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K_lo := (B.heap.heap.chunkK hX).lo; simp only at K_lo
  have rG := globRgn C.H
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbbl := B.heap.bb_lt bb hbb
  have hbA : binblocksAddr = 2147593496 := rfl
  have hbb' : read64 Mt 2147593496 = some bb := by
    rw [← hbA, B.read (rG.word (by omega) (by omega)) (by omega)]; exact hbb
  rw [← upd_self_eq L.a7]
  rgn_step O.live at 0x800074e4
  sx_norm
  simp (disch := decide) only [ldv_at hbb']
  have hbbv : (BitVec.ofNat 64 bb).toNat = bb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hq := sraiw2_toNat h12 (by unfold numBins at hj; omega)
  have hbit := shl_one hq (by unfold numBins at hj; omega)
  have hor : (1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
      (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 12)) 2#5))).toNat |||
      BitVec.ofNat 64 bb).toNat = bb ||| 2 ^ (j / 4) := by
    rw [BitVec.toNat_or, hbbv, hbit, Nat.or_comm]
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hoB := rG.offStack B.disj (by decide); unfold mHead at hoB
  refine fl_link O ((L.frame.store (by omega)).of_regs ?_ ?_ ?_ ?_) B hj0 hj L.idx
    (pre' := []) (post' := []) (by rw [hemp]; rfl) rfl rfl (by rw [hbA, read64_store_hit, hor])
    (lor_lt bb _ hbbl (by unfold numBins at hj; omega))
    (lor_bit_set bb _) (fun bb0 hbb0 k hk => by rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk)
    (fun w hw => by rw [writeLog_out]; simp only [OutL, and_true]; unfold binblocksAddr avAddr at hw; omega)
    (pres_log _ B.pres) (frame_log (by log_in) B.frame) ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h11, h13, L.a4, List.getLast_singleton]

structure FIdx (S : Nat) (R R' : Nat → BitVec 64) : Prop where
  a1 : (R' 11).toNat = 16 * binIndex S + 16
  a2 : (R' 12).toNat = binIndex S
  keep : ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → R' x = R x

theorem fl_idx {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {S : Nat}
    (h15 : (R 15).toNat = S) (hlo : 512 ≤ S) (hhi : S < 2 ^ 31)
    (hk : ∀ R', FIdx S R R' → AW C.live C.S C.Q 0x800074b8#64 R' Mt) :
    AW C.live C.S C.Q 0x80007498#64 R Mt := by
  have hbi := binIndex_large hlo
  refine (step% st 0x80007498) O.live ?_
  refine (step% st 0x8000749c) O.live ?_
  sx_norm
  have hx : (R 15 >>> 9).toNat = S / 512 := by
    rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
  refine (step% st 0x800074a0) O.live (fun h4 => ?_) (fun h4 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h4
  rotate_left
  ·
    have h4' : S / 512 ≤ 4 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 6).toNat = S / 64 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 56 + S / 64 := by
      unfold binIndex; rw [if_neg (by omega), if_pos h4']
    refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
  have h4' : 4 < S / 512 := by sx_norm; omega
  refine (step% st 0x80007584) O.live ?_
  refine (step% st 0x80007588) O.live (fun h20 => ?_) (fun h20 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h20
  ·
    have h20' : S / 512 ≤ 20 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hb : binIndex S = 91 + S / 512 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_pos h20']
    refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hx (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hx]; omega), hx, hb]; omega
  have h20' : 20 < S / 512 := by sx_norm; omega
  refine (step% st 0x8000758c) O.live ?_
  refine (step% st 0x80007590) O.live (fun h84 => ?_) (fun h84 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h84
  rotate_left
  ·
    have h84' : S / 512 ≤ 84 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 12).toNat = S / 4096 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 110 + S / 4096 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h84']
    refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
  have h84' : 84 < S / 512 := by sx_norm; omega
  refine (step% st 0x80007608) O.live ?_
  refine (step% st 0x8000760c) O.live (fun h340 => ?_) (fun h340 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h340
  rotate_left
  ·
    have h340' : S / 512 ≤ 340 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 15).toNat = S / 32768 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 119 + S / 32768 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h340']
    refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
  have h340' : 340 < S / 512 := by sx_norm; omega
  refine (step% st 0x80007628) O.live ?_
  refine (step% st 0x8000762c) O.live (fun h1364 => ?_) (fun h1364 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h1364
  rotate_left
  ·
    have h1364' : S / 512 ≤ 1364 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 18).toNat = S / 262144 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 124 + S / 262144 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h1364']
    refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega

  have h1364' : 1364 < S / 512 := by sx_norm; omega
  sx_run [8] O.live at 0x800074b8
  have hb : binIndex S = 126 := by
    unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  refine hk _ ⟨?_, ?_, by carry_close⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hb]; rfl
  · rw [hb]; rfl

theorem fl_head {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j)
    (h11 : (R 11).toNat = 16 * j + 16) (h12 : (R 12).toNat = j) :
    AW C.live C.S C.Q 0x800074b8#64 R Mt := by
  have B := L.bin
  have HH := B.heap.heap.heap
  obtain ⟨hj0, hj⟩ := L.j_range
  have hgj := binAt_geo j hj
  have hringJ := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  have hneJ := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).2
  obtain ⟨first, hof⟩ : ∃ f, (bins j ++ [binAt j]).head? = some f := by
    rcases h : bins j with _ | ⟨x, xs⟩ <;> simp
  have hfdJ := ring_fd_head hringJ hof
  have hfdJ' : read64 Mt (binAt j + 16) = some first := by
    rw [B.node_read (by omega) hj (.inl rfl) (.inl rfl)]; exact hfdJ
  have hoflt := Vsa.Sim.read64_lt _ _ _ hfdJ
  have ha7 : (R 17).toNat = 2147593488 := by rw [L.a7]; rfl
  have hbj : binAt j = 2147593488 + 16 * j := rfl
  have rB := binRgn C.H hj
  rgn_step O.live at 0x800074c4
  rgn_ld [hfdJ']
  sx_norm
  have hA1 : (R 17 + R 11 + 18446744073709551600#64).toNat = binAt j := by rgn_arith
  have L' := L.upd (R' := upd (upd (upd R 11 (R 17 + R 11)) 13 (BitVec.ofNat 64 first)) 11
    (R 17 + R 11 + 18446744073709551600#64)) (fun x h10 h11 h12 h13 => by carry_close)
  refine (step% st 0x800074c4) O.live (fun hne => ?_) (fun he => ?_)
  ·
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    rcases hbj : bins j with _ | ⟨x, rest⟩
    · rw [hbj] at hof; simp at hof; subst hof
      exact absurd (BitVec.eq_of_toNat_eq (by carry_close [hA1])) hne
    · rw [hbj] at hof; simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hof
      subst hof
      exact fl_walk O rest [] x _ L' (by rw [hbj]; rfl) (by carry_close) (by carry_close [hA1])
  ·
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq, Decidable.not_not] at he
    have hfb : first = binAt j := by
      have := congrArg BitVec.toNat he
      rw [hA1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt] at this; exact this.symm
    have hemp : bins j = [] := by
      rcases hbj : bins j with _ | ⟨x, rest⟩
      · rfl
      · exfalso
        rw [hbj] at hof; simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hof
        exact hneJ x (by rw [hbj]; exact List.mem_cons_self) (hof.trans hfb)
    refine (step% st 0x800074c8) O.live ?_
    exact fl_empty O L' hemp (by carry_close [h12]) (by carry_close [hA1]) (by carry_close [hfb])

theorem free_bin {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x800073e8#64 R Mt := by
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K := B.heap.heap.chunkK hX
  have hlo := K.lo; have hhi := K.hi; have hrm := K.room; have hbk := K.brk
  simp only at hlo hhi
  refine (step% st 0x800073e8) O.live ?_
  refine (step% st 0x800073ec) O.live (fun hl => ?_) (fun hs => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hl
    have hl' : 511 < S := by first | omega | (sx_norm; done) | (sx_norm; omega)
    exact fl_idx O (S := S) h15 (by omega) (by omega) fun R' I => fl_head O
      (FreeL.upd (R := upd R 13 _) ⟨F.of_regs rfl rfl rfl rfl, B, hl', rfl, h17, h14, h15⟩ fun x _ => I.keep x) I.a1 I.a2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hs
    exact fb_small O (F.of_regs rfl rfl rfl rfl) B (by first | omega | (sx_norm; done) | (sx_norm; omega)) h17 h14 h15

theorem free_bin2 {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x80007490#64 R Mt := by
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have K := B.heap.heap.chunkK hX
  have hlo := K.lo; have hhi := K.hi; have hrm := K.room; have hbk := K.brk
  simp only at hlo hhi
  refine (step% st 0x80007490) O.live ?_
  refine (step% st 0x80007494) O.live (fun hs => ?_) (fun hl => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hs
    exact fb_small O (F.of_regs rfl rfl rfl rfl) B (by first | omega | (sx_norm; done) | (sx_norm; omega)) h17 h14 h15
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hl
    have hl' : 511 < S := by first | omega | (sx_norm; done) | (sx_norm; omega)
    exact fl_idx O (S := S) h15 (by omega) (by omega) fun R' I => fl_head O
      (FreeL.upd (R := upd R 13 _) ⟨F.of_regs rfl rfl rfl rfl, B, hl', rfl, h17, h14, h15⟩ fun x _ => I.keep x) I.a1 I.a2

end VsaIris.VsaHeap
