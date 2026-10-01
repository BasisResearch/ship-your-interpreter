import VsaIris.Vsa.MallocRebinL
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.MallocGlue
import VsaIris.Vsa.Carry

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem slliw1_toNat {y : BitVec 64} (h : 2 * y.toNat < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 y <<< 1)).toNat = 2 * y.toNat := by
  have he : (BitVec.extractLsb 31 0 y).toNat = y.toNat := by
    rw [BitVec.extractLsb_toNat]; simp; omega
  have hs : (BitVec.extractLsb 31 0 y <<< 1).toNat = 2 * y.toNat := by
    rw [BitVec.toNat_shiftLeft, he, Nat.shiftLeft_eq]; simp; omega
  have hm : (BitVec.extractLsb 31 0 y <<< 1).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hs]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, hs]
  omega

structure LScanIdx (nb : Nat) (R R' : Nat → BitVec 64) : Prop where
  a0 : (R' 10).toNat = 16 * (binIndex nb + 1)
  a7 : (R' 17).toNat = binIndex nb + 1
  t3 : (R' 28).toNat = binIndex nb
  keep : ∀ x, x ≠ 10 → x ≠ 13 → x ≠ 15 → x ≠ 17 → x ≠ 28 → R' x = R x

theorem lscan_idx {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {nb : Nat}
    (h14 : (R 14).toNat = nb) (hnb16 : nb % 16 = 0) (hlo : 503 < nb) (hhi : nb < 2 ^ 31)
    (hk : ∀ R', LScanIdx nb R R' → AW C.live C.S C.Q 0x800048a8#64 R' Mt) :
    AW C.live C.S C.Q 0x80004884#64 R Mt := by
  have hbi := binIndex_large (sz := nb) (by omega)
  refine (step% st 0x80004884) O.live ?_
  sx_norm
  have hx : (R 14 >>> 9).toNat = nb / 512 := by
    rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
  refine (step% st 0x80004888) O.live (fun h0 => absurd h0 ?_) (fun _ => ?_)
  · simp only [upd_apply, ite_true]
    intro he; have := congrArg BitVec.toNat he; rw [hx] at this; simp at this; omega
  refine (step% st 0x8000488c) O.live ?_
  refine (step% st 0x80004890) O.live (fun h4 => ?_) (fun h4 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h4
  ·
    have h4' : 4 < nb / 512 := by sx_norm; omega
    refine (step% st 0x80004cd4) O.live ?_
    refine (step% st 0x80004cd8) O.live (fun h20 => ?_) (fun h20 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h20
    ·
      have h20' : nb / 512 ≤ 20 := by sx_norm; omega
      have hy := hx
      sx_run [8] O.live at 0x800048a8
      have hb : binIndex nb = 91 + nb / 512 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, h20', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 9) (k := 92) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_norm
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    have h20' : 20 < nb / 512 := by sx_norm; omega
    refine (step% st 0x80004cdc) O.live ?_
    refine (step% st 0x80004ce0) O.live (fun h84 => ?_) (fun h84 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h84
    rotate_left
    ·
      have h84' : nb / 512 ≤ 84 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 12).toNat = nb / 4096 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 110 + nb / 4096 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, h84', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 12) (k := 111) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_norm
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    have h84' : 84 < nb / 512 := by sx_norm; omega
    refine (step% st 0x80004f3c) O.live ?_
    refine (step% st 0x80004f40) O.live (fun h340 => ?_) (fun h340 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h340
    rotate_left
    ·
      have h340' : nb / 512 ≤ 340 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 15).toNat = nb / 32768 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 119 + nb / 32768 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega, h340', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 15) (k := 120) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_norm
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    have h340' : 340 < nb / 512 := by sx_norm; omega
    refine (step% st 0x80004fc0) O.live ?_
    refine (step% st 0x80004fc4) O.live (fun h1364 => ?_) (fun h1364 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h1364
    rotate_left
    ·
      have h1364' : nb / 512 ≤ 1364 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 18).toNat = nb / 262144 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 124 + nb / 262144 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega, show ¬ nb / 512 ≤ 340 by omega, h1364', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 18) (k := 125) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_norm
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega

    have h1364' : 1364 < nb / 512 := by sx_norm; omega
    sx_run [8] O.live at 0x800048a8
    have hb : binIndex nb = 126 := by
      unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega,
        show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega,
        show ¬ nb / 512 ≤ 340 by omega, show ¬ nb / 512 ≤ 1364 by omega, if_false]
    refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_close [hb]
  ·
    have h4' : nb / 512 ≤ 4 := by sx_norm; omega
    sx_run [8] O.live at 0x800048a8
    have hy : (R 14 >>> 6).toNat = nb / 64 := by
      rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
    have hb : binIndex nb = 56 + nb / 64 := by
      unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, h4', if_false, if_true]
    have h7 := sx32_add_toNat (x := R 14 >>> 6) (k := 57) (by rw [hy]; omega)
    rw [hy] at h7
    refine hk _ ⟨?_, ?_, ?_, by carry_close⟩ <;> carry_norm
    · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
    · rw [h7, hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega

structure LScan (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb j : Nat) (R : Nat → BitVec 64) : Prop where
  frame : MFrame C R Mt
  heap : MHeap C Mt brkv chunks bins
  nbok : NbOK C.n nb
  large : 503 < nb
  nb31 : nb < 2 ^ 31
  bin_idx : binIndex nb = j
  a4 : (R 14).toNat = nb
  a6 : R 16 = 0x8001ad10#64
  a7 : (R 17).toNat = j + 1
  t3 : (R 28).toNat = j
  a0 : (R 10).toNat = binAt j
  t1 : (R 6).toNat = 31
  s0 : R 8 = reentV

theorem LScan.upd {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {nb j : Nat} {R R' : Nat → BitVec 64} (L : LScan C Mt brkv chunks bins nb j R)
    (h : ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 15 → R' x = R x) : LScan C Mt brkv chunks bins nb j R' where
  frame := L.frame.of_regs (keep4 h 2) (keep4 h 9) (keep4 h 18) (keep4 h 19)
  heap := L.heap
  nbok := L.nbok
  large := L.large
  nb31 := L.nb31
  bin_idx := L.bin_idx
  a4 := by rw [keep4 h 14]; exact L.a4
  a6 := by rw [keep4 h 16]; exact L.a6
  a7 := by rw [keep4 h 17]; exact L.a7
  t3 := by rw [keep4 h 28]; exact L.t3
  a0 := by rw [keep4 h 10]; exact L.a0
  t1 := by rw [keep4 h 6]; exact L.t1
  s0 := by rw [keep4 h 8]; exact L.s0

abbrev LScanLR (C : MCtx) (Mt : Mem) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb : Nat) : Prop :=
  ∀ R' idx, idx < numBins → 1 < idx → ScanFrom chunks bins nb idx → MFrame C R' Mt →
    LRRegs nb idx R' → R' 8 = reentV →
    AW C.live C.S C.Q 0x800048ec#64 R' Mt

abbrev LScanTake (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb j : Nat) : Prop :=
  ∀ R' pre post x sz pred, LScan C Mt brkv chunks bins nb j R' → bins j = pre ++ x :: post →
    FreeAt chunks x sz → nb ≤ sz → sz < nb + 32 → (binAt j :: pre).getLast? = some pred →
    (R' 15).toNat = x → (R' 11).toNat = pred → (R' 13).toNat = sz →
    AW C.live C.S C.Q 0x80004c20#64 R' Mt

theorem toInt_small {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 63) :
    x.toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, h, if_pos (by omega)]

theorem lscan_step {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb j x : Nat} {pre post : List Nat}
    (L : LScan C Mt brkv chunks bins nb j R) (hj : j < numBins) (hmem : bins j = pre ++ x :: post)
    (h15 : (R 15).toNat = x) (hlr : LScanLR C Mt chunks bins nb) (htake : LScanTake C Mt brkv chunks bins nb j)
    (hprev : ∀ pre' y, pre = pre' ++ [y] → ∀ R', LScan C Mt brkv chunks bins nb j R' →
      (R' 15).toNat = y → AW C.live C.S C.Q 0x800048d8#64 R' Mt) :
    AW C.live C.S C.Q 0x800048d8#64 R Mt := by
  have HH := L.heap.heap.heap.heap
  have hnb16 := L.nbok.al
  have hbi := binIndex_large (sz := nb) (by have := L.large; omega)
  have hj0 : 1 < j := by rw [← L.bin_idx]; omega
  have hj126 : j ≤ 126 := by rw [← L.bin_idx]; exact hbi.2
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨⟨cxa, sz, cxi⟩, hcx, hxa, hxf⟩ := HH.member (by omega) hj hx
  simp only at hxa hxf
  subst hxa hxf
  have K := L.heap.heap.heap.chunkK hcx; have FS := L.heap.heap.heap.freeSpan hcx rfl
  open_fields K; simp only at FS
  obtain ⟨h, hr, hs, _⟩ := K_hdrv
  have hhlt := Vsa.Sim.read64_lt _ _ _ hr
  rgn_run O.live at 0x800048dc
  rgn_ld [hr]
  rgn_run O.live at 0x800048e4
  have hszv : (BitVec.ofNat 64 h &&& 18446744073709551612#64).toNat = sz := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt, ← hs]; rfl
  have hsz62 : sz < 2 ^ 62 := by omega
  have hcmp := lr_cmp hszv L.a4 hsz62 (by have := L.nb31; omega)
  have h31 : (R 6).toInt = (31 : Int) := toInt_small L.t1 (by decide)
  have h31' : ((31#64 : BitVec 64)).toInt = (31 : Int) := by decide

  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨nx, hnx⟩ : ∃ q, (post ++ [binAt j]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hbk := (ring_member hring hpred hnx).2
  have hplt := Vsa.Sim.read64_lt _ _ _ hbk
  refine (step% st 0x800048e4) O.live (fun hle => ?_) (fun hgt => ?_)
  ·
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h31] at hle
    have hlt32 : sz < nb + 32 := by
      have := hcmp.1; rw [h31'] at this; omega
    rgn_run O.live at 0x800048cc
    rgn_ld [hbk]
    have L' := L.upd (R' := upd (upd (upd (upd R 13 (BitVec.ofNat 64 h)) 13
      (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 12
      ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14)) 11 (BitVec.ofNat 64 pred))
      (fun y h11 h12 h13 h15 => by simp only [upd_apply, h11, h12, h13, ite_false])
    refine (step% st 0x800048cc) O.live (fun hge => ?_) (fun hneg => ?_)
    ·
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hge
      have hle' : nb ≤ sz := hcmp.2.1 hge
      refine htake _ pre post cxa sz pred L' hmem hcx hle' hlt32 hpred ?_ ?_ ?_ <;> carry_close [h15, hszv]
    ·
      rcases List.eq_nil_or_concat pre with rfl | ⟨pre', y, rfl⟩
      · simp only [List.getLast?_singleton, Option.some.injEq] at hpred
        subst hpred
        refine (step% st 0x800048d0) O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
        · refine hlr _ (j + 1) (by unfold numBins; omega) (by omega)
            (.inl (by rw [L.bin_idx]; omega)) L'.frame ⟨L'.a4, L'.a7, L'.a6⟩ L'.s0
        · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          apply BitVec.eq_of_toNat_eq
          rw [L.a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]
      · have hy : pred = y := by
          have e : (binAt j :: pre'.concat y).getLast? = some y := by
            rw [List.concat_eq_append, ← List.cons_append, List.getLast?_concat]
          rw [e] at hpred; simpa using hpred.symm
        subst hy
        have hylo : binAt j ≠ pred := by
          have hym : pred ∈ bins j := by rw [hmem]; simp
          have := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).2 pred hym
          exact fun he => this he.symm
        refine (step% st 0x800048d0) O.live (fun hc => absurd hc ?_) (fun _ => ?_)
        · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          intro he; apply hylo
          have := congrArg BitVec.toNat he
          rw [L.a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt] at this
          exact this
        refine (step% st 0x800048d4) O.live ?_
        exact hprev pre' pred (by simp) _ (L'.upd (by carry_close)) (by carry_norm; sx_norm; carry_close)
  ·
    refine (step% st 0x800048e8) O.live ?_
    have hgt := hcmp.1.1 (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h31] at hgt
      rw [h31']; omega)
    refine hlr _ j hj hj0 (.inr ⟨cxa, sz, hx, hcx, by omega⟩)
      (L.frame.of_regs rfl rfl rfl rfl) ⟨?_, by carry_norm; sx_norm; exact L.t3, ?_⟩ ?_ <;>
      carry_close [L.a4, L.a6, L.s0]

theorem lscan_walk {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb j : Nat} (hj : j < numBins) (hlr : LScanLR C Mt chunks bins nb)
    (htake : LScanTake C Mt brkv chunks bins nb j) :
    ∀ (rpre : List Nat) (x : Nat) (post : List Nat) (R : Nat → BitVec 64),
      LScan C Mt brkv chunks bins nb j R → bins j = rpre.reverse ++ x :: post →
      (R 15).toNat = x → AW C.live C.S C.Q 0x800048d8#64 R Mt := by
  intro rpre
  induction rpre with
  | nil =>
    intro x post R L hmem h15
    exact lscan_step O L hj (pre := []) hmem h15 hlr htake fun pre' y he => by simp at he
  | cons y rpre ih =>
    intro x post R L hmem h15
    simp only [List.reverse_cons] at hmem
    refine lscan_step O L hj (pre := rpre.reverse ++ [y]) hmem h15 hlr htake
      fun pre' y' he R' L' h15' => ?_
    obtain ⟨rfl, hy⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, and_true] at hy
    subst hy
    exact ih y (x :: post) R' L' (by rw [hmem]; simp) h15'

theorem take_ret {C : MCtx} {Mt M : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb i v sz pred succ : Nat} {pre post : List Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hi0 : 0 < i) (hi : i < numBins)
    (hbin : bins i = pre ++ v :: post) (hfree : FreeAt chunks v sz) (hfit : nb ≤ sz)
    (hpred : (binAt i :: pre).getLast? = some pred) (hsucc : (post ++ [binAt i]).head? = some succ)
    (hfd : fdOf M pred = some succ) (hbk : bkOf M succ = some pred)
    (hhdr : ∀ hd, read64 Mt (v + sz + 8) = some hd → read64 M (v + sz + 8) = some (hd + 1))
    (hag : ∀ a, vsaFoot C.H a → ¬ TakeW pred succ (v + sz) a → M[a]? = Mt[a]?)
    (hpres : ∀ a, vsaFoot C.H a → (M[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → M[a]? = C.Mt0[a]?) :
    TakeRet C M v := by
  have HH := Hp.heap.heap.heap
  obtain ⟨_, ⟨hd, hdr, hdp⟩⟩ := HH.headers hfree
  simp only at hdr hdp
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hfree
  have NB := (hsp ▸ HH : HeapAt Mt C.H (fun e => e ∈ C.H) C.top0 brkv
    (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) bins).freeNbrs
  have hd4 : hd % 4 < 2 := by
    obtain ⟨d, cs₃, h1, h2⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = v + sz := by
      have hw := HH.walk; rw [hsp] at hw
      rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
      · exact absurd he NB.not_top
      · exact ⟨d, cs₃, h1, h2⟩
    obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d (by rw [hsp, h1]; simp)
    rw [h2, hdr] at hd0r; cases hd0r; exact hd0l
  have hn8 : C.n.toNat + 8 ≤ sz := by have := hnb.fits; omega
  have hheap := Hp.heap.take hi0 hi hbin hfree rfl (n := C.n.toNat) hn8 hpred hsucc hfd hbk
    (hhdr hd hdr) (fun hd' hd'r => by rw [hdr] at hd'r; cases hd'r; exact ⟨by unfold chunkSize; omega, by omega⟩)
    (by unfold prevInuse; rw [beq_iff_eq]; omega) hag
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) hn8
  exact ⟨hfr, hal16, ⟨_, _, _, _, hheap, by omega, Hp.live.map_reflag _⟩, hpres, hframe⟩


theorem lscan_fin {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem} {v : Nat}
    (F : MFrame C R M) (h15 : (R 15).toNat = v) (hv : v < 2 ^ 32)
    (T : TakeRet C (writeLog M [(C.s.toNat - 96 + 8, 8, R 15)]) v) :
    AW C.live C.S C.Q 0x80004c40#64 R M := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [F.sp]; sx_addr
  have St := O.stackRgn
  rgn_run O.live at 0x80004c60
  all_goals rgn_ld [F.ra, F.s0]; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact O.ral
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith]
  refine O.fin_take ?_ T _ ⟨rfl, ?_, rfl, F.s1, F.s2, F.s3⟩ (fun _ _ _ _ => rfl) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · sx_addr
  · apply BitVec.eq_of_toNat_eq; sx_addr

theorem lscan_ret {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb j x sz pred succ hd : Nat} {pre post : List Nat}
    (hsp : MSp C.s) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hj0 : 0 < j)
    (hj : j < numBins) (hmem : bins j = pre ++ x :: post) (hfree : FreeAt chunks x sz)
    (hle : nb ≤ sz) (hpred : (binAt j :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt j]).head? = some succ) (hdr : read64 Mt (x + sz + 8) = some hd)
    {w1 w2 w3 w4 : BitVec 64} (h1 : w1.toNat = pred) (h2 : w2.toNat = succ)
    (h3 : w3.toNat = hd + 1) :
    TakeRet C (writeLog (writeLog (writeLog (writeLog Mt [(succ + 24, 8, w1)])
      [(pred + 16, 8, w2)]) [(x + sz + 8, 8, w3)]) [(C.s.toNat - 96 + 8, 8, w4)]) x := by
  have K := Hp.heap.heap.chunkK hfree
  obtain ⟨Np, Ns⟩ := Hp.heap.heap.nbrK hj0 hj hmem hpred hsucc
  open_fields K; open_fields Np; open_fields Ns
  have hlo := hsp.lo
  have oN := K_nhdr.offStack Hp.disj (by decide); have oP := Np_links.offStack Hp.disj (by decide)
  have oS := Ns_links.offStack Hp.disj (by decide)
  have bS := Ns.bnd _ K_next 16 (by omega) (by omega)
  simp only [mHead, Vsa.Sim.tohostAddr] at hlo oN oP oS
  refine take_ret Hp hnb hj0 hj hmem hfree hle hpred hsucc ?_ ?_ (fun hd' hd'r => ?_)
    (fun a ha hna => ?_) ?_ ?_
  · show read64 _ (pred + 16) = _; rd_log [h2]
  · show read64 _ (succ + 24) = _; rd_log [h1]
  · rw [hdr] at hd'r; cases hd'r; rd_log [h3]
  · have := offStack_pt Hp.disj ha; unfold TakeW at hna
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  all_goals simp only [writeLog_nest, List.cons_append, List.nil_append]
  · exact pres_log _ Hp.pres
  · exact frame_log (by log_in) Hp.frame

theorem lscan_take {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb j : Nat} (hj : j < numBins) :
    LScanTake C Mt brkv chunks bins nb j := by
  intro R pre post x sz pred L hmem hfree hle hlt hpred h15 h11 h13
  have Hp := L.heap
  have HH := Hp.heap.heap.heap
  have hnb16 := L.nbok.al
  have hj0 : 1 < j := by
    have := binIndex_large (sz := nb) (by have := L.large; omega); rw [← L.bin_idx]; omega
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt j]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  have K := Hp.heap.heap.chunkK hfree; have FS := Hp.heap.heap.freeSpan hfree rfl
  obtain ⟨Np, Ns⟩ := Hp.heap.heap.nbrK (by omega) hj hmem hpred hsucc
  open_fields K; open_fields Np; open_fields Ns; simp only at FS
  obtain ⟨hd, hdr, hdp⟩ := K_nhdrv
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  have hlo := O.sp.lo; have hhi := O.sp.hi; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [L.frame.sp]; sx_addr
  rgn_run O.live at 0x80004c24
  rgn_ld [hfd]
  rgn_run O.live at 0x80004c2c
  rgn_ld [hdr]
  rgn_run O.live at 0x80004c40
  rw [show (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 by rgn_arith,
    show (R 11 + 16#64).toNat = pred + 16 by rgn_arith,
    show (R 15 + R 13 + 8#64).toNat = x + sz + 8 by rgn_arith]
  have oN := K_nhdr.offStack Hp.disj (by decide); have oP := Np_links.offStack Hp.disj (by decide)
  have oS := Ns_links.offStack Hp.disj (by decide); unfold mHead at oN oP oS
  exact lscan_fin O ((((L.frame.store (by omega)).store (by omega)).store (by omega)).of_regs
      rfl rfl rfl rfl) h15 (by omega)
    (lscan_ret O.sp Hp L.nbok (by omega) hj hmem hfree hle hpred hsucc hdr h11
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl])
      (or1_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]) hdev))

theorem lscan {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb)
    (h503 : 503 < nb) (hnb31 : nb < 2 ^ 31) (h14 : (R 14).toNat = nb) (h8 : R 8 = reentV)
    (hlr : LScanLR C Mt chunks bins nb) :
    AW C.live C.S C.Q 0x80004884#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have hnb16 := hnb.al
  have hbi := binIndex_large (sz := nb) (by omega)
  have hj : binIndex nb < numBins := by unfold numBins; omega
  have hgj := binAt_geo (binIndex nb) hj
  refine lscan_idx O h14 hnb16 h503 hnb31 fun R' I => ?_
  have hk2 := I.keep 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk9 := I.keep 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk18 := I.keep 18 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk19 := I.keep 19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk14 := I.keep 14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk8 := I.keep 8 (by decide) (by decide) (by decide) (by decide) (by decide)

  have hring := (binList_iff_ring.1 (HH.bins_list (binIndex nb) (by omega) hj)).1
  obtain ⟨l, hl⟩ : ∃ l, (binAt (binIndex nb) :: bins (binIndex nb)).getLast? = some l :=
    ⟨_, List.getLast?_cons⟩
  have hbk := ring_bk_head hring hl
  have hbklt := Vsa.Sim.read64_lt _ _ _ hbk
  have Bn := binRgn C.H hj; have ha0 := I.a0
  have hbA : binAt (binIndex nb) = 2147593488 + 16 * binIndex nb := rfl
  sx_run [3] O.live at 0x800048b4
  rgn_run O.live at 0x800048b8
  rgn_ld [hbk]
  rgn_run O.live at 0x800048bc
  rw [show (2147593488#64 + R' 10 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (binIndex nb)) from
    BitVec.eq_of_toNat_eq (by rgn_arith)]
  have hbl : binAt (binIndex nb) < 2 ^ 64 := by omega
  refine (step% st 0x800048bc) O.live (fun heq => ?_) (fun hne => ?_)
  ·
    refine hlr _ (binIndex nb + 1) (by unfold numBins; omega) (by omega) (.inl (by omega))
      (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ?_ <;> carry_close [hk2, hk9, hk18, hk19, hk14, h14, I.a7, hk8, h8]
  ·
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    have hlne : l ≠ binAt (binIndex nb) := fun he => hne (by rw [he])
    obtain ⟨pre, hpre⟩ : ∃ pre, bins (binIndex nb) = pre ++ [l] := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
      rcases ys with _ | ⟨y, ys'⟩
      · simp at hys; exact absurd hys.1.symm hlne
      · simp only [List.cons_append, List.cons.injEq] at hys
        exact ⟨ys', hys.2⟩
    refine (step% st 0x800048c0) O.live ?_
    refine (step% st 0x800048c4) O.live ?_
    refine lscan_walk O hj hlr (lscan_take O hj) pre.reverse l [] _ ⟨F.of_regs ?_ ?_ ?_ ?_, Hp, hnb, h503,
      hnb31, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by rw [hpre, List.reverse_reverse]) ?_ <;>
      carry_close [hk2, hk9, hk18, hk19, hk14, h14, I.a7, I.t3, hk8, h8]

end VsaIris.VsaHeap
