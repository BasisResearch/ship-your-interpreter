import VsaIris.Vsa.MallocRebinL

/-!
# `_malloc_r`'s large requests

A request whose chunk exceeds 503 bytes (`0x80004884`) scans its own large bin
`binIndex nb` from the smallest member up (the bins are sorted, larger
first, so the walk goes backwards through `bk`):

* `lscan_idx`: the six-way cascade computing `binIndex nb`, into `t3`, and the
  next bin, into `a7`;
* members too small are passed; the first one that fits within `MINSIZE` is
  taken whole (`0x80004c20`, `PHeapAt.take`); one that would leave a larger
  remainder ends the scan at the last-remainder check with `a7 = binIndex nb`,
  and so does reaching the header, with `a7 = binIndex nb + 1`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `slliw x,y,1` on a small word. -/
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

/-- The registers the large-request cascade leaves at `0x800048a8`: the offset
of bin `binIndex nb + 1` from `__malloc_av_` in `a0`, the index `binIndex nb`
in `t3` and the next in `a7`; everything else but `a3` and `a5` kept. -/
structure LScanIdx (nb : Nat) (R R' : Nat → BitVec 64) : Prop where
  a0 : (R' 10).toNat = 16 * (binIndex nb + 1)
  a7 : (R' 17).toNat = binIndex nb + 1
  t3 : (R' 28).toNat = binIndex nb
  keep : ∀ x, x ≠ 10 → x ≠ 13 → x ≠ 15 → x ≠ 17 → x ≠ 28 → R' x = R x

/-- **The large-request cascade** (`0x80004884`): from the chunk size in
`a4`, `binIndex nb` and the next bin. -/
theorem lscan_idx {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {nb : Nat}
    (h14 : (R 14).toNat = nb) (hnb16 : nb % 16 = 0) (hlo : 503 < nb) (hhi : nb < 2 ^ 31)
    (hk : ∀ R', LScanIdx nb R R' → AW C.live C.S C.Q 0x800048a8#64 R' Mt) :
    AW C.live C.S C.Q 0x80004884#64 R Mt := by
  have hbi := binIndex_large (sz := nb) (by omega)
  refine st_80004884 O.live ?_
  sx_norm
  have hx : (R 14 >>> 9).toNat = nb / 512 := by
    rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
  refine st_80004888 O.live (fun h0 => absurd h0 ?_) (fun _ => ?_)
  · simp only [upd_apply, ite_true]
    intro he; have := congrArg BitVec.toNat he; rw [hx] at this; simp at this; omega
  refine st_8000488c O.live ?_
  refine st_80004890 O.live (fun h4 => ?_) (fun h4 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h4
  · -- `nb / 512 > 4`
    have h4' : 4 < nb / 512 := by sx_norm; omega
    refine st_80004cd4 O.live ?_
    refine st_80004cd8 O.live (fun h20 => ?_) (fun h20 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h20
    · -- `nb / 512 ≤ 20`: bins 96 to 111
      have h20' : nb / 512 ≤ 20 := by sx_norm; omega
      have hy := hx
      sx_run [8] O.live at 0x800048a8
      have hb : binIndex nb = 91 + nb / 512 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, h20', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 9) (k := 92) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
      · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]
    have h20' : 20 < nb / 512 := by sx_norm; omega
    refine st_80004cdc O.live ?_
    refine st_80004ce0 O.live (fun h84 => ?_) (fun h84 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h84
    rotate_left
    · -- `nb / 512 ≤ 84`: bins 111 to 120
      have h84' : nb / 512 ≤ 84 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 12).toNat = nb / 4096 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 110 + nb / 4096 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, h84', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 12) (k := 111) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
      · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]
    have h84' : 84 < nb / 512 := by sx_norm; omega
    refine st_80004f3c O.live ?_
    refine st_80004f40 O.live (fun h340 => ?_) (fun h340 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h340
    rotate_left
    · -- `nb / 512 ≤ 340`: bins 120 to 124
      have h340' : nb / 512 ≤ 340 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 15).toNat = nb / 32768 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 119 + nb / 32768 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega, h340', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 15) (k := 120) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
      · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]
    have h340' : 340 < nb / 512 := by sx_norm; omega
    refine st_80004fc0 O.live ?_
    refine st_80004fc4 O.live (fun h1364 => ?_) (fun h1364 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h1364
    rotate_left
    · -- `nb / 512 ≤ 1364`: bins 124 to 126
      have h1364' : nb / 512 ≤ 1364 := by sx_norm; omega
      sx_run [8] O.live at 0x800048a8
      have hy : (R 14 >>> 18).toNat = nb / 262144 := by
        rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
      have hb : binIndex nb = 124 + nb / 262144 := by
        unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega, show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega, show ¬ nb / 512 ≤ 340 by omega, h1364', if_false, if_true]
      have h7 := sx32_add_toNat (x := R 14 >>> 18) (k := 125) (by rw [hy]; omega)
      rw [hy] at h7
      refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
      · rw [h7, hb]; omega
      · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
      · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]
    -- the last bin, 126
    have h1364' : 1364 < nb / 512 := by sx_norm; omega
    sx_run [8] O.live at 0x800048a8
    have hb : binIndex nb = 126 := by
      unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, show ¬ nb / 512 ≤ 4 by omega,
        show ¬ nb / 512 ≤ 20 by omega, show ¬ nb / 512 ≤ 84 by omega,
        show ¬ nb / 512 ≤ 340 by omega, show ¬ nb / 512 ≤ 1364 by omega, if_false]
    refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [hb]; rfl
    · rw [hb]; rfl
    · rw [hb]; rfl
    · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]
  · -- `nb / 512 ≤ 4`: bins 64 to 72
    have h4' : nb / 512 ≤ 4 := by sx_norm; omega
    sx_run [8] O.live at 0x800048a8
    have hy : (R 14 >>> 6).toNat = nb / 64 := by
      rw [BitVec.toNat_ushiftRight, h14, Nat.shiftRight_eq_div_pow]
    have hb : binIndex nb = 56 + nb / 64 := by
      unfold binIndex; simp only [show ¬ nb / 512 = 0 by omega, h4', if_false, if_true]
    have h7 := sx32_add_toNat (x := R 14 >>> 6) (k := 57) (by rw [hy]; omega)
    rw [hy] at h7
    refine hk _ ⟨?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [BitVec.toNat_shiftLeft, slliw1_toNat (by rw [h7]; omega), h7, Nat.shiftLeft_eq, hb]; omega
    · rw [h7, hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h10 h13 h15 h17 h28; simp only [upd_apply, h10, h13, h15, h17, h28, ite_false]

/-- The state of the large-request scan: the heap (read only), the request's
chunk size `nb` in `a4`, its bin `j = binIndex nb` in `t3` and `j + 1` in `a7`,
the bin's header in `a0`, `31` in `t1`, and `__malloc_av_` in `a6`. -/
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
  frame := L.frame.of_regs (h 2 (by decide) (by decide) (by decide) (by decide))
    (h 9 (by decide) (by decide) (by decide) (by decide))
    (h 18 (by decide) (by decide) (by decide) (by decide))
    (h 19 (by decide) (by decide) (by decide) (by decide))
  heap := L.heap
  nbok := L.nbok
  large := L.large
  nb31 := L.nb31
  bin_idx := L.bin_idx
  a4 := by rw [h 14 (by decide) (by decide) (by decide) (by decide)]; exact L.a4
  a6 := by rw [h 16 (by decide) (by decide) (by decide) (by decide)]; exact L.a6
  a7 := by rw [h 17 (by decide) (by decide) (by decide) (by decide)]; exact L.a7
  t3 := by rw [h 28 (by decide) (by decide) (by decide) (by decide)]; exact L.t3
  a0 := by rw [h 10 (by decide) (by decide) (by decide) (by decide)]; exact L.a0
  t1 := by rw [h 6 (by decide) (by decide) (by decide) (by decide)]; exact L.t1
  s0 := by rw [h 8 (by decide) (by decide) (by decide) (by decide)]; exact L.s0

/-- The scan's exit to the last-remainder check, with the block search to
start at `idx`. -/
abbrev LScanLR (C : MCtx) (Mt : Mem) (nb : Nat) : Prop :=
  ∀ R' idx, idx < numBins → MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV →
    AW C.live C.S C.Q 0x800048ec#64 R' Mt

/-- The scan's take: member `x` of bin `j`, between `pred` (in `a1`) and its
successor, fits within `MINSIZE`. -/
abbrev LScanTake (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb j : Nat) : Prop :=
  ∀ R' pre post x sz pred, LScan C Mt brkv chunks bins nb j R' → bins j = pre ++ x :: post →
    FreeAt chunks x sz → nb ≤ sz → sz < nb + 32 → (binAt j :: pre).getLast? = some pred →
    (R' 15).toNat = x → (R' 11).toNat = pred → (R' 13).toNat = sz →
    AW C.live C.S C.Q 0x80004c20#64 R' Mt

/-- A small word's signed value is its unsigned one. -/
theorem toInt_small {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 63) :
    x.toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, h, if_pos (by omega)]

/-- One step of the large-request scan (`0x800048d8`): measure member `x`;
too big leaves the scan with the block search at `j`, a fit is taken, too small
moves on to its predecessor (or leaves at the header, with the search at
`j + 1`). -/
theorem lscan_step {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb j x : Nat} {pre post : List Nat}
    (L : LScan C Mt brkv chunks bins nb j R) (hj : j < numBins) (hmem : bins j = pre ++ x :: post)
    (h15 : (R 15).toNat = x) (hlr : LScanLR C Mt nb) (htake : LScanTake C Mt brkv chunks bins nb j)
    (hprev : ∀ pre' y, pre = pre' ++ [y] → ∀ R', LScan C Mt brkv chunks bins nb j R' →
      (R' 15).toNat = y → AW C.live C.S C.Q 0x800048d8#64 R' Mt) :
    AW C.live C.S C.Q 0x800048d8#64 R Mt := by
  have HH := L.heap.heap.heap.heap
  have B := L.heap.heap.heap
  have hnb16 := L.nbok.al
  have hbi := binIndex_large (sz := nb) (by have := L.large; omega)
  have hj0 : 1 < j := by rw [← L.bin_idx]; omega
  have hj126 : j ≤ 126 := by rw [← L.bin_idx]; exact hbi.2
  have hgj := binAt_geo j hj
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨cx, hcx, hxa, hxf⟩ := HH.member (by omega) hj hx
  obtain ⟨cxa, sz, cxi⟩ := cx
  simp only at hxa hxf
  subst hxa hxf
  have hb := HH.walk.chunk_bounds _ hcx
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hb; unfold heapEnd at hbrk
  simp only at hb
  have hfoot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (cxa + o) := by
    intro o h1 h2
    by_cases ho : o < 16
    · have := foot_header B (.inr ⟨_, hcx, rfl⟩) (o - 8) (by omega)
      rwa [show cxa + 8 + (o - 8) = cxa + o by omega] at this
    · exact B.node_foot (by omega) hj (.inr hx) o (by omega) h2
  obtain ⟨⟨h, hr, hs, _⟩, _⟩ := HH.headers hcx
  simp only at hr hs
  have hhlt := Vsa.Sim.read64_lt _ _ _ hr
  have hEh : ((R 15) + sign_extend (m := 64) (0x008#12)).toNat = cxa + 8 := by sx_addr
  refine st_800048d8 O.live ?_ ?_ ?_
  · rw [hEh]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEh]; exact O.foot (fun k hk => by
      have := hfoot (8 + k) (by omega) (by omega)
      rwa [show cxa + (8 + k) = cxa + 8 + k by omega] at this)
  rw [ldv_at hr _ hEh]
  refine st_800048dc O.live ?_
  refine st_800048e0 O.live ?_
  sx_norm
  have hszv : (BitVec.ofNat 64 h &&& 18446744073709551612#64).toNat = sz := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt, ← hs]; rfl
  have hsz62 : sz < 2 ^ 62 := by have := hb.2.1; omega
  have hcmp := lr_cmp hszv L.a4 hsz62 (by have := L.nb31; omega)
  have h31 : (R 6).toInt = (31 : Int) := toInt_small L.t1 (by decide)
  have h31' : ((31#64 : BitVec 64)).toInt = (31 : Int) := by decide
  -- the predecessor
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨nx, hnx⟩ : ∃ q, (post ++ [binAt j]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hbk := (ring_member hring hpred hnx).2
  have hplt := Vsa.Sim.read64_lt _ _ _ hbk
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hmem]; exact List.mem_append_left _ h1)
  refine st_800048e4 O.live (fun hle => ?_) (fun hgt => ?_)
  · -- at most `MINSIZE` over: its predecessor
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h31] at hle
    have hlt32 : sz < nb + 32 := by
      have := hcmp.1; rw [h31'] at this; omega
    have hEb : ((R 15) + sign_extend (m := 64) (0x018#12)).toNat = cxa + 24 := by sx_addr
    refine st_800048c8 O.live ?_ ?_ ?_
    · sx_norm; sx_addr
    · sx_norm; exact O.foot (fun k hk => by
        have := hfoot (24 + k) (by omega) (by omega)
        rwa [show cxa + (24 + k) = (R 15 + 24#64).toNat + k by sx_addr] at this)
    sx_norm
    rw [ldv_at hbk _ (by sx_addr)]
    have L' := L.upd (R' := upd (upd (upd (upd R 13 (BitVec.ofNat 64 h)) 13
      (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 12
      ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14)) 11 (BitVec.ofNat 64 pred))
      (fun y h11 h12 h13 h15 => by simp only [upd_apply, h11, h12, h13, ite_false])
    refine st_800048cc O.live (fun hge => ?_) (fun hneg => ?_)
    · -- a fit: take it
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hge
      have hle' : nb ≤ sz := hcmp.2.1 hge
      exact htake _ pre post cxa sz pred L' hmem hcx hle' hlt32 hpred
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
        (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt])
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hszv)
    · -- too small: on to the predecessor, or out at the header
      rcases List.eq_nil_or_concat pre with rfl | ⟨pre', y, rfl⟩
      · simp only [List.getLast?_singleton, Option.some.injEq] at hpred
        subst hpred
        refine st_800048d0 O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
        · refine hlr _ (j + 1) (by unfold numBins; omega) L'.frame ⟨L'.a4, L'.a7, L'.a6⟩ L'.s0
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
        refine st_800048d0 O.live (fun hc => absurd hc ?_) (fun _ => ?_)
        · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          intro he; apply hylo
          have := congrArg BitVec.toNat he
          rw [L.a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt] at this
          exact this
        refine st_800048d4 O.live ?_
        exact hprev pre' pred (by simp) _ (L'.upd fun z h11 h12 h13 h15 => by
          simp only [upd_apply, h15, ite_false]) (by
            simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
            sx_norm
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt])
  · -- more than `MINSIZE` over: the last-remainder check, the block search at `j`
    refine st_800048e8 O.live ?_
    refine hlr _ j hj (L.frame.of_regs rfl rfl rfl rfl) ⟨?_, ?_, ?_⟩ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact L.a4
    · sx_norm; exact L.t3
    · exact L.a6
    · exact L.s0

/-- **The large-request scan** (`0x800048d8`): at member `x` of bin `j`, with
the members after it (smaller than `nb`) passed. -/
theorem lscan_walk {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb j : Nat} (hj : j < numBins) (hlr : LScanLR C Mt nb)
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

/-- **What a take of a free chunk owes the caller**, for any bin and position:
`PHeapAt.take` over the memory the machine leaves (the unlink, the next
header with `PREV_INUSE`), packaged as `TakeRet`. -/
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
  exact ⟨hfr, hal16, ⟨_, _, _, _, hheap, by omega⟩, hpres, hframe⟩

/-- The end of a take's inline epilogue: at the caller's `ra` with the
caller's registers and the block in `a0`. -/
theorem fin_take_at {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem} {v : Nat}
    (T : TakeRet C M v) (hregs : MRegs C R) (h10 : (R 10).toNat = v + 16) :
    AW C.live C.S C.Q (R 1) R M := by
  rw [hregs.ra]; exact O.fin_take h10 T R hregs (fun _ _ _ _ => rfl)

/-- **The scan take's return** (`0x80004c40`): spill the victim, unlock,
restore the frame, and return `v + 16` owing `TakeRet`. -/
theorem lscan_fin {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem} {v : Nat}
    (F : MFrame C R M) (h15 : (R 15).toNat = v) (hv : v < 2 ^ 32)
    (T : TakeRet C (writeLog M [(C.s.toNat - 96 + 8, 8, R 15)]) v) :
    AW C.live C.S C.Q 0x80004c40#64 R M := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  have hra : read64 (writeLog M [(C.s.toNat - 96 + 8, 8, R 15)]) (C.s.toNat - 96 + 88) =
      some C.r.toNat := by rw [read64_store_miss _ _ (by omega)]; exact F.ra
  have hs0 : read64 (writeLog M [(C.s.toNat - 96 + 8, 8, R 15)]) (C.s.toNat - 96 + 80) =
      some (C.rv0 8).toNat := by rw [read64_store_miss _ _ (by omega)]; exact F.s0
  sx_run [8] O.live at 0x80004c4c
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
  have hEra : ((R 2) + sign_extend (m := 64) (0x058#12)).toNat = C.s.toNat - 96 + 88 := by sx_addr
  have hEs0 : ((R 2) + sign_extend (m := 64) (0x050#12)).toNat = C.s.toNat - 96 + 80 := by sx_addr
  refine st_80004c4c O.live ?_ ?_ ?_
  · sx_norm; rw [hEra]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEra]; exact O.stack (by unfold mHead; omega) (by omega)
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [hEra, ldv_ld hra]
  refine st_80004c50 O.live ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hEs0]
    unfold LdOK Vsa.Sim.tohostAddr; omega
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [hEs0]
    exact O.stack (by unfold mHead; omega) (by omega)
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [hEs0, ldv_ld hs0]
  refine st_80004c54 O.live ?_
  refine st_80004c58 O.live ?_
  refine st_80004c5c O.live ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact O.ral
  refine fin_take_at O T ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · apply BitVec.eq_of_toNat_eq; sx_addr
  · exact F.s1
  · exact F.s2
  · exact F.s3
  · sx_addr

/-- **What the scan's take owes the caller**: the four stores (the successor's
`bk`, the predecessor's `fd`, the next header with `PREV_INUSE`, the spill of
the victim), with the stored words named by their values. -/
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
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hlo := hsp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hb; unfold heapEnd at hbrk
  simp only at hb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hgj := binAt_geo j hj
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hmem]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hmem]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  have hpf := B.node_foot hj0 hj hpm
  have hsf := B.node_foot hj0 hj hsm
  obtain ⟨hp16, _⟩ := HH.node hj0 hj hpm
  obtain ⟨hs16, _⟩ := HH.node hj0 hj hsm
  have hnxf := foot_header B (HH.end_bnd hfree)
  simp only at hnxf
  obtain ⟨_, hpn⟩ := HH.node hj0 hj hpm
  obtain ⟨_, hsn⟩ := HH.node hj0 hj hsm
  have hbn : x + sz = C.top0 ∨ ∃ c ∈ chunks, c.addr = x + sz := HH.end_bnd hfree
  have hbp := HH.bnd_ne_node hj hpn hbn 8 (by omega) (by omega)
  have hbs := HH.bnd_ne_node hj hsn hbn 16 (by omega) (by omega)
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hoN := hns _ (hnxf 0 (by omega))
  have hoS := hns (succ + 24) (by have := hsf 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := hpf 16 (by omega) (by omega); simpa using this)
  simp only [Nat.add_zero] at hoN
  refine take_ret Hp hnb hj0 hj hmem hfree hle hpred hsucc ?_ ?_ ?_ ?_ ?_ ?_
  · show read64 _ (pred + 16) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega), read64_store_hit, h2]
  · show read64 _ (succ + 24) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_hit, h1]
  · intro hd' hd'r
    rw [hdr] at hd'r; cases hd'r
    rw [read64_store_miss _ _ (by omega), read64_store_hit, h3]
  · intro a ha hna
    unfold TakeW at hna
    have := hns a ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · intro a ha
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (Hp.pres a ha))))
  · exact frame_store (win_stack (by unfold mHead; omega) (by omega))
      (frame_store (win_foot hnxf) (frame_store (win_foot (fun k hk => by
        have := hpf (16 + k) (by omega) (by omega)
        rwa [show pred + (16 + k) = pred + 16 + k by omega] at this))
        (frame_store (win_foot (fun k hk => by
          have := hsf (24 + k) (by omega) (by omega)
          rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)) Hp.frame)))

/-- **The scan's take** (`0x80004c20`): unlink member `x` of bin `j` (its
predecessor in `a1`), set `PREV_INUSE` after it, unlock, and return `x + 16`. -/
theorem lscan_take {C : MCtx} (O : MOK C) {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb j : Nat} (hj : j < numBins) :
    LScanTake C Mt brkv chunks bins nb j := by
  intro R pre post x sz pred L hmem hfree hle hlt hpred h15 h11 h13
  have HH := L.heap.heap.heap.heap
  have B := L.heap.heap.heap
  have hnb16 := L.nbok.al
  have hbi := binIndex_large (sz := nb) (by have := L.large; omega)
  have hj0 : 1 < j := by rw [← L.bin_idx]; omega
  have hgj := binAt_geo j hj
  have hx : x ∈ bins j := by rw [hmem]; exact List.mem_append_right _ List.mem_cons_self
  have hb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hb; unfold heapEnd at hbrk
  simp only at hb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := L.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  -- the nodes around `x`
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt j]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list j (by omega) hj)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hmem]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hmem]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  have hpf := B.node_foot (by omega) hj hpm
  have hsf := B.node_foot (by omega) hj hsm
  have hvf := foot_free_span B hfree rfl
  simp only at hvf
  have hloc : ∀ y, (y = binAt j ∨ y ∈ bins j) →
      y % 16 = 0 ∧ (y = binAt j ∨ (0x8001c170 ≤ y ∧ y + 32 ≤ C.top0)) := by
    intro y hy
    obtain ⟨hy16, hyn⟩ := HH.node (by omega) hj hy
    refine ⟨hy16, ?_⟩
    rcases hyn with h | ⟨cy, hcy, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cy hcy; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
  obtain ⟨hp16, hploc⟩ := hloc pred hpm
  obtain ⟨hs16, hsloc⟩ := hloc succ hsm
  unfold binAt avAddr at hgj hploc hsloc
  -- the next chunk's header
  obtain ⟨_, ⟨hd, hdr, hdp⟩⟩ := HH.headers hfree
  simp only at hdr hdp
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  have hnxf := foot_header B (HH.end_bnd hfree)
  simp only at hnxf
  -- `ld a2,16(a5)`: the successor
  have hEf : ((R 15) + sign_extend (m := 64) (0x010#12)).toNat = x + 16 := by sx_addr
  refine st_80004c20 O.live ?_ ?_ ?_
  · rw [hEf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEf]; exact O.foot (fun k hk => hvf _ (by omega) (by omega))
  rw [ldv_at hfd _ hEf]
  -- `add a3,a5,a3; ld a4,8(a3)`: the next header
  refine st_80004c24 O.live ?_
  sx_norm
  have hEn : (R 15 + R 13 + 8#64).toNat = x + sz + 8 := by sx_addr
  refine st_80004c28 O.live ?_ ?_ ?_
  · sx_norm; rw [hEn]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEn]; exact O.foot_at hnxf _ rfl
  sx_norm
  rw [ldv_at hdr _ hEn]
  -- `sd a1,24(a2); sd a2,16(a1)`: the unlink
  have hEs : (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl]; simp; omega
  refine st_80004c2c O.live ?_ ?_ ?_
  · sx_norm; rw [hEs]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEs]; exact O.foot (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  sx_norm
  rw [hEs]
  have hEp : (R 11 + 16#64).toNat = pred + 16 := by sx_addr
  refine st_80004c30 O.live ?_ ?_ ?_
  · sx_norm; rw [hEp]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEp]; exact O.foot (fun k hk => by
      have := hpf (16 + k) (by omega) (by omega)
      rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  sx_norm
  rw [hEp]
  -- `ori a4,a4,1; mv a0,s0; sd a4,8(a3)`: `PREV_INUSE`
  refine st_80004c34 O.live ?_
  refine st_80004c38 O.live ?_
  refine st_80004c3c O.live ?_ ?_ ?_
  · sx_norm; rw [hEn]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEn]; exact O.foot_at hnxf _ rfl
  sx_norm
  rw [hEn]
  have hoN := L.heap.off_stack hnxf
  have hoS := L.heap.off_stack (a := succ + 24) (fun k hk => by
    have := hsf (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  have hoP := L.heap.off_stack (a := pred + 16) (fun k hk => by
    have := hpf (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  unfold mHead at hoN hoS hoP
  have hpl : pred < 2 ^ 64 := by rcases hploc with rfl | h <;> omega
  have hOr : (BitVec.ofNat 64 hd ||| 1#64).toNat = hd + 1 :=
    or1_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]) hdev
  exact lscan_fin O ((((L.frame.store (by omega)).store (by omega)).store (by omega)).of_regs
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]))
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15) (by omega)
    (lscan_ret O.sp L.heap L.nbok (by omega) hj hmem hfree hle hpred hsucc hdr h11
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl]) hOr)

/-- **A large request** (`0x80004884`): its bin by the cascade, then the
scan from the smallest member, or straight to the last-remainder check when
the bin is empty. -/
theorem lscan {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb)
    (h503 : 503 < nb) (hnb31 : nb < 2 ^ 31) (h14 : (R 14).toNat = nb) (h8 : R 8 = reentV)
    (hlr : LScanLR C Mt nb) :
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
  -- the bin's last member
  have hring := (binList_iff_ring.1 (HH.bins_list (binIndex nb) (by omega) hj)).1
  obtain ⟨l, hl⟩ : ∃ l, (binAt (binIndex nb) :: bins (binIndex nb)).getLast? = some l :=
    ⟨_, List.getLast?_cons⟩
  have hbk := ring_bk_head hring hl
  have hbklt := Vsa.Sim.read64_lt _ _ _ hbk
  have hEa : (2147593488#64 + R' 10 + 8#64).toNat = binAt (binIndex nb) + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, I.a0]; unfold binAt avAddr
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    unfold binAt avAddr at hgj; omega
  sx_run [3] O.live at 0x800048b4
  refine st_800048b4 O.live ?_ ?_ ?_
  · sx_norm; rw [hEa]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEa]; exact O.bin_link hj (.inr rfl)
  sx_norm
  rw [hEa, ldv_at hbk _ rfl]
  refine st_800048b8 O.live ?_
  sx_norm
  have hEb : (2147593488#64 + R' 10 + 18446744073709551600#64) = BitVec.ofNat 64 (binAt (binIndex nb)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, I.a0, BitVec.toNat_ofNat]; unfold binAt avAddr
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    unfold binAt avAddr at hgj; omega
  rw [hEb]
  have hbl : binAt (binIndex nb) < 2 ^ 64 := by omega
  refine st_800048bc O.live (fun heq => ?_) (fun hne => ?_)
  · -- an empty bin: the last-remainder check, the block search at the next bin
    refine hlr _ (binIndex nb + 1) (by unfold numBins; omega)
      (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hk2
    · exact hk9
    · exact hk18
    · exact hk19
    · rw [hk14]; exact h14
    · exact I.a7
    · rw [hk8]; exact h8
  · -- the scan, from the last member
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    have hlne : l ≠ binAt (binIndex nb) := fun he => hne (by rw [he])
    obtain ⟨pre, hpre⟩ : ∃ pre, bins (binIndex nb) = pre ++ [l] := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
      rcases ys with _ | ⟨y, ys'⟩
      · simp at hys; exact absurd hys.1.symm hlne
      · simp only [List.cons_append, List.cons.injEq] at hys
        exact ⟨ys', hys.2⟩
    refine st_800048c0 O.live ?_
    refine st_800048c4 O.live ?_
    refine lscan_walk O hj hlr (lscan_take O hj) pre.reverse l [] _ ⟨?_, Hp, hnb, h503, hnb31, rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by rw [hpre, List.reverse_reverse]) ?_ <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact F.of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hk2)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hk9)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hk18)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hk19)
    · rw [hk14]; exact h14
    · exact I.a7
    · exact I.t3
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbl]
    · rfl
    · rw [hk8]; exact h8
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbklt]

end VsaIris.VsaHeap
