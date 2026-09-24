import VsaIris.Vsa.FreeBin

/-!
# `_free_r`'s large-bin insertion

A released chunk of more than 511 bytes goes to its large bin `binIndex S`
(the cascade `fl_idx`), at the first member no larger than it, walking the
bin from its head (`fl_walk`: `fl_cmp`, `fl_adv`), or as the only member of
an empty bin, whose block bit is then set (`fl_empty`). `fl_link` links it in
and returns.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state of the large-bin insertion: the frame, the insertion state,
the chunk's size above 511 with its bin `j`, and `av`, `X` and `S` in
`a7`, `a4`, `a5`. -/
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
  frame := L.frame.of_regs (h 2 (by decide) (by decide) (by decide) (by decide))
    (h 9 (by decide) (by decide) (by decide) (by decide))
    (h 18 (by decide) (by decide) (by decide) (by decide))
    (h 19 (by decide) (by decide) (by decide) (by decide))
  bin := L.bin
  large := L.large
  idx := L.idx
  a7 := by rw [h 17 (by decide) (by decide) (by decide) (by decide)]; exact L.a7
  a4 := by rw [h 14 (by decide) (by decide) (by decide) (by decide)]; exact L.a4
  a5 := by rw [h 15 (by decide) (by decide) (by decide) (by decide)]; exact L.a5

theorem FreeL.j_range {C : MCtx} {R : Nat → BitVec 64} {Mt M2 : Mem} {X S top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j) : 1 < j ∧ j < numBins := by
  have := binIndex_large (sz := S) (by have := L.large; omega)
  rw [L.idx] at this; unfold numBins; omega

/-- A member `x` of a bin, seen from the insertion state: a free chunk other
than the next one, its footprint words (header and links), and its words
reading as in the virtual heap. -/
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
  have hb := HH.walk.chunk_bounds cx hcx
  unfold heapStart at hb
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  simp only at hXb
  have hfoot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (cx.addr + o) := by
    intro o h1 h2
    by_cases ho : o < 16
    · have := foot_header BB (.inr ⟨cx, hcx, rfl⟩) (o - 8) (by omega)
      rwa [show cx.addr + 8 + (o - 8) = cx.addr + o by omega] at this
    · exact BB.node_foot hj0 hj (.inr hx) o (by omega) h2
  -- `x` is not the chunk after `X`, which is in use
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
  have hbn := HH.bnd_ne_node hj (.inr ⟨cx, hcx, rfl, hf, hx⟩) (HH.end_bnd hX)
  have hal := HH.aligned.1 cx hcx
  have hXal := HH.aligned.1 _ hX
  obtain ⟨hS16, _⟩ := walk_sizes HH.walk _ hX
  simp only at hXal hS16
  refine ⟨cx, hcx, rfl, hf, hal, hb.1, hb.2.1, hb.2.2, hfoot, fun o h1 h2 h3 => ?_⟩
  refine B.read (fun k hk => by
    have := hfoot (o + k) (by omega) (by omega)
    rwa [show cx.addr + (o + k) = cx.addr + o + k by omega] at this) ?_
  rcases HH.walk.chunk_sep cx hcx _ hX with he | h4 | h4
  · rw [he] at hf; cases hf
  · simp only at h4; omega
  · simp only at h4; omega

/-- A node of bin `j` (its header or a member) reads as in the virtual heap at
its link words. -/
theorem FBin.node_read {C : MCtx} {Mt M2 : Mem} {X S top brkv : Nat} {cs₁ cs₂ : List Chunk}
    {bins : Nat → List Nat} (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins) {j y : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hy : y = binAt j ∨ y ∈ bins j) {o : Nat}
    (ho : o = 16 ∨ o = 24) : read64 Mt (y + o) = read64 M2 (y + o) := by
  have hgj := binAt_geo j hj
  have HH := B.heap.heap.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  simp only at hXb
  rcases hy with rfl | hy
  · exact B.read (fun k hk => .inl (.inl ⟨by rcases ho with rfl | rfl <;> omega,
      by rcases ho with rfl | rfl <;> omega⟩))
      (.inl (by unfold heapStart at hXb; rcases ho with rfl | rfl <;> omega))
  · obtain ⟨cx, M⟩ := B.member hj0 hj hy
    rcases ho with rfl | rfl
    · exact M.read 16 (by omega) (by omega) (by omega)
    · exact M.read 24 (by omega) (by omega) (by omega)

/-- **The walk's exit** (`0x800074e0`): `succ` in `a3`; load its `bk`, the
insertion point's `pred`, and link `X` in. -/
theorem fl_exit {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j succ : Nat}
    {pre' post' : List Nat} (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j)
    (hne : bins j ≠ []) (hpos : bins j = pre' ++ post')
    (hsucc : (post' ++ [binAt j]).head? = some succ) (h13 : (R 13).toNat = succ) :
    AW C.live C.S C.Q 0x800074e0#64 R Mt := by
  have B := L.bin
  have HH := B.heap.heap.heap
  have BB := B.heap.heap
  obtain ⟨hj0, hj⟩ := L.j_range
  have hgj := binAt_geo j hj
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt j :: pre').getLast? = some p := ⟨_, List.getLast?_cons⟩
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hs16, hsnode⟩ := HH.node (by omega) hj hsm
  have hsf := BB.node_foot (by omega) hj hsm
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
  have hbkS' : read64 Mt (succ + 24) = some pred := by
    rw [B.node_read (by omega) hj hsm (.inr rfl)]; exact hbkS
  have hsl : 0x8001ad20 ≤ succ ∧ succ + 32 ≤ 0x100000000 := by
    have := HH.top_le; have := HH.brk_le
    rcases hsnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · unfold binAt avAddr at hgj ⊢; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart heapEnd at *; omega
  have hEs : ((R 13) + sign_extend (m := 64) (0x018#12)).toNat = succ + 24 := by
    sx_norm; rw [BitVec.toNat_add, h13]; simp; omega
  refine st_800074e0 O.live ?_ ?_ ?_
  · rw [hEs]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEs]; exact O.foot (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  rw [ldv_at hbkS' _ hEs]
  have hpl := Vsa.Sim.read64_lt _ _ _ hbkS'
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  simp only at hXb
  unfold heapStart at hXb
  have hbb' : read64 Mt binblocksAddr = some bb := by
    rw [B.read (fun k hk => .inl (.inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩)) (.inl (by unfold binblocksAddr avAddr; omega))]
    exact hbb
  have L' := L.upd (R' := upd R 11 (BitVec.ofNat 64 pred)) (fun x h10 h11 h12 h13 => upd_other _ _ h11)
  exact fl_link O L'.frame B hj0 hj L.idx hpos hpred hsucc hbb' (B.heap.bb_lt bb hbb)
    (HH.binblocks bb hbb j hj0 hj hne) (fun bb0 hbb0 k h => by rw [hbb] at hbb0; cases hbb0; exact h)
    (fun _ _ => rfl) B.pres B.frame
    (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl])
    (by rw [upd_other _ _ (by decide)]; exact h13) L'.a4

/-- One test of the sorted walk (`0x800074d4`): read member `x`'s size; a
larger member is passed (`0x800074cc`), otherwise `x` is the insertion
point. -/
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
  have HH := L.bin.heap.heap.heap
  obtain ⟨⟨h, hr, hs, _⟩, _⟩ := HH.headers M.mem
  rw [M.addr] at hr
  have hr' : read64 Mt (x + 8) = some h := by rw [M.read 8 (by omega) (by omega) (by omega)]; exact hr
  have hlo := M.lo; have hhi := M.hi; have hmin := M.min
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapEnd at hbrk
  have hEh : ((R 13) + sign_extend (m := 64) (0x008#12)).toNat = x + 8 := by
    sx_norm; rw [BitVec.toNat_add, h13]; simp; omega
  have hhlt := Vsa.Sim.read64_lt _ _ _ hr'
  refine st_800074d4 O.live ?_ ?_ ?_
  · rw [hEh]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEh]; exact O.foot (fun k hk => by
      have := M.foot (8 + k) (by omega) (by omega)
      rwa [show x + (8 + k) = x + 8 + k by omega] at this)
  rw [ldv_at hr' _ hEh]
  refine st_800074d8 O.live ?_
  have L' := L.upd (R' := upd (upd R 12 (BitVec.ofNat 64 h)) 12
    (BitVec.ofNat 64 h &&& sign_extend (m := 64) (0xffc#12)))
    (fun y h10 h11 h12 h13 => by simp only [upd_apply, h12, ite_false])
  refine st_800074dc O.live (fun hlt => ?_) (fun hge => ?_)
  · exact hpass _ L' (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h13)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  · have hne : bins j ≠ [] := by rw [hmem]; simp
    exact fl_exit O L' hne (pre' := pre) (post' := x :: rest) hmem rfl
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h13)

/-- The walk's step (`0x800074cc`): move to member `x`'s successor; the
header ends the walk with `X` last in the bin. -/
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
  have hlo := M.lo; have hhi := M.hi; have hmin := M.min
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
  have hEf : ((R 13) + sign_extend (m := 64) (0x010#12)).toNat = x + 16 := by
    sx_norm; rw [BitVec.toNat_add, h13]; simp; omega
  refine st_800074cc O.live ?_ ?_ ?_
  · rw [hEf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEf]; exact O.foot (fun k hk => by
      have := M.foot (16 + k) (by omega) (by omega)
      rwa [show x + (16 + k) = x + 16 + k by omega] at this)
  rw [ldv_at hfd' _ hEf]
  have L' := L.upd (R' := upd R 13 (BitVec.ofNat 64 nx)) (fun y h10 h11 h12 h13 => upd_other _ _ h13)
  have hne : bins j ≠ [] := by rw [hmem]; simp
  rcases rest with _ | ⟨y, rest'⟩
  · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    refine st_800074d0 O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
    · exact fl_exit O L' hne (pre' := pre ++ [x]) (post' := []) (by rw [hmem]; simp) rfl
        (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt])
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt]
  · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hnx
    subst hnx
    have hym : y ∈ bins j := by rw [hmem]; simp
    obtain ⟨cy, My⟩ := L.bin.member (by omega) hj hym
    have hylo := My.lo
    refine st_800074d0 O.live (fun hc => absurd hc ?_) (fun _ => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      intro he
      have := congrArg BitVec.toNat he
      rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnxlt] at this
      unfold binAt avAddr at this hgj; omega
    · exact hloop y rest' rfl _ L' (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnxlt]) (by rw [upd_other _ _ (by decide)]; exact h11)

/-- **The sorted walk** (`0x800074d4`): at member `x` of bin `j`, with the
members before it passed over. -/
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

/-- **An empty large bin** (`0x800075ec`): set its block bit and make `X` its
only member. -/
theorem fl_empty {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {j : Nat}
    (L : FreeL C R Mt M2 X S top brkv cs₁ cs₂ bins j) (hemp : bins j = [])
    (h12 : (R 12).toNat = j) (h11 : (R 11).toNat = binAt j) (h13 : (R 13).toNat = binAt j) :
    AW C.live C.S C.Q 0x800075ec#64 R Mt := by
  have B := L.bin
  have HH := B.heap.heap.heap
  obtain ⟨hj0, hj⟩ := L.j_range
  have hgj := binAt_geo j hj
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  simp only at hXb
  unfold heapStart at hXb
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 M2 binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hbbl := B.heap.bb_lt bb hbb
  have hbA : binblocksAddr = 2147593496 := rfl
  have hbb' : read64 Mt 2147593496 = some bb := by
    rw [← hbA, B.read (fun k hk => .inl (.inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩)) (.inl (by unfold binblocksAddr avAddr; omega))]
    exact hbb
  rw [← upd_self_eq L.a7]
  refine st_800075ec O.live (by sx_norm; decide) (by sx_norm; sx_side) ?_
  sx_norm
  simp (disch := decide) only [ldv_at hbb']
  have hbbv : (BitVec.ofNat 64 bb).toNat = bb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hq := sraiw2_toNat h12 (by unfold numBins at hj; omega)
  have hbit := shl_one hq (by unfold numBins at hj; omega)
  refine st_800075f0 O.live ?_
  refine st_800075f4 O.live ?_
  refine st_800075f8 O.live ?_
  refine st_800075fc O.live ?_
  sx_norm
  have hor : (1#64 <<< (BitVec.extractLsb 5 0 (BitVec.signExtend 64
      (shift_bits_right_arith (BitVec.extractLsb 31 0 (R 12)) 2#5))).toNat |||
      BitVec.ofNat 64 bb).toNat = bb ||| 2 ^ (j / 4) := by
    rw [BitVec.toNat_or, hbbv, hbit, Nat.or_comm]
  refine st_80007600 O.live (by sx_norm; decide) (by sx_norm; sx_side) ?_
  sx_norm
  refine st_80007604 O.live ?_
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hoB := B.off_stack (a := 2147593496) (fun k hk => .inl (.inl ⟨by omega, by omega⟩))
  unfold mHead at hoB
  refine fl_link O ((L.frame.store (by omega)).of_regs ?_ ?_ ?_ ?_) B hj0 hj L.idx
    (pre' := []) (post' := []) (by rw [hemp]; rfl) rfl rfl ?_ (lor_lt bb _ hbbl (by unfold numBins at hj; omega))
    (lor_bit_set bb _) (fun bb0 hbb0 k hk => by rw [hbb] at hbb0; cases hbb0; exact lor_bit_keep bb _ k hk)
    (fun w hw => by rw [writeLog_out]; simp only [OutL, and_true]; unfold binblocksAddr avAddr at hw; omega)
    (fun a ha => writeLog_present _ _ _ (B.pres a ha))
    (frame_store (fun b h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩))) B.frame) ?_ ?_ ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hbA, read64_store_hit, hor]
  · exact h11
  · exact h13
  · exact L.a4

/-- The large-bin cascade's result: bin `binIndex S`'s `fd` offset in `a1`,
the index in `a2`, and the other registers but `a3` kept. -/
structure FIdx (S : Nat) (R R' : Nat → BitVec 64) : Prop where
  a1 : (R' 11).toNat = 16 * binIndex S + 16
  a2 : (R' 12).toNat = binIndex S
  keep : ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → R' x = R x

/-- **The large-bin cascade** (`0x80007498`): from the size in `a5`, the bin
`binIndex S` and its `fd` offset. -/
theorem fl_idx {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {S : Nat}
    (h15 : (R 15).toNat = S) (hlo : 512 ≤ S) (hhi : S < 2 ^ 31)
    (hk : ∀ R', FIdx S R R' → AW C.live C.S C.Q 0x800074b8#64 R' Mt) :
    AW C.live C.S C.Q 0x80007498#64 R Mt := by
  have hbi := binIndex_large hlo
  refine st_80007498 O.live ?_
  refine st_8000749c O.live ?_
  sx_norm
  have hx : (R 15 >>> 9).toNat = S / 512 := by
    rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
  refine st_800074a0 O.live (fun h4 => ?_) (fun h4 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h4
  rotate_left
  · -- `S / 512 ≤ 4`: bins 57 to 64
    have h4' : S / 512 ≤ 4 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 6).toNat = S / 64 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 56 + S / 64 := by
      unfold binIndex; rw [if_neg (by omega), if_pos h4']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]
  have h4' : 4 < S / 512 := by sx_norm; omega
  refine st_80007584 O.live ?_
  refine st_80007588 O.live (fun h20 => ?_) (fun h20 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h20
  · -- `S / 512 ≤ 20`: bins 92 to 111
    have h20' : S / 512 ≤ 20 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hb : binIndex S = 91 + S / 512 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_pos h20']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hx (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hx]; omega), hx, hb]; omega
    · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]
  have h20' : 20 < S / 512 := by sx_norm; omega
  refine st_8000758c O.live ?_
  refine st_80007590 O.live (fun h84 => ?_) (fun h84 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h84
  rotate_left
  · -- `S / 512 ≤ 84`: bins 111 to 120
    have h84' : S / 512 ≤ 84 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 12).toNat = S / 4096 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 110 + S / 4096 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h84']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]
  have h84' : 84 < S / 512 := by sx_norm; omega
  refine st_80007608 O.live ?_
  refine st_8000760c O.live (fun h340 => ?_) (fun h340 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h340
  rotate_left
  · -- `S / 512 ≤ 340`: bins 120 to 124
    have h340' : S / 512 ≤ 340 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 15).toNat = S / 32768 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 119 + S / 32768 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h340']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]
  have h340' : 340 < S / 512 := by sx_norm; omega
  refine st_80007628 O.live ?_
  refine st_8000762c O.live (fun h1364 => ?_) (fun h1364 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hx] at h1364
  rotate_left
  · -- `S / 512 ≤ 1364`: bins 124 to 126
    have h1364' : S / 512 ≤ 1364 := by sx_norm; omega
    sx_run [8] O.live at 0x800074b8
    have hy : (R 15 >>> 18).toNat = S / 262144 := by
      rw [BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]
    have hb : binIndex S = 124 + S / 262144 := by
      unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h1364']
    refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [cascade_off hy (by omega), hb]; omega
    · rw [sx32_add_toNat (by rw [hy]; omega), hy, hb]; omega
    · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]
  -- the last bin, 126
  have h1364' : 1364 < S / 512 := by sx_norm; omega
  sx_run [8] O.live at 0x800074b8
  have hb : binIndex S = 126 := by
    unfold binIndex; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  refine hk _ ⟨?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hb]; rfl
  · rw [hb]; rfl
  · intro x h11 h12 h13; simp only [upd_apply, h11, h12, h13, ite_false]

/-- **The large bin's head** (`0x800074b8`): the bin's `fd`; an empty bin
(`0x800075ec`), or the sorted walk from its first member. -/
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
  have ha7 := L.a7
  have hA : (R 17 + R 11).toNat = binAt j + 16 := by
    rw [BitVec.toNat_add, ha7, h11]; unfold binAt avAddr at hgj ⊢; unfold numBins at hj
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  refine st_800074b8 O.live ?_
  refine st_800074bc O.live ?_ ?_ ?_
  · sx_norm; rw [hA]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hA]; exact O.toWOK.bin_link hj (.inl rfl)
  sx_norm
  rw [hA, ldv_at hfdJ' _ rfl]
  refine st_800074c0 O.live ?_
  sx_norm
  have hA1 : (R 17 + R 11 + 18446744073709551600#64).toNat = binAt j := by
    rw [BitVec.toNat_add, hA]; unfold binAt avAddr at hgj ⊢
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have L' := L.upd (R' := upd (upd (upd R 11 (R 17 + R 11)) 13 (BitVec.ofNat 64 first)) 11
    (R 17 + R 11 + 18446744073709551600#64)) (fun x h10 h11 h12 h13 => by
      simp only [upd_apply, h11, h13, ite_false])
  refine st_800074c4 O.live (fun hne => ?_) (fun he => ?_)
  · -- a member: the walk
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hne
    rcases hbj : bins j with _ | ⟨x, rest⟩
    · rw [hbj] at hof; simp at hof; subst hof
      exact absurd (BitVec.eq_of_toNat_eq (by rw [hA1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt])) hne
    · rw [hbj] at hof; simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hof
      subst hof
      exact fl_walk O rest [] x _ L' (by rw [hbj]; rfl)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt])
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hA1)
  · -- the header: an empty bin
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
    refine st_800074c8 O.live ?_
    exact fl_empty O L' hemp
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hA1)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoflt, hfb])

/-- **The bin insertion** (`0x800073e8`): a chunk of at most 511 bytes goes to
the head of its small bin (`fb_small`), a larger one to its sorted place in
its large bin. -/
theorem free_bin {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x800073e8#64 R Mt := by
  have HH := B.heap.heap.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  have htle := HH.top_le; have hbrk := HH.brk_le
  simp only at hXb
  unfold heapStart heapEnd at *
  refine st_800073e8 O.live ?_
  refine st_800073ec O.live (fun hl => ?_) (fun hs => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hl
    have hl' : 511 < S := by first | omega | (sx_norm; done) | (sx_norm; omega)
    refine fl_idx O (S := S) (by rw [upd_other _ _ (by decide)]; exact h15) (by omega) (by omega)
      fun R' I => ?_
    have hk := I.keep
    have e : ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → R' x = R x := fun x h1 h2 h3 => by
      rw [hk x h1 h2 h3, upd_other _ _ h3]
    exact fl_head O ⟨F.of_regs (e 2 (by decide) (by decide) (by decide))
      (e 9 (by decide) (by decide) (by decide)) (e 18 (by decide) (by decide) (by decide))
      (e 19 (by decide) (by decide) (by decide)), B, hl', rfl,
      by rw [e 17 (by decide) (by decide) (by decide)]; exact h17,
      by rw [e 14 (by decide) (by decide) (by decide)]; exact h14,
      by rw [e 15 (by decide) (by decide) (by decide)]; exact h15⟩ I.a1 I.a2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hs
    exact fb_small O (F.of_regs (upd_other _ _ (by decide)) (upd_other _ _ (by decide))
      (upd_other _ _ (by decide)) (upd_other _ _ (by decide))) B
      (by first | omega | (sx_norm; done) | (sx_norm; omega))
      (by rw [upd_other _ _ (by decide)]; exact h17) (by rw [upd_other _ _ (by decide)]; exact h14)
      (by rw [upd_other _ _ (by decide)]; exact h15)

/-- **The bin insertion's second entry** (`0x80007490`): the same test as
`free_bin`, reached with the chunk's header and footer just written. -/
theorem free_bin2 {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt M2 : Mem}
    {X S top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (F : FFrame C R Mt) (B : FBin C Mt M2 X S top brkv cs₁ cs₂ bins)
    (h17 : R 17 = 0x8001ad10#64) (h14 : (R 14).toNat = X) (h15 : (R 15).toNat = S) :
    AW C.live C.S C.Q 0x80007490#64 R Mt := by
  have HH := B.heap.heap.heap
  have hX : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  have htle := HH.top_le; have hbrk := HH.brk_le
  simp only at hXb
  unfold heapStart heapEnd at *
  refine st_80007490 O.live ?_
  refine st_80007494 O.live (fun hs => ?_) (fun hl => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hs
    exact fb_small O (F.of_regs (upd_other _ _ (by decide)) (upd_other _ _ (by decide))
      (upd_other _ _ (by decide)) (upd_other _ _ (by decide))) B
      (by first | omega | (sx_norm; done) | (sx_norm; omega))
      (by rw [upd_other _ _ (by decide)]; exact h17) (by rw [upd_other _ _ (by decide)]; exact h14)
      (by rw [upd_other _ _ (by decide)]; exact h15)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15] at hl
    have hl' : 511 < S := by first | omega | (sx_norm; done) | (sx_norm; omega)
    refine fl_idx O (S := S) (by rw [upd_other _ _ (by decide)]; exact h15) (by omega) (by omega)
      fun R' I => ?_
    have hk := I.keep
    have e : ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → R' x = R x := fun x h1 h2 h3 => by
      rw [hk x h1 h2 h3, upd_other _ _ h3]
    exact fl_head O ⟨F.of_regs (e 2 (by decide) (by decide) (by decide))
      (e 9 (by decide) (by decide) (by decide)) (e 18 (by decide) (by decide) (by decide))
      (e 19 (by decide) (by decide) (by decide)), B, hl', rfl,
      by rw [e 17 (by decide) (by decide) (by decide)]; exact h17,
      by rw [e 14 (by decide) (by decide) (by decide)]; exact h14,
      by rw [e 15 (by decide) (by decide) (by decide)]; exact h15⟩ I.a1 I.a2

end VsaIris.VsaHeap
