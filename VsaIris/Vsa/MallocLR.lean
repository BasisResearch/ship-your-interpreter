import VsaIris.Vsa.MallocPro

/-!
# `_malloc_r`'s last-remainder check

`0x800048ec` is the join every request that no exact bin served reaches: the
small-bin miss (`j_small`), the large-bin scan's misses (`0x800048bc`,
`0x800048d0`) and its exhausted walk (`0x800048e8`). The code reads bin 1's
`fd` word — the last remainder — and dispatches:

* bin 1 empty (`fd` is the header itself): the block search (`0x80004be8`);
* the remainder is at least `nb + 32`: split it (`0x80004da0`);
* otherwise bin 1 is cleared (`0x80004910`, `0x80004914`) and
  * the remainder is within 31 bytes of `nb`: take it whole (`0x80004d78`),
  * it is smaller than `nb`: put it back on its own bin (`0x8000491c`).

Between the clearing stores and the re-binding the victim is free and on no
bin, so `HeapAt` does not hold. `MDetach` names exactly what the code owns
there: bin `i`'s link words point at the header, and the memory is the heap's
everywhere else.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The remainder's two signed comparisons.** `a3 := t1 - a4` with both
operands well below `2 ^ 63`: `blt a2,a3` at `0x8000490c` (with `a2 = 31`)
decides `nb + 32 ≤ sz`, and `bgez a3` at `0x80004918` decides `nb ≤ sz`. -/
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

/-- The registers at the last-remainder victim: its address in `a5`, its chunk
size in `t1`, the remainder `t1 - a4` in `a3`, the request in `a4`, and bin
1's header in `t4`. -/
structure LRVictim (nb sz v : Nat) (R : Nat → BitVec 64) : Prop where
  a5 : (R 15).toNat = v
  t1 : (R 6).toNat = sz
  a3 : R 13 = R 6 - R 14
  a4 : (R 14).toNat = nb
  t4 : (R 29).toNat = binAt 1

/-- **A detached victim.** Bin `i`'s only member `v` is unlinked: the header's
`fd` and `bk` point at itself and the memory is the heap's `Mt` everywhere
else. `_malloc_r` is in this state between clearing the last-remainder bin
(`0x80004914`) and either taking the victim whole (`0x80004d78`) or putting it
back on its own bin (`0x8000491c`). `HeapAt` does not hold there, so the facts
the code owns are named instead of being read off a shape. -/
structure MDetach (C : MCtx) (Mt Mt' : Mem) (bins : Nat → List Nat) (i v : Nat) : Prop where
  bin : bins i = [v]
  fd : fdOf Mt' (binAt i) = some (binAt i)
  bk : bkOf Mt' (binAt i) = some (binAt i)
  agree : ∀ a, vsaFoot C.H a → ¬ (binAt i + 16 ≤ a ∧ a < binAt i + 32) → Mt'[a]? = Mt[a]?
  pres : ∀ a, vsaFoot C.H a → (Mt'[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt'[a]? = C.Mt0[a]?

/-- **`J_lr`** (`0x800048ec`): the last-remainder check. -/
theorem lr_check {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb31 : nb < 2 ^ 31)
    (hscan : bins 1 = [] → ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV →
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
  have B := Hp.heap.heap
  have ha4 := G.a4; have ha7 := G.a7; have ha6 := G.a6
  have hgeo := binAt_geo 1 (by unfold numBins; decide)
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hbinI := HH.bins_list 1 (by decide) (by unfold numBins; decide)
  have hring := (binList_iff_ring.1 hbinI).1
  have hnev := (binList_iff_ring.1 hbinI).2
  -- the bin's `fd` word
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
  have hEA : ((R 16) + sign_extend (m := 64) (0x020#12)).toNat = binAt 1 + 16 := by
    rw [ha6]; unfold binAt avAddr; rfl
  refine st_800048ec O.live ?_ ?_ ?_
  · rw [hEA]; unfold LdOK Vsa.Sim.tohostAddr binAt avAddr; omega
  · rw [hEA]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inl rfl)
  rw [show ldv .ld Mt ((R 16) + sign_extend (m := 64) (0x020#12)).toNat =
    BitVec.ofNat 64 first from bin_link_ld hEA hfd hfirstlt]
  refine st_800048f0 O.live ?_
  refine st_800048f4 O.live ?_
  sx_norm
  have ht4 : (2147593504#64 : BitVec 64) = BitVec.ofNat 64 (binAt 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold binAt avAddr; decide
  refine st_800048f8 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc ⊢
  · -- bin 1 is empty
    rw [ht4] at hc
    have hb : bins 1 = [] := by
      rcases hfirst with ⟨h1, _⟩ | h1
      · exact h1
      · exfalso
        have he := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfirstlt,
          Nat.mod_eq_of_lt (by omega)] at he
        exact hnev first (by rw [h1]; exact List.mem_cons_self) he
    refine hscan hb _ (((F.upd (by decide)).upd (by decide)).upd (by decide)) ⟨?_, ?_, ?_⟩ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · exact ha4
    · exact ha7
    · exact ha6
    · exact h8
  · -- the last remainder is bin 1's only member
    rw [ht4] at hc
    have hb : bins 1 = [first] := by
      rcases hfirst with ⟨_, rfl⟩ | h1
      · exact absurd rfl hc
      · exact h1
    obtain ⟨sz, hfree⟩ := freeAt_of_member HH (j := 1) (by decide)
      (by unfold numBins; decide) (by rw [hb]; exact List.mem_cons_self)
    have hbnd := HH.walk.chunk_bounds _ hfree
    have htle := HH.top_le; have hbrk := HH.brk_le
    obtain ⟨⟨hh, hhr, hhsz, hhlow⟩, _⟩ := HH.headers hfree
    simp only at hbnd hhr hhsz
    unfold heapStart at hbnd
    unfold heapEnd at hbrk
    have hhlt := Vsa.Sim.read64_lt _ _ _ hhr
    have hhfoot := foot_header B (.inr ⟨_, hfree, rfl⟩)
    simp only at hhfoot
    -- `ld t1,8(a5)`: the victim's header
    refine st_800048fc O.live ?_ ?_ ?_
    · sx_norm; unfold LdOK Vsa.Sim.tohostAddr; sx_addr
    · sx_norm; exact O.foot_at hhfoot _ (by sx_addr)
    sx_norm
    rw [ldv_at hhr _ (by sx_addr)]
    refine st_80004900 O.live ?_
    refine st_80004904 O.live ?_
    refine st_80004908 O.live ?_
    sx_norm
    have hszv : ((BitVec.ofNat 64 hh) &&& 18446744073709551612#64).toNat = sz := by
      rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt]
      unfold chunkSize at hhsz; omega
    have hnb62 : nb < 2 ^ 62 := by omega
    have hsz62 : sz < 2 ^ 62 := by omega
    have hcmp := lr_cmp (x := (BitVec.ofNat 64 hh) &&& 18446744073709551612#64) (y := R 14)
      hszv ha4 hsz62 hnb62
    refine st_8000490c O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc2 ⊢
    · -- the remainder is at least `nb + 32`: split it
      refine hsplit first sz hb hfree (hcmp.1.1 hc2) _
        (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact ha4
      · exact ha7
      · exact ha6
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · exact hszv
      · exact ha4
      · unfold binAt avAddr; rfl
      · exact h8
    · -- bin 1 is cleared and the victim taken off it
      have hlt32 : sz < nb + 32 := by
        have := hcmp.1
        omega
      have hEB : ((R 16) + sign_extend (m := 64) (0x028#12)).toNat = binAt 1 + 24 := by
        rw [ha6]; unfold binAt avAddr; rfl
      refine st_80004910 O.live ?_ ?_ ?_
      · sx_norm; rw [hEB]; unfold StOK Vsa.Sim.tohostAddr binAt avAddr; omega
      · sx_norm; rw [hEB]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inr rfl)
      sx_norm
      rw [hEB]
      refine st_80004914 O.live ?_ ?_ ?_
      · sx_norm; rw [hEA]; unfold StOK Vsa.Sim.tohostAddr binAt avAddr; omega
      · sx_norm; rw [hEA]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inl rfl)
      sx_norm
      rw [hEA]
      have hb1 : binAt 1 = 2147593504 := by unfold binAt avAddr; rfl
      have hwv : ((2147593504#64 : BitVec 64)).toNat = binAt 1 := by rw [hb1]; rfl
      have hD : MDetach C Mt (writeLog (writeLog Mt [(binAt 1 + 24, 8, 2147593504#64)])
          [(binAt 1 + 16, 8, 2147593504#64)]) bins 1 first := by
        refine ⟨hb, ?_, ?_, ?_, pres_store (pres_store Hp.pres),
          frame_store ?_ (frame_store ?_ Hp.frame)⟩
        · show read64 _ (binAt 1 + 16) = _
          rw [read64_store_hit, hwv]
        · show read64 _ (binAt 1 + 24) = _
          rw [read64_store_miss _ _ (by omega), read64_store_hit, hwv]
        · intro a _ hna
          rw [writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩),
            writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩)]
        · exact fun b h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩))
        · exact fun b h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩))
      refine st_80004918 O.live (fun hc3 => ?_) (fun hc3 => ?_) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3
      · -- the remainder is within 31 bytes of `nb`: take the victim whole
        refine hexact first sz hfree (hcmp.2.1 hc3) hlt32 _ _
          (((F.of_regs ?_ ?_ ?_ ?_).store (by omega)).store (by omega)) hD
          ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · exact hszv
        · exact ha4
        · exact hwv
      · -- the remainder is smaller than `nb`: put the victim back on its own bin
        refine hrebin first sz hfree (by have := hcmp.2; omega) _ _
          (((F.of_regs ?_ ?_ ?_ ?_).store (by omega)).store (by omega)) hD
          ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
          simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        · exact ha4
        · exact ha7
        · exact ha6
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · exact hszv
        · exact ha4
        · exact hwv
        · exact h8

/-- A footprint doubleword off bin `i`'s link words reads the same after the
detach. -/
theorem MDetach.read {C : MCtx} {Mt Mt' : Mem} {bins : Nat → List Nat} {i v : Nat}
    (D : MDetach C Mt Mt' bins i v) {a : Nat} (hf : ∀ k, k < 8 → vsaFoot C.H (a + k))
    (hoff : a + 8 ≤ binAt i + 16 ∨ binAt i + 32 ≤ a) : read64 Mt' a = read64 Mt a :=
  read64_agreeP (P := fun b => vsaFoot C.H b ∧ ¬ (binAt i + 16 ≤ b ∧ b < binAt i + 32))
    (fun b hb => D.agree b hb.1 hb.2) (fun k hk => ⟨hf k hk, by omega⟩)

/-- **The exact-fit last remainder** (`0x80004d78`): the victim is already off
bin 1 (`MDetach`) and the remainder is below `MINSIZE`, so the whole chunk is
returned. Set `PREV_INUSE` in the next header, unlock, and return `v + 16`. -/
theorem lr_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt Mt' : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb sz v : Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb)
    (hfree : FreeAt chunks v sz) (hle : nb ≤ sz)
    (F : MFrame C R Mt') (D : MDetach C Mt Mt' bins 1 v) (G : LRVictim nb sz v R) :
    AW C.live C.S C.Q 0x80004d78#64 R Mt' := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hb1 : binAt 1 = 2147593504 := by unfold binAt avAddr; rfl
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hbnd := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  have hroom := Hp.heap.heap.top_room
  obtain ⟨_, ⟨hd, hdr, hdpi⟩⟩ := HH.headers hfree
  simp only at hbnd hdr hdpi
  unfold heapStart at hbnd
  unfold heapEnd at hbrk
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hnx := foot_header B (HH.end_bnd hfree)
  simp only at hnx
  have ha5 := G.a5; have ht1 := G.t1
  have hs2 := F.sp; have hsal := O.sp.align
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have halv := hal0 _ hfree
  have hszal := (walk_sizes HH.walk _ hfree).1
  simp only at halv hszal
  have hdr' : read64 Mt' (v + sz + 8) = some hd := (D.read hnx (by omega)).trans hdr
  have hES : ((R 2) + sign_extend (m := 64) (0x008#12)).toNat = C.s.toNat - 96 + 8 := by
    rw [hs2]; sx_addr
  -- `add t1,a5,t1`: the next chunk
  refine st_80004d78 O.live ?_
  sx_norm
  have hEN : ((R 15) + (R 6) + 8#64).toNat = v + sz + 8 := by sx_addr
  -- `ld a4,8(t1)`: its header
  refine st_80004d7c O.live ?_ ?_ ?_
  · sx_norm; rw [hEN]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEN]; exact O.foot_at hnx _ rfl
  sx_norm
  rw [ldv_at hdr' _ hEN]
  refine st_80004d80 O.live ?_
  -- `sd a5,8(sp)`: spill the victim
  refine st_80004d84 O.live ?_ ?_ ?_
  · sx_norm; rw [hES]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hES]; exact O.stack (by unfold mHead; omega) (by omega)
  sx_norm
  rw [hES]
  refine st_80004d88 O.live ?_
  -- `sd a4,8(t1)`: the next header, with `PREV_INUSE`
  refine st_80004d8c O.live ?_ ?_ ?_
  · sx_norm; rw [hEN]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEN]; exact O.foot_at hnx _ rfl
  sx_norm
  rw [hEN]
  -- the next chunk is a chunk, not the top: `v` is free
  have hdeven : hd % 2 = 0 := by
    unfold prevInuse at hdpi
    simp only [beq_eq_false_iff_ne, ne_eq] at hdpi; omega
  have hd4 : hd % 4 < 2 := by
    obtain ⟨dch, hdmem, hda⟩ : ∃ d ∈ chunks, d.addr = v + sz := by
      rcases HH.end_bnd hfree with he | hd'
      · exfalso
        simp only at he
        rw [he, HH.top_header] at hdr
        cases hdr
        have := HH.top_size
        omega
      · simpa using hd'
    obtain ⟨hd0, hd0r, _, hd0low⟩ := walk_header HH.walk dch hdmem
    rw [hda, hdr] at hd0r
    cases hd0r
    exact hd0low
  have hOr : ((BitVec.ofNat 64 hd) ||| 1#64).toNat = hd + 1 := by
    have hoe := or_one_even (BitVec.ofNat 64 hd)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]; exact hdeven)
    rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at hoe
    rw [hoe, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  -- the heap after the take
  have hfd2 : fdOf (writeLog (writeLog Mt' [(C.s.toNat - 96 + 8, 8, R 15)])
      [(v + sz + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (binAt 1) = some (binAt 1) := by
    show read64 _ (binAt 1 + 16) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega)]
    exact D.fd
  have hbk2 : bkOf (writeLog (writeLog Mt' [(C.s.toNat - 96 + 8, 8, R 15)])
      [(v + sz + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (binAt 1) = some (binAt 1) := by
    show read64 _ (binAt 1 + 24) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega)]
    exact D.bk
  have hhdr2 : read64 (writeLog (writeLog Mt' [(C.s.toNat - 96 + 8, 8, R 15)])
      [(v + sz + 8, 8, BitVec.ofNat 64 hd ||| 1#64)]) (v + sz + 8) = some (hd + 1) := by
    rw [read64_store_hit, hOr]
  have hszf : ∀ h0, read64 Mt (v + sz + 8) = some h0 →
      chunkSize (hd + 1) = chunkSize h0 ∧ (hd + 1) % 4 < 2 := by
    intro h0 h0r
    rw [hdr] at h0r; cases h0r
    unfold chunkSize; omega
  have hpi : prevInuse (hd + 1) = true := by unfold prevInuse; simp only [beq_iff_eq]; omega
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hag : ∀ a, vsaFoot C.H a → ¬ TakeW (binAt 1) (binAt 1) (v + sz) a →
      (writeLog (writeLog Mt' [(C.s.toNat - 96 + 8, 8, R 15)])
        [(v + sz + 8, 8, BitVec.ofNat 64 hd ||| 1#64)])[a]? = Mt[a]? := by
    intro a ha hna
    unfold TakeW at hna
    have := hns a ha
    rw [writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩),
      writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩)]
    exact D.agree a ha (by omega)
  have hn8 : C.n.toNat + 8 ≤ sz := by have := hnb.fits; omega
  have hheap := PHeapAt.take Hp.heap (i := 1) (by decide) (by unfold numBins; decide)
    (pre := []) (post := []) (v := v) D.bin hfree rfl (n := C.n.toNat) hn8 rfl rfl
    hfd2 hbk2 hhdr2 hszf hpi hag
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) hn8
  simp only at hfr hal16
  have hnsN : v + sz + 8 < C.s.toNat - 256 ∨ C.s.toNat ≤ v + sz + 8 :=
    hns (v + sz + 8) (by have := hnx 0 (by omega); simpa using this)
  sx_run [8] O.live at 0x8000484c
  have ha0 : ((R 15) + 16#64).toNat = v + 16 := by sx_addr
  refine epi_8000484c O ?F (O.fin_take (v := v) ?_
    ⟨hfr, hal16, ⟨_, _, _, _, hheap, by omega⟩,
      pres_store (pres_store D.pres),
      frame_store (win_foot hnx) (frame_store (win_stack (a := C.s.toNat - 96 + 8) (w := 8)
        (by unfold mHead; omega) (by omega)) D.frame)⟩)
  case F =>
    refine MFrame.of_regs ((F.store (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  exact ha0

/-- **The last-remainder check with its exact-fit return.** `lr_check` with
`lr_take` closing the whole-chunk arm, so only the split (`0x80004da0`), the
re-binding (`0x8000491c`) and the block search (`0x80004be8`) remain. -/
theorem lr_last {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hscan : bins 1 = [] → ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV →
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
