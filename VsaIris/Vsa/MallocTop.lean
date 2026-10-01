import VsaIris.Vsa.MallocLR
import VsaIris.Vsa.HeapSplit
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.MallocGlue2

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem sltiV_eq_zero (a b : BitVec 64) : sltiV a b = 0#64 ↔ ¬ (a.toInt < b.toInt) := by
  unfold sltiV
  by_cases h : a.toInt < b.toInt <;>
    simp [LeanRV64DExecutable.Functions.zopz0zI_s, h,
      LeanRV64DExecutable.Functions.bool_to_bit, LeanRV64DExecutable.zero_extend,
      LeanRV64DExecutable.Functions.bool_bit_forwards, Sail.BitVec.zeroExtend]

theorem sub_toInt {x y : BitVec 64} {sz nb : Nat} (hx : x.toNat = sz) (hy : y.toNat = nb)
    (hle : nb ≤ sz) (hsz : sz < 2 ^ 62) : (x - y).toInt = ((sz - nb : Nat) : Int) := by
  have hxy : (x - y).toNat = sz - nb := by
    rw [BitVec.toNat_sub, hx, hy]; omega
  rw [BitVec.toInt_eq_toNat_cond, hxy, if_pos (by omega)]

structure TopRegs (nb top topsz : Nat) (R : Nat → BitVec 64) : Prop where
  a5 : (R 15).toNat = top
  t1 : (R 6).toNat = topsz
  a3 : R 13 = R 6 - R 14
  a4 : (R 14).toNat = nb

theorem or1_toNat {x : BitVec 64} {v : Nat} (hx : x.toNat = v) (he : v % 2 = 0) :
    (x ||| 1#64).toNat = v + 1 := by
  have hoe := or_one_even x (by rw [hx]; exact he)
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at hoe
  have hlt := x.isLt
  rw [hoe, BitVec.toNat_add, hx]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

structure SplitRegs (nb top rem : Nat) (R : Nat → BitVec 64) : Prop where
  a5 : (R 15).toNat = top
  a4 : (R 14).toNat = nb
  a3 : (R 13).toNat = rem
  a6 : R 16 = 0x8001ad10#64

theorem top_split {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : SplitRegs nb C.top0 (brkv - C.top0 - nb) R) (hnb : NbOK C.n nb)
    (hroom : C.top0 + nb + 32 ≤ brkv) :
    AW C.live C.S C.Q 0x80004bf0#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have ha4 := G.a4; have ha5 := G.a5
  have ha6 : (R 16).toNat = 2147593488 := by rw [G.a6]; rfl
  have hsal := O.sp.align; have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [F.sp]; sx_addr
  have htle := HH.top_le; have hbrk := HH.brk_le; have hstart := HH.walk.le
  have htop16 := HH.aligned.2; have hnb16 := hnb.al
  unfold heapStart at hstart; unfold heapEnd at hbrk
  have T : Rgn (vsaFoot C.H) (C.top0 + 8) (brkv - C.top0 - 8) := ⟨fun k hk =>
    foot_of_arena HH (by unfold heapStart; omega) (by unfold heapEnd; omega) fun c hc _ => by
      have := HH.walk.chunk_bounds c hc; omega⟩
  have Gl := globRgn C.H; have St := O.stackRgn
  rgn_step O.live at 0x80004830
  have ha3 := G.a3; have htsz := HH.top_size; have hnbP := hnb.eq
  have hnb32 := hnb.lo; have hn8 := hnb.fits; have htad : topAddr = 2147593504 := rfl
  have hoT := T.offStack Hp.disj (by omega); unfold mHead at hoT
  rgn_norm
  rw [show (R 15 + 8#64).toNat = C.top0 + 8 by rgn_arith,
    show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith,
    show (R 16 + 16#64).toNat = topAddr by rgn_arith,
    show (R 15 + R 14 + 8#64).toNat = C.top0 + nb + 8 by rgn_arith]
  obtain ⟨hfr, hal16⟩ := Hp.heap.topSplit_fresh (n := C.n.toNat) hn8 (by omega)
  refine epi_80004830 O ?F (O.fin_take (v := C.top0) ?_
    ⟨hfr, hal16, ⟨_, _, _, _, Hp.heap.topSplit hnb16 (by omega) hn8 (by omega)
        (by rd_log [or1_toNat ha4 (by omega)])
        (by rd_log [show (R 15 + R 14).toNat = C.top0 + nb by rgn_arith])
        (by rd_log [or1_toNat ha3 (by omega)]) fun a ha hw => ?A,
      by omega, Hp.live.mono fun c hc _ => List.mem_append_left _ hc⟩, ?_, ?_⟩)
  case F =>
    refine MFrame.of_regs ((((F.store (by omega)).store (by omega)).store
      (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;> reg_close []
  case A =>
    refine (by wl_win <;> first
      | exact .inl (by unfold SplitW; omega)
      | exact .inr fun hf => by have := offStack_pt Hp.disj hf; omega :
      WinAgree (fun a => SplitW C.top0 nb a ∨ ¬ vsaFoot C.H a) _ Mt) a ?_
    rintro (h | h) <;> contradiction
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rgn_arith
  all_goals simp only [writeLog_nest, List.cons_append, List.nil_append]
  · exact pres_log _ Hp.pres
  · exact frame_log (by log_in) Hp.frame

theorem top_path {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hext : brkv - C.top0 < nb + 32 → ∀ R', MFrame C R' Mt → LRRegs nb idx R' →
      TopRegs nb C.top0 (brkv - C.top0) R' → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004a48#64 R' Mt) :
    AW C.live C.S C.Q 0x80004a2c#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have ha4 := G.a4; have ha7 := G.a7; have ha6 := G.a6
  have ha6n : (R 16).toNat = 2147593488 := by rw [G.a6]; rfl
  have htle := HH.top_le; have hbrk := HH.brk_le; have hroom := Hp.heap.heap.top_room
  have htsz := HH.top_size; have htad : topAddr = 2147593504 := rfl
  unfold heapEnd at hbrk
  have Gl := globRgn C.H
  have T : Rgn (vsaFoot C.H) (C.top0 + 8) 8 := ⟨foot_header Hp.heap.heap (.inl rfl)⟩
  rgn_step O.live at 0x80004a30
  rgn_ld [HH.top_ptr]
  rgn_step O.live at 0x80004a34
  rgn_ld [HH.top_header]
  rgn_run O.live at 0x80004a3c
  have htsizev : ((BitVec.ofNat 64 (brkv - C.top0 + 1)) &&& 18446744073709551612#64).toNat =
      brkv - C.top0 := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  refine (step% st 0x80004a3c) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  ·
    rw [htsizev, ha4] at hc
    refine hext (by omega) _ (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ <;>
      reg_close [ha4, ha7, ha6, htsizev, h8]
  · rw [htsizev, ha4] at hc
    have hsub : ((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14).toInt
        = ((brkv - C.top0 - nb : Nat) : Int) := sub_toInt htsizev ha4 (by omega) (by omega)
    have h32 : ((32#64 : BitVec 64)).toInt = (32 : Int) := by decide
    refine (step% st 0x80004a40) O.live ?_
    sx_norm
    refine (step% st 0x80004a44) O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, sltiV_eq_zero, Decidable.not_not,
        hsub, h32] at hc2
    ·
      have hdt : ((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14).toNat
          = brkv - C.top0 - nb := by
        rw [BitVec.toNat_sub, htsizev, ha4]; omega
      refine top_split O (F.of_regs ?_ ?_ ?_ ?_) Hp ⟨?_, ?_, ?_, ?_⟩ hnb (by omega) <;>
        reg_close [ha4, hdt, ha6]
    ·
      refine hext (by omega) _ (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ <;>
        reg_close [ha4, ha7, ha6, htsizev, h8]

theorem sraiw2_toNat {x : BitVec 64} {i : Nat} (hx : x.toNat = i) (hi : i < 2 ^ 31) :
    (BitVec.signExtend 64
      (shift_bits_right_arith (BitVec.extractLsb 31 0 x) (2#5))).toNat = i / 4 := by
  have he : (BitVec.extractLsb 31 0 x).toNat = i := by
    rw [BitVec.extractLsb_toNat, hx]; simp; omega
  have hm : (BitVec.extractLsb 31 0 x).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, he]; omega
  have hsr : shift_bits_right_arith (BitVec.extractLsb 31 0 x) (2#5)
      = (BitVec.extractLsb 31 0 x) >>> 2 := by
    show BitVec.sshiftRight _ (BitVec.toNatInt (2#5)) = _
    rw [BitVec.sshiftRight_eq_of_msb_false hm]
    rfl
  rw [hsr]
  have hn : ((BitVec.extractLsb 31 0 x) >>> 2).toNat = i / 4 := by
    rw [BitVec.toNat_ushiftRight, he, Nat.shiftRight_eq_div_pow]
  have hm2 : ((BitVec.extractLsb 31 0 x) >>> 2).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hn]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm2, BitVec.toNat_setWidth, hn]
  omega

theorem shl_one {y : BitVec 64} {j : Nat} (hy : y.toNat = j) (hj : j < 64) :
    ((1#64 : BitVec 64) <<< (BitVec.extractLsb 5 0 y).toNat).toNat = 2 ^ j := by
  have he : (BitVec.extractLsb 5 0 y).toNat = j := by
    rw [BitVec.extractLsb_toNat, hy]; simp; omega
  rw [BitVec.toNat_shiftLeft, he]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hlt : (2 : Nat) ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (a := 2) (by omega) hj
  omega

theorem bb_entry {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx bb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hidx : idx < numBins)
    (hbb : read64 Mt binblocksAddr = some bb) (h11 : (R 11).toNat = bb)
    (h29 : (R 29).toNat = binAt 1)
    (htop : ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004a2c#64 R' Mt)
    (hblocks : 2 ^ (idx / 4) ≤ bb →
      ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV → (R' 29).toNat = binAt 1 →
        (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
        AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x80004968#64 R Mt := by
  have ha4 := G.a4; have ha7 := G.a7; have ha6 := G.a6
  unfold numBins at hidx
  rgn_step O.live at 0x80004974
  sx_norm
  have ha5 := sraiw2_toNat ha7 (by omega)
  have ha0 := shl_one ha5 (by omega)
  refine (step% st 0x80004974) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  ·
    exact htop _ (F.of_regs rfl rfl rfl rfl) ⟨ha4, ha7, ha6⟩ h8
  · rw [ha0, h11] at hc
    exact hblocks (by omega) _ (F.of_regs rfl rfl rfl rfl) ⟨ha4, ha7, ha6⟩ h8 h29 h11 ha0

theorem bb_check {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hidx : idx < numBins)
    (h29 : (R 29).toNat = binAt 1)
    (htop : ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004a2c#64 R' Mt)
    (hblocks : ∀ bb, read64 Mt binblocksAddr = some bb → 2 ^ (idx / 4) ≤ bb →
      ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV → (R' 29).toNat = binAt 1 →
        (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
        AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x80004be8#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have ha4 := G.a4; have ha7 := G.a7; have ha6 := G.a6
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mt binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have ha6n : (R 16).toNat = 2147593488 := by rw [G.a6]; rfl
  have Gl := globRgn C.H; have hbbA : binblocksAddr = 2147593496 := rfl
  rgn_step O.live at 0x80004968
  rgn_ld [hbb]
  refine bb_entry O (F.upd (by decide)) Hp ⟨?_, ?_, ?_⟩ ?_ hidx hbb ?_ ?_ htop (hblocks bb hbb) <;>
    reg_close [ha4, ha7, ha6, h8, h29,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hbb)]]

theorem bb_top {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hidx : idx < numBins)
    (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hext : brkv - C.top0 < nb + 32 → ∀ R', MFrame C R' Mt → LRRegs nb idx R' →
      TopRegs nb C.top0 (brkv - C.top0) R' → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004a48#64 R' Mt)
    (h29 : (R 29).toNat = binAt 1)
    (hblocks : ∀ bb, read64 Mt binblocksAddr = some bb → 2 ^ (idx / 4) ≤ bb →
      ∀ R', MFrame C R' Mt → LRRegs nb idx R' → R' 8 = reentV → (R' 29).toNat = binAt 1 →
        (R' 11).toNat = bb → (R' 10).toNat = 2 ^ (idx / 4) →
        AW C.live C.S C.Q 0x80004978#64 R' Mt) :
    AW C.live C.S C.Q 0x80004be8#64 R Mt :=
  bb_check O F Hp G h8 hidx h29
    (fun R' F' G' h8' => top_path O F' Hp G' h8' hnb hnb31 hext) hblocks

end VsaIris.VsaHeap
