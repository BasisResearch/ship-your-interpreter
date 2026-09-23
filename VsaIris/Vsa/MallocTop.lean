import VsaIris.Vsa.MallocLR
import VsaIris.Vsa.HeapSplit

/-!
# `_malloc_r`'s top path

`0x80004a2c` is reached when no bin can serve the request. The top chunk is
read and measured; if it holds `nb` with `MINSIZE` to spare the top is split
(`0x80004bf0`) and the victim returned, otherwise `malloc_extend_top` runs
(`0x80004a48`).

`top_split` proves the split arm end to end over `PHeapAt.topSplit`; the
extension is the one residual.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `slti`'s result is zero exactly when the comparison fails. -/
theorem sltiV_eq_zero (a b : BitVec 64) : sltiV a b = 0#64 ↔ ¬ (a.toInt < b.toInt) := by
  unfold sltiV
  by_cases h : a.toInt < b.toInt <;>
    simp [LeanRV64DExecutable.Functions.zopz0zI_s, h,
      LeanRV64DExecutable.Functions.bool_to_bit, LeanRV64DExecutable.zero_extend,
      LeanRV64DExecutable.Functions.bool_bit_forwards, Sail.BitVec.zeroExtend]

/-- A difference of two small unsigned words, as a signed value. -/
theorem sub_toInt {x y : BitVec 64} {sz nb : Nat} (hx : x.toNat = sz) (hy : y.toNat = nb)
    (hle : nb ≤ sz) (hsz : sz < 2 ^ 62) : (x - y).toInt = ((sz - nb : Nat) : Int) := by
  have hxy : (x - y).toNat = sz - nb := by
    rw [BitVec.toNat_sub, hx, hy]; omega
  rw [BitVec.toInt_eq_toNat_cond, hxy, if_pos (by omega)]

/-- The registers at `malloc_extend_top`'s entry (`0x80004a48`): the top in
`a5`, its size in `t1`, the shortfall `t1 - a4` in `a3`, the request in `a4`. -/
structure TopRegs (nb top topsz : Nat) (R : Nat → BitVec 64) : Prop where
  a5 : (R 15).toNat = top
  t1 : (R 6).toNat = topsz
  a3 : R 13 = R 6 - R 14
  a4 : (R 14).toNat = nb

/-- **The top path** (`0x80004a2c`): the top chunk is measured and either
split (proved here, through the return) or grown by `malloc_extend_top`. -/
theorem top_path {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (h8 : R 8 = reentV) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hext : brkv - C.top0 < nb + 32 → ∀ R', MFrame C R' Mt → LRRegs nb idx R' →
      TopRegs nb C.top0 (brkv - C.top0) R' → R' 8 = reentV →
      AW C.live C.S C.Q 0x80004a48#64 R' Mt) :
    AW C.live C.S C.Q 0x80004a2c#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have ha4 := G.a4; have ha7 := G.a7; have ha6 := G.a6
  have hs2 := F.sp; have hsal := O.sp.align
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have htle := HH.top_le; have hbrk := HH.brk_le
  have hstart := HH.walk.le
  have hroom := B.top_room
  have htsz := HH.top_size
  have htop16 := HH.aligned.2
  have htptr := HH.top_ptr
  have hthdr := HH.top_header
  unfold heapStart at hstart
  unfold heapEnd at hbrk
  have htoplt : C.top0 < 2 ^ 64 := by omega
  have hEtop : ((R 16) + sign_extend (m := 64) (0x010#12)).toNat = topAddr := by
    rw [ha6]; unfold topAddr avAddr; rfl
  -- `ld a5,16(a6)`: the top chunk
  refine st_80004a2c O.live ?_ ?_ ?_
  · rw [hEtop]; unfold LdOK Vsa.Sim.tohostAddr topAddr avAddr; omega
  · rw [hEtop]; exact O.glob (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)
  rw [ldv_at htptr _ hEtop]
  -- `ld a2,8(a5)`: the top's header
  have hEh : ((BitVec.ofNat 64 C.top0) + sign_extend (m := 64) (0x008#12)).toNat =
      C.top0 + 8 := by sx_addr
  refine st_80004a30 O.live ?_ ?_ ?_
  · sx_norm; rw [hEh]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEh]; exact O.foot_at (foot_header B (.inl rfl)) _ rfl
  sx_norm
  rw [ldv_at hthdr _ hEh]
  refine st_80004a34 O.live ?_
  refine st_80004a38 O.live ?_
  sx_norm
  have htsizev : ((BitVec.ofNat 64 (brkv - C.top0 + 1)) &&& 18446744073709551612#64).toNat =
      brkv - C.top0 := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  refine st_80004a3c O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- the top is smaller than the request
    rw [htsizev, ha4] at hc
    refine hext (by omega) _ (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact ha4
    · exact ha7
    · exact ha6
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · exact htsizev
    · exact ha4
    · exact h8
  · rw [htsizev, ha4] at hc
    have hsub : ((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14).toInt
        = ((brkv - C.top0 - nb : Nat) : Int) := sub_toInt htsizev ha4 (by omega) (by omega)
    have h32 : ((32#64 : BitVec 64)).toInt = (32 : Int) := by decide
    refine st_80004a40 O.live ?_
    sx_norm
    refine st_80004a44 O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, sltiV_eq_zero, Decidable.not_not,
        hsub, h32] at hc2
    · -- the remainder is at least `MINSIZE`: split the top
      have hfootTop : ∀ a, C.top0 + 8 ≤ a → a < brkv → vsaFoot C.H a := by
        intro a h1 h2
        refine .inr ⟨by unfold heapStart; omega, by unfold heapEnd; omega, fun e he hin => ?_⟩
        obtain ⟨c, hc, _, hlo1, hhi1⟩ := HH.live e he
        have := HH.walk.chunk_bounds c hc
        unfold InExt at hin
        omega
      have hnb16 : nb % 16 = 0 := hnb.al
      have hnb32 : 32 ≤ nb := hnb.lo
      have hor_nb : ((R 14) ||| 1#64).toNat = nb + 1 := by
        have hoe := or_one_even (R 14) (by rw [ha4]; omega)
        rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at hoe
        rw [hoe, BitVec.toNat_add, ha4]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
        Classical.byContradiction fun hcx => Hp.disj a (by unfold mHead; omega) (by omega) ha
      have hnsT := hns (C.top0 + 8) (hfootTop _ (by omega) (by omega))
      have hnsR := hns (C.top0 + nb + 8) (hfootTop _ (by omega) (by omega))
      -- `ori a2,a4,1; sd a2,8(a5)`
      refine st_80004bf0 O.live ?_
      refine st_80004bf4 O.live ?_ ?_ ?_
      · sx_norm; rw [hEh]; unfold StOK Vsa.Sim.tohostAddr; omega
      · sx_norm; rw [hEh]
        exact O.foot (fun k hk => hfootTop _ (by omega) (by omega))
      sx_norm
      rw [hEh]
      -- `add a4,a5,a4; sd a5,8(sp)`
      refine st_80004bf8 O.live ?_
      sx_norm
      have hEs : ((R 2) + 8#64).toNat = C.s.toNat - 96 + 8 := by rw [hs2]; sx_addr
      refine st_80004bfc O.live ?_ ?_ ?_
      · sx_norm; rw [hEs]; unfold StOK Vsa.Sim.tohostAddr; omega
      · sx_norm; rw [hEs]; exact O.stack (by unfold mHead; omega) (by omega)
      sx_norm
      rw [hEs]
      -- `ori a3,a3,1; sd a4,16(a6)`
      refine st_80004c00 O.live ?_
      refine st_80004c04 O.live ?_ ?_ ?_
      · sx_norm; rw [hEtop]; unfold StOK Vsa.Sim.tohostAddr topAddr avAddr; omega
      · sx_norm; rw [hEtop]
        exact O.glob (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)
      sx_norm
      rw [hEtop]
      refine st_80004c08 O.live ?_
      sx_norm
      have hEr : ((BitVec.ofNat 64 C.top0) + (R 14) + 8#64).toNat = C.top0 + nb + 8 := by sx_addr
      refine st_80004c0c O.live ?_ ?_ ?_
      · sx_norm; rw [hEr]; unfold StOK Vsa.Sim.tohostAddr; omega
      · sx_norm; rw [hEr]
        exact O.foot (fun k hk => hfootTop _ (by omega) (by omega))
      sx_norm
      rw [hEr]
      have hdt : ((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14).toNat
          = brkv - C.top0 - nb := by
        rw [BitVec.toNat_sub, htsizev, ha4]; omega
      have hor_rem : (((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14)
          ||| 1#64).toNat = brkv - C.top0 - nb + 1 := by
        have hoe := or_one_even _ (by rw [hdt]; omega)
        rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl] at hoe
        rw [hoe, BitVec.toNat_add, hdt]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hnewtop : ((BitVec.ofNat 64 C.top0) + (R 14)).toNat = C.top0 + nb := by sx_addr
      have htad : topAddr = 2147593504 := by unfold topAddr avAddr; rfl
      have hvic : read64 (writeLog (writeLog (writeLog (writeLog Mt
          [(C.top0 + 8, 8, R 14 ||| 1#64)]) [(C.s.toNat - 96 + 8, 8, BitVec.ofNat 64 C.top0)])
          [(topAddr, 8, BitVec.ofNat 64 C.top0 + R 14)])
          [(C.top0 + nb + 8, 8,
            (BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14 ||| 1#64)])
          (C.top0 + 8) = some (nb + 1) := by
        rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
          read64_store_miss _ _ (by omega), read64_store_hit, hor_nb]
      have htopw : read64 (writeLog (writeLog (writeLog (writeLog Mt
          [(C.top0 + 8, 8, R 14 ||| 1#64)]) [(C.s.toNat - 96 + 8, 8, BitVec.ofNat 64 C.top0)])
          [(topAddr, 8, BitVec.ofNat 64 C.top0 + R 14)])
          [(C.top0 + nb + 8, 8,
            (BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14 ||| 1#64)])
          topAddr = some (C.top0 + nb) := by
        rw [read64_store_miss _ _ (by omega), read64_store_hit, hnewtop]
      have hremw : read64 (writeLog (writeLog (writeLog (writeLog Mt
          [(C.top0 + 8, 8, R 14 ||| 1#64)]) [(C.s.toNat - 96 + 8, 8, BitVec.ofNat 64 C.top0)])
          [(topAddr, 8, BitVec.ofNat 64 C.top0 + R 14)])
          [(C.top0 + nb + 8, 8,
            (BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) - R 14 ||| 1#64)])
          (C.top0 + nb + 8) = some (brkv - C.top0 - nb + 1) := by
        rw [read64_store_hit, hor_rem]
      have hag : ∀ a, vsaFoot C.H a → ¬ SplitW C.top0 nb a →
          (writeLog (writeLog (writeLog (writeLog Mt
            [(C.top0 + 8, 8, R 14 ||| 1#64)]) [(C.s.toNat - 96 + 8, 8, BitVec.ofNat 64 C.top0)])
            [(topAddr, 8, BitVec.ofNat 64 C.top0 + R 14)])
            [(C.top0 + nb + 8, 8,
              (BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64)
                - R 14 ||| 1#64)])[a]? = Mt[a]? := by
        intro a ha hna
        unfold SplitW at hna
        have := hns a ha
        rw [writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩),
          writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩),
          writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩),
          writeLog_out _ _ _ (by simp only [OutL]; exact ⟨by omega, trivial⟩)]
      have hn8 : C.n.toNat + 8 ≤ nb := hnb.fits
      have hheap := Hp.heap.topSplit hnb16 (by omega) hn8 (by omega) hvic htopw hremw hag
      obtain ⟨hfr, hal16⟩ := Hp.heap.topSplit_fresh (n := C.n.toNat) hn8 (by omega)
      have hnbP : nb = physSize C.n.toNat := hnb.eq
      sx_run [8] O.live at 0x80004830
      have ha0 : ((BitVec.ofNat 64 C.top0) + 16#64).toNat = C.top0 + 16 := by sx_addr
      refine epi_80004830 O ?F (O.fin_ok ?fr ?al ?heap
        (pres_store (pres_store (pres_store (pres_store Hp.pres))))
        (frame_store (fun b h1 h2 => .inl (hfootTop b (by omega) (by omega)))
          (frame_store (fun b h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩)))
            (frame_store (win_stack (a := C.s.toNat - 96 + 8) (w := 8)
                (by unfold mHead; omega) (by omega))
              (frame_store (fun b h1 h2 => .inl (hfootTop b (by omega) (by omega)))
                Hp.frame)))))
      case F =>
        refine MFrame.of_regs ((((F.store (by omega)).store (by omega)).store
          (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;>
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]
      case fr => simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [ha0]; exact hfr
      case al => simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [ha0]; exact hal16
      case heap =>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [ha0]
        exact ⟨_, _, _, _, hheap, by omega⟩
    · -- the remainder is too small: grow the top
      refine hext (by omega) _ (F.of_regs ?_ ?_ ?_ ?_) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact ha4
      · exact ha7
      · exact ha6
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · exact htsizev
      · exact ha4
      · exact h8

end VsaIris.VsaHeap
