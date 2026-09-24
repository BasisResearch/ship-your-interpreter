import VsaIris.Vsa.FreePaths
import VsaIris.Vsa.Sbrk

/-!
# `_malloc_trim_r`

`_free_r` calls `_malloc_trim_r(reent, 0)` when the merged top reaches the
trim threshold. It releases the whole pages above the top's first page
(`extra = ((topsize + 4063) / 4096 - 1) * 4096`) when there are any and the
break is where the top ends: `sbrk(0)` then `sbrk(-extra)`, which cannot fail.
The top keeps its address; its header and the break move down
(`PHeapAt.topResize`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The pages `_malloc_trim_r` releases from a top of size `ts`. -/
def trimExtra (ts : Nat) : Nat := ((ts + 4063) / 4096 - 1) * 4096

theorem trimExtra_le {ts : Nat} (h16 : ts % 16 = 0) (h : 4096 ≤ trimExtra ts) :
    trimExtra ts + 48 ≤ ts := by
  unfold trimExtra at *; omega

/-- The extra's word as the code forms it. -/
theorem trimE_word {x : BitVec 64} {t : Nat} (hx : x.toNat = t + 4063) (ht : t < 2 ^ 40) :
    ((x >>> 12 + 18446744073709551615#64) <<< 12).toNat =
      (if (t + 4063) / 4096 = 0 then 2 ^ 64 - 4096 else trimExtra t) := by
  have hs : (x >>> 12).toNat = (t + 4063) / 4096 := by
    rw [BitVec.toNat_ushiftRight, hx, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, hs, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  unfold trimExtra
  split <;> omega

/-- `_malloc_trim_r` trims exactly when the extra is at least a page. -/
theorem trimE {x : BitVec 64} {t : Nat} (hx : x.toNat = t + 4063) (ht : t < 2 ^ 40) :
    ((x >>> 12 + 18446744073709551615#64) <<< 12).toInt < (4096#64).toInt ↔ trimExtra t < 4096 := by
  rw [BitVec.toInt_eq_toNat_cond, trimE_word hx ht, show (4096#64 : BitVec 64).toInt = 4096 from rfl]
  unfold trimExtra
  split <;> split <;> omega

/-- The heap through a store to the stack window. -/
theorem PHeapAt.store_stack {C : MCtx} {M : Mem} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt M C.H top brkv chunks bins)
    (hd : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a) {a w : Nat} {v : BitVec 64}
    (h1 : C.s.toNat - mHead ≤ a) (h2 : a + w ≤ C.s.toNat) :
    PHeapAt (writeLog M [(a, w, v)]) C.H top brkv chunks bins :=
  h.transport_read fun x hx => by
    have ho : OutL [(a, w, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd x (by omega) (by omega) hx.1, trivial⟩
    rw [writeLog_out _ _ _ ho]

/-- The state at `_malloc_trim_r`'s call (`0x80007574`): `_free_r`'s frame,
the heap with the top `Y` below the entry top, and the call's arguments. -/
structure TrimIn (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) (Y brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  frame : FFrame C R Mt
  heap : PHeapAt Mt C.H Y brkv chunks bins
  top_le : Y ≤ C.top0
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?
  a0 : R 10 = reentV
  a1 : (R 11).toNat = 0
  ra : R 1 = 0x80007578#64
  s0 : R 8 = reentV

/-- The state inside `_malloc_trim_r` (after its prologue): the heap, the
caller's frame slots, the spilled registers in its 48-byte frame, and the
top `Y` in `s3`'s `av`, its size in `s1`, the extra in `s0`. -/
structure TrimSt (C : MCtx) (R : Nat → BitVec 64) (M : Mem) (Y brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt M C.H Y brkv chunks bins
  top_le : Y ≤ C.top0
  pres : ∀ a, vsaFoot C.H a → (M[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → M[a]? = C.Mt0[a]?
  fs0 : read64 M (C.s.toNat - 32 + 16) = some (C.rv0 8).toNat
  fra : read64 M (C.s.toNat - 32 + 24) = some C.r.toNat
  sra : read64 M (C.s.toNat - 80 + 40) = some 0x80007578
  ss0 : read64 M (C.s.toNat - 80 + 32) = some reentV.toNat
  ss1 : read64 M (C.s.toNat - 80 + 24) = some (C.rv0 9).toNat
  ss2 : read64 M (C.s.toNat - 80 + 16) = some (C.rv0 18).toNat
  ss3 : read64 M (C.s.toNat - 80 + 8) = some (C.rv0 19).toNat
  sp : R 2 = C.s + 18446744073709551536#64
  s2 : R 18 = reentV
  s3 : R 19 = 0x8001ad10#64
  s1 : (R 9).toNat = brkv - Y

/-- **`_malloc_trim_r`'s head** (`0x8000722c`): the frame, the lock, the top
and its size, and the extra; no whole page to release goes to the return
(`0x8000729c`), otherwise to `sbrk(0)` (`0x80007284`). -/
theorem trim_head {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {Y brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (T : TrimIn C R Mt Y brkv chunks bins)
    (hno : ∀ R' M, TrimSt C R' M Y brkv chunks bins → AW C.live C.S C.Q 0x8000729c#64 R' M)
    (hyes : ∀ R' M, TrimSt C R' M Y brkv chunks bins → (R' 8).toNat = trimExtra (brkv - Y) →
      4096 ≤ trimExtra (brkv - Y) → AW C.live C.S C.Q 0x80007284#64 R' M) :
    AW C.live C.S C.Q 0x8000722c#64 R Mt := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := T.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 32 := by
    rw [hs2, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  sx_run [30] O.live at 0x80007258
  rw [show (R 2 + 18446744073709551568#64 + 32#64).toNat = C.s.toNat - 80 + 32 by sx_addr,
    show (R 2 + 18446744073709551568#64 + 24#64).toNat = C.s.toNat - 80 + 24 by sx_addr,
    show (R 2 + 18446744073709551568#64 + 16#64).toNat = C.s.toNat - 80 + 16 by sx_addr,
    show (R 2 + 18446744073709551568#64 + 8#64).toNat = C.s.toNat - 80 + 8 by sx_addr,
    show (R 2 + 18446744073709551568#64 + 40#64).toNat = C.s.toNat - 80 + 40 by sx_addr]
  have hd := T.disj
  have Hp1 := ((((T.heap.store_stack hd (a := C.s.toNat - 80 + 32) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack hd (a := C.s.toNat - 80 + 24) (w := 8) (v := R 9) (by unfold mHead; omega)
    (by omega)).store_stack hd (a := C.s.toNat - 80 + 16) (w := 8) (v := R 18) (by unfold mHead; omega)
    (by omega)).store_stack hd (a := C.s.toNat - 80 + 8) (w := 8) (v := R 19) (by unfold mHead; omega)
    (by omega)).store_stack hd (a := C.s.toNat - 80 + 40) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [(C.s.toNat - 80 + 32, 8, R 8)]) [(C.s.toNat - 80 + 24, 8, R 9)]) [(C.s.toNat - 80 + 16, 8, R 18)])
    [(C.s.toNat - 80 + 8, 8, R 19)]) [(C.s.toNat - 80 + 40, 8, R 1)] = M1 at Hp1 ⊢
  have HH := Hp1.heap.heap
  have htp := HH.top_ptr; have hth := HH.top_header
  have htle := HH.top_le; have hbrk := HH.brk_le; have htsz := HH.top_size
  have hroom := Hp1.heap.top_room
  unfold heapEnd at hbrk
  have hlo' := HH.walk.le; unfold heapStart at hlo'
  sx_run [1] O.live at 0x8000725c
  rw [ldv_at htp 2147593504 (by unfold topAddr avAddr; rfl)]
  refine st_8000725c O.live ?_
  have hYlt : Y < 2 ^ 64 := by omega
  have hEY : (BitVec.ofNat 64 Y + sign_extend (m := 64) (0x008#12)).toNat = Y + 8 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hYlt]; simp; omega
  have hYf := fun k hk => foot_header Hp1.heap (.inl rfl) k hk
  refine st_80007260 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEY]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEY]; exact O.foot hYf
  rw [hEY, ldv_at hth _ rfl]
  refine st_80007264 O.live ?_
  refine st_80007268 O.live ?_
  refine st_8000726c O.live ?_
  refine st_80007270 O.live ?_
  refine st_80007274 O.live ?_
  refine st_80007278 O.live ?_
  refine st_8000727c O.live ?_
  sx_norm
  have hts : (BitVec.ofNat 64 (brkv - Y + 1) &&& 18446744073709551612#64).toNat = brkv - Y := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hx : ((BitVec.ofNat 64 (brkv - Y + 1) &&& 18446744073709551612#64) + 2047#64 + 2016#64 - R 11).toNat
      = brkv - Y + 4063 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, hts, T.a1]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  -- the state after the prologue
  have F := T.frame
  have hS : ∀ R' : Nat → BitVec 64, R' 2 = R 2 + 18446744073709551568#64 → R' 18 = R 10 →
      R' 19 = 2147593488#64 → (R' 9).toNat = brkv - Y → TrimSt C R' M1 Y brkv chunks bins := by
    intro R' h2 h18 h19 h9
    rw [← hM1] at Hp1 ⊢
    refine ⟨Hp1, T.top_le, fun a ha => ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h9⟩
    · exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
        (writeLog_present _ _ _ (writeLog_present _ _ _ (T.pres a ha)))))
    · exact frame_store (win_stack (by unfold mHead; omega) (by omega))
        (frame_store (win_stack (by unfold mHead; omega) (by omega))
          (frame_store (win_stack (by unfold mHead; omega) (by omega))
            (frame_store (win_stack (by unfold mHead; omega) (by omega))
              (frame_store (win_stack (by unfold mHead; omega) (by omega)) T.frameM))))
    · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
        rd_miss (by omega)]; exact F.s0
    · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
        rd_miss (by omega)]; exact F.ra
    · rw [read64_store_hit, T.ra]; rfl
    · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
        read64_store_hit, T.s0]
    · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit, F.s1]
    · rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, F.s2]
    · rw [rd_miss (by omega), read64_store_hit, F.s3]
    · rw [h2, hs2]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · rw [h18, T.a0]
    · rw [h19]
  refine st_80007280 O.live (fun hlt => ?_) (fun hge => ?_)
  · -- no whole page to release
    exact hno _ _ (hS _ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hts))
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hge
    have hyes2 : 4096 ≤ trimExtra (brkv - Y) := by
      have := mt (trimE hx (by omega)).2 hge; omega
    have hE := trimE_word hx (by omega)
    rw [if_neg (by unfold trimExtra at hyes2; omega)] at hE
    exact hyes _ _ (hS _ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hts))
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hE) hyes2

/-- **`_malloc_trim_r`'s epilogue** (`0x8000729c`, from any `TrimSt`): release
the lock, restore the frame and return to `_free_r`. -/
theorem trim_ret {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {M : Mem} {Y brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (S : TrimSt C R M Y brkv chunks bins)
    (hk : ∀ R' M', FFrame C R' M' → R' 8 = reentV → FDone C M' → AW C.live C.S C.Q 0x80007578#64 R' M') :
    AW C.live C.S C.Q 0x8000729c#64 R M := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := S.sp
  have hs2n : (R 2).toNat = C.s.toNat - 80 := by
    rw [hs2, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have l40 := ldv_at S.sra (R 2 + sign_extend (m := 64) (0x028#12)).toNat (by sx_norm; rw [BitVec.toNat_add, hs2n]; simp; omega)
  have l32 := ldv_at S.ss0 (R 2 + sign_extend (m := 64) (0x020#12)).toNat (by sx_norm; rw [BitVec.toNat_add, hs2n]; simp; omega)
  have l24 := ldv_at S.ss1 (R 2 + sign_extend (m := 64) (0x018#12)).toNat (by sx_norm; rw [BitVec.toNat_add, hs2n]; simp; omega)
  have l16 := ldv_at S.ss2 (R 2 + sign_extend (m := 64) (0x010#12)).toNat (by sx_norm; rw [BitVec.toNat_add, hs2n]; simp; omega)
  have l8 := ldv_at S.ss3 (R 2 + sign_extend (m := 64) (0x008#12)).toNat (by sx_norm; rw [BitVec.toNat_add, hs2n]; simp; omega)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at l40 l32 l24 l16 l8
  sx_run [12] O.live at 0x800072a4
  sx_run [12] O.live
  all_goals simp only [l40, l32, l24, l16, l8]
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide))
  refine hk _ M ⟨?_, S.fs0, S.fra, ?_, ?_, ?_⟩ ?_ ⟨⟨_, _, _, _, S.heap, S.top_le⟩, S.pres, S.frameM⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [hs2]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

/-- The trim state through a `_sbrk_r` call that keeps the break. -/
theorem TrimSt.sbrk {C : MCtx} {R R' : Nat → BitVec 64} {M M' : Mem} {Y brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (S : TrimSt C R M Y brkv chunks bins)
    (hsp : (R 2).toNat = C.s.toNat - 80) (hs : 256 ≤ C.s.toNat) (P : SbrkPost R R' M M' brkv)
    (h2 : R' 2 = R 2) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) (h9 : R' 9 = R 9) :
    TrimSt C R' M' Y brkv chunks bins := by
  have HH := S.heap.heap.heap
  have hlo := S.disj
  have hag : ∀ a, ¬ SbrkW (R 2).toNat a → M'[a]? = M[a]? := P.agree
  rw [hsp] at hag
  have hbrk := HH.brk
  have hbb := bytes_of_read64_eq hbrk P.brk
  have key : ∀ a, vsaFoot C.H a → ¬ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) → ¬ (0x8001b538 ≤ a ∧ a < 0x8001b53c) →
      M'[a]? = M[a]? := by
    intro a ha h1 h2
    by_cases hb : brkAddr ≤ a ∧ a < brkAddr + 8
    · have := hbb (a - brkAddr) (by omega); rwa [show brkAddr + (a - brkAddr) = a by omega] at this
    · refine hag a fun hw => ?_
      unfold SbrkW at hw
      rcases hw with hw | hw | hw | hw
      · exact S.disj a (by unfold mHead; omega) (by omega) ha
      · exact hb hw
      · exact h1 hw
      · exact h2 hw
  have hslot : ∀ a, C.s.toNat - 80 ≤ a → a < C.s.toNat → M'[a]? = M[a]? := fun a ha1 ha2 => hag a fun hw => by
    unfold SbrkW brkAddr at hw
    rcases hw with hw | hw | hw | hw
    · omega
    · exact S.disj a (by unfold mHead; omega) ha2 (.inl (by unfold allocGlobal InRange; omega))
    · exact S.disj a (by unfold mHead; omega) ha2 (.inl (by unfold allocGlobal InRange; omega))
    · exact S.disj a (by unfold mHead; omega) ha2 (.inl (by unfold allocGlobal InRange; omega))
  have rslot : ∀ a, C.s.toNat - 80 ≤ a → a + 8 ≤ C.s.toNat → read64 M' a = read64 M a :=
    fun a h1 h2 => read64_keep fun k hk => hslot _ (by omega) (by omega)
  refine ⟨S.heap.transport_read fun a ha => (key a ha.1 (fun h => ha.2.2 h) (fun h => ha.2.1 h)).symm,
    S.top_le, fun a ha => P.pres a (S.pres a ha), S.disj, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h2 ▸ S.sp, h18 ▸ S.s2, h19 ▸ S.s3, h9 ▸ S.s1⟩
  · rw [hag a fun hw => ha ?_]
    · exact S.frameM a ha
    unfold SbrkW brkAddr at hw
    rcases hw with hw | hw | hw | hw
    · exact .inr ⟨by unfold mHead; omega, by omega⟩
    · exact .inl (.inl (by unfold allocGlobal InRange; omega))
    · exact .inl (.inl (by unfold allocGlobal InRange; omega))
    · exact .inl (.inl (by unfold allocGlobal InRange; omega))
  all_goals first
    | (rw [rslot _ (by omega) (by omega)]; exact S.fs0)
    | (rw [rslot _ (by omega) (by omega)]; exact S.fra)
    | (rw [rslot _ (by omega) (by omega)]; exact S.sra)
    | (rw [rslot _ (by omega) (by omega)]; exact S.ss0)
    | (rw [rslot _ (by omega) (by omega)]; exact S.ss1)
    | (rw [rslot _ (by omega) (by omega)]; exact S.ss2)
    | (rw [rslot _ (by omega) (by omega)]; exact S.ss3)

end VsaIris.VsaHeap
