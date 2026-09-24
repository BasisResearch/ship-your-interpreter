import VsaIris.Vsa.FreeTrim

/-!
# `_free_r`'s top merge

A chunk whose successor is the top joins it (`0x80007534`), after absorbing a
free predecessor: the merged chunk becomes the top (`PHeapAt.toTop`, over the
virtual heap of `PHeapAt.coalPrev`). A top at the trim threshold goes to
`_malloc_trim_r` (`trim_run`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state at `0x80007558`: the chunk `p` of size `sz` ending at the top,
in use in the virtual heap `V`, with no live block at `p + 16` and its header
carrying `PREV_INUSE`; the machine memory `Mt` agrees with `V` on the
footprint but on `p`'s header. `p` is in `a4`, the merged size in `a3`. -/
structure FTop (C : MCtx) (R : Nat → BitVec 64) (Mt V : Mem) (brkv : Nat) (cs : List Chunk)
    (bins : Nat → List Nat) (p sz : Nat) : Prop where
  frame : FFrame C R Mt
  heap : PHeapAt V C.H C.top0 brkv (cs ++ [⟨p, sz, true⟩]) bins
  hno : ∀ e ∈ C.H, e.1 ≠ p + 16
  prev : ∀ h0, read64 V (p + 8) = some h0 → h0 % 2 = 1
  agree : ∀ w, vsaFoot C.H w → ¬ (p + 8 ≤ w ∧ w < p + 16) → Mt[w]? = V[w]?
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = p
  a3 : (R 13).toNat = brkv - p

/-- **The merged top** (`0x80007558`): `p` becomes the top; below the trim
threshold `_free_r` returns, otherwise it calls `_malloc_trim_r` first. -/
theorem top_tail {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt V : Mem} {brkv : Nat}
    {cs : List Chunk} {bins : Nat → List Nat} {p sz : Nat} (T : FTop C R Mt V brkv cs bins p sz) :
    AW C.live C.S C.Q 0x80007558#64 R Mt := by
  have HH := T.heap.heap.heap
  have hpm : (⟨p, sz, true⟩ : Chunk) ∈ cs ++ [⟨p, sz, true⟩] := by simp
  have hpb := HH.walk.chunk_bounds _ hpm
  have hp16 := HH.aligned.1 _ hpm
  have htop16 := HH.aligned.2
  simp only at hpb hp16
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  unfold heapStart heapEnd at *
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hhd := foot_header T.heap.heap (.inr ⟨_, hpm, rfl⟩)
  simp only at hhd
  have hoffH := off_stack_of T.disj hhd
  have hgT : ∀ k, k < 8 → vsaFoot C.H (0x8001ad20 + k) := fun k hk => .inl (by unfold allocGlobal InRange; omega)
  have hoffT := off_stack_of T.disj hgT
  have ha4 := T.a4; have ha3 := T.a3
  have hE8 : (R 14 + sign_extend (m := 64) (0x008#12)).toNat = p + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
  have hv : (R 13 ||| 1#64).toNat = brkv - p + 1 := or1_toNat ha3 (by omega)
  refine st_80007558 O.live ?_
  have hthr := O.foot (a := 0x8001b968) (w := 8) (fun k hk => .inl (by unfold allocGlobal InRange; omega))
  refine st_8000755c O.live (by sx_norm; exact hthr) ?_
  refine st_80007560 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hE8]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hE8]; exact O.foot hhd
  rw [hE8]
  have h17 := T.a7
  rw [← upd_self_eq h17]
  refine st_80007564 O.live (by sx_norm; decide) (by sx_norm; exact O.foot hgT) ?_
  sx_norm
  generalize hM2 : writeLog (writeLog Mt [(p + 8, 8, R 13 ||| 1#64)])
    [(2147593504, 8, R 14)] = M2
  have hM2o : ∀ a, ¬ (p + 8 ≤ a ∧ a < p + 16) → ¬ (0x8001ad20 ≤ a ∧ a < 0x8001ad28) → M2[a]? = Mt[a]? := by
    intro a h1 h2
    rw [← hM2, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have H' : PHeapAt M2 C.H p brkv cs bins := by
    refine T.heap.toTop T.hno T.prev ?_ ?_ fun w hw h1 h2 => ?_
    · rw [← hM2]; unfold topAddr avAddr; rw [read64_store_hit, ha4]
    · rw [← hM2, read64_store_miss _ _ (by omega), read64_store_hit, hv]
    · unfold topAddr avAddr at h2
      rw [hM2o w h1 (by omega)]; exact T.agree w hw h1
  have F' : FFrame C (upd (upd (upd R 17 0x8001ad10#64) 12 (R 13 ||| 1#64)) 15
      (ldv .ld Mt 2147596648)) M2 := by
    rw [← hM2]
    refine ((T.frame.store (by omega)).store (by omega)).of_regs
      ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have hpres : ∀ a, vsaFoot C.H a → (M2[a]?).isSome := fun a ha => by
    rw [← hM2]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (T.pres a ha))
  have hframe : ∀ a, ¬ MWin C.H C.s a → M2[a]? = C.Mt0[a]? := by
    rw [← hM2]; exact frame_store (win_foot hgT) (frame_store (win_foot hhd) T.frameM)
  have hle : p ≤ C.top0 := by omega
  refine st_80007568 O.live (fun _ => free_epi O F' ⟨_, _, _, _, H', hle⟩ hpres hframe) (fun _ => ?_)
  have hpadS := O.foot (a := 0x8001b9a8) (w := 8) (fun k hk => .inl (by unfold allocGlobal InRange; omega))
  refine st_8000756c O.live (by sx_norm; exact hpadS) ?_
  have hpad := H'.heap.heap.top_pad
  unfold topPadAddr at hpad
  sx_norm
  simp (disch := decide) only [ldv_at hpad]
  refine st_80007570 O.live ?_
  refine st_80007574 O.live ?_
  simp only [VsaIris.ra]
  refine trim_run O ⟨F'.of_regs ?_ ?_ ?_ ?_, H', hle, hpres, T.disj, hframe, ?_, ?_, ?_, ?_⟩
    (fun R' M' F h8 D => st_80007578 O.live (free_epi O F D.heap D.pres D.frame)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [T.s0]; rfl
  · rfl
  · exact T.s0

end VsaIris.VsaHeap
