import VsaIris.Interp.SpecEnv

/-!
# `realloc(NULL, n)` at the binary, both regimes

`realloc` (`0x8000527c`) moves the pointer to `a1` and the request to `a2`
and loads `_impure_ptr` into `a0`; `_realloc_r` tests the pointer
(`0x80005290: beqz a1`), moves the request back to `a1` (`0x80005480`) and
tail-calls `_malloc_r` (`0x80005484: j`). From there the run is H4's
`malloc_all`, over the same contexts as `mallocChgRun_proved` and
`mallocLocalRun_proved`, so the post is `malloc`'s.
-/

namespace VsaIris.Interp

open VsaIris.VsaHeap Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **`realloc(NULL, n)`** (`0x8000527c`): the entry moves, the NULL test
taken, the request back in `a1`, then `_malloc_r` (`malloc_all`). -/
theorem reallocNull_entry {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (hra : R 1 = C.r) (hsp : R 2 = C.s) (ha0 : R 10 = 0#64) (ha1 : R 11 = C.n)
    (h8 : R 8 = C.rv0 8) (h9 : R 9 = C.rv0 9) (h18 : R 18 = C.rv0 18) (h19 : R 19 = C.rv0 19)
    (Hp : MHeap C C.Mt0 brkv chunks bins) :
    AW C.live C.S C.Q reallocEntryBV R C.Mt0 := by
  rw [show reallocEntryBV = 0x8000527c#64 from rfl]
  refine st_8000527c O.live (st_80005280 O.live (st_80005284 O.live (st_80005288 O.live
    (st_8000528c O.live ?_))))
  refine st_80005290 O.live (fun _ => ?_) (fun hne => absurd ?_ hne)
  · refine st_80005480 O.live (st_80005484 O.live ?_)
    refine malloc_all O ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ Hp <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hra
    · exact hsp
    · decide
    · sx_norm; exact ha1
    · exact h8
    · exact h9
    · exact h18
    · exact h19
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    sx_norm
    exact ha0

/-- **Counted `realloc(NULL, n)` at the binary** (formerly `IrisHoles.reallocNull.chgRun`). -/
theorem reallocNullChgRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    ReallocNullChgRun (vsaModel live) := by
  intro H n s r saved rv mv k c hsv hchg hsp hral hR _ hroom hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap, hcap⟩ := hroom
  have O := mOK_chg (H := H) (k := k) (Mt0 := mt0 m1 s mv) (top0 := top) hl hsv hchg hsp hral
    hR.entry hst hcap
  have Hp := mHeap_entry (C := mChgCtx live H n r s saved k rv (mt0 m1 s mv) top) rfl
    (by simp only [mChgCtx]) hsp him hheap hdisj
  have h := reallocNull_entry O hR.entry.ra hR.entry.sp hR.entry.a0 hR.a1 rfl rfl rfl rfl Hp
  simp only [mChgCtx] at h
  exact aw_run h hR.entry.pc him hdisj

/-- **Uncounted `realloc(NULL, n)` at the binary** (formerly `IrisHoles.reallocNull.localRun`). -/
theorem reallocNullLocalRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    ReallocNullLocalRun (vsaModel live) := by
  intro H n s r saved rv mv hsv hsp hral hR hshape hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap⟩ := hshape
  have O := mOK_loc (H := H) (n := n) (Mt0 := mt0 m1 s mv) (top0 := top) hl hsv hsp hral hR.entry hst
  have Hp := mHeap_entry (C := mLocCtx live H n r s saved rv (mt0 m1 s mv) top) rfl
    (by simp only [mLocCtx]) hsp him hheap hdisj
  have h := reallocNull_entry O hR.entry.ra hR.entry.sp hR.entry.a0 hR.a1 rfl rfl rfl rfl Hp
  simp only [mLocCtx] at h
  exact aw_run h hR.entry.pc him hdisj

/-- **`realloc(NULL, n)` in both regimes**, proved. -/
theorem reallocNullHoles_proved : ReallocNullHoles where
  chgRun := reallocNullChgRun_proved
  localRun := reallocNullLocalRun_proved

end VsaIris.Interp
