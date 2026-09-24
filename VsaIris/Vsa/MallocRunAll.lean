import VsaIris.Vsa.MallocBlocks2

/-!
# `_malloc_r` at the binary, both regimes

`malloc` (`0x80004790`) moves the request to `a1`, loads `_impure_ptr` into
`a0` and jumps to `_malloc_r`, whose every path `malloc_all` proves.
`mHeap_entry` builds the run's heap invariant from the entry heap witness;
`mallocChgRun_proved` and `mallocLocalRun_proved` are the counted and
uncounted runs `AllocHoles` asked for.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The heap invariant at entry.** The heap witness `m1` with the stack
window inserted holds the heap, off the stack. -/
theorem mHeap_entry {C : MCtx} {m1 : Mem} {s : BitVec 64} {mv : Nat → BitVec 8} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (hs0 : C.s = s) (hMt : C.Mt0 = mt0 m1 s mv)
    (hsp : SpOKA s) (him : ImgOn (vsaFoot C.H) mv m1)
    (hheap : PHeapAt m1 C.H C.top0 brkv chunks bins)
    (hdisj : ∀ a, stackWin s allocHeadroom a → ¬ vsaFoot C.H a) :
    MHeap C C.Mt0 brkv chunks bins := by
  subst hs0
  have hs : 512 ≤ C.s.toNat := by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at this; omega
  have hag : ∀ a, vsaFoot C.H a → C.Mt0[a]? = m1[a]? := by
    intro a ha
    rw [hMt]; unfold mt0
    rw [stackBase_get, ite_eq_right_iff.2 fun h => absurd ha (hdisj a ⟨h.1, by simp only; omega⟩)]
  refine ⟨hheap.transport_read fun a ha => (hag a ha.1).symm, fun a ha => by
    rw [hag a ha, him a ha]; rfl, fun a h1 h2 hf => hdisj a ?_ hf, fun a _ => rfl⟩
  unfold mHead at h1
  refine ⟨?_, ?_⟩ <;> simp only [allocHeadroom]
  · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : 256 ≤ 512) _) h1
  · rw [Nat.sub_add_cancel hs]; exact h2

/-- **`malloc`** (`0x80004790`): `a1 := a0`, `a0 := _impure_ptr`, then
`_malloc_r` (`malloc_all`). -/
theorem malloc_entry {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (hra : R 1 = C.r) (hsp : R 2 = C.s) (ha0 : R 10 = C.n) (h8 : R 8 = C.rv0 8)
    (h9 : R 9 = C.rv0 9) (h18 : R 18 = C.rv0 18) (h19 : R 19 = C.rv0 19)
    (Hp : MHeap C C.Mt0 brkv chunks bins) :
    AW C.live C.S C.Q mallocEntryBV R C.Mt0 := by
  rw [show mallocEntryBV = 0x80004790#64 from rfl]
  refine st_80004790 O.live ?_
  refine st_80004794 O.live ?_
  refine st_80004798 O.live ?_
  refine malloc_all O ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ Hp <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hra
  · exact hsp
  · decide
  · sx_norm; exact ha0
  · exact h8
  · exact h9
  · exact h18
  · exact h19

/-- **Counted `malloc` at the binary** (formerly `IrisHoles.alloc.mallocChgRun`). -/
theorem mallocChgRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    MallocChgRun (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA mallocEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText := by
  refine mallocChgRun_of_aw fun H n s r saved rv mv k c m1 top _ _ _ hsv hchg hsp hral he him hheap
      hcap hdisj => ?_
  have O := mOK_chg (H := H) (k := k) (Mt0 := mt0 m1 s mv) (top0 := top) hl hsv hchg hsp hral he hcap
  have Hp := mHeap_entry (C := mChgCtx live H n r s saved k rv (mt0 m1 s mv) top) rfl
    (by simp only [mChgCtx]) hsp him hheap hdisj
  have hra : rv 1 = r := he.ra
  have hsp' : rv 2 = s := he.sp
  have ha0 : rv 10 = n := he.a0
  have h := malloc_entry O hra hsp' ha0 rfl rfl rfl rfl Hp
  simp only [mChgCtx] at h
  exact h

/-- **Uncounted `malloc` at the binary** (formerly `IrisHoles.alloc.mallocLocalRun`). -/
theorem mallocLocalRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    MallocLocalRun (vsaModel live) vsaLayoutP SpOKA mallocEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText := by
  intro H n s r saved rv mv hsv hsp hral he hshape hdisj
  obtain ⟨m1, top, brkv, chunks, bins, him, hheap⟩ := hshape
  have O := mOK_loc (H := H) (Mt0 := mt0 m1 s mv) (top0 := top) hl hsv hsp hral he
  have Hp := mHeap_entry (C := mLocCtx live H n r s saved rv (mt0 m1 s mv) top) rfl
    (by simp only [mLocCtx]) hsp him hheap hdisj
  have hra : rv 1 = r := he.ra
  have hsp' : rv 2 = s := he.sp
  have ha0 : rv 10 = n := he.a0
  have h := malloc_entry O hra hsp' ha0 rfl rfl rfl rfl Hp
  simp only [mLocCtx] at h
  exact aw_run h he.pc him hdisj

end VsaIris.VsaHeap
