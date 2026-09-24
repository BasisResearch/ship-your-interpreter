import VsaIris.Vsa.FreeTop

/-!
# `_free_r` at the binary, both regimes

`free` (`0x8000479c`) moves the block to `a1`, loads `_impure_ptr` into `a0`
and jumps to `_free_r`, whose every path `free_body` proves. A free run owns
its stack scratch, the heap footprint and the block (`freeBytes`); its
tracking memory `ft0` is the heap witness with the block's and the stack
window's bytes inserted, so the footprint after the free (which covers the
block) is present from the start. `freeChgRun_proved` and
`freeLocalRun_proved` are the counted and uncounted runs `AllocHoles` asked
for.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The bytes a free call owns at the binary. -/
abbrev fS (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) : Nat → Prop :=
  freeBytes vsaLayoutP H q n s allocHeadroom

/-- The tracking memory at a free's entry: the heap witness with the block's
bytes and the stack window. -/
abbrev ft0 (m1 : Mem) (q : BitVec 64) (n : Nat) (s : BitVec 64) (mv : Nat → BitVec 8) : Mem :=
  mt0 (stackBase m1 q.toNat n mv) s mv

/-- The footprint without the block is the footprint with it and the block. -/
theorem foot_block {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat}
    (h : vsaFoot H a) : vsaFoot (e :: H) a ∨ InExt e a := by
  rcases h with hg | ⟨h1, h2, h3⟩
  · exact .inl (.inl hg)
  · by_cases hin : InExt e a
    · exact .inr hin
    · refine .inl (.inr ⟨h1, h2, fun e' he => ?_⟩)
      rcases List.mem_cons.mp he with rfl | he
      · exact hin
      · exact h3 e' he

/-- The footprint without the block is owned by the free. -/
theorem fS_of_foot {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat} {s : BitVec 64} {a : Nat}
    (h : vsaFoot H a) : fS H q n s a := .inr (foot_block h)

/-- The write window of a free context is owned. -/
theorem fS_of_win {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat} {s : BitVec 64} (hsp : SpOKA s)
    (a : Nat) (ha : MWin H s a) : fS H q n s a := by
  rcases ha with hf | ha
  · exact fS_of_foot hf
  · rcases mChg_own hsp a (.inr ha) with h | h
    · exact .inl h
    · exact fS_of_foot h

/-- **A run from the symbolic run at entry.** Every byte the free owns reads
as the image in the tracking memory `ft0`. -/
theorem faw_run {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat}
    {s pc : BitVec 64} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} {m1 : Mem}
    (h : AW live (fS H q n s) Q pc rv (ft0 m1 q n s mv)) (hpc : rv VsaIris.PC = pc)
    (him : ImgOn (vsaFoot ((q.toNat, n) :: H)) mv m1) :
    ∃ fuel, LocalRun (vsaModel live) roR allocText aRegs (fS H q n s) Q fuel rv mv := by
  obtain ⟨fuel, hf⟩ := h
  refine ⟨fuel, hf rv mv ⟨hpc, fun _ _ _ => rfl, fun a ha => ?_⟩⟩
  unfold imgM ft0 mt0
  rw [stackBase_get, stackBase_get]
  by_cases h1 : s.toNat - allocHeadroom ≤ a ∧ a < s.toNat - allocHeadroom + allocHeadroom
  · rw [if_pos h1]; rfl
  rw [if_neg h1]
  by_cases h2 : q.toNat ≤ a ∧ a < q.toNat + n
  · rw [if_pos h2]; rfl
  rw [if_neg h2]
  rcases ha with hs | hh | hx
  · exact absurd ⟨hs.1, by unfold stackWin InExt at hs; simp only at hs; omega⟩ h1
  · rw [him a hh]; rfl
  · exact absurd hx h2

/-- **The heap invariant at a free's entry.** -/
theorem fHeap_entry {C : MCtx} {m1 : Mem} {q : BitVec 64} {n : Nat} {s : BitVec 64}
    {mv : Nat → BitVec 8} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hs0 : C.s = s) (hMt : C.Mt0 = ft0 m1 q n s mv) (hsp : SpOKA s)
    (him : ImgOn (vsaFoot ((q.toNat, n) :: C.H)) mv m1)
    (hheap : PHeapAt m1 ((q.toNat, n) :: C.H) C.top0 brkv chunks bins)
    (hst : Starts ((q.toNat, n) :: C.H))
    (hdisj : ∀ a, stackWin s allocHeadroom a →
      ¬ (heapFoot vsaLayoutP ((q.toNat, n) :: C.H) a ∨ InExt (q.toNat, n) a)) :
    FHeap C C.Mt0 q.toNat n brkv chunks bins := by
  subst hs0
  have hs : 512 ≤ C.s.toNat := by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at this; omega
  have hwin : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat - allocHeadroom + allocHeadroom →
      ¬ vsaFoot C.H a := fun a h1 h2 hf => by
    exact hdisj a ⟨h1, by simp only; omega⟩ (foot_block hf)
  have HH := hheap.heap.heap
  obtain ⟨c, hc, _, hca, hcn⟩ := HH.live _ List.mem_cons_self
  have hcb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := hheap.heap.top_room
  unfold heapStart at hcb; unfold heapEnd at hbrk
  simp only at hca hcn
  have hag : ∀ a, vsaFoot ((q.toNat, n) :: C.H) a → C.Mt0[a]? = m1[a]? := by
    intro a ha
    rw [hMt]; unfold ft0 mt0
    rw [stackBase_get, stackBase_get,
      ite_eq_right_iff.2 fun h => absurd (.inl ha) (hdisj a ⟨h.1, by simp only; omega⟩)]
    rcases ha with hg | ⟨_, _, h3⟩
    · exact ite_eq_right_iff.2 fun h => by
        have := allocGlobal_off_arena a hg; unfold heapStart heapEnd at this; omega
    · exact ite_eq_right_iff.2 fun h => absurd h (h3 _ List.mem_cons_self)
  refine ⟨hheap.transport_read fun a ha => (hag a ha.1).symm, hst, fun a ha => ?_,
    fun a h1 h2 hf => hwin a ?_ ?_ hf, fun a _ => rfl⟩
  · rw [hMt]; unfold ft0 mt0
    rw [stackBase_get, stackBase_get]
    by_cases h1 : C.s.toNat - allocHeadroom ≤ a ∧ a < C.s.toNat - allocHeadroom + allocHeadroom
    · rw [if_pos h1]; rfl
    rw [if_neg h1]
    by_cases h2 : q.toNat ≤ a ∧ a < q.toNat + n
    · rw [if_pos h2]; rfl
    rw [if_neg h2]
    rcases foot_block (e := (q.toNat, n)) ha with hh | hx
    · rw [him a hh]; rfl
    · exact absurd hx h2
  · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : mHead ≤ allocHeadroom) _) h1
  · rw [Nat.sub_add_cancel (by unfold allocHeadroom; omega)]; exact h2

/-- **`free`** (`0x8000479c`): `a1 := a0`, `a0 := _impure_ptr`, then
`_free_r` (`free_body`). -/
theorem free_entry {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (hra : R 1 = C.r) (hsp : R 2 = C.s) (ha0 : R 10 = C.n) (h8 : R 8 = C.rv0 8)
    (h9 : R 9 = C.rv0 9) (h18 : R 18 = C.rv0 18) (h19 : R 19 = C.rv0 19)
    (Hp : FHeap C C.Mt0 C.n.toNat n brkv chunks bins) :
    AW C.live C.S C.Q freeEntryBV R C.Mt0 := by
  rw [show freeEntryBV = 0x8000479c#64 from rfl]
  refine st_8000479c O.live ?_
  refine st_800047a0 O.live ?_
  refine st_800047a4 O.live ?_
  refine free_body O ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ Hp <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hra
  · exact hsp
  · decide
  · sx_norm; rw [ha0]
  · exact h8
  · exact h9
  · exact h18
  · exact h19

/-- The context of an uncounted `free` run at the binary. -/
def fLocCtx (live : Nat → Prop) (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) : MCtx :=
  ⟨live, fS H q n s, FreeEnd vsaLayoutP H r s saved, H, q, r, s, rv0, Mt0, top0⟩

/-- The context of a counted `free` run at the binary. -/
def fChgCtx (live : Nat → Prop) (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (k : Nat) (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) :
    MCtx :=
  ⟨live, fS H q n s, FreeRoomEnd vsaLayoutP vsaRoomB H r s saved k, H, q, r, s, rv0, Mt0, top0⟩

/-- **The uncounted context's obligations**: a return has the heap in shape
without the block. -/
theorem fOK_loc {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat}
    {r s : BitVec 64} {saved : List (Nat × BitVec 64)} {rv0 : Nat → BitVec 64} {Mt0 : Mem}
    {top0 : Nat} (hlive : AllocLive live) (hsv : saved.map Prod.fst = vsaSaved) (hsp : SpOKA s)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 freeEntryBV r q s saved) (hst : Starts H) :
    FOK (fLocCtx live H q n r s saved rv0 Mt0 top0) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := fS_of_win hsp
  ral := hral
  ok := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap, _⟩ := h.heap
    exact malloc_ret (F := vsaFoot H) hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs)
      (fun a ha => fS_of_foot ha) h.pres fun rv mv hfr _ him =>
        ⟨hfr, hst, Mt, top, brkv, chunks, bins, him, hheap⟩

/-- **The counted context's obligations**: the top no higher keeps the
credits. -/
theorem fOK_chg {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat}
    {r s : BitVec 64} {saved : List (Nat × BitVec 64)} {k : Nat} {rv0 : Nat → BitVec 64} {Mt0 : Mem}
    {top0 : Nat} (hlive : AllocLive live) (hsv : saved.map Prod.fst = vsaSaved) (hsp : SpOKA s)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 freeEntryBV r q s saved) (hst : Starts H)
    (hcap : 2 * k + extendSlack ≤ heapEnd - top0) :
    FOK (fChgCtx live H q n r s saved k rv0 Mt0 top0) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := fS_of_win hsp
  ral := hral
  ok := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap, htop⟩ := h.heap
    simp only [fChgCtx] at htop
    exact malloc_ret (F := vsaFoot H) hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs)
      (fun a ha => fS_of_foot ha) h.pres fun rv mv hfr _ him =>
        ⟨hfr, ⟨hst, Mt, top, brkv, chunks, bins, him, hheap⟩,
          hst, Mt, top, brkv, chunks, bins, him, hheap, by omega⟩

/-- **Uncounted `free` at the binary** (formerly `IrisHoles.alloc.freeLocalRun`). -/
theorem freeLocalRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    FreeLocalRun (vsaModel live) vsaLayoutP SpOKA freeEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText := by
  intro H q n s r saved rv mv hsv hsp hral he hshape hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap⟩ := hshape
  have O := fOK_loc (H := H) (n := n) (Mt0 := ft0 m1 q n s mv) (top0 := top) hl hsv hsp hral he
    (List.nodup_cons.1 hst).2
  have Hp := fHeap_entry (C := fLocCtx live H q n r s saved rv (ft0 m1 q n s mv) top) rfl
    (by simp only [fLocCtx]) hsp
    him hheap hst hdisj
  have h := free_entry O he.ra he.sp he.a0 rfl rfl rfl rfl Hp
  simp only [fLocCtx] at h
  exact faw_run h he.pc him

/-- **Counted `free` at the binary** (formerly `IrisHoles.alloc.freeChgRun`). -/
theorem freeChgRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    FreeRoomRun (vsaModel live) vsaLayoutP vsaRoomB vsaRoomB SpOKA freeEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText := by
  intro H q n s r saved rv mv k hsv hsp hral he _ hroom hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap, hcap⟩ := hroom
  have O := fOK_chg (H := H) (n := n) (k := k) (Mt0 := ft0 m1 q n s mv) (top0 := top) hl hsv hsp
    hral he (List.nodup_cons.1 hst).2 hcap
  have Hp := fHeap_entry (C := fChgCtx live H q n r s saved k rv (ft0 m1 q n s mv) top) rfl
    (by simp only [fChgCtx]) hsp
    him hheap hst hdisj
  have h := free_entry O he.ra he.sp he.a0 rfl rfl rfl rfl Hp
  simp only [fChgCtx] at h
  exact faw_run h he.pc him

end VsaIris.VsaHeap
