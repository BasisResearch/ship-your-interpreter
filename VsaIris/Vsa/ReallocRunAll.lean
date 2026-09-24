import VsaIris.Vsa.ReallocGrow

/-!
# `_realloc_r` at the binary, both regimes

`realloc` (`0x8000527c`) moves the block to `a1` and the request to `a2`,
loads `_impure_ptr` into `a0` and falls into `_realloc_r`: the prologue
(`realloc_pro`), the in-place decision (`realloc_dec`) and the growth dispatch
(`realloc_grow`). A realloc run owns what a free of the old block owns
(`freeBytes`), over the same tracking memory `ft0`. `reallocChgRun_proved` and
`reallocLocalRun_proved` are the counted and uncounted runs `AllocHoles` asked
for.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **`_realloc_r`'s body** (`0x80005290`). -/
theorem realloc_body {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (E : REntry C B R)
    (Hp : RHeap C B C.Mt0 brkv chunks bins) :
    AW C.live C.S C.Q 0x80005290#64 R C.Mt0 :=
  realloc_pro O E Hp fun _ _ _ F Hp' hnb hnb31 h8 h9 h11 h15 =>
    realloc_dec O F Hp' hnb hnb31 h8 h9 h11 h15 fun _ _ _ _ D h13 => realloc_grow O D h13

/-- **`realloc`** (`0x8000527c`): `a5 := a0`, `a0 := _impure_ptr`,
`a2 := a1`, `a1 := a5`, then `_realloc_r`. -/
theorem realloc_entry {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (hra : R 1 = C.r) (hsp : R 2 = C.s) (ha0 : (R 10).toNat = B.p) (ha1 : R 11 = C.n)
    (h8 : R 8 = C.rv0 8) (h9 : R 9 = C.rv0 9) (h18 : R 18 = C.rv0 18) (h19 : R 19 = C.rv0 19)
    (Hp : RHeap C B C.Mt0 brkv chunks bins) :
    AW C.live C.S C.Q reallocEntryBV R C.Mt0 := by
  rw [show reallocEntryBV = 0x8000527c#64 from rfl]
  refine st_8000527c O.live (st_80005280 O.live (st_80005284 O.live (st_80005288 O.live
    (st_8000528c O.live ?_))))
  refine realloc_body O ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ Hp <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hra
  · exact hsp
  · decide
  · sx_norm; exact ha0
  · sx_norm; exact ha1
  · exact h8
  · exact h9
  · exact h18
  · exact h19

/-- The old block of a realloc run. -/
abbrev rB (p : BitVec 64) (nOld : Nat) (old : Nat → BitVec 8) : RB := ⟨p.toNat, nOld, old⟩

/-- **The heap invariant at a realloc's entry**: a free's (`fHeap_entry`),
with the deeper stack window, the old block's bytes and contents. -/
theorem rHeap_entry {C : MCtx} {m1 : Mem} {p : BitVec 64} {nOld : Nat} {old : Nat → BitVec 8}
    {s : BitVec 64} {mv : Nat → BitVec 8} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hs0 : C.s = s) (hMt : C.Mt0 = ft0 m1 p nOld s mv) (hsp : SpOKA s)
    (him : ImgOn (vsaFoot ((p.toNat, nOld) :: C.H)) mv m1)
    (hheap : PHeapAt m1 ((p.toNat, nOld) :: C.H) C.top0 brkv chunks bins)
    (hst : Starts ((p.toNat, nOld) :: C.H))
    (hdisj : ∀ a, stackWin s allocHeadroom a →
      ¬ (heapFoot vsaLayoutP ((p.toNat, nOld) :: C.H) a ∨ InExt (p.toNat, nOld) a))
    (hcp : Copies old mv p.toNat p.toNat nOld) (hgrow : nOld < C.n.toNat) :
    RHeap C (rB p nOld old) C.Mt0 brkv chunks bins := by
  have F := fHeap_entry hs0 hMt hsp him hheap hst hdisj
  have hs : 512 ≤ s.toNat := by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at this; omega
  refine ⟨F.heap, F.starts, F.pres, F.disj, fun a h1 h2 hf => ?_, F.frame, F.heap.block_foot F.starts,
    fun k hk => ?_, hgrow⟩
  · subst hs0
    exact hdisj a ⟨h1, by simp only; omega⟩ (foot_block hf)
  · subst hs0
    simp only [rB] at hk ⊢
    rw [hMt]; unfold ft0 mt0
    rw [stackBase_get, stackBase_get, if_neg fun h => hdisj _ ⟨h.1, by simp only; omega⟩
      (.inr ⟨by simp only; omega, by simp only; omega⟩), if_pos ⟨by omega, by omega⟩, hcp k hk]

/-- The context of an uncounted realloc run at the binary. -/
def rLocCtx (live : Nat → Prop) (H : List (Nat × Nat)) (p : BitVec 64) (nOld nNew : Nat)
    (old : Nat → BitVec 8) (r s : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) : MCtx :=
  ⟨live, fS H p nOld s, ReallocEnd vsaLayoutP H p nOld nNew old r s saved, H, BitVec.ofNat 64 nNew, r, s,
    rv0, Mt0, top0⟩

/-- The context of a counted realloc run at the binary. -/
def rChgCtx (live : Nat → Prop) (H : List (Nat × Nat)) (p : BitVec 64) (nOld nNew : Nat)
    (old : Nat → BitVec 8) (r s : BitVec 64) (saved : List (Nat × BitVec 64)) (k : Nat)
    (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) : MCtx :=
  ⟨live, fS H p nOld s, ReallocChgEnd vsaLayoutP vsaRoomB H p nOld nNew old r s saved k, H,
    BitVec.ofNat 64 nNew, r, s, rv0, Mt0, top0⟩

/-- A fresh block's first bytes carry the old contents into the image. -/
theorem copies_of_img {H : List (Nat × Nat)} {Mt : Mem} {mv : Nat → BitVec 8} {q n nOld p : Nat}
    {old : Nat → BitVec 8} {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hheap : PHeapAt Mt ((q, n) :: H) top brkv chunks bins) (hst : Starts ((q, n) :: H))
    (him : ImgOn (vsaFoot H) mv Mt) (hlt : nOld ≤ n)
    (hd : ∀ k, k < nOld → Mt[q + k]? = some (old (p + k))) : Copies old mv p q nOld := by
  intro k hk
  have h1 := him _ (hheap.block_foot hst k (by omega))
  rw [hd k hk] at h1
  exact (Option.some.inj h1).symm

/-- **The uncounted context's obligations**: a fresh block with the old
contents, or NULL with the old block kept. -/
theorem rOK_loc {live : Nat → Prop} {H : List (Nat × Nat)} {p : BitVec 64} {nOld nNew : Nat}
    {old : Nat → BitVec 8} {r s : BitVec 64} {saved : List (Nat × BitVec 64)}
    {rv0 : Nat → BitVec 64} {Mt0 : Mem} {top0 : Nat} (hlive : AllocLive live)
    (hsv : saved.map Prod.fst = vsaSaved) (hsp : SpOKA s) (hral : r.toNat % 4 = 0)
    (hE : EntryRegs rv0 reallocEntryBV r p s saved) (hst : Starts ((p.toNat, nOld) :: H))
    (hlt : nOld < nNew) (h64 : nNew < 2 ^ 64) :
    ROK (rLocCtx live H p nOld nNew old r s saved rv0 Mt0 top0) (rB p nOld old) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := fS_of_win hsp
  ral := hral
  spA := hsp
  deep := fun a h1 h2 => .inl ⟨h1, by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at *; dsimp only [rLocCtx] at h1 h2 ⊢; omega⟩
  ok := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap, _⟩ := h.heap
    have hn : (BitVec.ofNat 64 nNew).toNat = nNew := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    have hf := h.fresh; have hd := h.data
    dsimp only [rLocCtx] at hheap hf hd
    rw [hn] at hheap hf
    have hst' : Starts (((R 10).toNat, nNew) :: H) := Starts.cons (List.nodup_cons.1 hst).2 hf.start
    exact malloc_ret (F := vsaFoot H) hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs)
      (fun a ha => fS_of_foot ha) h.pres fun rv mv hfr ha0 him => ⟨hfr, .inr ⟨by rw [ha0]; exact hf.block,
        by rw [ha0]; exact h.align,
        by rw [ha0]; exact ⟨hst', Mt, top, brkv, chunks, bins, fun a ha => him a (vsaFoot_cons_sub a ha), hheap⟩,
        by rw [ha0]; exact copies_of_img hheap hst' him (by omega) hd⟩⟩
  null := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap⟩ := h.heap
    exact malloc_ret (F := vsaFoot H) hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs)
      (fun a ha => fS_of_foot ha) h.pres fun rv mv hfr ha0 him => ⟨hfr, .inl ⟨ha0.trans h.a0,
        ⟨hst, Mt, top, brkv, chunks, bins, fun a ha => him a (vsaFoot_cons_sub a ha), hheap⟩,
        copies_of_img hheap hst him (Nat.le_refl _) h.data⟩⟩

/-- **The counted context's obligations**: the fresh block's chunk comes out
of the credits; a counted request never starves. -/
theorem rOK_chg {live : Nat → Prop} {H : List (Nat × Nat)} {p : BitVec 64} {nOld nNew : Nat}
    {old : Nat → BitVec 8} {r s : BitVec 64} {saved : List (Nat × BitVec 64)} {k c : Nat}
    {rv0 : Nat → BitVec 64} {Mt0 : Mem} {top0 : Nat} (hlive : AllocLive live)
    (hsv : saved.map Prod.fst = vsaSaved) (hchg : vsaChg nNew c) (hsp : SpOKA s)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 reallocEntryBV r p s saved)
    (hst : Starts ((p.toNat, nOld) :: H)) (hlt : nOld < nNew) (h64 : nNew < 2 ^ 64)
    (hcap : 2 * (k + c) + extendSlack ≤ heapEnd - top0) :
    ROK (rChgCtx live H p nOld nNew old r s saved k rv0 Mt0 top0) (rB p nOld old) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := fS_of_win hsp
  ral := hral
  spA := hsp
  deep := fun a h1 h2 => .inl ⟨h1, by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at *; dsimp only [rChgCtx] at h1 h2 ⊢; omega⟩
  ok := by
    intro R Mt h
    have hP := physSize_le_chg hchg
    obtain ⟨top, brkv, chunks, bins, hheap, htop⟩ := h.heap
    have hn : (BitVec.ofNat 64 nNew).toNat = nNew := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    have hf := h.fresh; have hd := h.data
    dsimp only [rChgCtx] at hheap hf hd htop
    rw [hn] at hheap hf htop
    have hst' : Starts (((R 10).toNat, nNew) :: H) := Starts.cons (List.nodup_cons.1 hst).2 hf.start
    exact malloc_ret (F := vsaFoot H) hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs)
      (fun a ha => fS_of_foot ha) h.pres fun rv mv hfr ha0 him =>
        have him' : ImgOn (vsaFoot (((R 10).toNat, nNew) :: H)) mv Mt := fun a ha => him a (vsaFoot_cons_sub a ha)
        ⟨hfr, by rw [ha0]; exact hf.block, by rw [ha0]; exact h.align,
          by rw [ha0]; exact ⟨hst', Mt, top, brkv, chunks, bins, him', hheap⟩,
          by rw [ha0]; exact ⟨hst', Mt, top, brkv, chunks, bins, him', hheap, by omega⟩,
          by rw [ha0]; exact copies_of_img hheap hst' him (by omega) hd⟩
  null := by
    intro R Mt h
    have hP := physSize_le_chg16 hchg
    have hn : (BitVec.ofNat 64 nNew).toNat = nNew := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    have := h.starved
    dsimp only [rChgCtx] at this
    rw [hn] at this
    unfold Starved extendSlack at *
    omega

/-- **Uncounted `realloc` at the binary** (formerly `IrisHoles.alloc.reallocLocalRun`). -/
theorem reallocLocalRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    ReallocLocalRun (vsaModel live) vsaLayoutP SpOKA reallocEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText := by
  intro H p nOld nNew s r saved rv mv old hsv hsp hral he ha1 hlt h64 hshape hcp hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap⟩ := hshape
  have hn : (BitVec.ofNat 64 nNew).toNat = nNew := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  have O := rOK_loc (H := H) (old := old) (Mt0 := ft0 m1 p nOld s mv) (top0 := top) hl hsv hsp hral he
    hst hlt h64
  have Hp := rHeap_entry (C := rLocCtx live H p nOld nNew old r s saved rv (ft0 m1 p nOld s mv) top) rfl
    (by simp only [rLocCtx]) hsp him hheap hst hdisj hcp (by dsimp only [rLocCtx]; rw [hn]; exact hlt)
  have h := realloc_entry O he.ra he.sp (by rw [show (10 : Nat) = a0 from rfl, he.a0]) ha1 rfl rfl rfl rfl Hp
  simp only [rLocCtx] at h
  exact faw_run h he.pc him

/-- **Counted `realloc` at the binary** (formerly `IrisHoles.alloc.reallocChgRun`). -/
theorem reallocChgRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    ReallocChgRun (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA reallocEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText := by
  intro H p nOld nNew s r saved rv mv old k c hsv hchg hsp hral he ha1 hlt _ hroom hcp hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap, hcap⟩ := hroom
  have h64 : nNew < 2 ^ 64 := by
    have := physSize_le_chg hchg; unfold physSize extendSlack heapEnd at *; omega
  have hn : (BitVec.ofNat 64 nNew).toNat = nNew := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  have O := rOK_chg (H := H) (old := old) (k := k) (Mt0 := ft0 m1 p nOld s mv) (top0 := top) hl hsv
    hchg hsp hral he hst hlt h64 hcap
  have Hp := rHeap_entry (C := rChgCtx live H p nOld nNew old r s saved k rv (ft0 m1 p nOld s mv) top)
    rfl (by simp only [rChgCtx]) hsp him hheap hst hdisj hcp (by dsimp only [rChgCtx]; rw [hn]; exact hlt)
  have h := realloc_entry O he.ra he.sp (by rw [show (10 : Nat) = a0 from rfl, he.a0]) ha1 rfl rfl rfl rfl Hp
  simp only [rChgCtx] at h
  exact faw_run h he.pc him

end VsaIris.VsaHeap
