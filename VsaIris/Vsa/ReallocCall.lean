import VsaIris.Vsa.ReallocPro

/-!
# `_realloc_r`'s nested calls

`_realloc_r` calls `_malloc_r` and `_free_r` from its 64-byte frame. Each
call is the callee's whole proof (`malloc_all`, `free_body`) over a nested
context: the realloc run's code, owned bytes and final postcondition, the
callee's live blocks, the link address as its return address, `sp` 64 bytes
below the caller's, and the current registers and memory as its entry
values. The callee's return obligation is the continuation at the link.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `sp` 64 bytes below a realloc caller's. -/
theorem sp64_toNat {s : BitVec 64} (h : SpOKA s) :
    (s + 18446744073709551552#64).toNat = s.toNat - 64 := by
  have := h.lo; have := h.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at *
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

/-- The callee's scratch window lies in the caller's. -/
theorem win64_le {t a : Nat} (h : t - 64 - mHead ≤ a) : t - allocHeadroom ≤ a := by
  rw [Nat.sub_sub] at h
  exact Nat.le_trans (Nat.sub_le_sub_left (by decide : 64 + mHead ≤ allocHeadroom) t) h

/-- The nested call's shared obligations. -/
theorem ROK.wok64 {C : MCtx} {B : RB} (O : ROK C B) {H' : List (Nat × Nat)} {link : BitVec 64}
    (hlink : link.toNat % 4 = 0) (hH' : ∀ a, vsaFoot H' a → vsaFoot C.H a) (n : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (top : Nat) :
    WOK ⟨C.live, C.S, C.Q, H', n, link, C.s + 18446744073709551552#64, R, Mt, top⟩ := by
  have hs := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  refine ⟨O.live, ⟨?_, ?_, ?_⟩, fun a ha => ?_, hlink⟩
  · show _ ≤ (C.s + 18446744073709551552#64).toNat
    rw [hs]; unfold mHead Vsa.Sim.tohostAddr; omega
  · show (C.s + 18446744073709551552#64).toNat ≤ _; rw [hs]; omega
  · show (C.s + 18446744073709551552#64).toNat % 16 = 0; rw [hs]; omega
  · rcases ha with hf | ⟨h1, h2⟩
    · exact O.own a (.inl (hH' a hf))
    · simp only at h1 h2
      rw [hs] at h1 h2
      exact O.deep a (win64_le h1) (by omega)

/-- **A nested `_free_r(q)`** from `_realloc_r`'s frame, the block `(q, n)`
live over the others `H'`: back at the link with the saved registers, the
heap without the block, its top no higher, and the memory kept outside the
callee's window. -/
theorem rcall_free {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {H' : List (Nat × Nat)} {q n top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {link : BitVec 64} (hlink : link.toNat % 4 = 0) (hH' : ∀ a, vsaFoot H' a → vsaFoot C.H a)
    (hsp : R 2 = C.s + 18446744073709551552#64) (ha0 : R 10 = reentV) (ha1 : (R 11).toNat = q)
    (hra : R 1 = link)
    (hheap : PHeapAt Mt ((q, n) :: H') top brkv chunks bins) (hst : Starts ((q, n) :: H'))
    (hpres : ∀ a, vsaFoot H' a → (Mt[a]?).isSome)
    (hdisjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hk : ∀ R' Mt', R' 1 = link → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 18 = R 18 →
      R' 19 = R 19 →
      (∃ top' brkv' chunks' bins', PHeapAt Mt' H' top' brkv' chunks' bins' ∧ top' ≤ top) →
      (∀ a, vsaFoot H' a → (Mt'[a]?).isSome) →
      (∀ a, ¬ MWin H' (C.s + 18446744073709551552#64) a → Mt'[a]? = Mt[a]?) →
      AW C.live C.S C.Q link R' Mt') :
    AW C.live C.S C.Q 0x80007350#64 R Mt := by
  have hs := sp64_toNat O.spA
  have hlo := O.spA.lo
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  let Cf : MCtx := ⟨C.live, C.S, C.Q, H', BitVec.ofNat 64 q, link, C.s + 18446744073709551552#64,
    R, Mt, top⟩
  have Of : FOK Cf := ⟨O.wok64 hlink hH' _ R Mt top, fun R' Mt' h =>
    hk R' Mt' h.regs.ra (h.regs.sp.trans hsp.symm) h.regs.s0 h.regs.s1 h.regs.s2 h.regs.s3 h.heap
      h.pres h.frame⟩
  exact free_body (C := Cf) Of ⟨hra, hsp, ha0, ha1, rfl, rfl, rfl, rfl⟩
    ⟨hheap, hst, hpres, fun a h1 h2 hf => hdisjD a (by
      simp only [Cf] at h1; rw [hs] at h1; exact win64_le h1)
      (by simp only [Cf] at h2; rw [hs] at h2; omega) (hH' a hf), fun _ _ => rfl⟩

/-- **A nested `_malloc_r(n)`** from `_realloc_r`'s frame over the live
blocks `H'`: back at the link with the saved registers, and either a fresh
block with the heap extended by it and the top grown by at most its chunk,
or NULL with the heap kept and the arena starved; the memory kept outside the
callee's window. -/
theorem rcall_malloc {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {H' : List (Nat × Nat)} {n : BitVec 64} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat}
    {link : BitVec 64} (hlink : link.toNat % 4 = 0) (hH' : ∀ a, vsaFoot H' a → vsaFoot C.H a)
    (hsp : R 2 = C.s + 18446744073709551552#64) (ha0 : R 10 = reentV) (ha1 : R 11 = n)
    (hra : R 1 = link)
    (hheap : PHeapAt Mt H' top brkv chunks bins)
    (hpres : ∀ a, vsaFoot H' a → (Mt[a]?).isSome)
    (hdisjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hok : ∀ R' Mt', R' 1 = link → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 18 = R 18 →
      R' 19 = R 19 → FreshAt H' (R' 10).toNat n.toNat → (R' 10).toNat % 16 = 0 →
      (∃ top' brkv' chunks' bins',
        PHeapAt Mt' (((R' 10).toNat, n.toNat) :: H') top' brkv' chunks' bins' ∧
          top' ≤ top + physSize n.toNat ∧
          LiveKeep ⟨C.live, C.S, C.Q, H', n, link, C.s + 18446744073709551552#64, R, Mt, top⟩ chunks') →
      (∀ a, vsaFoot H' a → (Mt'[a]?).isSome) →
      (∀ a, ¬ MWin H' (C.s + 18446744073709551552#64) a → Mt'[a]? = Mt[a]?) →
      AW C.live C.S C.Q link R' Mt')
    (hnull : ∀ R' Mt', R' 1 = link → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 18 = R 18 →
      R' 19 = R 19 → R' 10 = 0 →
      (∃ top' brkv' chunks' bins', PHeapAt Mt' H' top' brkv' chunks' bins') →
      (∀ a, vsaFoot H' a → (Mt'[a]?).isSome) →
      (∀ a, ¬ MWin H' (C.s + 18446744073709551552#64) a → Mt'[a]? = Mt[a]?) →
      Starved top n.toNat → AW C.live C.S C.Q link R' Mt') :
    AW C.live C.S C.Q 0x800047a8#64 R Mt := by
  have hs := sp64_toNat O.spA
  have hlo := O.spA.lo
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  let Cm : MCtx := ⟨C.live, C.S, C.Q, H', n, link, C.s + 18446744073709551552#64, R, Mt, top⟩
  have Om : MOK Cm := ⟨O.wok64 hlink hH' n R Mt top,
    fun R' Mt' h => hok R' Mt' h.regs.ra (h.regs.sp.trans hsp.symm) h.regs.s0 h.regs.s1 h.regs.s2
      h.regs.s3 h.fresh h.align h.heap h.pres h.frame,
    fun R' Mt' h => hnull R' Mt' h.regs.ra (h.regs.sp.trans hsp.symm) h.regs.s0 h.regs.s1 h.regs.s2
      h.regs.s3 h.a0 h.heap h.pres h.frame h.starved⟩
  exact malloc_all (C := Cm) Om ⟨hra, hsp, ha0, ha1, rfl, rfl, rfl, rfl⟩
    ⟨hheap, hpres, fun a h1 h2 hf => hdisjD a (by
      simp only [Cm] at h1; rw [hs] at h1; exact win64_le h1)
      (by simp only [Cm] at h2; rw [hs] at h2; omega) (hH' a hf), fun _ _ => rfl,
      LiveKeep.of_heap (C := Cm) hheap⟩

end VsaIris.VsaHeap
