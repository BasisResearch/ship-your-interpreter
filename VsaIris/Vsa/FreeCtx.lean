import VsaIris.Vsa.MallocRunAll
import VsaIris.Vsa.HeapFree

/-!
# The context of a `_free_r` run

A `_free_r(reent, q)` run is stated over an allocator context `MCtx` whose
live blocks `H` are those left after the free, with the obligations `FOK`:
the shared `WOK` (code, stack, owned write window, return address) and `ok`,
the continuation from a return (`FRet`): the heap in shape without the block,
its top no higher than at entry, the footprint present, and the memory outside
the write window at its entry value. The freed block's bytes join the
footprint of the heap without it, so the write window `MWin C.H C.s` covers
them.

`FFrame` is `_free_r`'s 32-byte frame (`s0` and `ra` saved, the argument
spilled), and `FEntry` the registers at its entry.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A return from `_free_r`: the caller's registers, the heap without the
block with the top no higher, the footprint present, and every byte outside
the write window at its entry value. -/
structure FRet (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  regs : MRegs C R
  heap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins ∧ top ≤ C.top0
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- The obligations of a `_free_r` call context. -/
structure FOK (C : MCtx) : Prop extends WOK C where
  ok : ∀ R Mt, FRet C R Mt → AW C.live C.S C.Q C.r R Mt

theorem FOK.stack {C : MCtx} (O : FOK C) {a w : Nat} (h1 : C.s.toNat - mHead ≤ a)
    (h2 : a + w ≤ C.s.toNat) : ∀ b ∈ accAddrs a w, C.S b := O.toWOK.stack h1 h2

theorem FOK.foot {C : MCtx} (O : FOK C) {a w : Nat} (h : ∀ k, k < w → vsaFoot C.H (a + k)) :
    ∀ b ∈ accAddrs a w, C.S b := O.toWOK.foot h

/-- Frame bytes are owned: the `sx_side` rule for stack accesses in a free run. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.FOK.stack ‹VsaIris.VsaHeap.FOK _› ?_ ?_ <;> ((try unfold VsaIris.VsaHeap.mHead) ; sx_addr)))

/-- Allocator globals are owned: the `sx_side` rule for literal global addresses in a free run. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.FOK.foot ‹VsaIris.VsaHeap.FOK _› (fun k hk => Or.inl ?_); unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange; omega))

/-- `_free_r`'s registers at its entry: the reentrancy structure in `a0`,
the block in `a1`. -/
structure FEntry (C : MCtx) (q : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = C.r
  sp : R 2 = C.s
  a0 : R 10 = reentV
  a1 : (R 11).toNat = q
  s0 : R 8 = C.rv0 8
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

/-- `_free_r`'s 32-byte frame: `sp` 32 bytes below the caller's, `s0` and `ra`
in their slots, `s1-s3` untouched. -/
structure FFrame (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  sp : R 2 = C.s + 18446744073709551584#64
  s0 : read64 Mt (C.s.toNat - 32 + 16) = some (C.rv0 8).toNat
  ra : read64 Mt (C.s.toNat - 32 + 24) = some C.r.toNat
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

theorem FFrame.of_regs {C : MCtx} {R R' : Nat → BitVec 64} {Mt : Mem} (F : FFrame C R Mt)
    (h2 : R' 2 = R 2) (h9 : R' 9 = R 9) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) :
    FFrame C R' Mt :=
  ⟨h2.trans F.sp, F.s0, F.ra, h9.trans F.s1, h18.trans F.s2, h19.trans F.s3⟩

/-- The frame through a store that misses the saved `s0` and `ra`. -/
theorem FFrame.store {C : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (F : FFrame C R Mt)
    {a w : Nat} {v : BitVec 64} (h : a + w ≤ C.s.toNat - 32 + 16 ∨ C.s.toNat - 32 + 32 ≤ a) :
    FFrame C R (writeLog Mt [(a, w, v)]) where
  sp := F.sp
  s0 := by rw [read64_store_miss _ _ (by omega)]; exact F.s0
  ra := by rw [read64_store_miss _ _ (by omega)]; exact F.ra
  s1 := F.s1
  s2 := F.s2
  s3 := F.s3

theorem MSp.sp32 {s : BitVec 64} (h : MSp s) (d : Nat) (hd : d ≤ 32) :
    (s + 18446744073709551584#64 + BitVec.ofNat 64 d).toNat = s.toNat - 32 + d := by
  have := h.lo; have := h.hi
  unfold mHead Vsa.Sim.tohostAddr at *
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

end VsaIris.VsaHeap
