import Vsa.Sim.EqNeDispatchSeg
import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprCopy
import Vsa.Sim.EvalNotSim

/-!
# `EqNeReprReadback` — Blocker B: read the copied operand `ValueRepr`s back out of
the reflected `eq`/`ne` dispatch block.

The `eqDispatch`/`neDispatch` block (`EqNeDispatchSeg.lean`) copies the two operand
`Value` structs from their spill slots into the two compare buffers.  Concretely, on
`lds = [b0,b1,b2,b3,b4,b5]` the block issues six loads and six stores; its reflected
write log (`(evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) lds)).log`) is the
six-`sd` list

  `bufa = sp+0x40`  ⇐  `ld` of `b0/b1/b2` from `sp+0x78/0x80/0x88`
  `bufb = sp+0x20`  ⇐  `ld` of `b3/b4/b5` from `sp+0x90/0x98/0xa0`,

so `writeLog m0 log` is a concrete six-layer `writeMap8` tower (`eqDispatch_mem_tower`,
by `rfl` — `neDispatch` is byte-identical, same tower).

The downstream `value_equal` precondition `ve_pre` needs
`ValueRepr mem N φc bufa.toNat vl` / `… bufb.toNat vr` on the *post-dispatch* memory
`mem`.  This file reads those back: the copied 24 bytes at each buffer equal the
source 24 bytes at `sp+0x78`/`sp+0x90` on the entry memory `m0` (each stored word is
the `.ld` of a source byte list, and `LPins8` — from the block's `ChainFacts` — ties
that byte list to `m0` at the source slot), so `ValueRepr` re-holds at the buffer via
the translation-copy lemma `valueRepr_copy` (`ReprCopy.lean`).

`valueRepr_of_reflected_copy` is the reusable core: it serves `bufa` and `bufb` in the
same call shape, and it serves `ne` for free because the tower is identical.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Byte-level building blocks -/

/-- Byte `k` of a `sd`-stored `.ld`-loaded value equals the `k`-th source byte
(`bs.getD k 0`).  This is the composition of `getElem_writeMap8_k` (the freshly
written window's byte is `d.extractLsb' (8k) 8`) with `sdData_sext_bytes` (that
extracted byte of the `.ld` value is the source byte). -/
theorem writeMap8_ld_byte (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (bs : List (BitVec 8)) (k : Nat) (hk : k < 8) :
    (writeMap8 mem a (sdData_val (bytesVal .ld bs)))[a + k]? = some (bs.getD k 0#8) := by
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7⟩ := sdData_sext_bytes (bs.getD 0 0#8) (bs.getD 1 0#8)
    (bs.getD 2 0#8) (bs.getD 3 0#8) (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)
  have hbv : bytesVal .ld bs = sign_extend (m := 64)
      ((((((((bs.getD 7 0#8).append (bs.getD 6 0#8)).append (bs.getD 5 0#8)).append
        (bs.getD 4 0#8)).append (bs.getD 3 0#8)).append (bs.getD 2 0#8)).append
        (bs.getD 1 0#8)).append (bs.getD 0 0#8)) := rfl
  match k, hk with
  | 0, _ => rw [Nat.add_zero, getElem_writeMap8_0, hbv, s0]
  | 1, _ => rw [getElem_writeMap8_1, hbv, s1]
  | 2, _ => rw [getElem_writeMap8_2, hbv, s2]
  | 3, _ => rw [getElem_writeMap8_3, hbv, s3]
  | 4, _ => rw [getElem_writeMap8_4, hbv, s4]
  | 5, _ => rw [getElem_writeMap8_5, hbv, s5]
  | 6, _ => rw [getElem_writeMap8_6, hbv, s6]
  | 7, _ => rw [getElem_writeMap8_7, hbv, s7]

/-- `(sp + off).toNat = sp.toNat + off` for a small `off`, under an sp-overflow
bound.  (Every frame offset in the block is `< 4096`.) -/
theorem sp_off_toNat (sp : BitVec 64) (off : Nat) (hoff : off < 4096)
    (hsp : sp.toNat + 4096 ≤ 2 ^ 64) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- `LPins8` read at byte offset `k`. -/
theorem lpins8_byte (m0 : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (bs : List (BitVec 8))
    (h : LPins8 m0 ea bs) (k : Nat) (hk : k < 8) : m0[ea + k]? = some (bs.getD k 0#8) := by
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7⟩ := h
  match k, hk with
  | 0, _ => rw [Nat.add_zero]; exact p0
  | 1, _ => exact p1
  | 2, _ => exact p2
  | 3, _ => exact p3
  | 4, _ => exact p4
  | 5, _ => exact p5
  | 6, _ => exact p6
  | 7, _ => exact p7

/-! ## The concrete post-dispatch memory tower -/

/-- The post-dispatch memory is a concrete six-layer `writeMap8` tower over `m0`,
one layer per `sd`.  Holds by `rfl` — the reflected log reduces to the six store
entries.  `neDispatch` gives the SAME tower (byte-identical block). -/
theorem eqDispatch_mem_tower (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) :
    writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log
      = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
          (sp + 0x40#64).toNat (sdData_val (bytesVal .ld b0)))
          (sp + 0x48#64).toNat (sdData_val (bytesVal .ld b1)))
          (sp + 0x50#64).toNat (sdData_val (bytesVal .ld b2)))
          (sp + 0x20#64).toNat (sdData_val (bytesVal .ld b3)))
          (sp + 0x28#64).toNat (sdData_val (bytesVal .ld b4)))
          (sp + 0x30#64).toNat (sdData_val (bytesVal .ld b5)) := rfl

theorem neDispatch_mem_tower (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) :
    writeLog m0 (evalBlocks neDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log
      = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
          (sp + 0x40#64).toNat (sdData_val (bytesVal .ld b0)))
          (sp + 0x48#64).toNat (sdData_val (bytesVal .ld b1)))
          (sp + 0x50#64).toNat (sdData_val (bytesVal .ld b2)))
          (sp + 0x20#64).toNat (sdData_val (bytesVal .ld b3)))
          (sp + 0x28#64).toNat (sdData_val (bytesVal .ld b4)))
          (sp + 0x30#64).toNat (sdData_val (bytesVal .ld b5)) := rfl

/-! ## Tower byte-reads: the copy (`bufa`/`bufb`) and the disjoint frame -/

section Tower
variable (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
  (b0 b1 b2 b3 b4 b5 : List (BitVec 8))

/-- Abbreviation for the six-layer tower (`= eqDispatch`/`neDispatch` post memory). -/
def eqTower : Std.ExtHashMap Nat (BitVec 8) :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
    (sp + 0x40#64).toNat (sdData_val (bytesVal .ld b0)))
    (sp + 0x48#64).toNat (sdData_val (bytesVal .ld b1)))
    (sp + 0x50#64).toNat (sdData_val (bytesVal .ld b2)))
    (sp + 0x20#64).toNat (sdData_val (bytesVal .ld b3)))
    (sp + 0x28#64).toNat (sdData_val (bytesVal .ld b4)))
    (sp + 0x30#64).toNat (sdData_val (bytesVal .ld b5))

/-- All six window `.toNat`s, normalized. -/
private theorem win_norm (hsp : sp.toNat + 4096 ≤ 2 ^ 64) :
    (sp + 0x40#64).toNat = sp.toNat + 64 ∧ (sp + 0x48#64).toNat = sp.toNat + 72 ∧
    (sp + 0x50#64).toNat = sp.toNat + 80 ∧ (sp + 0x20#64).toNat = sp.toNat + 32 ∧
    (sp + 0x28#64).toNat = sp.toNat + 40 ∧ (sp + 0x30#64).toNat = sp.toNat + 48 :=
  ⟨sp_off_toNat sp 64 (by omega) hsp, sp_off_toNat sp 72 (by omega) hsp,
   sp_off_toNat sp 80 (by omega) hsp, sp_off_toNat sp 32 (by omega) hsp,
   sp_off_toNat sp 40 (by omega) hsp, sp_off_toNat sp 48 (by omega) hsp⟩

/-- A byte outside all six windows (i.e. outside `[sp+0x20, sp+0x58)` on the frame)
passes through the tower to `m0`. -/
theorem eqTower_outside (hsp : sp.toNat + 4096 ≤ 2 ^ 64) (a : Nat)
    (ha : a < sp.toNat + 32 ∨ sp.toNat + 88 ≤ a) :
    (eqTower sp m0 b0 b1 b2 b3 b4 b5)[a]? = m0[a]? := by
  obtain ⟨e40,e48,e50,e20,e28,e30⟩ := win_norm sp hsp
  unfold eqTower
  rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30]; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by rw [e28]; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by rw [e20]; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by rw [e50]; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by rw [e48]; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by rw [e40]; omega)]

/-- The `bufa` window copy: the 24 bytes at `bufa = sp+0x40` in the tower equal the
24 bytes at the source `sp+0x78` in `m0`, given the three source `LPins8`
(`b0`@`0x78`, `b1`@`0x80`, `b2`@`0x88`). -/
theorem eqTower_copy_bufa (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    (h0 : LPins8 m0 (sp + 0x78#64).toNat b0) (h1 : LPins8 m0 (sp + 0x80#64).toNat b1)
    (h2 : LPins8 m0 (sp + 0x88#64).toNat b2) :
    ∀ j, j < 24 → (eqTower sp m0 b0 b1 b2 b3 b4 b5)[(sp + 0x40#64).toNat + j]?
      = m0[(sp + 0x78#64).toNat + j]? := by
  obtain ⟨e40,e48,e50,e20,e28,e30⟩ := win_norm sp hsp
  have e78 : (sp + 0x78#64).toNat = sp.toNat + 120 := sp_off_toNat sp 120 (by omega) hsp
  have e80 : (sp + 0x80#64).toNat = sp.toNat + 128 := sp_off_toNat sp 128 (by omega) hsp
  have e88 : (sp + 0x88#64).toNat = sp.toNat + 136 := sp_off_toNat sp 136 (by omega) hsp
  intro j hj
  unfold eqTower
  -- split j into which of the three bufa words it hits
  by_cases hj0 : j < 8
  · -- word 0: window 0x40 (innermost), peel the 5 outer disjoint layers
    rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30, e40]; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rw [e28, e40]; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rw [e20, e40]; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rw [e50, e40]; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rw [e48, e40]; omega),
        writeMap8_ld_byte _ (sp + 0x40#64).toNat b0 j hj0]
    rw [show (sp + 0x78#64).toNat + j = (sp + 0x78#64).toNat + j from rfl]
    exact (lpins8_byte m0 (sp + 0x78#64).toNat b0 h0 j hj0).symm
  · by_cases hj1 : j < 16
    · -- word 1: window 0x48; index = 0x48 + (j-8)
      have hk : j - 8 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30, e40]; omega),
          getElem_writeMap8_disjoint _ _ _ _ (by rw [e28, e40]; omega),
          getElem_writeMap8_disjoint _ _ _ _ (by rw [e20, e40]; omega),
          getElem_writeMap8_disjoint _ _ _ _ (by rw [e50, e40]; omega)]
      rw [show (sp + 0x40#64).toNat + j = (sp + 0x48#64).toNat + (j - 8) by rw [e40, e48]; omega,
          writeMap8_ld_byte _ (sp + 0x48#64).toNat b1 (j - 8) hk,
          show (sp + 0x78#64).toNat + j = (sp + 0x80#64).toNat + (j - 8) by rw [e78, e80]; omega]
      exact (lpins8_byte m0 (sp + 0x80#64).toNat b1 h1 (j - 8) hk).symm
    · -- word 2: window 0x50 (outermost of the bufa three); index = 0x50 + (j-16)
      have hk : j - 16 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30, e40]; omega),
          getElem_writeMap8_disjoint _ _ _ _ (by rw [e28, e40]; omega),
          getElem_writeMap8_disjoint _ _ _ _ (by rw [e20, e40]; omega)]
      rw [show (sp + 0x40#64).toNat + j = (sp + 0x50#64).toNat + (j - 16) by rw [e40, e50]; omega,
          writeMap8_ld_byte _ (sp + 0x50#64).toNat b2 (j - 16) hk,
          show (sp + 0x78#64).toNat + j = (sp + 0x88#64).toNat + (j - 16) by rw [e78, e88]; omega]
      exact (lpins8_byte m0 (sp + 0x88#64).toNat b2 h2 (j - 16) hk).symm

/-- The `bufb` window copy: the 24 bytes at `bufb = sp+0x20` in the tower equal the
24 bytes at the source `sp+0x90` in `m0`, given the three source `LPins8`
(`b3`@`0x90`, `b4`@`0x98`, `b5`@`0xa0`). -/
theorem eqTower_copy_bufb (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    (h3 : LPins8 m0 (sp + 0x90#64).toNat b3) (h4 : LPins8 m0 (sp + 0x98#64).toNat b4)
    (h5 : LPins8 m0 (sp + 0xa0#64).toNat b5) :
    ∀ j, j < 24 → (eqTower sp m0 b0 b1 b2 b3 b4 b5)[(sp + 0x20#64).toNat + j]?
      = m0[(sp + 0x90#64).toNat + j]? := by
  obtain ⟨e40,e48,e50,e20,e28,e30⟩ := win_norm sp hsp
  have e90 : (sp + 0x90#64).toNat = sp.toNat + 144 := sp_off_toNat sp 144 (by omega) hsp
  have e98 : (sp + 0x98#64).toNat = sp.toNat + 152 := sp_off_toNat sp 152 (by omega) hsp
  have ea0 : (sp + 0xa0#64).toNat = sp.toNat + 160 := sp_off_toNat sp 160 (by omega) hsp
  intro j hj
  unfold eqTower
  by_cases hj0 : j < 8
  · -- word 0: window 0x20; peel 3 outer (0x30,0x28) hit at 0x20, but 0x50/0x48/0x40 are ABOVE
    rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30, e20]; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rw [e28, e20]; omega),
        writeMap8_ld_byte _ (sp + 0x20#64).toNat b3 j hj0]
    exact (lpins8_byte m0 (sp + 0x90#64).toNat b3 h3 j hj0).symm
  · by_cases hj1 : j < 16
    · have hk : j - 8 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by rw [e30, e20]; omega)]
      rw [show (sp + 0x20#64).toNat + j = (sp + 0x28#64).toNat + (j - 8) by rw [e20, e28]; omega,
          writeMap8_ld_byte _ (sp + 0x28#64).toNat b4 (j - 8) hk,
          show (sp + 0x90#64).toNat + j = (sp + 0x98#64).toNat + (j - 8) by rw [e90, e98]; omega]
      exact (lpins8_byte m0 (sp + 0x98#64).toNat b4 h4 (j - 8) hk).symm
    · have hk : j - 16 < 8 := by omega
      rw [show (sp + 0x20#64).toNat + j = (sp + 0x30#64).toNat + (j - 16) by rw [e20, e30]; omega,
          writeMap8_ld_byte _ (sp + 0x30#64).toNat b5 (j - 16) hk,
          show (sp + 0x90#64).toNat + j = (sp + 0xa0#64).toNat + (j - 16) by rw [e90, ea0]; omega]
      exact (lpins8_byte m0 (sp + 0xa0#64).toNat b5 h5 (j - 16) hk).symm

/-! ## The reusable readback core -/

/-- **`valueRepr_of_reflected_copy`.**  Read a copied 24-byte `ValueRepr` out of the
reflected `eq`/`ne` dispatch tower.  Given the SOURCE repr `hv` on the entry memory
`m0` at `srcAddr`, the 24-byte copy `hcopy` (`mem` = source at the destination
window; supplied by `eqTower_copy_bufa`/`eqTower_copy_bufb`), and the payload-region
disjointness `hpaydisj` (the value's dereferenced string lives outside the frame
scribble window `[sp+0x20, sp+0x58)`, so it is preserved across the six stores),
conclude the DESTINATION repr on the post-dispatch memory `mem = eqTower …`.

Instantiated with `dstAddr := (sp+0x40).toNat`, `srcAddr := (sp+0x78).toNat` for
`bufa`, and `dstAddr := (sp+0x20).toNat`, `srcAddr := (sp+0x90).toNat` for `bufb`;
since `neDispatch` yields the identical tower (`neDispatch_mem_tower`), the same
lemma serves `ne`. -/
theorem valueRepr_of_reflected_copy (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    {N : NativeAddrs} {φc : Addr → Nat} {srcAddr dstAddr : Nat} {v : Value}
    (hcopy : ∀ j, j < 24 → (eqTower sp m0 b0 b1 b2 b3 b4 b5)[dstAddr + j]? = m0[srcAddr + j]?)
    (hpaydisj : ∀ (p : Nat) (s : String), read64 m0 (srcAddr + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat + 32 ∨ sp.toNat + 88 ≤ p + k))
    (hv : ValueRepr m0 N φc srcAddr v) :
    ValueRepr (eqTower sp m0 b0 b1 b2 b3 b4 b5) N φc dstAddr v := by
  refine valueRepr_copy hcopy ?_ hv
  intro p s hp a ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact (eqTower_outside sp m0 b0 b1 b2 b3 b4 b5 hsp (p + k) (hpaydisj p s hp k hk)).symm

end Tower

/-! ## Post-dispatch specialization: the two buffer reprs on the `EqDispatchPostS` memory

`EqDispatchPostS`/`NeDispatchPostS` carry
`c.σ.mem = writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) lds)).log`.
When `lds` is the six-element load list the block consumes, that memory is exactly
`eqTower …` (`eqDispatch_mem_tower`), so the copy lemmas apply directly. -/

/-- **`bufa` repr on the post-dispatch memory.**  From the source repr at `sp+0x78`
(the callee-frame slot the block reloads `vl` from — same address as the caller's
`sp-968`), the three source `LPins8` (block `ChainFacts`), and the payload
disjointness, conclude `ValueRepr mem N φc (sp+0x40).toNat vl` where `mem` is the
`eqDispatch`/`neDispatch` post-dispatch memory. -/
theorem eqDispatch_bufa_repr (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    {N : NativeAddrs} {φc : Addr → Nat} {vl : Value}
    (h0 : LPins8 m0 (sp + 0x78#64).toNat b0) (h1 : LPins8 m0 (sp + 0x80#64).toNat b1)
    (h2 : LPins8 m0 (sp + 0x88#64).toNat b2)
    (hpaydisj : ∀ (p : Nat) (s : String), read64 m0 ((sp + 0x78#64).toNat + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat + 32 ∨ sp.toNat + 88 ≤ p + k))
    (hvl : ValueRepr m0 N φc (sp + 0x78#64).toNat vl) :
    ValueRepr
      (writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log)
      N φc (sp + 0x40#64).toNat vl := by
  rw [eqDispatch_mem_tower]
  exact valueRepr_of_reflected_copy sp m0 b0 b1 b2 b3 b4 b5 hsp
    (eqTower_copy_bufa sp m0 b0 b1 b2 b3 b4 b5 hsp h0 h1 h2) hpaydisj hvl

/-- **`bufb` repr on the post-dispatch memory.**  Source at `sp+0x90` (= caller
`sp-944`), destination `bufb = sp+0x20`. -/
theorem eqDispatch_bufb_repr (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    {N : NativeAddrs} {φc : Addr → Nat} {vr : Value}
    (h3 : LPins8 m0 (sp + 0x90#64).toNat b3) (h4 : LPins8 m0 (sp + 0x98#64).toNat b4)
    (h5 : LPins8 m0 (sp + 0xa0#64).toNat b5)
    (hpaydisj : ∀ (p : Nat) (s : String), read64 m0 ((sp + 0x90#64).toNat + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat + 32 ∨ sp.toNat + 88 ≤ p + k))
    (hvr : ValueRepr m0 N φc (sp + 0x90#64).toNat vr) :
    ValueRepr
      (writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log)
      N φc (sp + 0x20#64).toNat vr := by
  rw [eqDispatch_mem_tower]
  exact valueRepr_of_reflected_copy sp m0 b0 b1 b2 b3 b4 b5 hsp
    (eqTower_copy_bufb sp m0 b0 b1 b2 b3 b4 b5 hsp h3 h4 h5) hpaydisj hvr

/-- `ne` sibling for `bufa`: identical tower, so identical proof (via
`neDispatch_mem_tower`). -/
theorem neDispatch_bufa_repr (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    {N : NativeAddrs} {φc : Addr → Nat} {vl : Value}
    (h0 : LPins8 m0 (sp + 0x78#64).toNat b0) (h1 : LPins8 m0 (sp + 0x80#64).toNat b1)
    (h2 : LPins8 m0 (sp + 0x88#64).toNat b2)
    (hpaydisj : ∀ (p : Nat) (s : String), read64 m0 ((sp + 0x78#64).toNat + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat + 32 ∨ sp.toNat + 88 ≤ p + k))
    (hvl : ValueRepr m0 N φc (sp + 0x78#64).toNat vl) :
    ValueRepr
      (writeLog m0 (evalBlocks neDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log)
      N φc (sp + 0x40#64).toNat vl := by
  rw [neDispatch_mem_tower]
  exact valueRepr_of_reflected_copy sp m0 b0 b1 b2 b3 b4 b5 hsp
    (eqTower_copy_bufa sp m0 b0 b1 b2 b3 b4 b5 hsp h0 h1 h2) hpaydisj hvl

/-- `ne` sibling for `bufb`. -/
theorem neDispatch_bufb_repr (sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 b4 b5 : List (BitVec 8)) (hsp : sp.toNat + 4096 ≤ 2 ^ 64)
    {N : NativeAddrs} {φc : Addr → Nat} {vr : Value}
    (h3 : LPins8 m0 (sp + 0x90#64).toNat b3) (h4 : LPins8 m0 (sp + 0x98#64).toNat b4)
    (h5 : LPins8 m0 (sp + 0xa0#64).toNat b5)
    (hpaydisj : ∀ (p : Nat) (s : String), read64 m0 ((sp + 0x90#64).toNat + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat + 32 ∨ sp.toNat + 88 ≤ p + k))
    (hvr : ValueRepr m0 N φc (sp + 0x90#64).toNat vr) :
    ValueRepr
      (writeLog m0 (evalBlocks neDispatch (SegEvalState.init (eqDispL sp) [b0,b1,b2,b3,b4,b5])).log)
      N φc (sp + 0x20#64).toNat vr := by
  rw [neDispatch_mem_tower]
  exact valueRepr_of_reflected_copy sp m0 b0 b1 b2 b3 b4 b5 hsp
    (eqTower_copy_bufb sp m0 b0 b1 b2 b3 b4 b5 hsp h3 h4 h5) hpaydisj hvr

#print axioms writeMap8_ld_byte
#print axioms eqDispatch_mem_tower
#print axioms neDispatch_mem_tower
#print axioms eqTower_copy_bufa
#print axioms eqTower_copy_bufb
#print axioms eqTower_outside
#print axioms valueRepr_of_reflected_copy
#print axioms eqDispatch_bufa_repr
#print axioms eqDispatch_bufb_repr
#print axioms neDispatch_bufa_repr
#print axioms neDispatch_bufb_repr

end Vsa.Sim
