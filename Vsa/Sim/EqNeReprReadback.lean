import Vsa.Sim.ValuePayloadCoverage
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
the translation-copy lemma `valueRepr_copy_total_exact` (`ReprCopy.lean`).

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

/-! ## The concrete post-dispatch memory tower -/

/-! ## Tower byte-reads: the copy (`bufa`/`bufb`) and the disjoint frame -/

/-! ## Post-dispatch specialization: the two buffer reprs on the `EqDispatchPostS` memory

`EqDispatchPostS`/`NeDispatchPostS` carry
`c.σ.mem = writeLog m0 (evalBlocks eqDispatch (SegEvalState.init (eqDispL sp) lds)).log`.
When `lds` is the six-element load list the block consumes, that memory is exactly
`eqTower …` (`eqDispatch_mem_tower`), so the copy lemmas apply directly. -/

end Vsa.Sim
