import Vsa.Sim.rows.CallClosureFoldStage
import Vsa.Sim.HelperCall
import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.WordLoadData
import Vsa.Sim.RuntimeOwnershipCopy

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Read windows and the caller's staging buffer for one parameter. -/
structure Geometry (m : Mem) (sp cursor closure cell : BitVec 64) : Prop where
  stack : FrameBundle m sp
  sourceLo : 0x80000000 ≤ cursor.toNat
  sourceHi : cursor.toNat + 24 ≤ 0x100000000
  sourceHtif : tohostAddr + 8 ≤ cursor.toNat
  sourceAfter : sp.toNat + 88 ≤ cursor.toNat
  closureLo : 0x80000000 ≤ closure.toNat + 16
  closureHi : closure.toNat + 24 ≤ 0x100000000
  closureHtif : closure.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ closure.toNat + 16
  cellLo : 0x80000000 ≤ cell.toNat
  cellHi : cell.toNat + 8 ≤ 0x100000000
  cellHtif : cell.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ cell.toNat
  cellOff : cell.toNat + 8 ≤ sp.toNat ∨ sp.toNat + 88 ≤ cell.toNat
  codeOff : sp.toNat + 88 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sp.toNat

def loads (m : Mem) (cursor closure cell : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m cursor.toNat,
   EvalChildArm.wordLds8 m (closure.toNat + 16),
   EvalChildArm.wordLds8 m (cursor.toNat + 8),
   EvalChildArm.wordLds8 m (cursor.toNat + 16),
   EvalChildArm.wordLds8 m cell.toNat]

def writes (m : Mem) (sp cursor index : BitVec 64) : List WEntry :=
  [(sp.toNat + 64, 8, bytesVal .ld (EvalChildArm.wordLds8 m cursor.toNat)),
   (sp.toNat + 72, 8, bytesVal .ld (EvalChildArm.wordLds8 m (cursor.toNat + 8))),
   (sp.toNat, 8, index),
   (sp.toNat + 80, 8, bytesVal .ld (EvalChildArm.wordLds8 m (cursor.toNat + 16)))]

/-- Stack addresses of the existing span, without modular wraparound. -/
theorem Geometry.stackAddr {m : Mem} {sp cursor closure cell : BitVec 64}
    (G : Geometry m sp cursor closure cell) (off : Nat) (bound : off ≤ 264) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show off < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp.toNat + off < 2^64 by have := G.stack.hi; omega)]

/-- A frozen total-read window remains valid through the preceding stores. -/
private theorem loadFacts {m m' : Mem} {L : GRegs} {a : MInstr} {addr : Nat}
    (kind : a.kind = .ld) (address : (eaddrM a L).toNat = addr)
    (lo : 0x80000000 ≤ addr) (hi : addr + 8 ≤ 0x100000000)
    (htif : addr + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr)
    (agree : ∀ j, j < 8 → m'[addr + j]? = m[addr + j]?) :
    MemFacts m' L (EvalChildArm.wordLds8 m addr) a := by
  unfold MemFacts
  rw [kind, address]
  refine ⟨⟨lo, hi, htif⟩, ?_⟩
  simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨by simpa only [Nat.add_zero] using congrArg (fun b => b.getD 0) (agree 0 (by decide)),
    congrArg (fun b => b.getD 0) (agree 1 (by decide)),
    congrArg (fun b => b.getD 0) (agree 2 (by decide)),
    congrArg (fun b => b.getD 0) (agree 3 (by decide)),
    congrArg (fun b => b.getD 0) (agree 4 (by decide)),
    congrArg (fun b => b.getD 0) (agree 5 (by decide)),
    congrArg (fun b => b.getD 0) (agree 6 (by decide)),
    congrArg (fun b => b.getD 0) (agree 7 (by decide))⟩

/-- The reflected memory is exactly the three argument words and saved index. -/
theorem log (m : Mem) (sp cursor index scope closure cell : BitVec 64)
    (G : Geometry m sp cursor closure cell) :
    (evalBlocks callClosureFoldStageSeg (SegEvalState.init
      (callClosureFoldStageL sp cursor index scope closure) (loads m cursor closure cell))).log =
      writes m sp cursor index := by
  change [((sp + 64#64).toNat, 8, _), ((sp + 72#64).toNat, 8, _),
    ((sp + 0#64).toNat, 8, index), ((sp + 80#64).toNat, 8, _)] = _
  rw [G.stackAddr 64 (by decide), G.stackAddr 72 (by decide), BitVec.add_zero,
    G.stackAddr 80 (by decide)]
  rfl

/-- Every later argument/name read uses the reached memory after prior stores. -/
theorem facts (m : Mem) (sp cursor index scope closure names : BitVec 64)
    (G : Geometry m sp cursor closure (names + index))
    (code : Code.Eval_exprLoaded m)
    (namesRead : read64 m (closure.toNat + 16) = some names.toNat) :
    ChainFacts m m (callClosureFoldStageL sp cursor index scope closure)
      (loads m cursor closure (names + index)) callClosureFoldStageSeg := by
  have namesValue := EvalChildArm.bytesVal_ld_wordLds m (closure.toNat + 16) names namesRead
  have closureAddr : (closure + 16#64).toNat = closure.toNat + 16 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := G.closureHi; change closure.toNat + 16 < 2^64; omega)]
    rfl
  have cursorAddr (off : Nat) (bound : off ≤ 16) :
      (cursor + BitVec.ofNat 64 off).toNat = cursor.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show off < 2^64 by omega),
      Nat.mod_eq_of_lt (show cursor.toNat + off < 2^64 by have := G.sourceHi; omega)]
  have stack64 := G.stackAddr 64 (by decide)
  have stack72 := G.stackAddr 72 (by decide)
  have stack80 := G.stackAddr 80 (by decide)
  chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  · apply loadFacts rfl
      (by change (cursor + 0#64).toNat = cursor.toNat; rw [BitVec.add_zero])
      G.sourceLo (by have := G.sourceHi; omega) (Or.inr G.sourceHtif)
    intro j _; rfl
  · apply loadFacts rfl (by exact closureAddr) G.closureLo G.closureHi G.closureHtif
    intro j _; rfl
  · exact frame_sd_auto _ m _ _ sp _ G.stack rfl rfl (by decide) (by decide)
  · apply loadFacts rfl (by exact cursorAddr 8 (by decide))
      (by have := G.sourceLo; omega) (by have := G.sourceHi; omega)
      (Or.inr (by have := G.sourceHtif; omega))
    intro j hj
    change (writeMap8 m (sp + 64#64).toNat _)[cursor.toNat + 8 + j]? = _
    rw [stack64]
    exact getElem_writeMap8_disjoint _ _ _ _ (by have := G.sourceAfter; omega)
  · exact frame_sd_auto _ m _ _ sp _ G.stack rfl rfl (by decide) (by decide)
  · apply loadFacts rfl (by exact cursorAddr 16 (by decide))
      (by have := G.sourceLo; omega) (by have := G.sourceHi; omega)
      (Or.inr (by have := G.sourceHtif; omega))
    intro j hj
    change (writeMap8 (writeMap8 m (sp + 64#64).toNat _) (sp + 72#64).toNat _)[cursor.toNat + 16 + j]? = _
    rw [stack64, stack72,
      getElem_writeMap8_disjoint _ _ _ _ (by have := G.sourceAfter; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by have := G.sourceAfter; omega)]
  · exact frame_sd_auto _ m _ _ sp _ G.stack rfl rfl (by decide) (by decide)
  · exact frame_sd_auto _ m _ _ sp _ G.stack rfl rfl (by decide) (by decide)
  · apply loadFacts rfl
      (by change (bytesVal .ld (EvalChildArm.wordLds8 m (closure.toNat + 16)) + index + 0#64).toNat = _
          rw [namesValue, BitVec.add_zero])
      G.cellLo G.cellHi G.cellHtif
    intro j hj
    change (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp + 64#64).toNat _)
      (sp + 72#64).toNat _) (sp + 0#64).toNat _) (sp + 80#64).toNat _)[(names + index).toNat + j]? = _
    rw [stack64, stack72, stack80, BitVec.add_zero]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := G.cellOff; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by have := G.cellOff; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by have := G.cellOff; omega),
      getElem_writeMap8_disjoint _ _ _ _ (by have := G.cellOff; omega)]

private theorem writeMap8_observe {m m' : Mem} (a k : Nat) (d : BitVec (8 * 8))
    (h : m[k]? = m'[k]?) : (writeMap8 m a d)[k]? = (writeMap8 m' a d)[k]? := by
  simp only [writeMap8, Std.ExtHashMap.getElem?_insert, h]

/-- The saved index does not alter the three-word copy at sp+64. -/
theorem copied (m : Mem) (sp cursor index : BitVec 64) :
    ∀ j, j < 24 → (writeLog m (writes m sp cursor index))[sp.toNat + 64 + j]? =
      some ((m[cursor.toNat + j]?).getD 0) := by
  intro j hj
  have eqCopy : (writeLog m (writes m sp cursor index))[sp.toNat + 64 + j]? =
      (copy3Log m cursor.toNat (sp.toNat + 64))[sp.toNat + 64 + j]? := by
    change (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp.toNat + 64) _)
      (sp.toNat + 72) _) sp.toNat _) (sp.toNat + 80) _)[sp.toNat + 64 + j]? =
      (writeMap8 (writeMap8 (writeMap8 m (sp.toNat + 64) _)
        (sp.toNat + 64 + 8) _) (sp.toNat + 64 + 16) _)[sp.toNat + 64 + j]?
    simp only [Nat.add_assoc, Nat.reduceAdd]
    apply writeMap8_observe
    exact getElem_writeMap8_disjoint _ _ _ _ (Or.inr (by omega))
  exact eqCopy.trans (copy3_total m cursor.toNat (sp.toNat + 64) j hj)

#print axioms facts
#print axioms copied

end Vsa.Sim.ClosureParam
