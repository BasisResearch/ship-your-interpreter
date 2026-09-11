import Vsa.Sim.rows.CallClosureDispatchStage
import Vsa.Sim.ClosureCallData
import Vsa.Sim.SnprintfSpec3

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Physical windows used by the existing closure dispatch and env_new call span. -/
structure Geometry (sp call object fn interp : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 1056 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  stackAlign : sp.toNat % 8 = 0
  callLo : 0x80000000 ≤ call.toNat + 4
  callHi : call.toNat + 8 ≤ 0x100000000
  callHtif : call.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ call.toNat + 4
  objectLo : 0x80000000 ≤ object.toNat
  objectHi : object.toNat + 16 ≤ 0x100000000
  objectHtif : object.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ object.toNat
  objectOff : object.toNat + 16 ≤ sp.toNat ∨ sp.toNat + 1056 ≤ object.toNat
  objectInterp : object.toNat + 16 ≤ interp.toNat + 8 ∨ interp.toNat + 12 ≤ object.toNat
  fnLo : 0x80000000 ≤ fn.toNat + 24
  fnHi : fn.toNat + 28 ≤ 0x100000000
  fnHtif : fn.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 8 ≤ fn.toNat + 24
  fnOff : fn.toNat + 28 ≤ sp.toNat ∨ sp.toNat + 1056 ≤ fn.toNat + 24
  interpAbove : sp.toNat + 1056 ≤ interp.toNat
  interpHi : interp.toNat + 12 ≤ 0x100000000
  interpAlign : interp.toNat % 4 = 0

/-- Semantic reads determining the closure, arity, and depth branches. -/
structure Reads (m : Mem) (sp object fn interp : BitVec 64) (count depth : Nat) : Prop where
  kind : read32 m (sp.toNat + 96) = some 4
  objectRead : read64 m (sp.toNat + 104) = some object.toNat
  nodeRead : read64 m object.toNat = some fn.toNat
  countRead : read32 m (fn.toNat + 24) = some count
  depthRead : read32 m (interp.toNat + 8) = some depth
  countBound : count ≤ 32
  depthBound : depth < 1000

/-- The represented callee and owned closure supply the dispatch's semantic reads. -/
theorem reads_of_closure {m : Mem} {N : NativeAddrs} {phiF phiC : Addr → Nat}
    {shared : Nat → Prop} {ca fn names body : Nat} {cd : ClosureData}
    {sp interp : BitVec 64} {count depth : Nat}
    (closure : ClosureObjectReads m phiF phiC shared ca fn names body cd)
    (callee : ValueRepr m N phiC (sp.toNat + 96) (.closure ca))
    (arity : count = cd.params.length) (countBound : count ≤ 32)
    (depthRead : read32 m (interp.toNat + 8) = some depth) (depthBound : depth < 1000) :
    Reads m sp (BitVec.ofNat 64 (phiC ca)) (BitVec.ofNat 64 fn) interp count depth := by
  rcases callee with ⟨kind, payload, _⟩
  have objectNat : (BitVec.ofNat 64 (phiC ca)).toNat = phiC ca := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ payload)]
  have fnNat : (BitVec.ofNat 64 fn).toNat = fn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ closure.nodeRead)]
  exact
    { kind := kind, objectRead := by simpa only [objectNat, Nat.add_assoc] using payload
      nodeRead := by rw [objectNat, fnNat]; exact closure.nodeRead
      countRead := by rw [fnNat, arity]; exact closure.node.countRead
      depthRead := depthRead, countBound := countBound, depthBound := depthBound }

def loads (m : Mem) (sp call object fn interp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (sp.toNat + 96), EvalChildArm.wordLds8 m (sp.toNat + 104),
   EvalChildArm.wordLds8 m (sp.toNat + 112), wordLds4 m (call.toNat + 4),
   wordLds4 m (sp.toNat + 96), EvalChildArm.wordLds8 m object.toNat,
   wordLds4 m (fn.toNat + 24), wordLds4 m (interp.toNat + 8),
   EvalChildArm.wordLds8 m (object.toNat + 8)]

def writes (m : Mem) (sp object interp saved5 saved3 : BitVec 64) (count depth : Nat) : List WEntry :=
  [(sp.toNat + 120, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 96))),
   (sp.toNat + 128, 8, object),
   (sp.toNat + 136, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 112))),
   (sp.toNat + 1032, 8, saved5), (interp.toNat + 8, 4, BitVec.ofNat 64 (depth + 1)),
   (sp.toNat + 1048, 8, saved3), (sp.toNat, 8, BitVec.ofNat 64 count)]

theorem Geometry.stackAddr {sp call object fn interp : BitVec 64}
    (G : Geometry sp call object fn interp) (off : Nat) (bound : off ≤ 1056) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp.toNat + off < 2^64 by have := G.stackHi; omega)]

theorem Geometry.interpAddr {sp call object fn interp : BitVec 64}
    (G : Geometry sp call object fn interp) : (interp + 8#64).toNat = interp.toNat + 8 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.interpHi; change interp.toNat + 8 < 2^64; omega)]
  rfl

/-- The reflected span writes only the caller spills and incremented interpreter depth. -/
theorem log {m : Mem} {sp call object fn interp : BitVec 64} {count depth : Nat}
    (G : Geometry sp call object fn interp) (h : Reads m sp object fn interp count depth)
    (a3 saved5 saved3 : BitVec 64) :
    (evalBlocks callClosureDispatchStageSeg (SegEvalState.init
      (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
      (loads m sp call object fn interp))).log = writes m sp object interp saved5 saved3 count depth := by
  have payload := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 104) object h.objectRead
  have depthValue := bytesVal_lw_wordLds4 m (interp.toNat + 8) depth (by have := h.depthBound; omega) h.depthRead
  simp [callClosureDispatchStageSeg, evalBlocks, evalBlock, SegEvalState.init,
    callClosureDispatchStageL, loads, writes, wlogM, wentryM, widthOfM,
    runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG,
    mkLine, decodeM, eaddrM, payload, depthValue]
  change (sp + 120#64).toNat = sp.toNat + 120 ∧
    (sp + 128#64).toNat = sp.toNat + 128 ∧
    (sp + 136#64).toNat = sp.toNat + 136 ∧
    (sp + 1032#64).toNat = sp.toNat + 1032 ∧
    ((interp + 8#64).toNat = interp.toNat + 8 ∧
      sign_extend (m := 64) (Sail.BitVec.extractLsb
        (BitVec.ofNat 64 depth + sign_extend (m := 64) (1#12)) 31 0) =
        BitVec.ofNat 64 (depth + 1)) ∧
    (sp + 1048#64).toNat = sp.toNat + 1048 ∧ (sp + 0#64).toNat = sp.toNat
  simp only [G.stackAddr 120 (by decide), G.stackAddr 128 (by decide),
    G.stackAddr 136 (by decide), G.stackAddr 1032 (by decide),
    G.stackAddr 1048 (by decide), G.interpAddr,
    addiw1_sn3 depth (by have := h.depthBound; omega), BitVec.add_zero, and_self]

def registers (m : Mem) (sp call object fn interp : BitVec 64) (saved3 : BitVec 64)
    (count depth : Nat) : GRegs :=
  [(10, bytesVal .ld (EvalChildArm.wordLds8 m (object.toNat + 8))),
   (14, BitVec.ofNat 64 (depth + 1)), (12, 1000#64), (21, fn),
   (23, bytesVal .lw (wordLds4 m (call.toNat + 4))),
   (11, bytesVal .lw (wordLds4 m (call.toNat + 4))),
   (16, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 112))),
   (13, object),
   (2, sp), (8, call), (15, BitVec.ofNat 64 count), (18, interp), (19, saved3)]

/-- The computed registers retain the function AST and diagnostic source line. -/
theorem regs {m : Mem} {sp call object fn interp : BitVec 64} {count depth : Nat}
    (h : Reads m sp object fn interp count depth) (a3 saved5 saved3 : BitVec 64) :
    (evalBlocks callClosureDispatchStageSeg (SegEvalState.init
      (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
      (loads m sp call object fn interp))).regs =
      registers m sp call object fn interp saved3 count depth := by
  have payload := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 104) object h.objectRead
  have node := EvalChildArm.bytesVal_ld_wordLds m object.toNat fn h.nodeRead
  have depthValue := bytesVal_lw_wordLds4 m (interp.toNat + 8) depth (by have := h.depthBound; omega) h.depthRead
  have increment := addiw1_sn3 depth (by have := h.depthBound; omega)
  simp [callClosureDispatchStageSeg, evalBlocks, evalBlock, SegEvalState.init,
    callClosureDispatchStageL, loads, registers, runGM, stepGM, stepLdsM,
    ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    payload, node, depthValue, increment,
    show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
    show (sign_extend (m := 64) (1000#12) : BitVec 64) = 1000#64 by decide]

end Vsa.Sim.ClosureCallPrefix
