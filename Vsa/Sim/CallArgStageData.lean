import Vsa.Sim.rows.ArgsHeadArmStagePre
import Vsa.Sim.BinaryPrefixData
import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.SegFrameFactsAuto

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def input (sp node interp env : BitVec 64) (index count : Nat) : GRegs :=
  argsHeadBodyL sp node (BitVec.ofNat 64 index) (BitVec.ofNat 64 count) interp env

def destination (sp : BitVec 64) (index : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 (24 * index) + 976#64) + (sp + 32#64)

def writes (sp env : BitVec 64) (index count : Nat) : List WEntry :=
  [(sp.toNat + 24, 8, BitVec.ofNat 64 count),
   (sp.toNat + 16, 8, BitVec.ofNat 64 index),
   (sp.toNat + 8, 8, env), (sp.toNat, 8, destination sp index)]

/-- The call node, indexed AST cell, and caller spill region are readable RAM. -/
structure Geometry (node base sp : BitVec 64) (index count : Nat) : Prop where
  caller : BinaryPrefix.Geometry node sp
  indexBound : index < count
  countBound : count ≤ 32
  cellLo : 0x80000000 ≤ base.toNat + 8 * index
  cellHi : base.toNat + 8 * index + 8 ≤ 0x100000000
  cellHtif : base.toNat + 8 * index + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base.toNat + 8 * index

private theorem shift_small (n k : Nat) (bound : n < 2^64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt bound]

/-- The compiled sext/shift/add sequence computes the 24-byte argument offset. -/
theorem indexOffset (index : Nat) (bound : index < 32) :
    (((sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 index + sign_extend (m := 64) (0#12)) 31 0)) <<< 1) +
      sign_extend (m := 64) (Sail.BitVec.extractLsb
        (BitVec.ofNat 64 index + sign_extend (m := 64) (0#12)) 31 0)) <<< 3 =
    BitVec.ofNat 64 (24 * index) := by
  rw [sextw_ofNat_sp index (by omega), shift_small index 1 (by omega), ← BitVec.ofNat_add]
  rw [shift_small (index * 2^1 + index) 3 (by omega)]
  congr 1
  omega

/-- The spill stores the destination with the load/store displacement still attached. -/
theorem Geometry.destinationAddress {node base sp : BitVec 64} {index count : Nat}
    (G : Geometry node base sp index count) :
    (destination sp index).toNat = sp.toNat + 1008 + 24 * index := by
  unfold destination
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := G.caller.stackHi; have := G.indexBound; have := G.countBound
  simp only [Nat.mod_eq_of_lt (show 24 * index < 2^64 by omega),
    Nat.mod_eq_of_lt (show 24 * index + 976 < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp.toNat + 32 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 24 * index + 976 + (sp.toNat + 32) < 2^64 by omega)]
  omega

/-- Both reflected loads retain their actual pointer values. -/
structure Data (m : Mem) (sp node interp env base child : BitVec 64) (index count : Nat)
    (baseBytes childBytes : List (BitVec 8)) : Prop where
  facts : ChainFacts m m (input sp node interp env index count) [baseBytes, childBytes] argsHeadBodySeg
  baseValue : bytesVal .ld baseBytes = base
  childValue : bytesVal .ld childBytes = child

/-- The represented argument array supplies both machine loads. -/
theorem data (m : Mem) (sp node interp env base child : BitVec 64) (index count : Nat)
    (G : Geometry node base sp index count) (code : Code.Eval_exprLoaded m)
    (baseRead : read64 m (node.toNat + 16) = some base.toNat)
    (childRead : read64 m (base.toNat + 8 * index) = some child.toNat) :
    ∃ bb cb, Data m sp node interp env base child index count bb cb := by
  let L := input sp node interp env index count
  let loadBase := mkLine 0x800031dc#64 0x01043603#32
  let loadChild := mkLine 0x800031f4#64 0x00063603#32
  have baseAddr : (eaddrM loadBase L).toNat = node.toNat + 16 := by
    change (node + 16#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.caller.nodeHi; change node.toNat + 16 < 2^64; omega)]
    rfl
  obtain ⟨bb, B⟩ := wordLoadFacts_of_read64 m L loadBase base rfl
    (by rw [baseAddr]; have := G.caller.nodeLo; omega)
    (by rw [baseAddr]; have := G.caller.nodeHi; omega)
    (by rw [baseAddr]; have := G.caller.nodeHtif; omega) (by rw [baseAddr]; exact baseRead)
  let middle := runGM (argsHeadBodySeg[0].body.take 6) L [bb, []]
  have childAddr : (eaddrM loadChild middle).toNat = base.toNat + 8 * index := by
    change (bytesVal .ld bb + (BitVec.ofNat 64 index <<< 3) + 0#64).toNat = _
    rw [B.value, BitVec.add_zero, shift_small index 3 (by have := G.indexBound; have := G.countBound; omega)]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show index * 2^3 < 2^64 by have := G.cellHi; omega),
      Nat.mod_eq_of_lt (show base.toNat + index * 2^3 < 2^64 by have := G.cellHi; omega)]
    omega
  obtain ⟨cb, C⟩ := wordLoadFacts_of_read64 m middle loadChild child rfl
    (by rw [childAddr]; exact G.cellLo) (by rw [childAddr]; exact G.cellHi)
    (by rw [childAddr]; exact G.cellHtif) (by rw [childAddr]; exact childRead)
  refine ⟨bb, cb, ?_, B.value, C.value⟩
  chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  · exact B.facts
  · exact C.facts
  · exact BinaryPrefix.store_facts G.caller 24 rfl (by srcval_peel) rfl (by decide) (by decide)
  · exact BinaryPrefix.store_facts G.caller 16 rfl (by srcval_peel) rfl (by decide) (by decide)
  · exact BinaryPrefix.store_facts G.caller 8 rfl (by srcval_peel) rfl (by decide) (by decide)
  · exact BinaryPrefix.store_facts G.caller 0 rfl (by srcval_peel) rfl (by decide) (by decide)

def offsetRegs (sp node interp env : BitVec 64) (index count : Nat)
    (cb : List (BitVec 8)) : GRegs :=
  [(14, BitVec.ofNat 64 (24 * index)), (12, bytesVal .ld cb),
   (11, sign_extend (m := 64) (Sail.BitVec.extractLsb
     (BitVec.ofNat 64 index + sign_extend (m := 64) (0#12)) 31 0)),
   (2, sp), (8, node), (16, BitVec.ofNat 64 index), (15, BitVec.ofNat 64 count),
   (18, interp), (13, env)]

/-- Normalize the indexed address before the four spill instructions. -/
theorem offset_regs (sp node interp env : BitVec 64) (index count : Nat)
    (bb cb : List (BitVec 8)) (bound : index < 32) :
    runGM (argsHeadBodySeg[0].body.take 8) (input sp node interp env index count) [bb, cb] =
      offsetRegs sp node interp env index count cb := by
  change (14, (((sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 index + sign_extend (m := 64) (0#12)) 31 0)) <<< 1) +
      sign_extend (m := 64) (Sail.BitVec.extractLsb
        (BitVec.ofNat 64 index + sign_extend (m := 64) (0#12)) 31 0)) <<< 3) ::
    (12, bytesVal .ld cb) :: _ = _
  rw [indexOffset index bound]
  rfl

/-- The reflected stores are the four actual caller spill words. -/
theorem log (sp node interp env : BitVec 64) (index count : Nat)
    (bb cb : List (BitVec 8)) (bound : index < 32) (ram : sp.toNat + 1056 ≤ 0x100000000) :
    (evalBlocks argsHeadBodySeg (SegEvalState.init (input sp node interp env index count) [bb, cb])).log =
      writes sp env index count := by
  have address (n : Nat) (hn : n ≤ 24) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2^64 by omega), Nat.mod_eq_of_lt (show sp.toNat + n < 2^64 by omega)]
  change wlogM (argsHeadBodySeg[0].body.drop 8)
    (runGM (argsHeadBodySeg[0].body.take 8) (input sp node interp env index count) [bb, cb]) [] = _
  rw [offset_regs sp node interp env index count bb cb bound]
  change [((sp + 24#64).toNat, 8, BitVec.ofNat 64 count),
    ((sp + 16#64).toNat, 8, BitVec.ofNat 64 index), ((sp + 8#64).toNat, 8, env),
    ((sp + 0#64).toNat, 8, _)] = _
  rw [address 24 (by decide), address 16 (by decide), address 8 (by decide), BitVec.add_zero]
  rfl

end Vsa.Sim.CallArgStage
