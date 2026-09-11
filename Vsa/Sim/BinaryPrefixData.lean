import Vsa.Sim.BinaryPrefixSegments
import Vsa.Sim.BinHeadSites
import Vsa.Sim.WordLoadData
import Vsa.Sim.SegFrameFacts

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr

namespace Vsa.Sim.BinaryPrefix

/-- Local node and parent-frame windows used by both argument prefixes. -/
structure Geometry (node sp : BitVec 64) : Prop where
  nodeLo : 0x80000000 ≤ node.toNat
  nodeHi : node.toNat + 32 ≤ 0x100000000
  nodeHtif : node.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 8 ≤ node.toNat
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 1056 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  stackAlign : sp.toNat % 8 = 0

/-- Each generated store uses a bounded, aligned offset in the same parent frame. -/
theorem store_facts {m : Mem} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    {node sp : BitVec 64} (geometry : Geometry node sp) (off : Nat)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 1056) (halign : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by have := geometry.stackHi; omega)]
  apply memFacts_sd_frame m L a bs hk
  all_goals
    rw [hea]
    have := geometry.stackLo
    have := geometry.stackHi
    have := geometry.stackHtif
    have := geometry.stackAlign
    omega

/-- The represented left pointer supplies the only read of the first prefix. -/
structure FirstData (m : Mem) (node sp saved env left : BitVec 64)
    (bs : List (BitVec 8)) : Prop where
  load : WordLoadFacts m (firstInput node sp saved env)
    (mkLine 0x800034e8#64 0x01063603#32) left bs
  facts : ChainFacts m m (firstInput node sp saved env) [bs] firstSeg

theorem first_data (m : Mem) (node sp saved env left : BitVec 64)
    (geometry : Geometry node sp) (hcode : Code.Eval_exprLoaded m)
    (hread : read64 m (node.toNat + 16) = some left.toNat) :
    ∃ bs, FirstData m node sp saved env left bs := by
  have hea : (eaddrM (mkLine 0x800034e8#64 0x01063603#32)
      (firstInput node sp saved env)).toNat = node.toNat + 16 :=
    off_ed_10 node (by have := geometry.nodeHi; omega)
  obtain ⟨bs, hw⟩ := wordLoadFacts_of_read64 m (firstInput node sp saved env)
    (mkLine 0x800034e8#64 0x01063603#32) left (by rfl)
    (by rw [hea]; have := geometry.nodeLo; omega)
    (by rw [hea]; have := geometry.nodeHi; omega)
    (by rw [hea]; have := geometry.nodeHtif; omega)
    (by rw [hea]; exact hread)
  refine ⟨bs, hw, ?_⟩
  chain_facts hcode with "Vsa.Sim.Code.eval_expr_at_"
  · exact hw.facts
  · exact store_facts geometry 1048 (by decide) (by rfl) (by decide) (by decide) (by decide)
  · exact store_facts geometry 0 (by decide) (by rfl) (by decide) (by decide) (by decide)

#print axioms store_facts
#print axioms first_data

end Vsa.Sim.BinaryPrefix
