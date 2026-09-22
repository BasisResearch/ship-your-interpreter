import Vsa.Sim.BinaryPrefixData
import Vsa.Sim.EvalChildArm

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr

namespace Vsa.Sim.BinaryPrefix

/-- Total stack loads use the bytes at their actual addresses, including dead payloads. -/
theorem total_load_facts (m : Mem) (L : GRegs) (a : MInstr) (address : Nat)
    (hk : a.kind = .ld ∨ a.kind = .lw)
    (hea : (eaddrM a L).toNat = address)
    (hlo : 0x80000000 ≤ address) (hhi : address + 8 ≤ 0x100000000)
    (hhtif : tohostAddr + 8 ≤ address) :
    MemFacts m L (EvalChildArm.wordLds8 m address) a := by
  rcases hk with hd | hw
  · simp only [MemFacts, hd, hea]
    exact ⟨⟨hlo, hhi, Or.inr hhtif⟩, by simp [LPins8, EvalChildArm.wordLds8]⟩
  · simp only [MemFacts, hw, hea]
    exact ⟨⟨hlo, by omega, Or.inr hhtif⟩, by simp [LPins4, EvalChildArm.wordLds8]⟩

theorem stack_load_facts {m : Mem} {L : GRegs} {a : MInstr}
    {node sp : BitVec 64} (geometry : Geometry node sp) (off : Nat)
    (hk : a.kind = .ld ∨ a.kind = .lw) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 1056) :
    MemFacts m L (EvalChildArm.wordLds8 m (sp.toNat + off)) a := by
  have hea : (eaddrM a L).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by have := geometry.stackHi; omega)]
  exact total_load_facts m L a (sp.toNat + off) hk hea
    (by have := geometry.stackLo; omega)
    (by have := geometry.stackHi; omega)
    (by have := geometry.stackHtif; omega)

def secondLoads (m : Mem) (sp : BitVec 64) (br : List (BitVec 8)) : List (List (BitVec 8)) :=
  [br, EvalChildArm.wordLds8 m sp.toNat, EvalChildArm.wordLds8 m (sp.toNat + 120),
   EvalChildArm.wordLds8 m (sp.toNat + 128)]

/-- The right pointer is represented; the other words are the actual total reads. -/
structure SecondData (m : Mem) (node sp interp right : BitVec 64)
    (br : List (BitVec 8)) : Prop where
  load : WordLoadFacts m (secondInput node sp interp)
    (mkLine 0x800034fc#64 0x01843603#32) right br
  facts : ChainFacts m m (secondInput node sp interp) (secondLoads m sp br) secondSeg

theorem second_data (m : Mem) (node sp interp right : BitVec 64)
    (geometry : Geometry node sp) (hcode : Code.Eval_exprLoaded m)
    (hread : read64 m (node.toNat + 24) = some right.toNat) :
    ∃ br, SecondData m node sp interp right br := by
  have hea : (eaddrM (mkLine 0x800034fc#64 0x01843603#32)
      (secondInput node sp interp)).toNat = node.toNat + 24 := by
    change (node + sign_extend (m := 64) (0x018#12)).toNat = node.toNat + 24
    rw [BitVec.toNat_add]
    change (node.toNat + 24) % 2^64 = node.toNat + 24
    exact Nat.mod_eq_of_lt (by have := geometry.nodeHi; omega)
  obtain ⟨br, hw⟩ := wordLoadFacts_of_read64 m (secondInput node sp interp)
    (mkLine 0x800034fc#64 0x01843603#32) right (by rfl)
    (by rw [hea]; have := geometry.nodeLo; omega)
    (by rw [hea]; have := geometry.nodeHi; omega)
    (by rw [hea]; have := geometry.nodeHtif; omega)
    (by rw [hea]; exact hread)
  refine ⟨br, hw, ?_⟩
  unfold secondLoads
  chain_facts hcode with "Vsa.Sim.Code.eval_expr_at_"
  · exact hw.facts
  · simpa +ground only [Nat.add_zero, stepLdsM, stepMemM, List.tail_cons, List.headD_cons] using
      stack_load_facts geometry 0 (by decide) (by rfl) (by decide) (by decide)
  · exact stack_load_facts geometry 120 (by decide) (by rfl) (by decide) (by decide)
  · exact stack_load_facts geometry 128 (by decide) (by rfl) (by decide) (by decide)
  · exact store_facts geometry 0 (by decide) (by rfl) (by decide) (by decide) (by decide)

#print axioms total_load_facts
#print axioms stack_load_facts
#print axioms second_data

end Vsa.Sim.BinaryPrefix
