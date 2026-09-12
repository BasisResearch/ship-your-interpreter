import EvalVarTailShape
import Vsa.Sim.WordLoadData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- The evaluator frame and final destination used by its shared return tail. -/
structure ValueTailGeom (sp dst : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 1088 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  destLo : 0x80000000 ≤ dst.toNat
  destHi : dst.toNat + 24 ≤ 0x100000000
  destHtif : tohostAddr + 16 ≤ dst.toNat
  destAlign : dst.toNat % 8 = 0
  savedDisjoint : dst.toNat + 24 ≤ sp.toNat + 1056 ∨ sp.toNat + 1088 ≤ dst.toNat

structure ValueTailSaved (m : Mem) (sp ret r8 r9 r18 : BitVec 64) : Prop where
  ra : read64 m (sp.toNat + 1080) = some ret.toNat
  s0 : read64 m (sp.toNat + 1072) = some r8.toNat
  s1 : read64 m (sp.toNat + 1064) = some r9.toNat
  s2 : read64 m (sp.toNat + 1056) = some r18.toNat

/-- Each stack word uses the same bounded frame argument. -/
theorem value_tail_load (m : Mem) (sp dst v : BitVec 64) (a : MInstr) (off : Nat)
    (h : ValueTailGeom sp dst) (hk : a.kind = .ld) (hrs : a.rs1 = 2)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 1088)
    (hread : read64 m (sp.toNat + off) = some v.toNat) :
    ∃ bs, WordLoadFacts m [(2, sp)] a v bs := by
  have hea : (eaddrM a [(2, sp)]).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hrs]
    change (sp + sign_extend (m := 64) a.imm).toNat = _
    rw [BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by have := h.stackHi; omega)]
  exact wordLoadFacts_of_read64 m [(2, sp)] a v hk
    (by rw [hea]; have := h.stackLo; omega)
    (by rw [hea]; have := h.stackHi; omega)
    (by rw [hea]; right; have := h.stackHtif; omega)
    (by rw [hea]; exact hread)

theorem value_tail_store {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {sp dst : BitVec 64} (h : ValueTailGeom sp dst) (off : Nat)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = dst)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 24) (halign : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = dst.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by have := h.destHi; omega)]
  apply memFacts_sd_frame m L a bs hk
  · rw [hea]; have := h.destLo; omega
  · rw [hea]; have := h.destHi; omega
  · rw [hea]; have := h.destHtif; omega
  · rw [hea]; have := h.destAlign; omega

/-- All loads and stores are justified at the memories used by the reflected tail. -/
theorem value_tail_facts (m : Mem) (sp dst ret : BitVec 64)
    (h : ValueTailGeom sp dst) (hcode : Code.Eval_exprLoaded m)
    (b0 b1 b2 br b8 b18 b9 : List (BitVec 8))
    (w0 : MemFacts m [(2, sp)] b0 (mkLine 0x80003448#64 0x0f013683#32))
    (w1 : MemFacts m [(2, sp)] b1 (mkLine 0x8000344c#64 0x0f813703#32))
    (w2 : MemFacts m [(2, sp)] b2 (mkLine 0x80003450#64 0x10013783#32))
    (wr : MemFacts m [(2, sp)] br (mkLine 0x80003454#64 0x43813083#32))
    (w8 : MemFacts m [(2, sp)] b8 (mkLine 0x80003458#64 0x43013403#32))
    (w18 : MemFacts (valueTailCopy m dst b0 b1 b2) [(2, sp)] b18
      (mkLine 0x80003468#64 0x42013903#32))
    (w9 : MemFacts (valueTailCopy m dst b0 b1 b2) [(2, sp)] b9
      (mkLine 0x80003470#64 0x42813483#32))
    (hr : bytesVal .ld br = ret) (halign : ret.toNat % 4 = 0) :
    ChainFacts m m (evalValueReturnTailL sp dst)
      (valueTailLoads b0 b1 b2 br b8 b18 b9) evalValueReturnTailSeg := by
  chain_facts hcode with "Vsa.Sim.Code.eval_expr_at_"
  · exact w0
  · exact w1
  · exact w2
  · exact wr
  · exact w8
  · exact value_tail_store h 0 (by rfl) (by rfl) (by decide) (by decide) (by decide)
  · exact value_tail_store h 8 (by rfl) (by rfl) (by decide) (by decide) (by decide)
  · exact value_tail_store h 16 (by rfl) (by rfl) (by decide) (by decide) (by decide)
  · exact w18
  · exact w9
  · change (Sail.BitVec.update (bytesVal .ld br + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [hr, ret_tgt ret halign]
    exact halign

#print axioms value_tail_load
#print axioms value_tail_store
#print axioms value_tail_facts

end Vsa.Sim.EnvGetReflected
