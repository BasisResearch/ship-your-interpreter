import Vsa.Sim.EnvGetReflected.EvalVarTailFacts

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The three source reads and the memory they produce at the destination. -/
structure ValueTailOperands (m : Mem) (sp dst : BitVec 64)
    (b0 b1 b2 : List (BitVec 8)) : Prop where
  first : MemFacts m [(2, sp)] b0 (mkLine 0x80003448#64 0x0f013683#32)
  second : MemFacts m [(2, sp)] b1 (mkLine 0x8000344c#64 0x0f813703#32)
  third : MemFacts m [(2, sp)] b2 (mkLine 0x80003450#64 0x10013783#32)
  copy : valueTailCopy m dst b0 b1 b2 = copy3Log m (sp.toNat + 240) dst.toNat

theorem value_tail_operands (m : Mem) (sp dst : BitVec 64)
    (h : ValueTailGeom sp dst) (hw : ValueWordsTotal m (sp.toNat + 240)) :
    ∃ b0 b1 b2, ValueTailOperands m sp dst b0 b1 b2 := by
  obtain ⟨d0, d1, d2, hr0, hr1, hr2⟩ := hw
  obtain ⟨b0, w0⟩ := value_tail_load m sp dst d0 (mkLine 0x80003448#64 0x0f013683#32)
    240 h (by rfl) (by rfl) (by decide) (by decide) hr0
  obtain ⟨b1, w1⟩ := value_tail_load m sp dst d1 (mkLine 0x8000344c#64 0x0f813703#32)
    248 h (by rfl) (by rfl) (by decide) (by decide) (by simpa only [Nat.add_assoc] using hr1)
  obtain ⟨b2, w2⟩ := value_tail_load m sp dst d2 (mkLine 0x80003450#64 0x10013783#32)
    256 h (by rfl) (by rfl) (by decide) (by decide) (by simpa only [Nat.add_assoc] using hr2)
  refine ⟨b0, b1, b2, w0.facts, w1.facts, w2.facts, ?_⟩
  exact value_tail_copy m dst (sp.toNat + 240) b0 b1 b2 (by have := h.destHi; omega)
    (w0.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d0 hr0).symm)
    (w1.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d1 hr1).symm)
    (w2.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d2 hr2).symm)

/-- Preserve the saved words across the actual final copy. -/
theorem ValueTailSaved.after_copy
    {m : Mem} {sp dst ret r8 r9 r18 : BitVec 64}
    (h : ValueTailSaved m sp ret r8 r9 r18) (hg : ValueTailGeom sp dst) :
    ValueTailSaved (copy3Log m (sp.toNat + 240) dst.toNat) sp ret r8 r9 r18 := by
  have ha : ∀ k, sp.toNat + 1056 ≤ k ∧ k < sp.toNat + 1088 →
      (copy3Log m (sp.toNat + 240) dst.toNat)[k]? = m[k]? := by
    intro k hk
    exact copy3_frame m _ _ k (by have := hg.savedDisjoint; omega)
  have hr (off : Nat) (hlo : 1056 ≤ off) (hhi : off + 8 ≤ 1088) :
      read64 (copy3Log m (sp.toNat + 240) dst.toNat) (sp.toNat + off) =
        read64 m (sp.toNat + off) := read64_agreeP ha (fun k hk => by omega)
  exact
    { ra := (hr 1080 (by decide) (by decide)).trans h.ra
      s0 := (hr 1072 (by decide) (by decide)).trans h.s0
      s1 := (hr 1064 (by decide) (by decide)).trans h.s1
      s2 := (hr 1056 (by decide) (by decide)).trans h.s2 }

/-- All observations of one reflected final-copy execution. -/
structure ValueTailData (m : Mem) (sp dst ret r8 r9 r18 : BitVec 64)
    (lds : List (List (BitVec 8))) : Prop where
  facts : ChainFacts m m (evalValueReturnTailL sp dst) lds evalValueReturnTailSeg
  regs : GProjects (evalBlocks evalValueReturnTailSeg
    (SegEvalState.init (evalValueReturnTailL sp dst) lds)).regs
    (valueTailRegs sp dst ret r8 r9 r18)
  pc : evalBlocksPC 0x80003448#64
    (SegEvalState.init (evalValueReturnTailL sp dst) lds) evalValueReturnTailSeg = ret
  mem : writeLog m (evalBlocks evalValueReturnTailSeg
    (SegEvalState.init (evalValueReturnTailL sp dst) lds)).log =
    copy3Log m (sp.toNat + 240) dst.toNat

theorem value_tail_data (m : Mem) (sp dst ret r8 r9 r18 : BitVec 64)
    (h : ValueTailGeom sp dst) (hcode : Code.Eval_exprLoaded m)
    (hw : ValueWordsTotal m (sp.toNat + 240))
    (hs : ValueTailSaved m sp ret r8 r9 r18) (halign : ret.toNat % 4 = 0) :
    ∃ lds, ValueTailData m sp dst ret r8 r9 r18 lds := by
  obtain ⟨b0, b1, b2, ho⟩ := value_tail_operands m sp dst h hw
  obtain ⟨br, wr⟩ := value_tail_load m sp dst ret (mkLine 0x80003454#64 0x43813083#32)
    1080 h (by rfl) (by rfl) (by decide) (by decide) hs.ra
  obtain ⟨b8, w8⟩ := value_tail_load m sp dst r8 (mkLine 0x80003458#64 0x43013403#32)
    1072 h (by rfl) (by rfl) (by decide) (by decide) hs.s0
  let mc := valueTailCopy m dst b0 b1 b2
  have hsaved : ValueTailSaved mc sp ret r8 r9 r18 := by
    dsimp only [mc]
    rw [ho.copy]
    exact hs.after_copy h
  obtain ⟨b18, w18⟩ := value_tail_load mc sp dst r18 (mkLine 0x80003468#64 0x42013903#32)
    1056 h (by rfl) (by rfl) (by decide) (by decide) hsaved.s2
  obtain ⟨b9, w9⟩ := value_tail_load mc sp dst r9 (mkLine 0x80003470#64 0x42813483#32)
    1064 h (by rfl) (by rfl) (by decide) (by decide) hsaved.s1
  exact ⟨valueTailLoads b0 b1 b2 br b8 b18 b9,
    { facts := value_tail_facts m sp dst ret h hcode b0 b1 b2 br b8 b18 b9
        ho.first ho.second ho.third wr.facts w8.facts w18.facts w9.facts wr.value halign
      regs := value_tail_regs sp dst ret r8 r9 r18 b0 b1 b2 br b8 b18 b9
        wr.value w8.value w18.value w9.value
      pc := value_tail_pc sp dst ret b0 b1 b2 br b8 b18 b9 wr.value halign
      mem := (value_tail_log m sp dst b0 b1 b2 br b8 b18 b9).trans ho.copy }⟩

#print axioms value_tail_operands
#print axioms ValueTailSaved.after_copy
#print axioms value_tail_data

end Vsa.Sim.EnvGetReflected
