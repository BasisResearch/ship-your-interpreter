import EvalVarTailData
import EvalVarCallFrame

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The final evaluator return retains the copied value and its actual frame. -/
structure ValueTailResult (N : NativeAddrs) (phiC : Vsa.While.Addr → Nat)
    (shared : Nat → Prop) (v : Vsa.While.Value)
    (sp dst ret r8 r9 r18 : BitVec 64) (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some ret
  regs : GHolds after.σ (valueTailRegs sp dst ret r8 r9 r18)
  value : ValueWordRepr after.σ.mem N phiC dst.toNat v
  owned : ValueOwned after.σ.mem shared dst.toNat v
  mem : after.σ.mem = copy3Log before.σ.mem (sp.toNat + 240) dst.toNat
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  outside : ∀ k, ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24) → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, valueTailKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the shared copy/return segment with the actual owned value. -/
theorem value_tail_framed
    {N : NativeAddrs} {phiC : Vsa.While.Addr → Nat} {shared : Nat → Prop}
    {v : Vsa.While.Value} (sp dst ret r8 r9 r18 : BitVec 64) (c : Config)
    (hg : ValueTailGeom sp dst) (hgood : GoodState c.σ)
    (hcode : Code.Eval_exprLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some 0x80003448#64) (htick : c.tick < 2)
    (hL : GHolds c.σ (evalValueReturnTailL sp dst))
    (hsaved : ValueTailSaved c.σ.mem sp ret r8 r9 r18) (halign : ret.toNat % 4 = 0)
    (hvalue : ValueWordRepr c.σ.mem N phiC (sp.toNat + 240) v)
    (howned : ValueOwned c.σ.mem shared (sp.toNat + 240) v)
    (hoff : ∀ k, shared k → ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24)) :
    ∃ after, ValueTailResult N phiC shared v sp dst ret r8 r9 r18 c after := by
  obtain ⟨lds, hd⟩ := value_tail_data c.σ.mem sp dst ret r8 r9 r18
    hg hcode hvalue.raw hsaved halign
  have hf : ∀ k, ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24) → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks evalValueReturnTailSeg
        (SegEvalState.init (evalValueReturnTailL sp dst) lds)).log)[k]? := by
    intro k hk
    rw [hd.mem]
    exact (copy3_frame c.σ.mem _ _ k hk).symm
  obtain ⟨vm, hvm⟩ := hgood.minstret
  obtain ⟨after, hs⟩ := segEval_selected_framed evalValueReturnTailSeg
    (evalValueReturnTailL sp dst) lds 0x80003448#64 vm
    (fun k => dst.toNat ≤ k ∧ k < dst.toNat + 24) valueTailKeep
    (valueTailRegs sp dst ret r8 r9 r18) c hgood hpc hvm hL
    (by show KeysOK [2, 9]; decide) hd.facts
    (by show ChainOK 0x80003448#64 [2, 9] _; decide) htick hf
    (by decide) (by decide) hd.regs
  have hm := hs.mem.trans hd.mem
  obtain ⟨hv, ho, he⟩ := copy_value hm hoff hvalue howned
  exact ⟨after,
    { steps := hs.steps, good := hs.good, tick := hs.tick
      pc := by simpa only [hd.pc] using hs.pc
      regs := hs.selected_regs, value := hv, owned := ho, mem := hm
      extendsMemory := he
      outside := fun k hk => (hs.outside k hk).symm
      output := hs.output, frame := hs.reg_frame }⟩

/- The successful variable branch immediately before the shared tail. -/
#derive_case varFoundSeg chain []
  terminator ⟨0x80003444#64, 0x32050ee3#32, 0xe3#8, 0x0e#8, 0x05#8, 0x32#8,
    .br bop.BEQ false, 10, 0, 0x0b3c#13, 0#21, 0#12⟩

def varFoundInput (sp dst : BitVec 64) : GRegs := [(10, 1#64), (2, sp), (9, dst)]

theorem value_found_branch (sp dst : BitVec 64) (c : Config)
    (hg : GoodState c.σ) (hcode : Code.Eval_exprLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some 0x80003444#64) (htick : c.tick < 2)
    (hL : GHolds c.σ (varFoundInput sp dst)) :
    ∃ after, SelectedFramedSegResult varFoundSeg (varFoundInput sp dst) []
      0x80003444#64 (fun _ => False) valueTailKeep (evalValueReturnTailL sp dst) c after := by
  have hf : ChainFacts c.σ.mem c.σ.mem (varFoundInput sp dst) [] varFoundSeg := by
    chain_facts hcode with "Vsa.Sim.Code.eval_expr_at_"
    change guardB bop.BEQ 1#64 0#64 = false
    decide
  obtain ⟨vm, hvm⟩ := hg.minstret
  exact segEval_selected_framed varFoundSeg (varFoundInput sp dst) [] 0x80003444#64 vm
    (fun _ => False) valueTailKeep (evalValueReturnTailL sp dst) c hg hpc hvm hL
    (by show KeysOK [10, 2, 9]; decide) hf
    (by show ChainOK 0x80003444#64 [10, 2, 9] _; decide) htick (fun _ _ => rfl)
    (by decide) (by decide) (by exact ⟨rfl, rfl, trivial⟩)

/-- The successful variable branch and shared tail retain one owned return. -/
theorem value_found_tail
    {N : NativeAddrs} {phiC : Vsa.While.Addr → Nat} {shared : Nat → Prop}
    {v : Vsa.While.Value} (sp dst ret r8 r9 r18 : BitVec 64) (c : Config)
    (hg : ValueTailGeom sp dst) (hgood : GoodState c.σ)
    (hcode : Code.Eval_exprLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some 0x80003444#64) (htick : c.tick < 2)
    (hL : GHolds c.σ (varFoundInput sp dst))
    (hsaved : ValueTailSaved c.σ.mem sp ret r8 r9 r18) (halign : ret.toNat % 4 = 0)
    (hvalue : ValueWordRepr c.σ.mem N phiC (sp.toNat + 240) v)
    (howned : ValueOwned c.σ.mem shared (sp.toNat + 240) v)
    (hoff : ∀ k, shared k → ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24)) :
    ∃ after, ValueTailResult N phiC shared v sp dst ret r8 r9 r18 c after := by
  obtain ⟨head, hb⟩ := value_found_branch sp dst c hgood hcode hpc htick hL
  have hm : head.σ.mem = c.σ.mem := hb.mem
  obtain ⟨after, ht⟩ := value_tail_framed sp dst ret r8 r9 r18 head hg hb.good
    (hm.symm ▸ hcode) hb.pc hb.tick hb.selected_regs (hm.symm ▸ hsaved) halign
    (hm.symm ▸ hvalue) (hm.symm ▸ howned) hoff
  exact ⟨after,
    { steps := hb.steps.trans ht.steps, good := ht.good, tick := ht.tick, pc := ht.pc
      regs := ht.regs, value := ht.value, owned := ht.owned
      mem := by rw [ht.mem, hm]
      extendsMemory := by rw [← hm]; exact ht.extendsMemory
      outside := fun k hk => (ht.outside k hk).trans (congrArg (fun m : Mem => m[k]?) hm)
      output := ht.output.trans hb.output
      frame := fun R hR => (ht.frame R hR).trans (hb.reg_frame R hR) }⟩

#print axioms value_tail_framed
#print axioms value_found_branch
#print axioms value_found_tail

end Vsa.Sim.EnvGetReflected
