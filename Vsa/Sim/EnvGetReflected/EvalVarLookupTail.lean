import Vsa.Sim.EnvGetReflected.EvalVarLookupEntry
import Vsa.Sim.EnvGetReflected.EvalVarTailFramed

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

theorem CallerTailWindow.stack_output
    {A : Arena} {SL : StackLayout} {sp : BitVec 64}
    (w : CallerTailWindow A SL (sp + 240#64) (sp - 64#64)) :
    (sp + 240#64).toNat = sp.toNat + 240 := by
  have hb := w.stack_base
  have hs := w.spill
  have hr := w.ram
  rw [BitVec.toNat_add]
  change (sp.toNat + 240) % 2^64 = _
  exact Nat.mod_eq_of_lt (by omega)

section Handoff
variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value}
    {name sp link c8 c9 c18 c19 c20 c21 : BitVec 64} {before call : Config}
    (h : LookupReturnResult N A SL phiF phiC alloc exts shared s query v
      name (sp + 240#64) sp link c8 c9 c18 c19 c20 c21 before call)
    (w : CallerTailWindow A SL (sp + 240#64) (sp - 64#64))

include h w

/-- Lookup's actual write windows exclude the evaluator's four saved words. -/
theorem LookupReturnResult.tail_saved {ret r8 r9 r18 : BitVec 64}
    (hsaved : ValueTailSaved before.σ.mem sp ret r8 r9 r18) :
    ValueTailSaved call.σ.mem sp ret r8 r9 r18 := by
  have ha : ∀ k, sp.toNat + 1056 ≤ k ∧ k < sp.toNat + 1088 →
      call.σ.mem[k]? = before.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    change ¬ ((sp + 240#64).toNat ≤ k ∧ k < (sp + 240#64).toNat + 24) ∧
      ¬ ((sp - 64#64).toNat ≤ k ∧ k < (sp - 64#64).toNat + 64)
    rw [w.stack_output]
    have hb := w.stack_base
    omega
  have hr (off : Nat) (hlo : 1056 ≤ off) (hhi : off + 8 ≤ 1088) :
      read64 call.σ.mem (sp.toNat + off) = read64 before.σ.mem (sp.toNat + off) :=
    read64_agreeP ha (fun k hk => by omega)
  exact
    { ra := (hr 1080 (by decide) (by decide)).trans hsaved.ra
      s0 := (hr 1072 (by decide) (by decide)).trans hsaved.s0
      s1 := (hr 1064 (by decide) (by decide)).trans hsaved.s1
      s2 := (hr 1056 (by decide) (by decide)).trans hsaved.s2 }

theorem LookupReturnResult.eval_code (hcode : Code.Eval_exprLoaded before.σ.mem) :
    Code.Eval_exprLoaded call.σ.mem := by
  apply loaded_eval_expr_agreeP before.σ.mem call.σ.mem _ hcode
  intro k hk
  apply Eq.symm
  apply h.outside k
  change ¬ ((sp + 240#64).toNat ≤ k ∧ k < (sp + 240#64).toNat + 24) ∧
    ¬ ((sp - 64#64).toNat ≤ k ∧ k < (sp - 64#64).toNat + 64)
  have ho := w.output
  have hs := w.spill
  have ht := w.htif
  have hh : tohostAddr = 0x8001ad00 := rfl
  omega
end Handoff

def varReturnRegs (sp dst ret r8 r9 r18 r19 r20 r21 : BitVec 64) : GRegs :=
  valueTailRegs sp dst ret r8 r9 r18 ++ [(19, r19), (20, r20), (21, r21)]

/-- The complete variable execution from its prefix to the evaluator's return. -/
structure VarReturnResult
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (s : Vsa.While.Store)
    (query : String) (v : Vsa.While.Value)
    (name sp dst ret r8 r9 r18 r19 r20 r21 : BitVec 64) (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some ret
  regs : GHolds after.σ (varReturnRegs sp dst ret r8 r9 r18 r19 r20 r21)
  value : ValueWordRepr after.σ.mem N phiC dst.toNat v
  owned : ValueOwned after.σ.mem shared dst.toNat v
  data : LookupData N A SL phiF phiC alloc exts shared s query name after.σ.mem
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  outside : ∀ k, EnvGetFootprint (sp + 240#64) sp k →
    ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24) → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem var_lookup_tail
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value}
    {name sp dst c8 c18 r19 r20 r21 : BitVec 64} {before call : Config}
    (h : LookupReturnResult N A SL phiF phiC alloc exts shared s query v
      name (sp + 240#64) sp 0x80003444#64 c8 dst c18 r19 r20 r21 before call)
    (w : CallerTailWindow A SL (sp + 240#64) (sp - 64#64))
    (ret r8 r9 r18 : BitVec 64) (hg : ValueTailGeom sp dst)
    (hslot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi)
    (hsaved : ValueTailSaved before.σ.mem sp ret r8 r9 r18) (halign : ret.toNat % 4 = 0)
    (hcode : Code.Eval_exprLoaded before.σ.mem) :
    ∃ after, VarReturnResult N A SL phiF phiC alloc exts shared s query v
      name sp dst ret r8 r9 r18 r19 r20 r21 before after := by
  obtain ⟨_, hsp, _, hdst, _, h19, h20, h21, hfound, _⟩ := h.regs
  have hL : GHolds call.σ (varFoundInput sp dst) := by
    exact ⟨hfound, by simpa only [BitVec.sub_add_cancel] using hsp, hdst, trivial⟩
  have hoff : ∀ k, shared k → ¬ (dst.toNat ≤ k ∧ k < dst.toNat + 24) := by
    intro k hk hin
    have hs := h.data.geometry.stack k hk
    omega
  obtain ⟨after, ht⟩ := value_found_tail sp dst ret r8 r9 r18 call hg h.good
    (h.eval_code w hcode) h.pc h.tick hL (h.tail_saved w hsaved) halign
    (by simpa only [w.stack_output] using h.value)
    (by simpa only [w.stack_output] using h.owned) hoff
  obtain ⟨hr', hsp', h8', h9', h18', hdst', _⟩ := ht.regs
  have hf19 := (ht.frame .x19 (by decide)).trans (by simpa [gprGet] using h19)
  have hf20 := (ht.frame .x20 (by decide)).trans (by simpa [gprGet] using h20)
  have hf21 := (ht.frame .x21 (by decide)).trans (by simpa [gprGet] using h21)
  exact ⟨after,
    { steps := h.steps.trans ht.steps, good := ht.good, tick := ht.tick, pc := ht.pc
      regs := ⟨hr', hsp', h8', h9', h18', hdst',
        by simpa [gprGet] using hf19, by simpa [gprGet] using hf20,
        by simpa [gprGet] using hf21, trivial⟩
      value := ht.value, owned := ht.owned
      data := h.data.after_stack_slot hslot w.arena w.htif ht.outside
      extendsMemory := h.extendsMemory.trans ht.extendsMemory
      outside := fun k hk hd => (ht.outside k hd).trans (h.outside k hk)
      output := ht.output.trans h.output
      kept_frame := fun R hR => (ht.frame R (by simp [valueTailKeep, hR])).trans
        (h.kept_frame R hR) }⟩

#print axioms CallerTailWindow.stack_output
#print axioms LookupReturnResult.tail_saved
#print axioms LookupReturnResult.eval_code
#print axioms var_lookup_tail

end Vsa.Sim.EnvGetReflected
