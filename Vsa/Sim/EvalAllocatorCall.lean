import Vsa.Sim.AllocatorAt

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic
open Vsa.Sim.Code

namespace Vsa.Sim
open RuntimeOwnership

/-- A child call retains coherent allocator data independently of its register ghost. -/
structure EvalAllocatorCallData (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (st : Vsa.While.St) (v : Value) (dst : Nat) (m0 : Mem) (c : Config) : Prop where
  repr : EvalReturnData N A SL phiF phiC nf nc st v dst
    (AllocatorResult M N shared reserve st.store [(dst, v)] m0) c
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- Retain allocator ownership and the global pointer across one child call. -/
theorem EvalAllocatorAt.at_call
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {N : NativeAddrs}
    (ih : EvalAllocatorAt N st d env e st' v cost maxRequest)
    {gpre gsub : (R : Register) → Option (RegisterType R)}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {sp ret dst aIn aOperand : BitVec 64} {mcall : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared aOperand.toNat e)
    (gp : gpre .x3 = some gpv)
    (frame : ∀ R, AbiPreservedNoise R → gsub R = gpre R) :
    Triple (EvalEntry gsub N A SL phiF phiC st d env e sp ret dst aIn aOperand mcall)
      (ReturnedWith
        (EvalExitD gsub N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst mcall)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v dst.toNat mcall)) := by
  intro before entry
  have owned : EvalAllocatorEntry gsub N M phiF phiC alloc exts shared (cost + reserve)
      st d env e sp ret dst aIn aOperand mcall before :=
    { entry := entry
      allocator := entry.mem.symm ▸ allocator
      ast := entry.mem.symm ▸ ast
      gp := (entry.frame .x3 (by decide)).trans ((frame .x3 (by decide)).trans gp) }
  obtain ⟨after, steps, result⟩ := ih.run gsub A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve sp ret dst aIn aOperand mcall before owned
  exact ⟨after, steps, result.returned.exit, result.returned.repr, result.gp⟩

/-- At one call memory, the retained ABI relation supplies the actual global pointer. -/
theorem EvalAllocatorIH.at_call
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    (ih : EvalAllocatorIH st d env e st' v cost maxRequest)
    {gpre gsub : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {sp ret dst aIn aOperand : BitVec 64} {mcall : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared aOperand.toNat e)
    (gp : gpre .x3 = some gpv)
    (frame : ∀ R, AbiPreservedNoise R → gsub R = gpre R) :
    Triple (EvalEntry gsub N A SL phiF phiC st d env e sp ret dst aIn aOperand mcall)
      (ReturnedWith
        (EvalExitD gsub N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst mcall)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v dst.toNat mcall)) :=
  (ih.at N).at_call L hrequest allocator ast gp frame

/-- Invoke a child at the current native addresses through the shared JAL proof. -/
def armTail_rec_allocator_at
    (gpre : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (st st' : Vsa.While.St) (d env : Nat) (esub : Expr) (vsub : Value)
    (cost maxRequest reserve : Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (hjaltgt : callPC + sign_extend (m := 64) jalImm = BitVec.ofNat 64 evalExprEntry)
    (hlink : BitVec.addInt callPC 4 = retPC) (hretAl : retPC.toNat % 4 = 0)
    (henvValid : EnvValid st env)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1
          (BitVec.addInt callPC 4)))
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared aOperand.toNat esub)
    (gp : gpre .x3 = some gpv)
    (ih : EvalAllocatorAt N st d env esub st' vsub cost maxRequest) :=
  armTail_rec_frame
    (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
      shared reserve st' vsub subsret.toNat mcall)
    gpre N A SL phiF phiC st st' d env esub vsub callPC retPC jalImm
    sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall
    hjaltgt hlink hretAl henvValid hjalSite
    (fun _ frame => ih.at_call L hrequest allocator ast gp frame)

/-- Invoke the allocator-aware child through the shared JAL and return proof. -/
def armTail_rec_allocator
    (gpre : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (st st' : Vsa.While.St) (d env : Nat) (esub : Expr) (vsub : Value)
    (cost maxRequest reserve : Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (hjaltgt : callPC + sign_extend (m := 64) jalImm = BitVec.ofNat 64 evalExprEntry)
    (hlink : BitVec.addInt callPC 4 = retPC) (hretAl : retPC.toNat % 4 = 0)
    (henvValid : EnvValid st env)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1
          (BitVec.addInt callPC 4)))
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared aOperand.toNat esub)
    (gp : gpre .x3 = some gpv)
    (ih : EvalAllocatorIH st d env esub st' vsub cost maxRequest) :=
  armTail_rec_allocator_at gpre N M phiF phiC alloc exts shared st st' d env esub vsub
    cost maxRequest reserve callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18
    out0 mcall hjaltgt hlink hretAl henvValid hjalSite L hrequest allocator ast gp (ih.at N)

#print axioms EvalAllocatorAt.at_call
#print axioms EvalAllocatorIH.at_call
#print axioms armTail_rec_allocator_at
#print axioms armTail_rec_allocator

end Vsa.Sim
