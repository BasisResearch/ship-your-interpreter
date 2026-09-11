import Vsa.Sim.CallArgsSetup
import Vsa.Sim.BinaryPrefixOwnership

namespace Vsa.Sim.CallArgsSetup

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The setup spill retains the owned callee result and its selected allocator maps. -/
theorem Post.owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC resultF resultC : Addr → Nat} {nf nc reserve : Nat} {shared : Nat → Prop}
    {st : Vsa.While.St} {value : Value} {node sp saved7 env : BitVec 64} {count : Nat} {empty : Bool}
    {m0 : Mem} {before after : Config}
    (h : Post node sp saved7 env count empty before after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (window : BinaryPrefix.Window SL sp) (ram : sp.toNat + 1056 ≤ 0x100000000)
    (repr : ReturnRepr N A phiF phiC resultF resultC nf nc st.store [((sp + 96#64).toNat, value)]
      (AllocatorResult M N shared reserve st.store [((sp + 96#64).toNat, value)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) before.σ.mem) :
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store [((sp + 96#64).toNat, value)]
      (AllocatorResult M N shared reserve st.store [((sp + 96#64).toNat, value)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
  obtain ⟨alloc, exts, currentShared, data⟩ := repr.owned.selected
  have resultAddr : (sp + 96#64).toNat = sp.toNat + 96 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 96 < 2^64; omega)]
    rfl
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    have := window.lo; have := window.hi; omega
  let preserved := fun k => currentShared k ∨ valHeader (sp + 96#64).toNat k
  have agreement : AgreeP preserved before.σ.mem after.σ.mem := by
    intro k hk
    rcases hk with hs | hh
    · exact stackFrame k ((data.allocator.runtime L).shared_off_stack hs)
    · apply h.outside k
      change (sp + 96#64).toNat ≤ k ∧ k < (sp + 96#64).toNat + 24 at hh
      rw [resultAddr] at hh
      omega
  have owned := data.values _ _ (List.mem_singleton_self _)
  have next : AllocatorResultAt M N shared reserve st.store [((sp + 96#64).toNat, value)] m0
      resultF resultC alloc exts currentShared after.σ.mem :=
    { allocator := data.allocator.after_stack L stackFrame
      includes := data.includes
      values := by
        intro a v hv
        cases List.mem_singleton.mp hv
        exact owned.transport agreement (fun _ hk => Or.inr hk) (fun _ hk => Or.inl hk)
      agreement := fun k hk => (data.agreement k hk).trans (agreement k (Or.inl (data.includes k hk))) }
  apply next.coherent L repr.frames repr.closures
  intro a v hv
  cases List.mem_singleton.mp hv
  exact valueRepr_agreeP agreement (fun _ hk => Or.inr hk)
    (owned.covered (fun _ hk => Or.inl hk)) (repr.values _ _ (List.mem_singleton_self _))

/-- Callee evaluation and count setup have reached the actual argument-loop boundary. -/
structure Started (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (st : Vsa.While.St) (value : Value) (node sp saved7 env : BitVec 64)
    (count : Nat) (empty : Bool) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (nextPC empty)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(8, node), (2, sp), (23, saved7), (13, env), (15, BitVec.ofNat 64 count), (16, 0#64)]
  empty_iff : empty = true ↔ count = 0
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store [((sp + 96#64).toNat, value)]
      (AllocatorResult M N shared reserve st.store [((sp + 96#64).toNat, value)] before.σ.mem)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv
  support : EvalCallSupport after.σ.mem SL A sp
  saved7Read : read64 after.σ.mem (sp.toNat + 1016) = some saved7.toNat
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R
  memoryFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat + 1024) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?
  out : OutRepr after.σ st

/-- The represented call supplies the count at the actual callee return. -/
theorem _root_.Vsa.Sim.CallCallee.Input.start_arguments
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {cost request reserve : Nat}
    {st final : Vsa.While.St} {d env : Nat} {e : Expr} {args : List Expr} {value : Value}
    {node sp interp child saved7 : BitVec 64} {before : Config}
    (I : CallCallee.Input SL A phiF st d env e node sp interp child before)
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve) st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared node.toNat (.call e args))
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (nodeReg : before.σ.regs.get? Register.x8 = some node)
    (saved7Reg : before.σ.regs.get? Register.x23 = some saved7)
    (window : BinaryPrefix.Window SL sp) (countBound : args.length ≤ 32)
    (ih : EvalAllocatorAt N st d env e final value cost request) :
    ∃ after empty, Steps before after ∧ Started N M phiF phiC st.store.frames.size st.store.closures.size
      shared reserve final value node sp saved7 (BitVec.ofNat 64 (phiF env)) args.length empty before after := by
  obtain ⟨middle, steps, evaluated⟩ := I.evaluate L requestBound allocator (ast.child (.callee e args) I.childRead) gp ih
  obtain ⟨resultF, resultC, repr⟩ := evaluated.selected
  have call := (ast.transport repr.owned.shared_agree).erase
  have pre : Pre node sp saved7 (BitVec.ofNat 64 (phiF env)) args.length middle :=
    { good := evaluated.good, tick := evaluated.tick, pc := evaluated.pc
      regs := ⟨(evaluated.frame .x8 (by decide)).trans nodeReg, evaluated.spReg,
        (evaluated.frame .x23 (by decide)).trans saved7Reg, trivial⟩
      geometry := I.geometry, countRead := call.call_count.1, countBound := countBound
      envRead := evaluated.savedEnv, code := evaluated.support.image.text.Eval_exprLoaded }
  obtain ⟨after, empty, setupSteps, setup⟩ := run pre
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → middle.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply setup.outside k
    have := window.lo; have := window.hi; omega
  have abi : ∀ R, AbiPreservedNoise R → AbiPreserved R = true := by intro R; cases R <;> decide
  have resultAddr : (sp + 96#64).toNat = sp.toNat + 96 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := I.geometry.stackHi; change sp.toNat + 96 < 2^64; omega)]
    rfl
  refine ⟨after, empty, steps.trans setupSteps,
    { good := setup.good, tick := setup.tick, pc := setup.pc, minstret := setup.minstret
      regs := setup.regs, empty_iff := setup.empty_iff
      selected := ⟨resultF, resultC, setup.owned L window I.geometry.stackHi repr⟩
      gp := (setup.frame .x3 (by decide)).trans evaluated.gp
      support := evaluated.support.transport_stack (fun k hk => (stackFrame k hk).symm)
      saved7Read := setup.saved7Read
      presence := evaluated.presence.trans (by rw [setup.memory]; exact memExtends_writeLog _ _)
      frame := fun R hr => (setup.frame R (abi R hr)).trans (evaluated.frame R hr)
      memoryFrame := ?_
      out := by simpa [OutRepr, output, setup.output] using evaluated.out }⟩
  intro k hs ha
  exact (evaluated.memoryFrame k (by omega) ha (by rw [resultAddr]; have := window.lo; omega)).trans
    (setup.outside k (by have := window.lo; omega))

end Vsa.Sim.CallArgsSetup
