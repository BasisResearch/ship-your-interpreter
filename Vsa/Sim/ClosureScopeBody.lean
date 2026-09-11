import Vsa.Sim.ClosureBodyTransport

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

/-- Scope allocation preserves the caller spills and interpreter state above them. -/
theorem ClosureScopePost.high_stack
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp p savedS6 : BitVec 64} {count : Nat} {hasParams : Bool}
    {m : Mem} {out : Array String} {after : Config}
    (h : ClosureScopePost g N M phiF phiC alloc exts shared credits st env
      sp p savedS6 count hasParams m out after)
    (L : AllocLedger A SL gpv headroom maxReq M) (stackLo : SL.lo ≤ sp.toNat) :
    ∀ k, sp.toNat + 1032 ≤ k → k < SL.hi → m[k]? = after.σ.mem[k]? := by
  intro k hlo hhi
  symm
  apply h.memoryFrame k
  · have := L.arena_stack; omega
  · omega
  · omega

/-- The zero-parameter bypass supplies the body initializer at the allocated scope. -/
theorem ClosureScopePost.empty_body_input
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env d : Addr}
    {sp p closure body base interp savedS6 : BitVec 64} {ss : List Stmt}
    {m : Mem} {before after : Config}
    (h : ClosureScopePost g N M phiF phiC alloc exts shared credits st env
      sp p savedS6 0 false m before.σ.sailOutput after)
    (data : FoldBodyData N A SL shared (st.store.allocFrame (some env)).1 d ss
      sp closure body base interp after)
    (closureReg : g Register.x21 = some closure)
    (stack : StackOK SL sp (176 + 1088))
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 168 ≤ SL.hi) :
    ClosureBodyInput N A SL (pushFrameMap phiF st.store.frames.size p.toNat) shared
      ⟨(st.store.allocFrame (some env)).1, Vsa.Machine.output before.σ⟩
      d st.store.frames.size ss sp closure body base interp after := by
  refine
    { good := h.good, tick := h.tick, pc := h.pc, minstret := h.minstret
      spReg := gholds_lookup _ h.regs (show lookupG 2 _ = some sp from rfl)
      closureReg := (h.frame .x21 (by decide)).trans closureReg
      interpReg := data.interpReg, envReg := ?_
      bodyRead := data.bodyRead, bodyCovered := data.bodyCovered
      baseRead := data.baseRead, countRead := data.countRead, countBound := data.countBound
      suffix := data.suffix, resources := data.resources, support := h.support
      envValid := by simp [EnvValid, Store.allocFrame]
      storeBodies := data.storeBodies
      out := by simp only [OutRepr, Vsa.Machine.output, h.output]
      stackOK := stack, stackRam := stackRam, stackWin := stackWin, bufferHi := bufferHi }
  rw [pushFrameMap_fresh, BitVec.ofNat_toNat]
  exact gholds_lookup _ h.regs (show lookupG 19 _ = some p from rfl)

end Vsa.Sim
