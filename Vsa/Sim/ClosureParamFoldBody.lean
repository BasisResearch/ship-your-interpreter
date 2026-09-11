import Vsa.Sim.ClosureParamFoldEntry
import Vsa.Sim.ClosureBodyAllocator
import Vsa.Sim.SeqSuffixHeap

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
  {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
  {phiF phiC : Addr → Nat} {entryShared : Nat → Prop} {reserve : Nat}
  {store : Store} {cd : ClosureData} {values : List Value} {target : Addr}
  {sp scope closure names savedS6 : BitVec 64} {origin before : Config}
  {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {index : Nat}

/-- The actual binding frame preserves each body's hereditary statement facts. -/
theorem FoldLoopAt.stmt_ground
    (h : FoldLoopAt M N phiF phiC entryShared reserve store cd values target
      sp scope closure names savedS6 origin alloc exts shared index before)
    {d a : Nat} {s : Stmt}
    (ground : SeqStmtGround origin.σ.mem SL A sp (sp + 144#64) d a s) :
    SeqStmtGround before.σ.mem SL A sp (sp + 144#64) d a s :=
  ground.transport_heap_stack h.presence h.memoryFrame

/-- All body statements retain their owned reads and ground facts through the entire fold. -/
theorem FoldLoopAt.body_suffix
    (h : FoldLoopAt M N phiF phiC entryShared reserve store cd values target
      sp scope closure names savedS6 origin alloc exts shared index before)
    {d a : Nat} {ss : List Stmt}
    (suffix : SeqSuffixOwned origin.σ.mem entryShared SL A sp (sp + 144#64) d a ss) :
    SeqSuffixOwned before.σ.mem shared SL A sp (sp + 144#64) d a ss :=
  suffix.transport_heap_stack h.presence h.memoryFrame h.agreement h.includes

/-- Closure body data retained at the initial parameter-loop head. -/
structure FoldBodyData (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (shared : Nat → Prop) (store : Store) (d : Nat) (ss : List Stmt)
    (sp closure body base interp : BitVec 64) (origin : Config) : Prop where
  bodyRead : read64 origin.σ.mem (closure.toNat + 32) = some body.toNat
  bodyCovered : Covers shared (closure.toNat + 32) 8
  baseRead : read64 origin.σ.mem (body.toNat + 8) = some base.toNat
  countRead : read32 origin.σ.mem (body.toNat + 16) = some ss.length
  countBound : ss.length < 2^31
  suffix : SeqSuffixOwned origin.σ.mem shared SL A sp (sp + 144#64) d base.toNat ss
  resources : ExecSeqClosureResources A SL shared body origin.σ.regs.get?
  interpReg : origin.σ.regs.get? Register.x18 = some interp
  storeBodies : StoreBodiesBound store perCallBudget

/-- Repeated definitions preserve the closure bodies already present in the source store. -/
private theorem fold_bodies (store : Store) (cd : ClosureData) (values : List Value)
    (target index : Nat) (bodies : StoreBodiesBound store perCallBudget) :
    StoreBodiesBound (foldStore store cd values target index) perCallBudget := by
  unfold foldStore
  generalize (cd.params.zip values).take index = pairs
  induction pairs generalizing store with
  | nil => exact bodies
  | cons pair rest ih => exact ih (store.define target pair.1 pair.2) bodies

/-- The final checked loop state supplies the existing concrete body initializer. -/
theorem FoldLoopAt.body_input
    (h : FoldLoopAt M N phiF phiC entryShared reserve store cd values target
      sp scope closure names savedS6 origin alloc exts shared values.length before)
    (context : FoldContext SL maxReq phiF store cd values target sp scope)
    {d : Nat} {body base interp : BitVec 64}
    (bodyData : FoldBodyData N A SL entryShared store d cd.body sp closure body base interp origin)
    (stack : StackOK SL sp (176 + 1088)) :
    ClosureBodyInput N A SL phiF shared
      ⟨foldStore store cd values target values.length, Vsa.Machine.output origin.σ⟩
      d target cd.body sp closure body base interp before := by
  refine
    { good := h.good, tick := h.tick, pc := by simpa only [Nat.lt_irrefl, if_false] using h.pc
      minstret := h.minstret, spReg := h.spReg, closureReg := h.closureReg
      interpReg := (h.frame .x18 (by decide)).trans bodyData.interpReg
      envReg := by rw [← context.scopeAddr, BitVec.ofNat_toNat]; exact h.scopeReg
      bodyRead := (bodyData.bodyCovered.read64_eq h.agreement).symm.trans bodyData.bodyRead
      bodyCovered := bodyData.bodyCovered.mono h.includes
      baseRead := (bodyData.resources.baseCovered.read64_eq h.agreement).symm.trans bodyData.baseRead
      countRead := (bodyData.resources.countCovered.read32_eq h.agreement).symm.trans bodyData.countRead
      countBound := bodyData.countBound, suffix := h.body_suffix bodyData.suffix
      resources := ?_, support := h.support
      envValid := by
        change target < (foldStore store cd values target values.length).frames.size
        rw [(fold_sizes store cd values target values.length).1]
        exact context.valid
      storeBodies := fold_bodies store cd values target values.length bodyData.storeBodies
      out := by change Vsa.Machine.output before.σ = Vsa.Machine.output origin.σ
                simp only [Vsa.Machine.output, h.output]
      stackOK := stack, stackRam := context.stackRam, stackWin := context.stackWin
      bufferHi := by have := context.stackHi; omega }
  exact
    { bodyData.resources with
      baseCovered := bodyData.resources.baseCovered.mono h.includes
      countCovered := bodyData.resources.countCovered.mono h.includes
      spill9 := by
        obtain ⟨v, hv⟩ := bodyData.resources.spill9
        exact ⟨v, (h.frame .x9 (by decide)).trans hv⟩
      spill20 := by
        obtain ⟨v, hv⟩ := bodyData.resources.spill20
        exact ⟨v, (h.frame .x20 (by decide)).trans hv⟩
      spill21 := ⟨closure, h.closureReg⟩ }

/-- Initialize the result slot and enter the owned body sequence after all bindings. -/
theorem FoldLoopAt.run_body
    (h : FoldLoopAt M N phiF phiC entryShared reserve store cd values target
      sp scope closure names savedS6 origin alloc exts shared values.length before)
    (context : FoldContext SL maxReq phiF store cd values target sp scope)
    {d : Nat} {body base interp : BitVec 64}
    (bodyData : FoldBodyData N A SL entryShared store d cd.body sp closure body base interp origin)
    (stack : StackOK SL sp (176 + 1088))
    (L : AllocLedger A SL gpv headroom maxReq M) :
    ∃ after, Steps before after ∧
      ClosureBodyPost N M phiF phiC alloc exts shared reserve
        ⟨closureBoundStore store cd values target, Vsa.Machine.output origin.σ⟩
        d target cd.body sp before after := by
  have full : foldStore store cd values target values.length = closureBoundStore store cd values target := by
    have length : (cd.params.zip values).length = values.length := by
      simp only [List.length_zip, ← context.arity, Nat.min_self]
    simpa only [length] using foldStore_full store cd values target
  obtain ⟨after, steps, post⟩ := closureBodyAllocator_run L (h.body_input context bodyData stack)
    (by simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using h.allocator) h.gp
  exact ⟨after, steps, by simpa only [full] using post⟩

end Vsa.Sim.ClosureParam
