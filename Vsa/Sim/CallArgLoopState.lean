import Vsa.Sim.CallArgSource
import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.rows.StoreWF

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

def loopPC (index count : Nat) : BitVec 64 :=
  if index < count then 0x800031dc#64 else 0x80003254#64

/-- The represented source, selected allocator, and completed values at an argument boundary. -/
structure LoopState (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (entryF entryC : Addr → Nat) (nf nc : Nat)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (prior : List (Nat × Value))
    (d env : Nat) (callee : Expr) (args : List Expr) (node sp interp : BitVec 64)
    (index : Nat) (m0 : Mem) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (loopPC index args.length)
  regs : GHolds cfg.σ (input sp node interp (BitVec.ofNat 64 (entryF env)) index args.length)
  caller : BinaryPrefix.Geometry node sp
  window : BinaryPrefix.Window SL sp
  ground : Ground cfg.σ.mem SL A sp node d callee args
  ast : ExprReprWithin m0 shared node.toNat (.call callee args)
  selected : ∃ resultF resultC,
    ReturnRepr N A entryF entryC resultF resultC nf nc st.store prior
      (AllocatorResult M N shared credits st.store prior m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) cfg.σ.mem
  gp : cfg.σ.regs.get? Register.x3 = some gpv
  indexBound : index ≤ args.length
  countBound : args.length ≤ 32
  sizeF : nf ≤ st.store.frames.size
  sizeC : nc ≤ st.store.closures.size
  envBound : env < nf
  envValid : EnvValid st env
  storeBodies : StoreBodiesBound st.store perCallBudget
  storeBounded : StoreClosuresBounded st.store
  priorBound : ∀ a v, (a, v) ∈ prior → ValueClosuresBounded st.store.closures.size v
  priorWindow : ∀ a v, (a, v) ∈ prior → sp.toNat + 96 ≤ a ∧ a + 24 ≤ CallArgReturn.slot sp index
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  present9 : (cfg.σ.regs.get? Register.x9).isSome = true
  present19 : (cfg.σ.regs.get? Register.x19).isSome = true
  present20 : (cfg.σ.regs.get? Register.x20).isSome = true
  present21 : (cfg.σ.regs.get? Register.x21).isSome = true
  out : OutRepr cfg.σ st

/-- The complete loop step preserves the caller bytes above the argument array. -/
structure LoopFrame (SL : StackLayout) (A : Arena) (sp : BitVec 64) (before after : Config) : Prop where
  presence : MemExtends before.σ.mem after.σ.mem
  regs : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R
  memory : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat + 1008) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?

/-- Derive the next argument state from the actual source and the child's recursive contract. -/
theorem LoopState.advance
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {entryF entryC : Addr → Nat} {nf nc : Nat}
    {shared : Nat → Prop} {cost reserve request : Nat} {st final : Vsa.While.St}
    {prior : List (Nat × Value)} {d env : Nat} {callee : Expr} {args : List Expr}
    {node sp interp : BitVec 64} {index : Nat} {m0 : Mem} {before : Config} {value : Value}
    (h : LoopState N M entryF entryC nf nc shared (cost + reserve) st prior d env callee args node sp interp index m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (more : index < args.length)
    (source : EvalE st d env args[index] final value)
    (child : EvalAllocatorAt N st d env args[index] final value cost request) :
    ∃ after, Steps before after ∧
      LoopState N M entryF entryC nf nc shared reserve final (prior ++ [(CallArgReturn.slot sp index, value)])
        d env callee args node sp interp (index + 1) m0 after ∧ LoopFrame SL A sp before after := by
  obtain ⟨middleF, middleC, first⟩ := h.selected
  obtain ⟨alloc, exts, currentShared, data⟩ := first.owned.selected
  have ast := (h.ast.transport data.agreement).mono data.includes
  obtain ⟨base, ptr, selected⟩ := h.ground.select ast h.caller index more h.countBound
  have envEq := first.frames env h.envBound
  obtain ⟨spReg, nodeReg, indexReg, countReg, interpReg, envReg, _⟩ := h.regs
  change before.σ.regs.get? Register.x8 = some node at nodeReg
  change before.σ.regs.get? Register.x18 = some interp at interpReg
  have input : Input SL A middleF st d env args[index] node sp interp base ptr index args.length before :=
    { geometry := selected.geometry, good := h.good, tick := h.tick
      pc := by simpa [loopPC, more] using h.pc
      regs := by rw [envEq]; exact h.regs
      baseRead := selected.baseRead, childRead := selected.childRead, ground := selected.ground
      stackRam := h.stackRam, stackWin := h.stackWin, envValid := h.envValid, storeBodies := h.storeBodies
      present8 := by rw [nodeReg]; rfl
      present9 := h.present9, present18 := by rw [interpReg]; rfl
      present19 := h.present19, present20 := h.present20, present21 := h.present21, out := h.out }
  obtain ⟨after, again, steps, advanced⟩ := input.iterate L requestBound h.window data first h.sizeF h.sizeC h.priorBound
    (by
      intro a v member
      have bounds := h.priorWindow a v member
      have := h.indexBound; have := h.countBound
      unfold CallArgReturn.slot at bounds
      exact ⟨bounds.1, by omega⟩)
    (fun a v member => Or.inl (h.priorWindow a v member).2) selected.ast h.gp child
  have buffer : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := h.caller.stackHi; change sp.toNat + 64 < 2^64; omega)]
    rfl
  have frame : LoopFrame SL A sp before after :=
    { presence := advanced.presence, regs := advanced.frame
      memory := by
        intro k hs ha
        apply advanced.memoryFrame k (by omega) ha
        · rw [buffer]
          have := h.window.lo
          omega
        · unfold CallArgReturn.slot
          have := h.window.lo; have := h.countBound
          omega }
  have memory : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hs ha
    exact frame.memory k (by have := h.window.hi; omega) ha
  have stores := evalE_store_mono source
  have bounded := storeClosuresBounded_mutual.onEvalE source h.storeBounded
  obtain ⟨spAfter, nodeAfter, interpAfter, envAfter, countAfter, indexAfter, _⟩ := advanced.regs
  refine ⟨after, steps,
    { good := advanced.good, tick := advanced.tick, pc := ?_
      regs := ⟨spAfter, nodeAfter, indexAfter, countAfter, interpAfter, by rw [envEq] at envAfter; exact envAfter, trivial⟩
      caller := h.caller, window := h.window, ground := h.ground.transport_heap_stack advanced.presence memory
      ast := h.ast, selected := advanced.selected, gp := advanced.gp, indexBound := by omega
      countBound := h.countBound, sizeF := Nat.le_trans h.sizeF stores.1, sizeC := Nat.le_trans h.sizeC stores.2
      envBound := h.envBound, envValid := h.envValid.mono stores.1
      storeBodies := StoreBodiesBound.afterEvalE source selected.ground.bodies h.storeBodies
      storeBounded := bounded.1, priorBound := ?_, priorWindow := ?_
      stackRam := h.stackRam, stackWin := h.stackWin
      present9 := by rw [advanced.frame .x9 (by decide)]; exact h.present9
      present19 := by rw [advanced.frame .x19 (by decide)]; exact h.present19
      present20 := by rw [advanced.frame .x20 (by decide)]; exact h.present20
      present21 := by rw [advanced.frame .x21 (by decide)]; exact h.present21
      out := advanced.out }, frame⟩
  · have pc := advanced.pc
    cases again
    · have done : ¬ index + 1 < args.length := by simpa using advanced.more_iff.symm
      simpa [CallArgReturn.nextPC, loopPC, done] using pc
    · have next : index + 1 < args.length := advanced.more_iff.mp rfl
      simpa [CallArgReturn.nextPC, loopPC, next] using pc
  · intro a v member
    rcases List.mem_append.mp member with hp | hn
    · exact ValueClosuresBounded.mono stores.2 (h.priorBound a v hp)
    · cases List.mem_singleton.mp hn
      exact bounded.2
  · intro a v member
    rcases List.mem_append.mp member with hp | hn
    · have old := h.priorWindow a v hp
      unfold CallArgReturn.slot at old ⊢
      exact ⟨old.1, by omega⟩
    · cases List.mem_singleton.mp hn
      unfold CallArgReturn.slot
      constructor <;> omega

end Vsa.Sim.CallArgStage
