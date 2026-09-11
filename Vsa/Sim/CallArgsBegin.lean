import Vsa.Sim.CallArgLoop
import Vsa.Sim.CallArgsEntryGround
import Vsa.Sim.CallAllocatorStart

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Callee evaluation supplies the initial owned argument-loop state, including the empty route. -/
theorem Started.loop_state
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {cost reserve : Nat}
    {st final : Vsa.While.St} {d env : Nat} {e : Expr} {args : List Expr} {value : Value}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {empty : Bool} {before after : Config}
    (h : Started g N M phiF phiC alloc exts shared cost reserve st final d env e args value
      sp ret dst node interp saved7 m0 empty after)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env (.call e args) sp ret dst interp node m0 before)
    (source : EvalE st d env e final value) (bounded : StoreClosuresBounded st.store)
    (countBound : args.length ≤ 32) :
    CallArgStage.LoopState N M phiF phiC st.store.frames.size st.store.closures.size shared reserve final
      [(((sp - 1088#64) + 96#64).toNat, value)] d env e args node (sp - 1088#64) interp 0 m0 after := by
  obtain ⟨arm, child, v8, v9, v18, path⟩ := h.path
  have ready := path.result
  have arguments := path.extra
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800031b0#64 (fun _ => True)
    (.call e args) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 arm.σ.mem arm ready.retained.arm
  have memory : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      m0[k]? = after.σ.mem[k]? := by
    intro k hs ha
    exact (p.memFrame k (by have := entry.entry.stackOK.2.1; omega)).symm.trans
      (arguments.memoryFrame k (by have := ready.window.hi; omega) ha)
  have ground := entry.entry.arguments_ground.transport_heap_stack
    (ready.retained.presence.trans arguments.presence) memory
  have resultAddr : ((sp - 1088#64) + 96#64).toNat = (sp - 1088#64).toNat + 96 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := ready.input.geometry.stackHi; change (sp - 1088#64).toNat + 96 < 2^64; omega)]
    rfl
  have stores := evalE_store_mono source
  have valueBound := storeClosuresBounded_mutual.onEvalE source bounded
  obtain ⟨nodeReg, spReg, _, envReg, countReg, indexReg, _⟩ := arguments.regs
  refine
    { good := arguments.good, tick := arguments.tick, pc := ?_
      regs := ⟨spReg, nodeReg, indexReg, countReg,
        (arguments.frame .x18 (by decide)).trans p.env, envReg, trivial⟩
      caller := ready.input.geometry, window := ready.window, ground := ground
      ast := entry.entry.mem ▸ entry.ast, selected := h.repr.selected, gp := arguments.gp
      indexBound := Nat.zero_le _, countBound := countBound, sizeF := stores.1, sizeC := stores.2
      envBound := entry.entry.env_valid, envValid := entry.entry.env_valid.mono stores.1
      storeBodies := StoreBodiesBound.afterEvalE source (Expr.bodiesBound_call entry.entry.expr_bodies).1 entry.entry.store_bodies
      storeBounded := valueBound.1, priorBound := ?_, priorWindow := ?_
      stackRam := entry.entry.stack_ram, stackWin := entry.entry.stack_win
      present9 := by rw [arguments.frame .x9 (by decide)]; exact ready.input.present9
      present19 := by rw [arguments.frame .x19 (by decide)]; exact ready.input.present19
      present20 := by rw [arguments.frame .x20 (by decide)]; exact ready.input.present20
      present21 := by rw [arguments.frame .x21 (by decide)]; exact ready.input.present21
      out := arguments.out }
  · cases empty
    · have nonzero : args.length ≠ 0 := by
        intro zero
        have impossible := arguments.empty_iff.mpr zero
        cases impossible
      have positive : 0 < args.length := by omega
      simpa [CallArgsSetup.nextPC, CallArgStage.loopPC, positive] using arguments.pc
    · have zero : args.length = 0 := arguments.empty_iff.mp rfl
      simpa [CallArgsSetup.nextPC, CallArgStage.loopPC, zero] using arguments.pc
  · intro a v member
    cases List.mem_singleton.mp member
    exact valueBound.2
  · intro a v member
    cases List.mem_singleton.mp member
    rw [resultAddr]
    unfold CallArgReturn.slot
    constructor <;> omega

end Vsa.Sim.CallCallee
