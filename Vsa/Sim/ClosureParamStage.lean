import Vsa.Sim.ClosureParamData
import Vsa.Sim.ClosureParamSites
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads
import Vsa.Sim.RuntimeAllocatorState

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual loop head supplies the selected name and argument cursor. -/
structure Pre (sp cursor index scope closure names name : BitVec 64) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x800032dc#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (callClosureFoldStageL sp cursor index scope closure)
  geometry : Geometry before.σ.mem sp cursor closure (names + index)
  namesRead : read64 before.σ.mem (closure.toNat + 16) = some names.toNat
  nameRead : read64 before.σ.mem (names + index).toNat = some name.toNat
  code : Code.Eval_exprLoaded before.σ.mem

def footprint (sp : BitVec 64) (k : Nat) : Prop :=
  (sp.toNat ≤ k ∧ k < sp.toNat + 8) ∨ (sp.toNat + 64 ≤ k ∧ k < sp.toNat + 88)

/-- The env_define call endpoint retains the copied argument and complete call frame. -/
structure Post (sp cursor index scope closure name : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80002a5c#64
  ra : after.σ.regs.get? Register.x1 = some 0x80003314#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(10, scope), (11, name), (12, sp + 64#64), (2, sp),
    (8, cursor + 24#64), (15, index), (19, scope), (21, closure)]
  memory : after.σ.mem = writeLog before.σ.mem (writes before.σ.mem sp cursor index)
  copied : ∀ j, j < 24 → after.σ.mem[sp.toNat + 64 + j]? = some ((before.σ.mem[cursor.toNat + j]?).getD 0)
  savedIndex : read64 after.σ.mem sp.toNat = some index.toNat
  outside : ∀ k, ¬ footprint sp k → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
    (∀ n ∈ wrChain callClosureFoldStageSeg, (gprReg n == R) = false) →
    (Register.x1 == R) = false → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the existing staging span and generated env_define JAL. -/
theorem run {sp cursor index scope closure names name : BitVec 64} {before : Config}
    (h : Pre sp cursor index scope closure names name before) :
    ∃ after, Steps before after ∧ Post sp cursor index scope closure name before after := by
  let L := callClosureFoldStageL sp cursor index scope closure
  let lds := loads before.σ.mem cursor closure (names + index)
  have F := facts before.σ.mem sp cursor index scope closure names h.geometry h.code h.namesRead
  obtain ⟨after, C⟩ := bridgeOfSegFull callClosureFoldStageSeg L lds
    0x800032dc#64 0x80002a5c#64 0x80003314#64 before h.good h.pc h.minstret h.tick h.regs
    (by change KeysOK [2, 8, 15, 19, 21]; decide) F
    (by change ChainOK 0x800032dc#64 [2, 8, 15, 19, 21] callClosureFoldStageSeg; decide)
    (by change KeysOK [11, 8, 13, 10, 14, 12, 2, 15, 19, 21]; decide)
    (by change ∀ n ∈ ([11, 8, 13, 10, 14, 12, 2, 15, 19, 21] : List Nat), n ≠ 1; decide)
    (by
      intro middle good tick pc minstret memory _
      have mem : middle.σ.mem = writeLog before.σ.mem (writes before.σ.mem sp cursor index) :=
        memory.trans (congrArg (writeLog before.σ.mem)
          (log before.σ.mem sp cursor index scope closure (names + index) h.geometry))
      have code : Code.Eval_exprLoaded middle.σ.mem := by
        apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ h.code
        intro k hk
        rw [mem]
        symm
        apply writeLog_out
        simp only [writes, OutL, and_true]
        have := h.geometry.codeOff
        exact ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨vm, hvm⟩ := minstret
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_80003310_closureParam middle.σ middle.tick middle.steps 0x80003310#64 vm
          good pc hvm code rfl tick
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem)
    (log before.σ.mem sp cursor index scope closure (names + index) h.geometry))
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      regs := ?_, memory := memory, copied := by rw [memory]; exact copied _ _ _ _
      savedIndex := ?_, outside := ?_, output := C.output, frame := C.frame }⟩
  · apply gholds_selected (hregs := C.registers)
    have nameValue := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (names + index).toNat name h.nameRead
    change some (scope + 0#64) = some scope ∧
      some (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (names + index).toNat)) = some name ∧
      some (sp + 64#64) = some (sp + 64#64) ∧ some sp = some sp ∧
      some (cursor + 24#64) = some (cursor + 24#64) ∧ some index = some index ∧
      some scope = some scope ∧ some closure = some closure ∧ True
    simp only [nameValue, BitVec.add_zero, and_true]
  · rw [memory]
    exact read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp cursor index) 2 _ _ rfl
      (by simp only [writes, List.drop, OutLRange, and_true]; omega)
  · intro k hk
    rw [memory]
    symm
    apply writeLog_out
    simp only [writes, OutL, and_true]
    unfold footprint at hk
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Ownership, allocation credit, and the semantic argument at the same call endpoint. -/
structure OwnedPost (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (store : Store) (value : Value) (param : String)
    (sp cursor index scope closure name : BitVec 64) (before after : Config) : Prop where
  call : Post sp cursor index scope closure name before after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store after.σ.mem
  word : ValueWordRepr after.σ.mem N phiC (sp.toNat + 64) value
  owned : ValueOwned after.σ.mem shared (sp.toNat + 64) value
  name : SharedCString after.σ.mem shared name.toNat param
  agreement : AgreeP shared before.σ.mem after.σ.mem
  presence : MemExtends before.σ.mem after.σ.mem
  stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]?
  gp : after.σ.regs.get? Register.x3 = some gpv

/-- Transport the caller's allocator through the actual stack-only staging writes. -/
theorem Post.owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before after : Config}
    (h : Post sp cursor index scope closure name before after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store before.σ.mem)
    (slot : ValueRepr before.σ.mem N phiC cursor.toNat value)
    (owned : ValueOwned before.σ.mem shared cursor.toNat value)
    (nameOwned : SharedCString before.σ.mem shared name.toNat param)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 88 ≤ SL.hi)
    (gp : before.σ.regs.get? Register.x3 = some gpv) :
    OwnedPost N M phiF phiC alloc exts shared credits store value param
      sp cursor index scope closure name before after := by
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply h.outside k
    unfold footprint
    omega
  have agreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => stackFrame k ((allocator.runtime L).shared_off_stack hk)
  have repr := valueRepr_copy_total_exact h.copied (owned.covered agreement) slot
  refine
    { call := h, allocator := allocator.after_stack L stackFrame
      word := ValueWordRepr.of_reads repr
        (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem cursor.toNat))
        (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (cursor.toNat + 8)))
        (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (cursor.toNat + 16))) ?_ ?_ ?_
      owned := owned.copy_total h.copied agreement, name := nameOwned.transport agreement
      agreement := agreement, presence := by rw [h.memory]; exact memExtends_writeLog _ _
      stackFrame := stackFrame, gp := (h.frame .x3 (by decide) (by decide) (by decide)).trans gp }
  · rw [h.memory]
    exact read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp cursor index) 0 _ _ rfl
      (by simp only [writes, List.drop, OutLRange, and_true]; exact ⟨by omega, by omega, by omega⟩)
  · rw [h.memory]
    exact read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp cursor index) 1 _ _
      (by simp only [writes, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (by simp only [writes, List.drop, OutLRange, and_true]; exact ⟨by omega, by omega⟩)
  · rw [h.memory]
    exact read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp cursor index) 3 _ _
      (by simp only [writes, List.getElem?_cons_succ, List.getElem?_cons_zero])
      (by simp [writes, OutLRange])

#print axioms run
#print axioms Post.owned

end Vsa.Sim.ClosureParam
