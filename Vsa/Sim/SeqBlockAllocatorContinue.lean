import Vsa.Sim.SeqBlockReadback
import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The owned tail and caller registers retained at the block statement call. -/
structure SeqBlockContinueCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (phiF : Addr → Nat) (shared : Nat → Prop)
    (d env : Nat) (sp aRet block base interp : BitVec 64) (index count : Nat)
    (ss : List Stmt) (m0 mCall : Mem) : Prop
    extends SeqBlockNormalCarrier g gExec A SL shared sp aRet block index count m0 mCall where
  interpReg : gExec .x9 = some interp
  envReg : gExec .x19 = some (BitVec.ofNat 64 (phiF env))
  retReg : gExec .x18 = some aRet
  baseRead : read64 mCall (block.toNat + 8) = some base.toNat
  baseCovered : Covers shared (block.toNat + 8) 8
  remaining : index + 1 + ss.length = count
  nonempty : ss ≠ []
  suffix : SeqSuffixOwned mCall shared SL A sp aRet d (base.toNat + 8 * (index + 1)) ss
  stackHi : sp.toNat + 16 ≤ SL.hi
  spill20 : ∃ v, gExec .x20 = some v
  spill21 : ∃ v, gExec .x21 = some v

/-- Run the actual child's normal back edge and reconstruct the owned tail entry. -/
theorem seqBlockAllocatorContinue_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet block base interp : BitVec 64} {index count : Nat}
    {m0 mCall : Mem} {cfg : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (h : SeqBlockContinueCarrier g gExec A SL phiF shared d env
      sp aRet block base interp index count ss m0 mCall)
    (source : ExecS st d env s final .normal) (envValid : EnvValid st env)
    (bodies : Stmt.bodiesBound perCallBudget s = true)
    (storeBodies : StoreBodiesBound st.store perCallBudget)
    (stackOK : StackOK SL sp (176 + 1088))
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo)
    (support : EvalCallSupport mCall SL A sp)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve
      final .normal sp 0x800041c8#64 aRet mCall cfg) :
    ∃ after, Steps cfg after ∧ ∃ resultF resultC alloc exts returnedShared,
      SeqAllocatorContinueAt .blockBody g N M phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size alloc exts shared returnedShared
        reserve final d env ss sp aRet m0 after := by
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  obtain ⟨alloc, exts, returnedShared, data⟩ := repr.owned.selected
  have more : index + 1 < count := by
    have := List.length_pos_iff.mpr h.nonempty
    have := h.remaining
    omega
  have pre := h.toSeqBlockNormalCarrier.normalPre support child.exit data.agreement
    (more := true) (decide_eq_true more)
  have baseRead := (read64_agreeP data.agreement h.baseCovered).symm.trans h.baseRead
  have tail := h.suffix.transport_execExit child.exit.1 child.exit.2.1
    data.agreement data.includes
  obtain ⟨after, steps, post⟩ := SeqBlockNormal.run pre
  obtain ⟨spReg, blockReg, indexReg, _, _⟩ := post.registers
  have keep (R : Register) (hR : ExecSeqFrameReg .blockBody R) :
      after.σ.regs.get? R = gExec R :=
    (post.frame R hR.1.1).trans (child.exit.1.frame R hR.1)
  have interpReg : after.σ.regs.get? Register.x9 = some interp :=
    (keep .x9 ⟨by decide, trivial⟩).trans h.interpReg
  have retReg : after.σ.regs.get? Register.x18 = some aRet :=
    (keep .x18 ⟨by decide, trivial⟩).trans h.retReg
  have environment : resultF env = phiF env := repr.frames env envValid
  have envReg : after.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (resultF env)) := by
    rw [environment]
    exact (keep .x19 ⟨by decide, trivial⟩).trans h.envReg
  have reachedTail : SeqSuffixOwned after.σ.mem returnedShared SL A sp aRet d
      (base.toNat + 8 * (index + 1)) ss := by rw [post.memory]; exact tail
  have allocator : RuntimeAllocatorState M N resultF resultC alloc exts returnedShared
      reserve final.store after.σ.mem := by rw [post.memory]; exact data.allocator
  have survives : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A resultF resultC final.store :=
    fun m' hm => ((allocator.runtime L).after_stack hm).repr
  have ready : ExecSeqLoopReady .blockBody N A SL resultF resultC final d env ss sp aRet after :=
    { env_valid := envValid.mono (execS_store_mono source).1
      code := by rw [post.memory]; exact pre.code
      cursor := ⟨block, base, index + 1, count, blockReg, indexReg, envReg, retReg, spReg,
        by rw [post.memory]; exact baseRead,
        by rw [post.memory]; exact pre.blockCount,
        h.remaining, h.countBound, reachedTail.ground.array⟩
      head_ground := by
        cases ss with
        | nil => exact False.elim (h.nonempty rfl)
        | cons next rest =>
          obtain ⟨p, cell, ground⟩ := reachedTail.head
          have hp : p < 2^64 := read64_lt_eg4 _ _ _ cell.read
          refine ⟨BitVec.ofNat 64 p, ?_, ?_, ?_, ?_, stackOK,
            ground.stackBudget, ground.bodies,
            StoreBodiesBound.afterExecS source bodies storeBodies⟩
          · exact ⟨block, base, index + 1, blockReg, indexReg,
              by rw [post.memory]; exact baseRead,
              by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using cell.read⟩
          · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using ground.stmt
          · exact ⟨interp, interpReg, envReg, retReg⟩
          · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using ground.ground
      store_survives := survives, stack_ram := stackRam, stack_win := stackWin }
  refine ⟨after, steps, resultF, resultC, alloc, exts, returnedShared,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick
              pc := by cases ss with
                | nil => exact False.elim (h.nonempty rfl)
                | cons _ _ => exact post.pc
              store := allocator.repr, store_survives := survives
              out := by simpa [OutRepr, output, post.output] using child.exit.1.out
              mem := rfl, ready := fun _ => ready
              empty_status := fun empty => False.elim (h.nonempty empty)
              frame := fun R hR => (keep R hR).trans (h.frame R hR)
              minstret := post.minstret }
          allocator := allocator
          suffix := fun _ => ⟨_, .blockBody blockReg indexReg
            (by rw [post.memory]; exact baseRead), reachedTail⟩
          closureResources := by intro impossible; cases impossible
          interpResources := by intro impossible; cases impossible
          blockResources := fun _ _ => .intro block blockReg
            { baseCovered := fun k hk => data.includes _ (h.baseCovered k hk)
              countCovered := fun k hk => data.includes _ (h.countCovered k hk)
              savedOffArena := h.savedOffArena, stackHi := h.stackHi, savedOffRet := h.savedOffRet
              spill20 := h.spill20.imp (fun _ hv => (keep .x20 ⟨by decide, trivial⟩).trans hv)
              spill21 := h.spill21.imp (fun _ hv => (keep .x21 ⟨by decide, trivial⟩).trans hv) }
          gp := (post.frame .x3 (by decide)).trans child.gp }
      frames := repr.frames, closures := repr.closures, includes := data.includes
      agreement := ?_, memFrame := ?_, highStack := ?_, presence := ?_ }⟩
  · intro k hk
    rw [post.memory]
    exact (beforeShared k hk).trans (data.agreement k hk)
  · intro k hs hA
    rw [post.memory]
    have spLe := h.spLe
    have ret := h.retInStack
    exact ((child.exit.1.memFrame k (by omega) hA).resolve_left (by omega)).trans
      (h.memFrame k hs hA)
  · rw [post.memory]
    exact h.highStack.trans (blockBodyStackFrame_of_execExitD child.exit)
  · rw [post.memory]
    exact h.presence.trans child.exit.2.1

#print axioms seqBlockAllocatorContinue_of_return

end Vsa.Sim
