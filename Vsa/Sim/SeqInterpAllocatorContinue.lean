import Vsa.Sim.SeqInterpReadback
import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual normal child and back edge supply the owned interpreter tail entry. -/
theorem seqInterpAllocatorContinue_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp : BitVec 64} {m0 mCall : Mem} {cfg : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (h : SeqInterpContinueCarrier g gExec A SL phiF shared d env
      sp aRet cursor finish interp ss m0 mCall)
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
      final .normal sp 0x80004478#64 aRet mCall cfg) :
    ∃ after, Steps cfg after ∧ ∃ resultF resultC alloc exts returnedShared,
      SeqAllocatorContinueAt .interpRun g N M phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size alloc exts shared returnedShared
        reserve final d env ss sp aRet m0 after := by
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  obtain ⟨alloc, exts, returnedShared, data⟩ := repr.owned.selected
  have advance : (cursor + 8#64).toNat = cursor.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (cursor.toNat + 8) % 2^64 = cursor.toNat + 8
    apply Nat.mod_eq_of_lt
    have := finish.isLt
    have := h.remaining
    omega
  have branch : guardB bop.BEQ (cursor + 8#64) finish = false := by
    simp only [guardB, beq_eq_false_iff_ne]
    intro equal
    have values := congrArg BitVec.toNat equal
    rw [advance] at values
    have := List.length_pos_iff.mpr h.nonempty
    have := h.remaining
    omega
  have pre := h.toSeqInterpCaller.normalPre support child.exit branch
  have readback := h.readback child.exit
  have tail := h.suffix.transport_execExit child.exit.1 child.exit.2.1
    data.agreement data.includes
  obtain ⟨after, steps, post⟩ := SeqInterpNormal.run pre
  have keep (R : Register) (hR : ExecSeqFrameReg .interpRun R) :
      after.σ.regs.get? R = gExec R :=
    (post.frame R (by simp [SeqInterpNormal.keep, hR.1.1, hR.2.1])).trans
      (child.exit.1.frame R hR.1)
  have spReg : after.σ.regs.get? Register.x2 = some sp :=
    (post.frame .x2 (by decide)).trans child.exit.1.spReg
  have environment : resultF env = phiF env := repr.frames env envValid
  have reachedTail : SeqSuffixOwned after.σ.mem returnedShared SL A sp aRet d
      (cursor + 8#64).toNat ss := by
    rw [post.memory, advance]
    exact tail
  have allocator : RuntimeAllocatorState M N resultF resultC alloc exts returnedShared
      reserve final.store after.σ.mem := by rw [post.memory]; exact data.allocator
  have survives : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A resultF resultC final.store :=
    fun m' hm => ((allocator.runtime L).after_stack hm).repr
  have ready : ExecSeqLoopReady .interpRun N A SL resultF resultC final d env ss sp aRet after :=
    { env_valid := envValid.mono (execS_store_mono source).1
      code := by rw [post.memory]; exact pre.code
      cursor := ⟨cursor + 8#64, finish, post.cursorReg, post.finishReg, spReg, h.retSlot,
        by rw [advance]; have := h.remaining; omega,
        by rw [post.memory]; exact readback.script, reachedTail.ground.array⟩
      head_ground := by
        cases ss with
        | nil => exact False.elim (h.nonempty rfl)
        | cons next rest =>
          obtain ⟨p, cell, ground⟩ := reachedTail.head
          have hp : p < 2^64 := read64_lt_eg4 _ _ _ cell.read
          refine ⟨BitVec.ofNat 64 p, ?_, ?_, ?_, ?_, stackOK,
            ground.stackBudget, ground.bodies,
            StoreBodiesBound.afterExecS source bodies storeBodies⟩
          · exact ⟨cursor + 8#64, post.cursorReg,
              by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using cell.read⟩
          · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using ground.stmt
          · exact ⟨interp, by rw [post.memory]; exact readback.savedInterp,
              by rw [post.memory, environment]; exact readback.environment, h.retSlot⟩
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
          suffix := fun _ => ⟨_, .interpRun post.cursorReg, reachedTail⟩
          closureResources := by intro impossible; cases impossible
          blockResources := by intro impossible; cases impossible
          interpResources := fun _ _ => .intro interp
            (by rw [post.memory]; exact readback.savedInterp)
            { arenaBelow := h.arenaBelow, interpAbove := h.interpAbove
              interpHi := h.interpHi, interpOffRet := h.interpOffRet
              breakReg := (keep .x19 ⟨by decide, by decide, by decide⟩).trans h.breakReg
              continueReg := (keep .x20 ⟨by decide, by decide, by decide⟩).trans h.continueReg
              spill21 := h.spill21.imp (fun _ hv =>
                (keep .x21 ⟨by decide, by decide, by decide⟩).trans hv) }
          gp := (post.frame .x3 (by decide)).trans child.gp }
      frames := repr.frames, closures := repr.closures, includes := data.includes
      agreement := ?_, memFrame := ?_, highStack := trivial, presence := ?_ }⟩
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
    exact h.presence.trans child.exit.2.1

#print axioms seqInterpAllocatorContinue_of_return

end Vsa.Sim
