import Vsa.Sim.ExecSeqAllocatorAt

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Every physical empty-sequence boundary preserves the complete caller reserve. -/
theorem execSeqAllocatorAt_nil (N : NativeAddrs) (copy : ExecSeqCopy)
    (st : Vsa.While.St) (d env : Nat) :
    ExecSeqAllocatorAt N copy st d env [] st .normal 0 0 where
  run := by
    intro g A SL gpv headroom maxReq M L _ phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    have owned : AllocatorResultAt M N shared reserve st.store
        (statusResults aRet.toNat .normal) m0 phiF phiC alloc exts shared before.σ.mem :=
      { allocator := by simpa only [Nat.zero_add] using entry.allocator
        includes := fun _ hk => hk
        values := fun _ _ hv => False.elim (List.not_mem_nil hv)
        agreement := fun _ _ => by rw [entry.entry.mem] }
    exact ⟨before, .refl before,
      { exit := ExecSeqEntryI.nilExit copy g N A SL phiF phiC st d env sp aRet m0
          (execSeqCopy_supports_normal copy) entry.entry
        selected := ⟨phiF, phiC, owned.coherent L (PhiExtends.refl _ _) (PhiExtends.refl _ _)
          (fun _ _ hv => False.elim (List.not_mem_nil hv))⟩
        gp := entry.gp }⟩

#print axioms execSeqAllocatorAt_nil

end Vsa.Sim
