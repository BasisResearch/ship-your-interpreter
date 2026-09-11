import Vsa.Sim.ExecSeqInterpResources
import Vsa.Sim.InitialLoopHead

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Actual loop setup supplies interpreter placement and all retained registers. -/
theorem OwnedLoopHeadFacts.interpResources
    {inp : BitVec 64} {stmts count : Nat} {before after : Config} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {D : RuntimeOwnership.InitialOwnershipData} {aLeft : Nat}
    (H : OwnedLoopHeadFacts inp stmts count before after p N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    ExecSeqInterpResources.At A LayoutInstance.stackSL 0x87fffc50#64 0x87fffca8#64
      after.σ.mem after.σ.regs.get? := by
  exact .intro inp H.saved.input
    { arenaBelow := H.initial.heapUpper
      interpAbove := by rw [F.interp_local]; decide
      interpHi := by rw [F.interp_local]; decide
      interpOffRet := Or.inr (by rw [F.interp_local]; decide)
      breakReg := H.breakFlag, continueReg := H.continueFlag
      spill21 := ⟨0#64, H.preservation.return_latch⟩ }

#print axioms OwnedLoopHeadFacts.interpResources

end Vsa.Sim
