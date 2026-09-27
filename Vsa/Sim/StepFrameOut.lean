import Vsa.Sim.StepObs
import Vsa.Sim.RegPins

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Register

namespace Vsa.Sim

structure StepFrameOut (W : List Register) (σ σ' : MState) : Prop where
  out   : σ'.sailOutput = σ.sailOutput
  frame : ∀ R : Register, (∀ r ∈ W, (r == R) = false) →
            σ'.regs.get? R = σ.regs.get? R

namespace StepFrameOut

theorem trans {W₁ W₂ : List Register} {σ σ' σ'' : MState}
    (h1 : StepFrameOut W₁ σ σ') (h2 : StepFrameOut W₂ σ' σ'') :
    StepFrameOut (W₁ ++ W₂) σ σ'' where
  out := h2.out.trans h1.out
  frame := by
    intro R hR
    have hR1 : ∀ r ∈ W₁, (r == R) = false := fun r hr => hR r (List.mem_append_left _ hr)
    have hR2 : ∀ r ∈ W₂, (r == R) = false := fun r hr => hR r (List.mem_append_right _ hr)
    exact (h2.frame R hR2).trans (h1.frame R hR1)

theorem of_alu {σ σ' : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_alu σ pc vm rd v)
  frame := by
    intro R hR
    have h := all_notin (S := rd :: noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))

    have hrd : (rd == R) = false := h _ (List.mem_cons_self ..)
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_alu σ pc vm rd v R hms hpc hrd hnp hmi')

theorem of_jal {σ σ' : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd link)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_jal σ pc vm imm rd link)
  frame := by
    intro R hR
    have h := all_notin (S := rd :: noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hrd : (rd == R) = false := h _ (List.mem_cons_self ..)
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_jal σ pc vm imm rd link R hms hpc hrd hnp hmi')

theorem of_jr {σ σ' : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_jump_x0 σ pc vm tgt)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_jump_x0 σ pc vm tgt R hms hpc hnp hmi')

theorem of_branch_taken {σ σ' : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_branch_taken σ pc vm imm)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_branch_taken σ pc vm imm R hms hpc hnp hmi')

theorem of_branch_nottaken {σ σ' : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_branch_nottaken σ pc vm)
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_branch_nottaken σ pc vm R hms hpc hnp hmi')

theorem of_store {σ σ' : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    StepFrameOut noiseRegs σ σ' where
  out := (hobs.out).trans (sailOutput_sigmaPost_store σ pc vm m')
  frame := by
    intro R hR
    have h := all_notin (S := noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_store σ pc vm m' R hms hpc hnp hmi')

end StepFrameOut

end Vsa.Sim
