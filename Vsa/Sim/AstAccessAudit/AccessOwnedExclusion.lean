import Vsa.Sim.AstAccessAudit.AccessReadability

/-! The approved readability boundary excludes the earlier owned-access
snapshot. The exclusion quantifies over all data witnesses and programs. -/

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.AstAccessAudit

open Vsa.Sim.OutputAliasLoaded

/-- The physical register pins determine the array indices as natural numbers.
The RAM bound excludes alternative witnesses congruent modulo 2^64. -/
theorem access_physical_indices
    {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {budget : Nat}
    (F : LayoutInstance.InterpRunPhysicalFacts accessConfig
      stmts count inp N A φf φc budget) :
    stmts = 0x82000000 ∧ count = 2 := by
  have hbound := F.stmts_ram.2
  have hsBound : stmts < 2 ^ 64 := by omega
  have hnBound : count < 2 ^ 64 := by omega
  have hs := F.stmts_arg
  have hn := F.count_arg
  change physicalRegs.get? Register.x11 = some (BitVec.ofNat 64 stmts) at hs
  change physicalRegs.get? Register.x12 = some (BitVec.ofNat 64 count) at hn
  rw [physicalRegs_x11] at hs
  rw [physicalRegs_x12] at hn
  have hsNat := congrArg BitVec.toNat (Option.some.inj hs)
  have hnNat := congrArg BitVec.toNat (Option.some.inj hn)
  change 0x82000000 = stmts % 2 ^ 64 at hsNat
  change 2 = count % 2 ^ 64 at hnNat
  rw [Nat.mod_eq_of_lt hsBound] at hsNat
  rw [Nat.mod_eq_of_lt hnBound] at hnNat
  exact ⟨hsNat.symm, hnNat.symm⟩

/-- No alternative arena, map, count, or address witness makes this state ready. -/
theorem access_not_readyFacts
    {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {budget : Nat} :
    ¬ LayoutInstance.InterpRunReadyFacts accessConfig
      stmts count inp N A φf φc budget := by
  intro F
  obtain ⟨hs, hn⟩ := access_physical_indices F.toInterpRunPhysicalFacts
  subst stmts
  subst count
  exact access_not_readable
    (F.ast_readable accessProgram access_program_owned.erase)

/-- The live boundary excludes the exact snapshot for every source program. -/
theorem access_not_loaded (p : Program) :
    ¬ Vsa.Refine.Loaded LayoutInstance.interpRunLayout p accessConfig := by
  rintro ⟨stmts, count, _, inp, N, A, φf, φc, budget, F⟩
  exact access_not_readyFacts F

#print axioms access_physical_indices
#print axioms access_not_readyFacts
#print axioms access_not_loaded

end Vsa.Sim.AstAccessAudit
