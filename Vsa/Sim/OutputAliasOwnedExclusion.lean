import Vsa.Sim.OutputAliasLoaded
import Vsa.MemReprWithin
import Vsa.Sim.AstMutableByte

/-! The output-alias snapshot is excluded by the AST ownership boundary.
The exclusion covers every possible entry witness, including alternative
array addresses, counts, arenas, and store maps. -/

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.While.LoadedOutputAlias

/-- The second statement's empty literal owns stdout's buffer byte, including
its NUL. Every intermediate pointer is fixed by a concrete memory read. -/
theorem ProgramReads.owned_consoleBuf {m : Mem} {P : Nat → Prop}
    (h : ProgramReads m)
    (hp : ProgramReprWithin m P 0x82000000 2 program) : P consoleBuf := by
  obtain ⟨ha, _⟩ := hp
  cases ha with
  | cons _ _ _ ht =>
    cases ht with
    | cons hp _ hs _ =>
      have hptr := Option.some.inj (hp.symm.trans h.array_second)
      rw [hptr] at hs
      cases hs with
      | ifNoElse _ _ hc _ he _ _ _ _ _ =>
        have hcond := Option.some.inj (hc.symm.trans h.if_cond)
        rw [hcond] at he
        cases he with
        | binary _ _ _ _ hl _ hel _ _ _ =>
          have hleft := Option.some.inj (hl.symm.trans h.equal_left)
          rw [hleft] at hel
          cases hel with
          | str _ _ hs _ hcstr =>
            have hstr := Option.some.inj (hs.symm.trans h.empty_ptr)
            rw [hstr] at hcstr
            exact hcstr.2 0 (by decide)

/-- Register pins plus the existing RAM bound fix the natural-number array
indices. This rules out alternate witnesses congruent modulo 2^64. -/
theorem snapshot_physical_indices
    {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {budget : Nat}
    (F : LayoutInstance.InterpRunPhysicalFacts snapshotConfig
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

/-- No choice of the new entry record's data witnesses admits this snapshot. -/
theorem snapshot_not_readyFacts
    {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {budget : Nat} :
    ¬ LayoutInstance.InterpRunReadyFacts snapshotConfig
      stmts count inp N A φf φc budget := by
  intro F
  obtain ⟨hs, hn⟩ := snapshot_physical_indices F.toInterpRunPhysicalFacts
  subst stmts
  subst count
  have hp := F.ast_owned program snapshot_program
  have hnot := snapshot_programReads.owned_consoleBuf hp
  exact hnot (Or.inl (by decide))

/-- The exact alias machine state is outside the new boundary for every
represented source program, not merely for its chosen historical witness. -/
theorem snapshot_not_loaded (p : Program) :
    ¬ Vsa.Refine.Loaded LayoutInstance.interpRunLayout p snapshotConfig := by
  rintro ⟨stmts, count, _, inp, N, A, φf, φc, budget, F⟩
  exact snapshot_not_readyFacts F

#print axioms ProgramReads.owned_consoleBuf
#print axioms snapshot_physical_indices
#print axioms snapshot_not_readyFacts
#print axioms snapshot_not_loaded

end Vsa.Sim.OutputAliasLoaded
