import Vsa.Sim.AstAccessAudit.AccessSnapshot

/-! A data-only readability condition excludes the constructed low-address AST.
This file does not add the condition to the project's initial-state boundary. -/

open Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit

theorem access_program_reads_badAddr {P : Nat → Prop}
    (h : ProgramReprWithin accessMem P 0x82000000 2 accessProgram) : P 0x4000 := by
  cases h.1 with
  | cons hp hc hs ht =>
    have hptr := Option.some.inj (hp.symm.trans access_array0)
    rw [hptr] at hs
    cases hs <;> exact (show Covers P 0x4000 4 from by assumption) 0 (by decide)

theorem access_not_readable :
    ¬ ProgramReprWithin accessMem
      (fun k => 0x80000000 ≤ k ∧ k < 0x100000000)
      0x82000000 2 accessProgram := by
  intro h
  have hk := access_program_reads_badAddr h
  omega

#print axioms access_program_reads_badAddr
#print axioms access_not_readable
end Vsa.Sim.AstAccessAudit
