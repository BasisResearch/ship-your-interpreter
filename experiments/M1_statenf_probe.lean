import Vsa.Elf

/-! Probe: read-over-write normal forms for the Sail state containers.
Validates the Layer-0 item-2 simp interface before freezing it in
`Vsa/Sim/StateNF.lean`. -/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 1000000

section Regs
variable (σ : SequentialState RegisterType trivialChoiceSource)
variable (v : RegisterType Register.x1) (w : RegisterType Register.x2)

-- same-key read-over-write
example : (σ.regs.insert Register.x1 v).get? Register.x1 = some v := by
  simp

-- distinct-key read-over-write, attempt A: explicit get?_insert + decide on beq
example : (σ.regs.insert Register.x2 w).get? Register.x1 = σ.regs.get? Register.x1 := by
  simp [Std.ExtDHashMap.get?_insert]

-- attempt B for two pending writes
example :
    ((σ.regs.insert Register.x2 w).insert Register.x1 v).get? Register.x1 = some v := by
  simp [Std.ExtDHashMap.get?_insert]

example :
    ((σ.regs.insert Register.x1 v).insert Register.x2 w).get? Register.x1 = some v := by
  simp [Std.ExtDHashMap.get?_insert]

end Regs

section Mem
variable (σ : SequentialState RegisterType trivialChoiceSource)
variable (b : BitVec 8)

example : (σ.mem.insert 0x80000000 b).get? 0x80000000 = some b := by
  simp

example : (σ.mem.insert 0x80000000 b).get? 0x80000001 = σ.mem.get? 0x80000001 := by
  simp [Std.ExtHashMap.getElem?_insert]

example (a : Nat) : (σ.mem.insert (a + 1) b).get? a = σ.mem.get? a := by
  simp [Std.ExtHashMap.getElem?_insert]

end Mem
