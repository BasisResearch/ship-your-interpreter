import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

theorem facts004 : TraceCallFacts traceD004 0xb90fe0ef#32
    (instruction.JAL (0x1fe390#21, gprIdx 1)) 0xef#8 0xe0#8 0xf#8 0xb9#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_b90fe0ef

theorem run004 {c : Config} (h : AccessHolds traceD004 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD005 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb90fe0ef#32 0x1fe390#21 0xef#8 0xe0#8 0xf#8 0xb9#8 facts004 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run004
end Vsa.Sim.AstAccessAudit
