import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

theorem facts007 : TraceCallFacts traceD007 0xb6dff0ef#32
    (instruction.JAL (0x1ffb6c#21, gprIdx 1)) 0xef#8 0xf0#8 0xdf#8 0xb6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_b6dff0ef

theorem run007 {c : Config} (h : AccessHolds traceD007 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD008 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb6dff0ef#32 0x1ffb6c#21 0xef#8 0xf0#8 0xdf#8 0xb6#8 facts007 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run007
end Vsa.Sim.AstAccessAudit
