import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch11Part14
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

theorem facts001 : TraceCallFacts traceD001 0x3d9020ef#32
    (instruction.JAL (0x2bd8#21, gprIdx 1)) 0xef#8 0x20#8 0x90#8 0x3d#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_3d9020ef

theorem run001 {c : Config} (h : AccessHolds traceD001 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD002 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x3d9020ef#32 0x2bd8#21 0xef#8 0x20#8 0x90#8 0x3d#8 facts001 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run001
end Vsa.Sim.AstAccessAudit
