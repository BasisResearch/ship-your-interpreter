import Vsa.Sim.AstAccessAudit.AccessPrefix
import Vsa.Sim.AstAccessAudit.StuckLoad
import Vsa.Sim.EndToEnd

/-! A complete finite execution obstruction under the historical ownership-only boundary.
The program evaluates two integer literals and produces no output. The admitted
initial memory places their statement node at a PMA-denied address. -/

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.Refine Vsa.While
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

theorem access_final_stuck {c : Config} (h : AccessHolds traceD009 c) : Stuck c := by
  have hx8 : c.σ.regs.get? Register.x8 = some badAddr :=
    gholds_lookup traceD009.regs h.regs (by decide :
      lookupG 8 traceD009.regs = some badAddr)
  apply local_stuck c.σ c.tick c.steps h.good h.pc hx8 h.mcause_absent
  all_goals rw [h.mem, snapshot_logRead]; decide

/-- Every possible output and exit code are excluded by the actual stuck prefix. -/
theorem access_not_halts (out : String) (code : Nat) :
    ¬ Halts accessConfig out code := by
  obtain ⟨c, hs, h⟩ := access_prefix
  exact hs.not_halts_of_stuck (access_final_stuck h)

/-- The boundary before AST readability admits an incompatible execution. -/
theorem access_not_interpSim : ¬ InterpSim BeforeAstReadability.interpRunLayout := by
  intro H
  exact access_not_halts "" 0
    (H.term_sim accessProgram accessConfig "" access_loaded access_bigStep)

theorem access_not_remainingWork : EndToEnd.RemainingWork BeforeAstReadability.interpRunLayout → False :=
  fun W => access_not_interpSim (EndToEnd.interpSim_ofWork W)

theorem access_not_behavioralCorrespondence :
    ¬ (∀ p c, Loaded BeforeAstReadability.interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)) := by
  intro H
  exact access_not_halts "" 0
    (((H accessProgram accessConfig access_loaded).1 "").mp access_bigStep)

#print axioms access_final_stuck
#print axioms access_not_halts
#print axioms access_not_interpSim
#print axioms access_not_remainingWork
#print axioms access_not_behavioralCorrespondence

end Vsa.Sim.AstAccessAudit
