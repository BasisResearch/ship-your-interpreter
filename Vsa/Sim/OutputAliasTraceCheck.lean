import Vsa.Sim.OutputAliasTrace

/-! Finite checks for normalising the reached data of a concrete trace.
Register order may change in a reflected segment; every target pin is checked
against the segment's computed result. -/

open LeanRV64DExecutable Vsa Vsa.Machine

namespace Vsa.Sim.OutputAliasLoaded

structure TraceFits (source target : TraceData) : Prop where
  pc : source.pc = target.pc
  log : source.log = target.log
  out : source.out = target.out
  payload : source.payload = target.payload
  regs : ∀ pin ∈ target.regs, lookupG pin.1 source.regs = some pin.2

private theorem gholds_of_all_lookup {σ : MState} (source target : GRegs)
    (h : GHolds σ source)
    (hp : ∀ pin ∈ target, lookupG pin.1 source = some pin.2) : GHolds σ target := by
  induction target with
  | nil => trivial
  | cons pin rest ih =>
    exact ⟨gholds_lookup source h (hp pin (List.mem_cons_self ..)),
      ih (fun pin hmem => hp pin (List.mem_cons_of_mem _ hmem))⟩

/-- The target data must describe the same reached memory, output, PC, and pins. -/
theorem TraceHolds.rebase {source target : TraceData} {c : Config}
    (h : TraceHolds source c) (fit : TraceFits source target) : TraceHolds target c where
  good := h.good
  tick := h.tick
  pc := h.pc.trans (congrArg some fit.pc)
  minstret := h.minstret
  regs := gholds_of_all_lookup source.regs target.regs h.regs fit.regs
  mem := h.mem.trans (congrArg (writeLog snapshotMem) fit.log)
  out := h.out.trans fit.out
  payload := h.payload.trans (congrArg some fit.payload)

#print axioms TraceHolds.rebase

end Vsa.Sim.OutputAliasLoaded
