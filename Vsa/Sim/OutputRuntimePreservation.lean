import Vsa.Sim.OutputRuntimeGeometry
import Vsa.Sim.rows.FnFflushREffect

/-! Extra exit-data preservation from actual successful flush memories. -/

open Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim

private theorem exitRuntimeExtra_output_disjoint {a : Nat}
    (ha : ExitRuntimeExtraFoot a) :
    (a < consoleStdout ∨ consoleStdout + 8 ≤ a) ∧
    (a < consoleStdout + 12 ∨ consoleStdout + 16 ≤ a) ∧
    (a < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ a) := by
  have hcursor : ¬ (consoleStdout ≤ a ∧ a < consoleStdout + 8) := by
    intro h
    exact outputTransient_not_exitRuntimeExtra
      ⟨(consoleStdout, 8), by simp [outputTransientRegions], h⟩ ha
  have hcount : ¬ (consoleStdout + 12 ≤ a ∧ a < consoleStdout + 16) := by
    intro h
    exact outputTransient_not_exitRuntimeExtra
      ⟨(consoleStdout + 12, 4), by simp [outputTransientRegions], h⟩ ha
  have herrno : ¬ (wrErrnoAddr ≤ a ∧ a < wrErrnoAddr + 4) := by
    intro h
    exact outputPersistent_not_exitRuntimeExtra
      ⟨(wrErrnoAddr, 4), by simp [outputPersistentRegions], h⟩ ha
  exact ⟨by omega, by omega, by omega⟩

theorem SflushFnPost.exitRuntimeData {g : SflushG} {c : Config}
    (h : SflushFnPost g c) (hg : SflushGOk g)
    (hdata : ExitRuntimeData g.m0)
    (hstack : 0x87800000 + 96 ≤ g.sp.toNat) :
    ExitRuntimeData c.σ.mem := by
  apply hdata.transport
  intro a ha
  obtain ⟨hcursor, hcount, herrno⟩ := exitRuntimeExtra_output_disjoint ha
  have hlo := exitRuntimeExtraFoot_below_stack ha
  rw [h.mem]
  exact (sflushCallbackM_getElem g hg a (Or.inl (by omega))
    hcursor hcount herrno).symm

theorem FflushFnPost.exitRuntimeData {g : FflushG} {c : Config}
    (h : FflushFnPost g c) (hg : FflushGOk g)
    (hdata : ExitRuntimeData g.m0)
    (hstack : 0x87800000 + 128 ≤ g.sp.toNat) :
    ExitRuntimeData c.σ.mem := by
  apply hdata.transport
  intro a ha
  obtain ⟨hcursor, hcount, herrno⟩ := exitRuntimeExtra_output_disjoint ha
  have hlo := exitRuntimeExtraFoot_below_stack ha
  rw [h.mem]
  exact (fflushReleaseM_getElem g hg a (Or.inl (by omega))
    hcursor hcount herrno).symm

/-- Run the existing `_fflush_r` summary and preserve the extra exit fields
at its actual return. Its original post also records the emitted byte. -/
theorem fflush_exitRuntimeData (g : FflushG)
    (hstack : 0x87800000 + 128 ≤ g.sp.toNat) :
    Vsa.Logic.Triple
      (fun c => PCAt 0x8000edcc#64 c ∧ FflushFnPre g c ∧
        ExitRuntimeData c.σ.mem)
      (fun c => FflushFnPost g c ∧ ExitRuntimeData c.σ.mem) := by
  intro c h
  obtain ⟨hpc, hpre, hdata⟩ := h
  have hdata0 : ExitRuntimeData g.m0 := by
    rw [← hpre.mem]
    exact hdata
  obtain ⟨result, hsteps, hpost⟩ := (fflush_summary g).run c ⟨hpc, hpre⟩
  exact ⟨result, hsteps, hpost, hpost.exitRuntimeData hpre.ok hdata0 hstack⟩

#print axioms SflushFnPost.exitRuntimeData
#print axioms FflushFnPost.exitRuntimeData
#print axioms fflush_exitRuntimeData

end Vsa.Sim
