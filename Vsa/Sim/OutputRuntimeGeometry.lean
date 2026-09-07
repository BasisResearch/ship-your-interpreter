import Vsa.Sim.ExitRuntimeDataTransport
import Vsa.Sim.rows.FnWriteRFold

/-!
Finite geometry for known output writes, and preservation from the actual
_write_r summary memory image. The two write inventories are not a theorem
about the complete native print path. In particular, stack spills are handled
separately and full FILE/output preservation still requires reached proofs.
-/

open LeanRV64DExecutable Sail
open Vsa.MemRepr
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- Known persistent output mutations: the one-byte console buffer and errno. -/
def outputPersistentRegions : List (Nat × Nat) :=
  [(consoleBuf, 1), (wrErrnoAddr, 4)]

def OutputPersistentByte : Nat → Prop :=
  ExitRegionFoot outputPersistentRegions

/-- Transient FILE fields touched by output/flush paths. Their restored values
must be proved by the actual successful return path. -/
def outputTransientRegions : List (Nat × Nat) :=
  [(consoleStdout, 8), (consoleStdout + 12, 4), (consoleStdout + 16, 2)]

def OutputTransientByte : Nat → Prop :=
  ExitRegionFoot outputTransientRegions

private theorem exitRegionFoot_disjoint
    {left right : List (Nat × Nat)}
    (hregions : ∀ x ∈ left, ∀ y ∈ right,
      x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1)
    {a : Nat} (hleft : ExitRegionFoot left a) : ¬ ExitRegionFoot right a := by
  rintro ⟨y, hy, hylo, hyhi⟩
  obtain ⟨x, hx, hxlo, hxhi⟩ := hleft
  rcases hregions x hx y hy with hxy | hyx <;> omega

/-- Neither persistent output byte extent intersects the protected image,
extra exit fields, or main's saved pair. -/
theorem outputPersistent_not_protected {a : Nat}
    (h : OutputPersistentByte a) : ¬ ProtectedInitialByte a := by
  apply exitRegionFoot_disjoint (left := outputPersistentRegions)
    (right := exitProtectedRegions) (a := a) ?_ h
  decide

/-- Cursor, write count, and flags are outside the separately protected extra
exit fields. They remain part of ConsoleStream's own invariant. -/
theorem outputTransient_not_protected {a : Nat}
    (h : OutputTransientByte a) : ¬ ProtectedInitialByte a := by
  apply exitRegionFoot_disjoint (left := outputTransientRegions)
    (right := exitProtectedRegions) (a := a) ?_ h
  decide

private theorem exitRuntimeExtraFoot_protected {a : Nat}
    (h : ExitRuntimeExtraFoot a) : ProtectedInitialByte a := by
  obtain ⟨region, hregion, hlo, hhi⟩ := h
  exact ⟨region, by simp [exitProtectedRegions, hregion], hlo, hhi⟩

theorem outputPersistent_not_exitRuntimeExtra {a : Nat}
    (h : OutputPersistentByte a) : ¬ ExitRuntimeExtraFoot a :=
  fun hextra => outputPersistent_not_protected h (exitRuntimeExtraFoot_protected hextra)

theorem outputTransient_not_exitRuntimeExtra {a : Nat}
    (h : OutputTransientByte a) : ¬ ExitRuntimeExtraFoot a :=
  fun hextra => outputTransient_not_protected h (exitRuntimeExtraFoot_protected hextra)

/-- The actual _write_r memory image changes errno and its two stack saves.
Agreement with the extra runtime fields follows from their exact disjointness. -/
theorem wrM1_exitRuntimeExtra_agree (g : WRG) (hg : WRGOk g)
    (hstack : ∀ a, ExitRuntimeExtraFoot a →
      a < g.sp0.toNat - 16 ∨ g.sp0.toNat ≤ a) :
    AgreeP ExitRuntimeExtraFoot g.m0 (wrM1 g) := by
  intro a ha
  have herrno : ¬ (wrErrnoAddr ≤ a ∧ a < wrErrnoAddr + 4) := by
    intro hrange
    have hwrite : OutputPersistentByte a :=
      ⟨(wrErrnoAddr, 4), by simp [outputPersistentRegions], hrange⟩
    exact outputPersistent_not_exitRuntimeExtra hwrite ha
  exact (wrM1_getElem_lo g hg a (hstack a ha) (by omega)).symm

/-- Preserve ExitRuntimeData at a reached _write_r return. The conclusion uses
its exact post memory, without an assumed whole-output frame. -/
theorem WriteRFnPost.exitRuntimeData {g : WRG} {cfg : Config}
    (hpost : WriteRFnPost g cfg) (hg : WRGOk g)
    (hdata : ExitRuntimeData g.m0)
    (hstack : ∀ a, ExitRuntimeExtraFoot a →
      a < g.sp0.toNat - 16 ∨ g.sp0.toNat ≤ a) :
    ExitRuntimeData cfg.σ.mem := by
  rw [hpost.mem]
  exact hdata.transport (wrM1_exitRuntimeExtra_agree g hg hstack)

/-- Concrete stack-low geometry supplies the low-level spill separation. -/
theorem WriteRFnPost.exitRuntimeData_of_stackLow {g : WRG} {cfg : Config}
    (hpost : WriteRFnPost g cfg) (hg : WRGOk g)
    (hdata : ExitRuntimeData g.m0)
    (hstack : 0x87800000 + 16 ≤ g.sp0.toNat) :
    ExitRuntimeData cfg.σ.mem := by
  apply hpost.exitRuntimeData hg hdata
  intro a ha
  have hlo := exitRuntimeExtraFoot_below_stack ha
  exact Or.inl (by omega)

/-- Execute the existing low-level summary and retain the extra exit data.
This is only _write_r; it does not cover native output or FILE updates. -/
theorem write_r_exitRuntimeData (g : WRG)
    (hstack : 0x87800000 + 16 ≤ g.sp0.toNat) :
    Triple
      (fun cfg => PCAt 0x800104fc#64 cfg ∧ WriteRFnPre g cfg ∧
        ExitRuntimeData cfg.σ.mem)
      (fun cfg => WriteRFnPost g cfg ∧ ExitRuntimeData cfg.σ.mem) := by
  intro cfg h
  obtain ⟨hpc, hpre, hdata⟩ := h
  have hdata0 : ExitRuntimeData g.m0 := by
    rw [← hpre.mem]
    exact hdata
  obtain ⟨cfg', hsteps, hpost⟩ := (write_r_summary g).run cfg ⟨hpc, hpre⟩
  exact ⟨cfg', hsteps, hpost, hpost.exitRuntimeData_of_stackLow hpre.ok hdata0 hstack⟩

#print axioms outputPersistent_not_protected
#print axioms outputTransient_not_protected
#print axioms outputPersistent_not_exitRuntimeExtra
#print axioms outputTransient_not_exitRuntimeExtra
#print axioms wrM1_exitRuntimeExtra_agree
#print axioms WriteRFnPost.exitRuntimeData
#print axioms WriteRFnPost.exitRuntimeData_of_stackLow
#print axioms write_r_exitRuntimeData

end Vsa.Sim
