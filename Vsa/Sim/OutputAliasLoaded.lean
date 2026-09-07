import Vsa.Sim.OutputAliasSnapshot
import Vsa.Sim.OutputAliasPhysical

/-! An explicit historical Loaded witness for the output-alias program.
The boundary predates the approved hereditary AST ownership requirement.
-/

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine
open Vsa.Sim.LayoutInstance
open Vsa.While.LoadedOutputAlias

/-- The concrete arena misses every protected image/runtime/main-return extent. -/
theorem arena_protected : ∀ a, ProtectedInitialByte a →
    ¬ (arena.lo ≤ a ∧ a < arena.hi) := by
  have hregions : ∀ r ∈ exitProtectedRegions,
      r.1 + r.2 ≤ arena.lo ∨ arena.hi ≤ r.1 := by decide
  intro a hp ha
  rcases hp with ⟨r, hr, hlo, hhi⟩
  rcases hregions r hr with hbefore | hafter <;> omega

def snapshotConfig : Config := physicalConfig snapshotMem

/-- Every required physical, memory, geometry, and prefix-survival field is proved. -/
theorem snapshot_readyFacts :
    InterpRunPhysicalFacts snapshotConfig 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 where
  good := (physical_carrier snapshotMem).good
  tick := (physical_carrier snapshotMem).tick
  pc := (physical_carrier snapshotMem).pc
  interp_arg := (physical_carrier snapshotMem).interp_arg
  interp_local := rfl
  stmts_arg := (physical_carrier snapshotMem).stmts_arg
  count_arg := (physical_carrier snapshotMem).count_arg
  repl_arg := (physical_carrier snapshotMem).repl_arg
  ra := (physical_carrier snapshotMem).ra
  sp := (physical_carrier snapshotMem).sp
  gp := (physical_carrier snapshotMem).gp
  main_ra := snapshot_mainRa
  htif_payload := (physical_carrier snapshotMem).htif_payload
  s0 := ⟨0, (physical_carrier snapshotMem).s0⟩
  s1 := ⟨0, (physical_carrier snapshotMem).s1⟩
  s2 := ⟨0, (physical_carrier snapshotMem).s2⟩
  s3 := ⟨0, (physical_carrier snapshotMem).s3⟩
  s4 := ⟨0, (physical_carrier snapshotMem).s4⟩
  s5 := ⟨0, (physical_carrier snapshotMem).s5⟩
  s6 := ⟨0, (physical_carrier snapshotMem).s6⟩
  s7 := ⟨0, (physical_carrier snapshotMem).s7⟩
  s8 := ⟨0, (physical_carrier snapshotMem).s8⟩
  s9 := ⟨0, (physical_carrier snapshotMem).s9⟩
  s10 := ⟨0, (physical_carrier snapshotMem).s10⟩
  s11 := ⟨0, (physical_carrier snapshotMem).s11⟩
  text_image := snapshot_text
  rodata_image := snapshot_rodata
  statics := snapshot_statics
  console := snapshot_console
  exit_runtime := snapshot_exitRuntime
  arena_protected := arena_protected
  out := (physical_carrier snapshotMem).out
  globals := snapshot_globals
  call_depth := snapshot_depth
  interp_geom := (physical_carrier snapshotMem).interp_geom
  setjmp_geom := (physical_carrier snapshotMem).setjmp_geom
  stack_ok := (physical_carrier snapshotMem).stack_ok
  stack_bytes := snapshot_stackBytes
  stmts_align := (physical_carrier snapshotMem).stmts_align
  stmts_ram := (physical_carrier snapshotMem).stmts_ram
  stmts_win := (physical_carrier snapshotMem).stmts_win
  stmts_stack := (physical_carrier snapshotMem).stmts_stack
  store := snapshot_storeFacts.store
  native_addrs := by decide
  store_survives := snapshot_storeFacts.store_survives
  arena_budget := by decide

/-- The historical physical boundary admits this exact finite alias snapshot. -/
theorem snapshot_loaded :
    Vsa.Refine.Loaded BeforeAstOwnership.interpRunLayout program snapshotConfig := by
  exact ⟨0x82000000, 2, snapshot_program,
    fixedInp, Nfixed, arena, phif, phic, 0, snapshot_readyFacts⟩

#print axioms arena_protected
#print axioms snapshot_readyFacts
#print axioms snapshot_loaded

end Vsa.Sim.OutputAliasLoaded
