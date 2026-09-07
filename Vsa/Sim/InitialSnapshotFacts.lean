import Vsa.Sim.OutputAliasLoaded

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Machine

namespace Vsa.Sim.OutputAliasLoaded
open Vsa.Sim.LayoutInstance

/-- Memory obligations for the fixed initial register snapshot. -/
structure SnapshotMemoryFacts (m : Mem) : Prop where
  mainRa : read64 m 0x87fffff8 = some 0x80000038
  text : Code.FixedTextLoaded m
  rodata : Code.FixedRodataLoaded m
  statics : Code.ImageStaticsLoaded m
  console : ConsoleStream m
  exitRuntime : ExitRuntimeData m
  globals : read64 m interpObject = some 0x81000000
  depth : read32 m (interpObject + 8) = some 0
  stackBytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b : BitVec 8, m[k]? = some b
  store : StoreRepr m Nfixed arena phif phic initSt.store
  storeSurvives : ∀ m' : Mem,
    (∀ k, ¬ interpRunWriteFootprint fixedInp k → m[k]? = m'[k]?) →
    StoreRepr m' Nfixed arena phif phic initSt.store

theorem SnapshotMemoryFacts.physicalFacts {m : Mem} (M : SnapshotMemoryFacts m) :
    InterpRunPhysicalFacts (physicalConfig m) 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 where
  good := (physical_carrier m).good
  tick := (physical_carrier m).tick
  pc := (physical_carrier m).pc
  interp_arg := (physical_carrier m).interp_arg
  interp_local := rfl
  stmts_arg := (physical_carrier m).stmts_arg
  count_arg := (physical_carrier m).count_arg
  repl_arg := (physical_carrier m).repl_arg
  ra := (physical_carrier m).ra
  sp := (physical_carrier m).sp
  gp := (physical_carrier m).gp
  main_ra := M.mainRa
  htif_payload := (physical_carrier m).htif_payload
  s0 := ⟨0, (physical_carrier m).s0⟩
  s1 := ⟨0, (physical_carrier m).s1⟩
  s2 := ⟨0, (physical_carrier m).s2⟩
  s3 := ⟨0, (physical_carrier m).s3⟩
  s4 := ⟨0, (physical_carrier m).s4⟩
  s5 := ⟨0, (physical_carrier m).s5⟩
  s6 := ⟨0, (physical_carrier m).s6⟩
  s7 := ⟨0, (physical_carrier m).s7⟩
  s8 := ⟨0, (physical_carrier m).s8⟩
  s9 := ⟨0, (physical_carrier m).s9⟩
  s10 := ⟨0, (physical_carrier m).s10⟩
  s11 := ⟨0, (physical_carrier m).s11⟩
  text_image := M.text
  rodata_image := M.rodata
  statics := M.statics
  console := M.console
  exit_runtime := M.exitRuntime
  arena_protected := arena_protected
  out := (physical_carrier m).out
  globals := M.globals
  call_depth := M.depth
  interp_geom := (physical_carrier m).interp_geom
  setjmp_geom := (physical_carrier m).setjmp_geom
  stack_ok := (physical_carrier m).stack_ok
  stack_bytes := M.stackBytes
  stmts_align := (physical_carrier m).stmts_align
  stmts_ram := (physical_carrier m).stmts_ram
  stmts_win := (physical_carrier m).stmts_win
  stmts_stack := (physical_carrier m).stmts_stack
  store := M.store
  native_addrs := by decide
  store_survives := M.storeSurvives
  arena_budget := by decide

#print axioms SnapshotMemoryFacts.physicalFacts
end Vsa.Sim.OutputAliasLoaded
