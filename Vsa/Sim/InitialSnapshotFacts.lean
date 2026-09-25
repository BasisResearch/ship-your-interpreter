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

/-- The physical facts from any register carrier over the memory `m`. -/
theorem SnapshotMemoryFacts.physicalFactsOf {m : Mem} {c : Config} (C : PhysicalCarrier c)
    (hm : c.σ.mem = m) (M : SnapshotMemoryFacts m) :
    InterpRunPhysicalFacts c 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 := by
  subst hm
  exact {
   good := C.good,
   tick := C.tick,
   pc := C.pc,
   interp_arg := C.interp_arg,
   interp_local := rfl,
   stmts_arg := C.stmts_arg,
   count_arg := C.count_arg,
   repl_arg := C.repl_arg,
   ra := C.ra,
   sp := C.sp,
   gp := C.gp,
   main_ra := M.mainRa,
   htif_payload := C.htif_payload,
   s0 := C.s0,
   s1 := ⟨0, C.s1⟩,
   s2 := ⟨0, C.s2⟩,
   s3 := ⟨0, C.s3⟩,
   s4 := ⟨0, C.s4⟩,
   s5 := ⟨0, C.s5⟩,
   s6 := ⟨0, C.s6⟩,
   s7 := ⟨0, C.s7⟩,
   s8 := ⟨0, C.s8⟩,
   s9 := ⟨0, C.s9⟩,
   s10 := ⟨0, C.s10⟩,
   s11 := ⟨0, C.s11⟩,
   text_image := M.text,
   rodata_image := M.rodata,
   statics := M.statics,
   console := M.console,
   exit_runtime := M.exitRuntime,
   arena_protected := arena_protected,
   out := C.out,
   globals := M.globals,
   call_depth := M.depth,
   interp_geom := C.interp_geom,
   setjmp_geom := C.setjmp_geom,
   stack_ok := C.stack_ok,
   stack_bytes := M.stackBytes,
   stmts_align := C.stmts_align,
   stmts_ram := C.stmts_ram,
   stmts_win := C.stmts_win,
   stmts_stack := C.stmts_stack,
   store := M.store,
   native_addrs := by decide,
   store_survives := M.storeSurvives,
   arena_budget := by decide }

theorem SnapshotMemoryFacts.physicalFacts {m : Mem} (M : SnapshotMemoryFacts m) :
    InterpRunPhysicalFacts (physicalConfig m) 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 :=
  M.physicalFactsOf (physical_carrier m) rfl

/-- The same facts at the snapshot with `main`'s `s0` (`physicalConfigS0`). -/
theorem SnapshotMemoryFacts.physicalFactsS0 {m : Mem} (M : SnapshotMemoryFacts m) :
    InterpRunPhysicalFacts (physicalConfigS0 m) 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 :=
  M.physicalFactsOf (physical_carrierS0 m) rfl

#print axioms SnapshotMemoryFacts.physicalFacts
end Vsa.Sim.OutputAliasLoaded
