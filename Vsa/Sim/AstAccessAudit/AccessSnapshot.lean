import Vsa.Sim.OutputAliasTrace
import Vsa.MemReprWithin
import Vsa.Sim.ExitRuntimeDataTransport

/-! A historical owned AST whose child address is outside machine-readable regions.
The six writes define the initial memory; they are not machine steps.
This file establishes admission under the ownership-only boundary and source
behavior. The boundary predates the approved AST readability requirement. -/

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.AstAccessAudit

open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

def accessLog : List WEntry :=
  [(0x82000000, 8, 0x4000#64), (0x82000008, 8, 0x4000#64),
   (0x4000, 4, 0#64), (0x4008, 8, 0x82000080#64),
   (0x82000080, 4, 0#64), (0x82000088, 8, 0#64)]

def accessMem : Mem := writeLog snapshotMem accessLog
def accessConfig : Config := physicalConfig accessMem
def accessStmt : Stmt := .expr (.int 0)
def accessProgram : Program := [accessStmt, accessStmt]

/-- The complete original RAM map remains, with the six finite overrides. -/
theorem access_lookup (a : Nat) :
    accessMem[a]? = logRead snapshotInitialRead accessLog a :=
  snapshot_logRead accessLog a

/-- Two unchanged intervals cover image, runtime, store, and C-stack reads. -/
def AccessStable (a : Nat) : Prop :=
  (0x80000000 ≤ a ∧ a < 0x82000000) ∨
  (0x87800000 ≤ a ∧ a < 0x88000000)

theorem access_unchanged (a : Nat) (ha : AccessStable a) :
    accessMem[a]? = snapshotMem[a]? := by
  apply writeLog_out
  simp only [accessLog, OutL, and_true]
  unfold AccessStable at ha
  omega

theorem access_image_byte (a : Nat) (hlo : 0x80000000 ≤ a)
    (hhi : a < 0x82000000) : accessMem[a]? = snapshotMem[a]? :=
  access_unchanged a (Or.inl ⟨hlo, hhi⟩)

theorem access_stable_agree : AgreeP AccessStable snapshotMem accessMem :=
  fun a ha => (access_unchanged a ha).symm

theorem access_storeView : StoreView accessMem :=
  snapshot_storeFacts.view.transport (fun a ha =>
    access_stable_agree a (Or.inl (by unfold StorePage at ha; omega)))

theorem access_store_survives : ∀ m' : Mem,
    (∀ k, ¬ interpRunWriteFootprint fixedInp k → accessMem[k]? = m'[k]?) →
    StoreRepr m' Nfixed arena phif phic initSt.store := by
  intro m' hag
  exact (access_storeView.transport (fun k hk =>
    hag k (storePage_outside_prefix hk))).store

theorem access_text : Code.FixedTextLoaded accessMem :=
  snapshot_text.transport (fun a hlo hhi => access_image_byte a hlo (by omega))

theorem access_rodata : Code.FixedRodataLoaded accessMem :=
  snapshot_rodata.transport (fun a hlo hhi => access_image_byte a (by omega) (by omega))

theorem access_statics : Code.ImageStaticsLoaded accessMem := by
  simpa (disch := decide) only [Code.ImageStaticsLoaded, Code.imgLldFmt,
    Code.imgDecPointStr, Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot,
    Code.imgDecPointPtr, Code.imgMbCurMax, Code.imgImpurePtr, access_image_byte]
    using snapshot_statics

theorem access_console : ConsoleStream accessMem := by
  apply ConsoleStream.of_agree _ snapshot_console
  intro a ha
  apply access_image_byte
  all_goals
    simp only [ConsoleFoot, consoleImpurePtrAddr, consoleReent,
      consoleStdout, consoleBuf] at ha
    omega

theorem access_exitRuntime : ExitRuntimeData accessMem := by
  apply snapshot_exitRuntime.transport
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  have hbounds : ∀ r ∈ exitRuntimeExtraRegions,
      0x80000000 ≤ r.1 ∧ r.1 + r.2 ≤ 0x82000000 := by decide
  have hb := hbounds r hr
  exact (access_image_byte a (by omega) (by omega)).symm

theorem access_mainRa : read64 accessMem 0x87fffff8 = some 0x80000038 := by
  rw [← read64_agreeP access_stable_agree (by
    intro k hk; right; omega)]
  exact snapshot_mainRa

theorem access_globals : read64 accessMem interpObject = some 0x81000000 := by
  rw [← read64_agreeP access_stable_agree (by
    intro k hk; right
    change 0x87800000 ≤ 0x87fffe10 + k ∧ 0x87fffe10 + k < 0x88000000
    omega)]
  exact snapshot_globals

theorem access_depth : read32 accessMem (interpObject + 8) = some 0 := by
  rw [← read32_agreeP access_stable_agree (by
    intro k hk; right
    change 0x87800000 ≤ 0x87fffe10 + 8 + k ∧ 0x87fffe10 + 8 + k < 0x88000000
    omega)]
  exact snapshot_depth

theorem access_stackBytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b : BitVec 8, accessMem[k]? = some b := by
  intro k hlo hhi
  rw [access_unchanged k (Or.inr ⟨hlo, hhi⟩)]
  exact snapshot_stackBytes k hlo hhi

/-- All physical boundary fields are proved from the constructed memory. -/
theorem access_physicalFacts :
    InterpRunPhysicalFacts accessConfig 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 where
  good := (physical_carrier accessMem).good
  tick := (physical_carrier accessMem).tick
  pc := (physical_carrier accessMem).pc
  interp_arg := (physical_carrier accessMem).interp_arg
  interp_local := rfl
  stmts_arg := (physical_carrier accessMem).stmts_arg
  count_arg := (physical_carrier accessMem).count_arg
  repl_arg := (physical_carrier accessMem).repl_arg
  ra := (physical_carrier accessMem).ra
  sp := (physical_carrier accessMem).sp
  gp := (physical_carrier accessMem).gp
  main_ra := access_mainRa
  htif_payload := (physical_carrier accessMem).htif_payload
  s0 := ⟨0, (physical_carrier accessMem).s0⟩
  s1 := ⟨0, (physical_carrier accessMem).s1⟩
  s2 := ⟨0, (physical_carrier accessMem).s2⟩
  s3 := ⟨0, (physical_carrier accessMem).s3⟩
  s4 := ⟨0, (physical_carrier accessMem).s4⟩
  s5 := ⟨0, (physical_carrier accessMem).s5⟩
  s6 := ⟨0, (physical_carrier accessMem).s6⟩
  s7 := ⟨0, (physical_carrier accessMem).s7⟩
  s8 := ⟨0, (physical_carrier accessMem).s8⟩
  s9 := ⟨0, (physical_carrier accessMem).s9⟩
  s10 := ⟨0, (physical_carrier accessMem).s10⟩
  s11 := ⟨0, (physical_carrier accessMem).s11⟩
  text_image := access_text
  rodata_image := access_rodata
  statics := access_statics
  console := access_console
  exit_runtime := access_exitRuntime
  arena_protected := arena_protected
  out := (physical_carrier accessMem).out
  globals := access_globals
  call_depth := access_depth
  interp_geom := (physical_carrier accessMem).interp_geom
  setjmp_geom := (physical_carrier accessMem).setjmp_geom
  stack_ok := (physical_carrier accessMem).stack_ok
  stack_bytes := access_stackBytes
  stmts_align := (physical_carrier accessMem).stmts_align
  stmts_ram := (physical_carrier accessMem).stmts_ram
  stmts_win := (physical_carrier accessMem).stmts_win
  stmts_stack := (physical_carrier accessMem).stmts_stack
  store := access_storeView.store
  native_addrs := by decide
  store_survives := access_store_survives
  arena_budget := by decide

local macro "access_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, access_lookup]; decide))

theorem access_array0 : read64 accessMem 0x82000000 = some 0x4000 := by access_read
theorem access_array1 : read64 accessMem 0x82000008 = some 0x4000 := by access_read
theorem access_stmt_tag : read32 accessMem 0x4000 = some 0 := by access_read
theorem access_stmt_ptr : read64 accessMem 0x4008 = some 0x82000080 := by access_read
theorem access_expr_tag : read32 accessMem 0x82000080 = some 0 := by access_read
theorem access_expr_value : read64 accessMem 0x82000088 = some 0 := by access_read
theorem access_expr_int : readI64 accessMem 0x82000088 = some 0 := by
  simp [readI64, access_expr_value]

def AccessOwned (k : Nat) : Prop :=
  ¬ LayoutInstance.AstMutableByte accessMem arena (phif 0) k

/-- All represented reads miss the four mutable-storage categories. -/
theorem access_owned_byte {k : Nat}
    (hk : (0x4000 ≤ k ∧ k < 0x4010) ∨
      (0x82000000 ≤ k ∧ k < 0x82000090)) : AccessOwned k := by
  intro hm
  change Vsa.Sim.AstMutableByte accessMem stackSL arena 0x81000000 k at hm
  rcases hm with he | hs | ha | hh | ⟨cap, names, hc, hn, hw⟩ |
    ⟨cap, values, hc, hv, hw⟩
  · omega
  · change 0x87800000 ≤ k ∧ k < 0x88000000 at hs
    omega
  · change 0x81000000 ≤ k ∧ k < 0x81001000 at ha
    omega
  · change 0x81000000 ≤ k ∧ k < 0x81000000 + 32 at hh
    omega
  · have hc' := Option.some.inj (hc.symm.trans access_storeView.capacity)
    have hn' := Option.some.inj (hn.symm.trans access_storeView.names)
    subst cap
    subst names
    change 0x81000040 ≤ k ∧ k < 0x81000040 + 8 * 8 at hw
    omega
  · have hc' := Option.some.inj (hc.symm.trans access_storeView.capacity)
    have hv' := Option.some.inj (hv.symm.trans access_storeView.values)
    subst cap
    subst values
    change 0x81000080 ≤ k ∧ k < 0x81000080 + 24 * 8 at hw
    omega

theorem access_expr_owned :
    ExprReprWithin accessMem AccessOwned 0x82000080 (.int 0) := by
  apply ExprReprWithin.int access_expr_tag _ access_expr_int
  all_goals intro i hi; apply access_owned_byte; right; omega

theorem access_stmt_owned : StmtReprWithin accessMem AccessOwned 0x4000 accessStmt := by
  apply StmtReprWithin.expr access_stmt_tag _ access_stmt_ptr _ access_expr_owned
  all_goals intro i hi; apply access_owned_byte; left; omega

theorem access_program_owned :
    ProgramReprWithin accessMem AccessOwned 0x82000000 2 accessProgram := by
  refine ⟨StmtArrayReprWithin.cons access_array0 ?_ access_stmt_owned
    (StmtArrayReprWithin.cons access_array1 ?_ access_stmt_owned StmtArrayReprWithin.nil), rfl⟩
  all_goals intro i hi; apply access_owned_byte; right; omega

/-- Tag and value reads determine the sole represented expression at this node. -/
theorem access_expr_unique {e : Expr}
    (h : ExprRepr accessMem 0x82000080 e) : e = .int 0 := by
  cases h <;> simp_all [access_expr_tag, access_expr_int]

theorem access_stmt_unique {s : Stmt}
    (h : StmtRepr accessMem 0x4000 s) : s = accessStmt := by
  unfold accessStmt
  cases h <;> simp_all [access_stmt_tag, access_stmt_ptr]
  all_goals subst_vars; apply access_expr_unique; assumption

/-- Universal ownership is justified for every program represented at entry. -/
theorem access_program_unique {p : Program}
    (h : ProgramRepr accessMem 0x82000000 2 p) : p = accessProgram := by
  cases h.1 with
  | cons hp hs ht =>
    have hptr := Option.some.inj (hp.symm.trans access_array0)
    rw [hptr] at hs
    have hfirst := access_stmt_unique hs
    cases ht with
    | cons hp hs ht =>
      have hptr := Option.some.inj (hp.symm.trans access_array1)
      rw [hptr] at hs
      have hsecond := access_stmt_unique hs
      cases ht
      simp_all [accessProgram]

/-- The historical ownership-only entry record admits this snapshot. -/
theorem access_readyFacts :
    InterpRunOwnedFacts accessConfig 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 where
  toInterpRunPhysicalFacts := access_physicalFacts
  ast_owned := by
    intro p hp
    have heq := access_program_unique hp
    subst p
    exact access_program_owned

/-- Admission is retained only under the boundary before AST readability. -/
theorem access_loaded :
    Vsa.Refine.Loaded BeforeAstReadability.interpRunLayout accessProgram accessConfig := by
  exact ⟨0x82000000, 2, access_program_owned.erase,
    fixedInp, Nfixed, arena, phif, phic, 0, access_readyFacts⟩

theorem access_stmt_exec : ExecS initSt 0 0 accessStmt initSt .normal :=
  ExecS.expr initSt 0 0 (.int 0) initSt (.int 0) (EvalE.int initSt 0 0 0)

theorem access_bigStep : BigStep accessProgram "" := by
  refine ⟨initSt, ?_, rfl⟩
  exact ExecSeq.consNormal initSt 0 0 accessStmt [accessStmt] initSt initSt .normal
    access_stmt_exec (ExecSeq.consNormal initSt 0 0 accessStmt [] initSt initSt .normal
      access_stmt_exec (ExecSeq.nil initSt 0 0))

#print axioms access_physicalFacts
#print axioms access_program_owned
#print axioms access_program_unique
#print axioms access_readyFacts
#print axioms access_loaded
#print axioms access_bigStep

end Vsa.Sim.AstAccessAudit
