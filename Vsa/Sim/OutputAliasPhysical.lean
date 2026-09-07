import Vsa.Sim.LayoutInstance
import Std.Data.ExtDHashMap.Lemmas

/- Explicit physical state for the finite alias witness. Memory is a parameter.
   This constructs a state satisfying register predicates; it does not claim
   that startup reaches this register map, or assume a GoodState witness. -/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open Vsa.Sim Vsa.Sim.LayoutInstance

namespace Vsa.Sim.OutputAliasLoaded

def physicalAssignments : List ((r : Register) × RegisterType r) :=
  [⟨Register.cur_privilege, Privilege.Machine⟩,
   ⟨Register.misa, initMisa⟩,
   ⟨Register.mstatus, initMstatus⟩,
   ⟨Register.mie, 0#64⟩,
   ⟨Register.mseccfg, 0#64⟩,
   ⟨Register.satp, 0#64⟩,
   ⟨Register.mtvec, 0#64⟩,
   ⟨Register.mideleg, 0#64⟩,
   ⟨Register.medeleg, 0#64⟩,
   ⟨Register.hart_state, HartState.HART_ACTIVE ()⟩,
   ⟨Register.htif_done, false⟩,
   ⟨Register.htif_tohost, 0#64⟩,
   ⟨Register.htif_tohost_base, some (BitVec.ofNat 64 tohostAddr)⟩,
   ⟨Register.elp, 0#1⟩,
   ⟨Register.pmpcfg_n, initPmpcfg⟩,
   ⟨Register.pmpaddr_n, initPmpaddr⟩,
   ⟨Register.pma_regions, initPmaRegions⟩,
   ⟨Register.menvcfg, 0#64⟩,
   ⟨Register.mcountinhibit, 0#32⟩,
   ⟨Register.mcyclecfg, 0#64⟩,
   ⟨Register.minstretcfg, 0#64⟩,
   ⟨Register.mip, 0#64⟩,
   ⟨Register.sig_meip, 0#1⟩,
   ⟨Register.sig_seip, 0#1⟩,
   ⟨Register.mtime, 0#64⟩,
   ⟨Register.mtimecmp, 0#64⟩,
   ⟨Register.minstret, 0#64⟩,
   ⟨Register.minstret_increment, false⟩,
   ⟨Register.mcycle, 0#64⟩,
   ⟨Register.nextPC, 0x800043ec#64⟩,
   ⟨Register.PC, 0x800043ec#64⟩,
   ⟨Register.htif_payload_writes, 0#4⟩,
   ⟨Register.x1, 0x800045ec#64⟩,
   ⟨Register.x2, BitVec.ofNat 64 spEntry⟩,
   ⟨Register.x3, BitVec.ofNat 64 gpEntry⟩,
   ⟨Register.x4, 0#64⟩,
   ⟨Register.x5, 0#64⟩,
   ⟨Register.x6, 0#64⟩,
   ⟨Register.x7, 0#64⟩,
   ⟨Register.x8, 0#64⟩,
   ⟨Register.x9, 0#64⟩,
   ⟨Register.x10, BitVec.ofNat 64 interpObject⟩,
   ⟨Register.x11, 0x82000000#64⟩,
   ⟨Register.x12, 2#64⟩,
   ⟨Register.x13, 0#64⟩,
   ⟨Register.x14, 0#64⟩,
   ⟨Register.x15, 0#64⟩,
   ⟨Register.x16, 0#64⟩,
   ⟨Register.x17, 0#64⟩,
   ⟨Register.x18, 0#64⟩,
   ⟨Register.x19, 0#64⟩,
   ⟨Register.x20, 0#64⟩,
   ⟨Register.x21, 0#64⟩,
   ⟨Register.x22, 0#64⟩,
   ⟨Register.x23, 0#64⟩,
   ⟨Register.x24, 0#64⟩,
   ⟨Register.x25, 0#64⟩,
   ⟨Register.x26, 0#64⟩,
   ⟨Register.x27, 0#64⟩,
   ⟨Register.x28, 0#64⟩,
   ⟨Register.x29, 0#64⟩,
   ⟨Register.x30, 0#64⟩,
   ⟨Register.x31, 0#64⟩]

private theorem assignments_distinct :
    physicalAssignments.Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide

def physicalRegs : Std.ExtDHashMap Register RegisterType :=
  Std.ExtDHashMap.ofList physicalAssignments

private theorem physicalRegs_get {r : Register} {v : RegisterType r}
    (h : ⟨r, v⟩ ∈ physicalAssignments) : physicalRegs.get? r = some v := by
  simpa [physicalRegs] using Std.ExtDHashMap.get?_ofList_of_mem
    (k := r) (k' := r) (by simp) assignments_distinct h

@[simp] theorem physicalRegs_cur_privilege :
    physicalRegs.get? Register.cur_privilege = some (Privilege.Machine) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_misa :
    physicalRegs.get? Register.misa = some (initMisa) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mstatus :
    physicalRegs.get? Register.mstatus = some (initMstatus) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mie :
    physicalRegs.get? Register.mie = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mseccfg :
    physicalRegs.get? Register.mseccfg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_satp :
    physicalRegs.get? Register.satp = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mtvec :
    physicalRegs.get? Register.mtvec = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mideleg :
    physicalRegs.get? Register.mideleg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_medeleg :
    physicalRegs.get? Register.medeleg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_hart_state :
    physicalRegs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_htif_done :
    physicalRegs.get? Register.htif_done = some (false) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_htif_tohost :
    physicalRegs.get? Register.htif_tohost = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_htif_tohost_base :
    physicalRegs.get? Register.htif_tohost_base = some (some (BitVec.ofNat 64 tohostAddr)) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_elp :
    physicalRegs.get? Register.elp = some (0#1) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_pmpcfg_n :
    physicalRegs.get? Register.pmpcfg_n = some (initPmpcfg) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_pmpaddr_n :
    physicalRegs.get? Register.pmpaddr_n = some (initPmpaddr) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_pma_regions :
    physicalRegs.get? Register.pma_regions = some (initPmaRegions) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_menvcfg :
    physicalRegs.get? Register.menvcfg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mcountinhibit :
    physicalRegs.get? Register.mcountinhibit = some (0#32) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mcyclecfg :
    physicalRegs.get? Register.mcyclecfg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_minstretcfg :
    physicalRegs.get? Register.minstretcfg = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mip :
    physicalRegs.get? Register.mip = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_sig_meip :
    physicalRegs.get? Register.sig_meip = some (0#1) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_sig_seip :
    physicalRegs.get? Register.sig_seip = some (0#1) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mtime :
    physicalRegs.get? Register.mtime = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mtimecmp :
    physicalRegs.get? Register.mtimecmp = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_minstret :
    physicalRegs.get? Register.minstret = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_minstret_increment :
    physicalRegs.get? Register.minstret_increment = some (false) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_mcycle :
    physicalRegs.get? Register.mcycle = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_nextPC :
    physicalRegs.get? Register.nextPC = some (0x800043ec#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_PC :
    physicalRegs.get? Register.PC = some (0x800043ec#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_htif_payload_writes :
    physicalRegs.get? Register.htif_payload_writes = some (0#4) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x1 :
    physicalRegs.get? Register.x1 = some (0x800045ec#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x2 :
    physicalRegs.get? Register.x2 = some (BitVec.ofNat 64 spEntry) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x3 :
    physicalRegs.get? Register.x3 = some (BitVec.ofNat 64 gpEntry) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x4 :
    physicalRegs.get? Register.x4 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x5 :
    physicalRegs.get? Register.x5 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x6 :
    physicalRegs.get? Register.x6 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x7 :
    physicalRegs.get? Register.x7 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x8 :
    physicalRegs.get? Register.x8 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x9 :
    physicalRegs.get? Register.x9 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x10 :
    physicalRegs.get? Register.x10 = some (BitVec.ofNat 64 interpObject) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x11 :
    physicalRegs.get? Register.x11 = some (0x82000000#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x12 :
    physicalRegs.get? Register.x12 = some (2#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x13 :
    physicalRegs.get? Register.x13 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x14 :
    physicalRegs.get? Register.x14 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x15 :
    physicalRegs.get? Register.x15 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x16 :
    physicalRegs.get? Register.x16 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x17 :
    physicalRegs.get? Register.x17 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x18 :
    physicalRegs.get? Register.x18 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x19 :
    physicalRegs.get? Register.x19 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x20 :
    physicalRegs.get? Register.x20 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x21 :
    physicalRegs.get? Register.x21 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x22 :
    physicalRegs.get? Register.x22 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x23 :
    physicalRegs.get? Register.x23 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x24 :
    physicalRegs.get? Register.x24 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x25 :
    physicalRegs.get? Register.x25 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x26 :
    physicalRegs.get? Register.x26 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x27 :
    physicalRegs.get? Register.x27 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x28 :
    physicalRegs.get? Register.x28 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x29 :
    physicalRegs.get? Register.x29 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x30 :
    physicalRegs.get? Register.x30 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

@[simp] theorem physicalRegs_x31 :
    physicalRegs.get? Register.x31 = some (0#64) := by
  apply physicalRegs_get
  simp [physicalAssignments]

def physicalState (m : Mem) : MState :=
  ⟨physicalRegs, (), m, (), 0, #[]⟩

def physicalConfig (m : Mem) : Config := ⟨physicalState m, 0, 0⟩

@[simp] theorem physicalConfig_mem (m : Mem) :
    (physicalConfig m).σ.mem = m := rfl

theorem physical_good (m : Mem) : GoodState (physicalState m) where
  cur_privilege := physicalRegs_cur_privilege
  misa := physicalRegs_misa
  mstatus := physicalRegs_mstatus
  mie := physicalRegs_mie
  mseccfg := physicalRegs_mseccfg
  satp := physicalRegs_satp
  mtvec := physicalRegs_mtvec
  mideleg := physicalRegs_mideleg
  medeleg := physicalRegs_medeleg
  hart_state := physicalRegs_hart_state
  htif_done := physicalRegs_htif_done
  htif_tohost := ⟨_, physicalRegs_htif_tohost⟩
  htif_tohost_base := physicalRegs_htif_tohost_base
  elp := physicalRegs_elp
  pmpcfg_n := physicalRegs_pmpcfg_n
  pmpaddr_n := physicalRegs_pmpaddr_n
  pma_regions := physicalRegs_pma_regions
  menvcfg := physicalRegs_menvcfg
  mcountinhibit := physicalRegs_mcountinhibit
  mcyclecfg := physicalRegs_mcyclecfg
  minstretcfg := physicalRegs_minstretcfg
  mip := ⟨_, physicalRegs_mip⟩
  sig_meip := ⟨_, physicalRegs_sig_meip⟩
  sig_seip := ⟨_, physicalRegs_sig_seip⟩
  mtime := ⟨_, physicalRegs_mtime⟩
  mtimecmp := ⟨_, physicalRegs_mtimecmp⟩
  minstret := ⟨_, physicalRegs_minstret⟩
  minstret_increment := ⟨_, physicalRegs_minstret_increment⟩
  mcycle := ⟨_, physicalRegs_mcycle⟩
  nextPC := ⟨_, physicalRegs_nextPC⟩
  PC := ⟨_, physicalRegs_PC⟩

/-- Every non-memory field needed by the fixed two-statement entry. -/
structure PhysicalCarrier (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRunEntry)
  interp_arg : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 interpObject)
  stmts_arg : c.σ.regs.get? Register.x11 = some (0x82000000#64)
  count_arg : c.σ.regs.get? Register.x12 = some (2#64)
  repl_arg : c.σ.regs.get? Register.x13 = some (0#64)
  ra : c.σ.regs.get? Register.x1 = some (0x800045ec#64)
  sp : c.σ.regs.get? Register.x2 = some (BitVec.ofNat 64 spEntry)
  gp : c.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 gpEntry)
  htif_payload : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  s0 : c.σ.regs.get? Register.x8 = some (0#64)
  s1 : c.σ.regs.get? Register.x9 = some (0#64)
  s2 : c.σ.regs.get? Register.x18 = some (0#64)
  s3 : c.σ.regs.get? Register.x19 = some (0#64)
  s4 : c.σ.regs.get? Register.x20 = some (0#64)
  s5 : c.σ.regs.get? Register.x21 = some (0#64)
  s6 : c.σ.regs.get? Register.x22 = some (0#64)
  s7 : c.σ.regs.get? Register.x23 = some (0#64)
  s8 : c.σ.regs.get? Register.x24 = some (0#64)
  s9 : c.σ.regs.get? Register.x25 = some (0#64)
  s10 : c.σ.regs.get? Register.x26 = some (0#64)
  s11 : c.σ.regs.get? Register.x27 = some (0#64)
  tp : c.σ.regs.get? Register.x4 = some (0#64)
  out : OutRepr c.σ Vsa.While.initSt
  interp_geom : ObjGeom ((BitVec.ofNat 64 interpObject).toNat, 384) stackSL spEntry
  setjmp_geom : WinRAM (BitVec.ofNat 64 interpObject + 16#64)
  stack_ok : StackOK stackSL (BitVec.ofNat 64 spEntry) (176 + 1088)
  stmts_align : (0x82000000 : Nat) % 8 = 0
  stmts_ram : 0x80000000 ≤ (0x82000000 : Nat) ∧ 0x82000000 + 8 * 2 ≤ 0x100000000
  stmts_win : tohostAddr + 16 ≤ (0x82000000 : Nat)
  stmts_stack : 0x82000000 + 8 * 2 ≤ stackSL.lo ∨ spEntry ≤ 0x82000000

theorem physical_carrier (m : Mem) : PhysicalCarrier (physicalConfig m) where
  good := physical_good m
  tick := by change (0 : Nat) < 2; decide
  pc := physicalRegs_PC
  interp_arg := physicalRegs_x10
  stmts_arg := physicalRegs_x11
  count_arg := physicalRegs_x12
  repl_arg := physicalRegs_x13
  ra := physicalRegs_x1
  sp := physicalRegs_x2
  gp := physicalRegs_x3
  htif_payload := physicalRegs_htif_payload_writes
  s0 := physicalRegs_x8
  s1 := physicalRegs_x9
  s2 := physicalRegs_x18
  s3 := physicalRegs_x19
  s4 := physicalRegs_x20
  s5 := physicalRegs_x21
  s6 := physicalRegs_x22
  s7 := physicalRegs_x23
  s8 := physicalRegs_x24
  s9 := physicalRegs_x25
  s10 := physicalRegs_x26
  s11 := physicalRegs_x27
  tp := physicalRegs_x4
  out := rfl
  interp_geom := ⟨by decide, by unfold RSub; decide, by decide, by decide⟩
  setjmp_geom := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  stack_ok := by unfold StackOK; decide
  stmts_align := by decide
  stmts_ram := by decide
  stmts_win := by decide
  stmts_stack := by decide

end Vsa.Sim.OutputAliasLoaded
