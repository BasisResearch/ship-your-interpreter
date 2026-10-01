import Vsa.Sim.LayoutInstance
import Std.Data.ExtDHashMap.Lemmas

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

def physicalState (m : Mem) : MState :=
  ⟨physicalRegs, (), m, (), 0, #[]⟩

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

end Vsa.Sim.OutputAliasLoaded
