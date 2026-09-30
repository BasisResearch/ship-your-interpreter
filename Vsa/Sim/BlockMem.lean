import Vsa.Sim.BlockPilot
import Vsa.Sim.ValueSites
import Vsa.Sim.ObsAvoid
import Vsa.Sim.ExecLoadTotal
import Vsa.Sim.RamReadValue

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem exec_sb_bm (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat) :
    (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert
              (vbase + sign_extend (m := 64) imm).toNat (sbData vdata))) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hwrite := vmem_write_addr_1 (afterNextPC (afterPrelude σ) pc)
    (vbase + sign_extend (m := 64) imm) (sbData vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin
  have hchar := execute_STORE_char imm rs2 rs1 1
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      ((afterNextPC (afterPrelude σ) pc).mem.insert
        (vbase + sign_extend (m := 64) imm).toNat (sbData vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 1
          (sbData vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert
              (vbase + sign_extend (m := 64) imm).toNat (sbData vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

abbrev shData (vdata : BitVec 64) : BitVec (8 * 2) :=
  Sail.BitVec.extractLsb vdata 15 0

theorem exec_sh_bm (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 2 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (halign : (vbase + sign_extend (m := 64) imm).toNat % 2 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (((afterNextPC (afterPrelude σ) pc).mem.insert
                (vbase + sign_extend (m := 64) imm).toNat ((shData vdata).extractLsb' 0 8)).insert
              ((vbase + sign_extend (m := 64) imm).toNat + 1) ((shData vdata).extractLsb' 8 8))) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hwrite := vmem_write_addr_2 (afterNextPC (afterPrelude σ) pc)
    (vbase + sign_extend (m := 64) imm) (shData vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char imm rs2 rs1 2
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      (((afterNextPC (afterPrelude σ) pc).mem.insert
          (vbase + sign_extend (m := 64) imm).toNat ((shData vdata).extractLsb' 0 8)).insert
        ((vbase + sign_extend (m := 64) imm).toNat + 1) ((shData vdata).extractLsb' 8 8)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 2
          (shData vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            (((afterNextPC (afterPrelude σ) pc).mem.insert
                (vbase + sign_extend (m := 64) imm).toNat ((shData vdata).extractLsb' 0 8)).insert
              ((vbase + sign_extend (m := 64) imm).toNat + 1) ((shData vdata).extractLsb' 8 8)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 2))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

abbrev WEntry := Nat × Nat × BitVec 64

def applyW (m : Std.ExtHashMap Nat (BitVec 8)) : WEntry → Std.ExtHashMap Nat (BitVec 8)
  | (a, 1, d) => m.insert a (sbData d)
  | (a, 2, d) => (m.insert a ((shData d).extractLsb' 0 8)).insert (a + 1) ((shData d).extractLsb' 8 8)
  | (a, 4, d) => writeMap4 m a (swData d)
  | (a, 8, d) => writeMap8 m a (sdData_val d)
  | (_, _, _) => m

def writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) :
    Std.ExtHashMap Nat (BitVec 8) :=
  log.foldl applyW m

theorem insert_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (j : Nat) (hj : j < k) : (m.insert k v)[j]? = m[j]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem writeMap2_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 2))
    (j : Nat) (hj : j < k) :
    ((m.insert k (d.extractLsb' 0 8)).insert (k + 1) (d.extractLsb' 8 8))[j]? = m[j]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem writeMap4_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 4))
    (j : Nat) (hj : j < k) : (writeMap4 m k d)[j]? = m[j]? := by
  show ((((m.insert k _).insert (k + 1) _).insert (k + 2) _).insert (k + 3) _)[j]? = m[j]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem writeMap8_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (j : Nat) (hj : j < k) : (writeMap8 m k d)[j]? = m[j]? := by
  show ((((((((m.insert k _).insert (k + 1) _).insert (k + 2) _).insert (k + 3) _).insert
      (k + 4) _).insert (k + 5) _).insert (k + 6) _).insert (k + 7) _)[j]? = m[j]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem obs_gpr_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    ∀ (w : BitVec 64), gprGet σ n = some w → gprGet σ' n = some w
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, _, w, h => obs_store_other' hobs Register.x1 (by decide) h
  | 2, _, _, w, h => obs_store_other' hobs Register.x2 (by decide) h
  | 3, _, _, w, h => obs_store_other' hobs Register.x3 (by decide) h
  | 4, _, _, w, h => obs_store_other' hobs Register.x4 (by decide) h
  | 5, _, _, w, h => obs_store_other' hobs Register.x5 (by decide) h
  | 6, _, _, w, h => obs_store_other' hobs Register.x6 (by decide) h
  | 7, _, _, w, h => obs_store_other' hobs Register.x7 (by decide) h
  | 8, _, _, w, h => obs_store_other' hobs Register.x8 (by decide) h
  | 9, _, _, w, h => obs_store_other' hobs Register.x9 (by decide) h
  | 10, _, _, w, h => obs_store_other' hobs Register.x10 (by decide) h
  | 11, _, _, w, h => obs_store_other' hobs Register.x11 (by decide) h
  | 12, _, _, w, h => obs_store_other' hobs Register.x12 (by decide) h
  | 13, _, _, w, h => obs_store_other' hobs Register.x13 (by decide) h
  | 14, _, _, w, h => obs_store_other' hobs Register.x14 (by decide) h
  | 15, _, _, w, h => obs_store_other' hobs Register.x15 (by decide) h
  | 16, _, _, w, h => obs_store_other' hobs Register.x16 (by decide) h
  | 17, _, _, w, h => obs_store_other' hobs Register.x17 (by decide) h
  | 18, _, _, w, h => obs_store_other' hobs Register.x18 (by decide) h
  | 19, _, _, w, h => obs_store_other' hobs Register.x19 (by decide) h
  | 20, _, _, w, h => obs_store_other' hobs Register.x20 (by decide) h
  | 21, _, _, w, h => obs_store_other' hobs Register.x21 (by decide) h
  | 22, _, _, w, h => obs_store_other' hobs Register.x22 (by decide) h
  | 23, _, _, w, h => obs_store_other' hobs Register.x23 (by decide) h
  | 24, _, _, w, h => obs_store_other' hobs Register.x24 (by decide) h
  | 25, _, _, w, h => obs_store_other' hobs Register.x25 (by decide) h
  | 26, _, _, w, h => obs_store_other' hobs Register.x26 (by decide) h
  | 27, _, _, w, h => obs_store_other' hobs Register.x27 (by decide) h
  | 28, _, _, w, h => obs_store_other' hobs Register.x28 (by decide) h
  | 29, _, _, w, h => obs_store_other' hobs Register.x29 (by decide) h
  | 30, _, _, w, h => obs_store_other' hobs Register.x30 (by decide) h
  | 31, _, _, w, h => obs_store_other' hobs Register.x31 (by decide) h
  | _+32, _, h, _, _ => absurd h (by omega)

theorem gholds_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∀ (L : GRegs), KeysOK (keysG L) → GHolds σ L → GHolds σ' L := by
  intro L
  induction L with
  | nil => intro _ _; exact trivial
  | cons p L ih =>
    obtain ⟨n, w⟩ := p
    intro hK hL
    have hn := hK n (List.mem_cons_self ..)
    exact ⟨obs_gpr_store hobs n hn.1 hn.2 w hL.1,
      ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2⟩

theorem keysOK_cons_erase {n : Nat} (hn1 : 1 ≤ n) (hn31 : n ≤ 31) (L : GRegs)
    (hkeys : KeysOK (keysG L)) : KeysOK (n :: keysG (eraseG n L)) := by
  intro k hk
  cases hk with
  | head => exact ⟨hn1, hn31⟩
  | tail _ h => exact hkeys k (mem_of_mem_keysG_eraseG L h)

theorem dom_cons_erase {n : Nat} {dom : List Nat} {L : GRegs}
    (hdom : ∀ k ∈ dom, k ∈ keysG L) :
    ∀ k ∈ (n :: dom), k ∈ n :: keysG (eraseG n L) := by
  intro k hk
  cases hk with
  | head => exact List.mem_cons_self ..
  | tail _ h =>
    cases Nat.decEq k n with
    | isTrue e => rw [e]; exact List.mem_cons_self ..
    | isFalse ne => exact List.mem_cons_of_mem _ (mem_keysG_eraseG ne L (hdom k h))

theorem frame_step_alu {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false)
    (hrd : (gprReg n == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_alu σ pc vm (gprReg n) _ R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      hrd (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

theorem frame_step_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_store σ pc vm m' R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

inductive MKind where
  | addi : MKind
  | add  : MKind
  | sub  : MKind
  | or   : MKind
  | and  : MKind
  | srl  : MKind
  | xor  : MKind
  | sll  : MKind
  | lw   : MKind
  | lwu  : MKind
  | ld   : MKind
  | lbu  : MKind
  | lh   : MKind
  | lhu  : MKind
  | sw   : MKind
  | sd   : MKind
  | sb   : MKind
  | sh   : MKind
  | addiw : MKind
  | slli  : MKind
  | srli  : MKind
  | slti  : MKind
  | slt   : MKind
  | subw  : MKind
  | addw  : MKind
  | sllw  : MKind
  | srlw  : MKind
  | sraw  : MKind
  | auipc : MKind
  | lui   : MKind
  | xori  : MKind
  | andi  : MKind
  | ori   : MKind
  | srai  : MKind
  | slliw : MKind
  | srliw : MKind
  | sraiw : MKind
deriving DecidableEq

structure MInstr where
  pc   : BitVec 64
  word : BitVec 32
  b0   : BitVec 8
  b1   : BitVec 8
  b2   : BitVec 8
  b3   : BitVec 8
  kind : MKind
  rd   : Nat
  rs1  : Nat
  rs2  : Nat
  imm  : BitVec 12

def shamtOf (a : MInstr) : BitVec 6 :=
  a.imm.extractLsb' 0 6

def imm20Of (a : MInstr) : BitVec 20 :=
  a.word.extractLsb' 12 20

def shamt5Of (a : MInstr) : BitVec 5 :=
  a.word.extractLsb' 20 5

def astOfM (a : MInstr) : instruction :=
  match a.kind with
  | .addi => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.ADDI)
  | .add  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.ADD)
  | .sub  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SUB)
  | .or   => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.OR)
  | .and  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.AND)
  | .srl  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SRL)
  | .xor  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.XOR)
  | .sll  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SLL)
  | .lw   => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, false, 4)
  | .lwu  => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, true, 4)
  | .ld   => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, false, 8)
  | .lbu  => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, true, 1)
  | .lh   => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, false, 2)
  | .lhu  => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, true, 2)
  | .sw   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 4)
  | .sd   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 8)
  | .sb   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 1)
  | .sh   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 2)
  | .addiw => instruction.ADDIW (a.imm, gprIdx a.rs1, gprIdx a.rd)
  | .slli  => instruction.SHIFTIOP (shamtOf a, gprIdx a.rs1, gprIdx a.rd, sop.SLLI)
  | .srli  => instruction.SHIFTIOP (shamtOf a, gprIdx a.rs1, gprIdx a.rd, sop.SRLI)
  | .slti  => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.SLTI)
  | .slt   => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SLT)
  | .subw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.SUBW)
  | .addw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.ADDW)
  | .sllw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.SLLW)
  | .srlw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.SRLW)
  | .sraw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.SRAW)
  | .auipc => instruction.UTYPE (imm20Of a, gprIdx a.rd, uop.AUIPC)
  | .lui   => instruction.UTYPE (imm20Of a, gprIdx a.rd, uop.LUI)
  | .xori  => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.XORI)
  | .andi  => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.ANDI)
  | .ori   => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.ORI)
  | .srai  => instruction.SHIFTIOP (shamtOf a, gprIdx a.rs1, gprIdx a.rd, sop.SRAI)
  | .slliw => instruction.SHIFTIWOP (shamt5Of a, gprIdx a.rs1, gprIdx a.rd, sopw.SLLIW)
  | .srliw => instruction.SHIFTIWOP (shamt5Of a, gprIdx a.rs1, gprIdx a.rd, sopw.SRLIW)
  | .sraiw => instruction.SHIFTIWOP (shamt5Of a, gprIdx a.rs1, gprIdx a.rd, sopw.SRAIW)

def eaddrM (a : MInstr) (L : GRegs) : BitVec 64 :=
  srcVal a.rs1 L + sign_extend (m := 64) a.imm

def widthOfM : MKind → Nat
  | .lw | .lwu | .sw => 4
  | .ld | .sd => 8
  | .lbu | .sb => 1
  | .lh | .lhu | .sh => 2
  | _ => 0

def bytesVal (k : MKind) (bs : List (BitVec 8)) : BitVec 64 :=
  match k with
  | .lw => sign_extend (m := 64)
      (((((bs.getD 3 0#8).append (bs.getD 2 0#8)).append (bs.getD 1 0#8)).append
        (bs.getD 0 0#8)) : BitVec (8 * 4))
  | .lwu => zero_extend (m := 64)
      (((((bs.getD 3 0#8).append (bs.getD 2 0#8)).append (bs.getD 1 0#8)).append
        (bs.getD 0 0#8)) : BitVec (8 * 4))
  | .ld => sign_extend (m := 64)
      (((((((((bs.getD 7 0#8).append (bs.getD 6 0#8)).append (bs.getD 5 0#8)).append
        (bs.getD 4 0#8)).append (bs.getD 3 0#8)).append (bs.getD 2 0#8)).append
        (bs.getD 1 0#8)).append (bs.getD 0 0#8)) : BitVec (8 * 8))
  | .lbu => zero_extend (m := 64) ((bs.getD 0 0#8) : BitVec (8 * 1))
  | .lh => sign_extend (m := 64) ((((bs.getD 1 0#8).append (bs.getD 0 0#8))) : BitVec (8 * 2))
  | .lhu => zero_extend (m := 64) ((((bs.getD 1 0#8).append (bs.getD 0 0#8))) : BitVec (8 * 2))
  | _ => 0#64

def wvalM (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) : BitVec 64 :=
  match a.kind with
  | .addi => srcVal a.rs1 L + sign_extend (m := 64) a.imm
  | .add  => srcVal a.rs1 L + srcVal a.rs2 L
  | .sub  => srcVal a.rs1 L - srcVal a.rs2 L
  | .or   => srcVal a.rs1 L ||| srcVal a.rs2 L
  | .and  => srcVal a.rs1 L &&& srcVal a.rs2 L
  | .srl  => shift_bits_right (srcVal a.rs1 L) (Sail.BitVec.extractLsb (srcVal a.rs2 L) 5 0)
  | .xor  => srcVal a.rs1 L ^^^ srcVal a.rs2 L
  | .sll  => shift_bits_left (srcVal a.rs1 L) (Sail.BitVec.extractLsb (srcVal a.rs2 L) 5 0)
  | .addiw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (srcVal a.rs1 L + sign_extend (m := 64) a.imm) 31 0)
  | .slli => shift_bits_left (srcVal a.rs1 L) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .srli => shift_bits_right (srcVal a.rs1 L) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .srai => shift_bits_right_arith (srcVal a.rs1 L) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .slti => zero_extend (m := 64)
      (bool_to_bit (zopz0zI_s (srcVal a.rs1 L) (sign_extend (m := 64) a.imm)))
  | .slt  => zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal a.rs1 L) (srcVal a.rs2 L)))
  | .subw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0
        - Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0)
  | .addw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0
        + Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0)
  | .sllw => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0) 4 0))
  | .srlw => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0) 4 0))
  | .sraw => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0) 4 0))
  | .auipc => a.pc + sign_extend (m := 64) (imm20Of a +++ (0x000#12))
  | .lui => sign_extend (m := 64) (imm20Of a +++ (0x000#12))
  | .xori => srcVal a.rs1 L ^^^ sign_extend (m := 64) a.imm
  | .andi => srcVal a.rs1 L &&& sign_extend (m := 64) a.imm
  | .ori => srcVal a.rs1 L ||| sign_extend (m := 64) a.imm
  | .slliw => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0) (shamt5Of a))
  | .srliw => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0) (shamt5Of a))
  | .sraiw => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0) (shamt5Of a))
  | k => bytesVal k bs

def stepGM (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) : GRegs :=
  match a.kind with
  | .sw | .sd | .sb | .sh => L
  | _ => (a.rd, wvalM a L bs) :: eraseG a.rd L

def stepLdsM (k : MKind) (lds : List (List (BitVec 8))) : List (List (BitVec 8)) :=
  match k with
  | .lw | .lwu | .ld | .lbu | .lh | .lhu => lds.tail
  | _ => lds

def wentryM (a : MInstr) (L : GRegs) : WEntry :=
  ((eaddrM a L).toNat, widthOfM a.kind, srcVal a.rs2 L)

def stepMemM (m : Std.ExtHashMap Nat (BitVec 8)) (a : MInstr) (L : GRegs) :
    Std.ExtHashMap Nat (BitVec 8) :=
  match a.kind with
  | .sw | .sd | .sb | .sh => applyW m (wentryM a L)
  | _ => m

def runGM : List MInstr → GRegs → List (List (BitVec 8)) → GRegs
  | [], L, _ => L
  | a :: r, L, lds => runGM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)

def wlogM : List MInstr → GRegs → List (List (BitVec 8)) → List WEntry
  | [], _, _ => []
  | a :: r, L, lds =>
    match a.kind with
    | .sw | .sd | .sb | .sh => wentryM a L :: wlogM r L lds
    | _ => wlogM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)

def wrRegsM : List MInstr → List Nat
  | [] => []
  | a :: r =>
    match a.kind with
    | .sw | .sd | .sb | .sh => wrRegsM r
    | _ => a.rd :: wrRegsM r

def endPCM (pc0 : BitVec 64) : List MInstr → BitVec 64
  | [] => pc0
  | a :: r => endPCM (BitVec.addInt a.pc 4) r

def BytePinsM (m : Std.ExtHashMap Nat (BitVec 8)) (a : MInstr) : Prop :=
  m[a.pc.toNat]? = some a.b0 ∧ m[a.pc.toNat + 1]? = some a.b1 ∧
  m[a.pc.toNat + 2]? = some a.b2 ∧ m[a.pc.toNat + 3]? = some a.b3

def DecodeFactM (a : MInstr) : Prop :=
  ∀ s : SequentialState RegisterType trivialChoiceSource,
    s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
    s.regs.get? Register.cur_privilege =
      some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
    s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode a.word).run s = .ok (astOfM a) s

def LPins4 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (bs : List (BitVec 8)) : Prop :=
  (m[ea]?).getD 0 = bs.getD 0 0#8 ∧ (m[ea + 1]?).getD 0 = bs.getD 1 0#8 ∧
  (m[ea + 2]?).getD 0 = bs.getD 2 0#8 ∧ (m[ea + 3]?).getD 0 = bs.getD 3 0#8

def LPins8 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (bs : List (BitVec 8)) : Prop :=
  (m[ea]?).getD 0 = bs.getD 0 0#8 ∧ (m[ea + 1]?).getD 0 = bs.getD 1 0#8 ∧
  (m[ea + 2]?).getD 0 = bs.getD 2 0#8 ∧ (m[ea + 3]?).getD 0 = bs.getD 3 0#8 ∧
  (m[ea + 4]?).getD 0 = bs.getD 4 0#8 ∧ (m[ea + 5]?).getD 0 = bs.getD 5 0#8 ∧
  (m[ea + 6]?).getD 0 = bs.getD 6 0#8 ∧ (m[ea + 7]?).getD 0 = bs.getD 7 0#8

theorem lpin_of_present {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {b : BitVec 8}
    (h : m[a]? = some b) : (m[a]?).getD 0 = b := by rw [h]; rfl

theorem bytesT1_of_pin {m : Std.ExtHashMap Nat (BitVec 8)} {ea : Nat} {b : BitVec 8}
    (h : (m[ea]?).getD 0 = b) : (bytesT1 m ea : BitVec (8 * 1)) = b := h

theorem bytesT2_of_pins {m : Std.ExtHashMap Nat (BitVec 8)} {ea : Nat} {b0 b1 : BitVec 8}
    (h0 : (m[ea]?).getD 0 = b0) (h1 : (m[ea + 1]?).getD 0 = b1) :
    (bytesT2 m ea : BitVec (8 * 2)) = b1.append b0 := by
  simp only [bytesT2, h0, h1]

theorem bytesT4_of_lpins4 {m : Std.ExtHashMap Nat (BitVec 8)} {ea : Nat} {bs : List (BitVec 8)}
    (h : LPins4 m ea bs) :
    (bytesT4 m ea : BitVec (8 * 4))
      = (((bs.getD 3 0#8).append (bs.getD 2 0#8)).append (bs.getD 1 0#8)).append (bs.getD 0 0#8) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [bytesT4, h0, h1, h2, h3]

theorem bytesT8_of_lpins8 {m : Std.ExtHashMap Nat (BitVec 8)} {ea : Nat} {bs : List (BitVec 8)}
    (h : LPins8 m ea bs) :
    (bytesT8 m ea : BitVec (8 * 8))
      = (((((((bs.getD 7 0#8).append (bs.getD 6 0#8)).append (bs.getD 5 0#8)).append
          (bs.getD 4 0#8)).append (bs.getD 3 0#8)).append (bs.getD 2 0#8)).append
          (bs.getD 1 0#8)).append (bs.getD 0 0#8) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [bytesT8, h0, h1, h2, h3, h4, h5, h6, h7]

def MemFacts (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (bs : List (BitVec 8))
    (a : MInstr) : Prop :=
  match a.kind with
  | .addi | .add | .sub | .or | .and | .srl | .xor | .sll => True
  | .addiw | .slli | .srli | .srai | .slti | .slt | .subw | .addw | .auipc | .lui
  | .xori | .andi | .ori | .slliw | .srliw | .sraiw | .sllw | .srlw | .sraw => True
  | .lw =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    LPins4 m (eaddrM a L).toNat bs
  | .lwu =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    LPins4 m (eaddrM a L).toNat bs
  | .ld =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 8 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    LPins8 m (eaddrM a L).toNat bs
  | .lbu =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 1 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    ((m[(eaddrM a L).toNat]?).getD 0 = bs.getD 0 0#8)
  | .lh =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 2 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    (m[(eaddrM a L).toNat]?).getD 0 = bs.getD 0 0#8 ∧
    (m[(eaddrM a L).toNat + 1]?).getD 0 = bs.getD 1 0#8
  | .lhu =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 2 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    (m[(eaddrM a L).toNat]?).getD 0 = bs.getD 0 0#8 ∧
    (m[(eaddrM a L).toNat + 1]?).getD 0 = bs.getD 1 0#8
  | .sw =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat % 4 = 0
  | .sd =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat % 8 = 0
  | .sb =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat
  | .sh =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 2 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat % 2 = 0

def ProgFactsM (mc : Std.ExtHashMap Nat (BitVec 8)) :
    Std.ExtHashMap Nat (BitVec 8) → GRegs → List (List (BitVec 8)) → List MInstr → Prop
  | _, _, _, [] => True
  | m, L, lds, a :: r =>
    BytePinsM mc a ∧ DecodeFactM a ∧ MemFacts m L (lds.headD []) a ∧
    ProgFactsM mc (stepMemM m a L) (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) r

def KindOK (dom : List Nat) (k : MKind) (rd rs1 rs2 : Nat) : Prop :=
  match k with
  | .addi => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .add  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .sub  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .or   => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .and  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .srl  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .lw | .lwu | .ld | .lbu | .lh | .lhu => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .sw | .sd | .sb | .sh => SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .addiw | .slti => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slli | .srli | .srai => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slt | .subw | .addw => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .xor | .sll | .sllw | .srlw | .sraw =>
      (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .auipc => (1 ≤ rd ∧ rd ≤ 31)
  | .lui => (1 ≤ rd ∧ rd ≤ 31)
  | .xori => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .andi => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .ori => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slliw => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .srliw => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .sraiw => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom

instance instDecKindOK (dom : List Nat) (k : MKind) (rd rs1 rs2 : Nat) :
    Decidable (KindOK dom k rd rs1 rs2) :=
  match k with
  | .addi => inferInstanceAs (Decidable (_ ∧ _))
  | .add  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .sub  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .or   => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .and  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .srl  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .lw   => inferInstanceAs (Decidable (_ ∧ _))
  | .lwu  => inferInstanceAs (Decidable (_ ∧ _))
  | .ld   => inferInstanceAs (Decidable (_ ∧ _))
  | .lbu  => inferInstanceAs (Decidable (_ ∧ _))
  | .lh   => inferInstanceAs (Decidable (_ ∧ _))
  | .lhu  => inferInstanceAs (Decidable (_ ∧ _))
  | .sw   => inferInstanceAs (Decidable (_ ∧ _))
  | .sd   => inferInstanceAs (Decidable (_ ∧ _))
  | .sb   => inferInstanceAs (Decidable (_ ∧ _))
  | .sh   => inferInstanceAs (Decidable (_ ∧ _))
  | .addiw => inferInstanceAs (Decidable (_ ∧ _))
  | .slli  => inferInstanceAs (Decidable (_ ∧ _))
  | .srli  => inferInstanceAs (Decidable (_ ∧ _))
  | .slti  => inferInstanceAs (Decidable (_ ∧ _))
  | .slt   => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .subw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .addw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .xor   => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .sll   => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .sllw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .srlw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .sraw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .auipc => inferInstanceAs (Decidable (_ ∧ _))
  | .lui   => inferInstanceAs (Decidable (_ ∧ _))
  | .xori  => inferInstanceAs (Decidable (_ ∧ _))
  | .andi  => inferInstanceAs (Decidable (_ ∧ _))
  | .ori   => inferInstanceAs (Decidable (_ ∧ _))
  | .srai  => inferInstanceAs (Decidable (_ ∧ _))
  | .slliw => inferInstanceAs (Decidable (_ ∧ _))
  | .srliw => inferInstanceAs (Decidable (_ ∧ _))
  | .sraiw => inferInstanceAs (Decidable (_ ∧ _))

abbrev InstrOKM (pc0 : BitVec 64) (dom : List Nat) (a : MInstr) : Prop :=
  a.pc.toNat = pc0.toNat ∧
  (((a.b3.append a.b2).append a.b1).append a.b0).toNat = a.word.toNat ∧
  (Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0).toNat
    = (0b11#2 : BitVec 2).toNat ∧
  0x80000000 ≤ a.pc.toNat ∧
  a.pc.toNat + 4 ≤ tohostAddr ∧
  a.pc.toNat % 4 = 0 ∧
  KindOK dom a.kind a.rd a.rs1 a.rs2

def domStepM (a : MInstr) (dom : List Nat) : List Nat :=
  match a.kind with
  | .sw | .sd | .sb | .sh => dom
  | _ => a.rd :: dom

def BlockOKM (pc0 : BitVec 64) (dom : List Nat) : List MInstr → Prop
  | [] => True
  | a :: r => InstrOKM pc0 dom a ∧ BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r

instance instDecBlockOKM (pc0 : BitVec 64) (dom : List Nat) :
    (is : List MInstr) → Decidable (BlockOKM pc0 dom is)
  | [] => isTrue trivial
  | a :: r =>
    have : Decidable (BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r) :=
      instDecBlockOKM _ _ r
    inferInstanceAs (Decidable (_ ∧ _))

theorem block_mem_run (is : List MInstr) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (lds : List (List (BitVec 8)))
      (mc m : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m →
    (∀ j, j < tohostAddr → m[j]? = mc[j]?) →
    GHolds σ L →
    KeysOK (keysG L) →
    (∀ n ∈ dom, n ∈ keysG L) →
    ProgFactsM mc m L lds is →
    BlockOKM pc0 dom is →
    i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog m (wlogM is L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCM pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM is L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction is with
  | nil =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem _ hL _ _ _ _ hi
    exact ⟨σ, i, Steps.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons a r ih =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hfacts hwf hi
    subst hmem
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    have hfacts' : BytePinsM mc ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        DecodeFactM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        MemFacts σ.mem L (lds.headD [])
          ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        ProgFactsM mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L)
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM akind lds) r := hfacts
    obtain ⟨hbp, hdec, hextra, hfr⟩ := hfacts'
    have hwf' : InstrOKM pc0 dom ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        BlockOKM (BitVec.addInt apc 4)
          (domStepM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ dom) r := hwf
    obtain ⟨hwfa, hwfr⟩ := hwf'
    obtain ⟨hpcn, hwn, hrvcn, hlo, hhi, halign, hkok⟩ := hwfa
    have hpceq : apc = pc0 := BitVec.eq_of_toNat_eq hpcn
    subst hpceq
    have hword : (((ab3.append ab2).append ab1).append ab0) = aword :=
      BitVec.eq_of_toNat_eq hwn
    have hnotrvc : Sail.BitVec.extractLsb (((ab3.append ab2).append ab1).append ab0) 1 0
        = (0b11#2 : BitVec 2) := BitVec.eq_of_toNat_eq hrvcn
    have hhi' : apc.toNat + 4 ≤ tohostAddr := hhi
    have hb0 : σ.mem[apc.toNat]? = some ab0 := (hlow _ (by omega)).trans hbp.1
    have hb1 : σ.mem[apc.toNat + 1]? = some ab1 := (hlow _ (by omega)).trans hbp.2.1
    have hb2 : σ.mem[apc.toNat + 2]? = some ab2 := (hlow _ (by omega)).trans hbp.2.2.1
    have hb3 : σ.mem[apc.toNat + 3]? = some ab3 := (hlow _ (by omega)).trans hbp.2.2.2
    have hdec' := hdec (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
    cases akind with
    | addi =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .addi ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_addi_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.ADDI))
          (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .addi lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | add =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .add ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_add_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.ADD))
          (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .add lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sub =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .sub ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L - srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_sub_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L - srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SUB))
          (gprReg ard) (gprRT ard (srcVal ars1 L - srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L - srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sub lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | or =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .or ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L ||| srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_or_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L ||| srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.OR))
          (gprReg ard) (gprRT ard (srcVal ars1 L ||| srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .or, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L ||| srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .or, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .or, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .or, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .or lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lw ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0, hp1, hp2, hp3⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lw (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lw_ramv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lw (lds.headD []))))
        (srcVal ars1 L) (bytesVal .lw (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 4) => (sign_extend (m := 64) w : BitVec 64))
              (bytesT4_of_lpins4 ⟨hp0, hp1, hp2, hp3⟩))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, false, 4))
          (gprReg ard) (gprRT ard (bytesVal .lw (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lw (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lwu =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lwu ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0, hp1, hp2, hp3⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lwu (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lwu_ramv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lwu (lds.headD []))))
        (srcVal ars1 L) (bytesVal .lwu (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 4) => (zero_extend (m := 64) w : BitVec 64))
              (bytesT4_of_lpins4 ⟨hp0, hp1, hp2, hp3⟩))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, true, 4))
          (gprReg ard) (gprRT ard (bytesVal .lwu (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lwu (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lwu lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | ld =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .ld ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .ld (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_ld_ramv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .ld (lds.headD []))))
        (srcVal ars1 L) (bytesVal .ld (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 8) => (sign_extend (m := 64) w : BitVec 64))
              (bytesT8_of_lpins8 ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, false, 8))
          (gprReg ard) (gprRT ard (bytesVal .ld (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .ld (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .ld lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lbu =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lbu ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lbu (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lbu_totv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lbu (lds.headD []))))
        (srcVal ars1 L) (bytesVal .lbu (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 1) => (zero_extend (m := 64) w : BitVec 64))
              (bytesT1_of_pin hp0))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, true, 1))
          (gprReg ard) (gprRT ard (bytesVal .lbu (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lbu (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lbu lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lh =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lh ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0, hp1⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lh (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lh_ramv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lh (lds.headD []))))
        (srcVal ars1 L) (bytesVal .lh (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 2) => (sign_extend (m := 64) w : BitVec 64))
              (bytesT2_of_pins hp0 hp1))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, false, 2))
          (gprReg ard) (gprRT ard (bytesVal .lh (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lh, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lh (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lh, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lh, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lh, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lh lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sw =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sw ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin, haalign⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sw σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin haalign
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 4))
          (writeMap4 (afterNextPC (afterPrelude σ) apc).mem
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (swData (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (writeMap4_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sw lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | sd =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sd ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin, haalign⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sd_val σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin haalign
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 8))
          (writeMap8 (afterNextPC (afterPrelude σ) apc).mem
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (sdData_val (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (writeMap8_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sd lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | sb =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sb ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sb_bm σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 1))
          ((afterNextPC (afterPrelude σ) apc).mem.insert
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (sbData (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (insert_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sb lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | sh =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sh ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin, haalign2⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sh_bm σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin haalign2
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 2))
          (((afterNextPC (afterPrelude σ) apc).mem.insert
              (srcVal ars1 L + sign_extend (m := 64) aimm).toNat
              ((shData (srcVal ars2 L)).extractLsb' 0 8)).insert
            ((srcVal ars1 L + sign_extend (m := 64) aimm).toNat + 1)
            ((shData (srcVal ars2 L)).extractLsb' 8 8))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sh, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sh, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (writeMap2_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sh lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sh, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | addiw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .addiw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)) ard hrd1 hrd31
      have hexec := execute_addiw_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ADDIW (aimm, gprIdx ars1, gprIdx ard))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .addiw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slli =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slli ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_left (srcVal ars1 L)
          (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0))
        ard hrd1 hrd31
      have hexec := execute_shiftiop_slli_char
          (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_left (srcVal ars1 L)
            (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIOP (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sop.SLLI))
          (gprReg ard) (gprRT ard
            (shift_bits_left (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_left (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slli lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srli =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .srli ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_right (srcVal ars1 L)
          (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0))
        ard hrd1 hrd31
      have hexec := execute_shiftiop_srli_char
          (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_right (srcVal ars1 L)
            (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIOP (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sop.SRLI))
          (gprReg ard) (gprRT ard
            (shift_bits_right (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_right (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srli lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slti =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slti ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (zero_extend (m := 64)
          (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))) ard hrd1 hrd31
      have hexec := execute_itype_slti_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm))))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.SLTI))
          (gprReg ard) (gprRT ard
            (zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slti lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | xori =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .xori ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L ^^^ sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_xori_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (srcVal ars1 L ^^^ sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.XORI))
          (gprReg ard) (gprRT ard
            (srcVal ars1 L ^^^ sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (srcVal ars1 L ^^^ sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .xori lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | andi =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .andi ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L &&& sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_andi_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (srcVal ars1 L &&& sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.ANDI))
          (gprReg ard) (gprRT ard
            (srcVal ars1 L &&& sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .andi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (srcVal ars1 L &&& sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .andi, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .andi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .andi, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .andi lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slliw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slliw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
            (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)))
        ard hrd1 hrd31
      have hexec := execute_shiftiwop_slliw_char
          (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
              (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIWOP (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sopw.SLLIW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slliw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slt =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .slt ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))) ard hrd1 hrd31
      have hexec := execute_rtype_slt_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L))))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SLT))
          (gprReg ard) (gprRT ard
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slt lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | subw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .subw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
            - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) ard hrd1 hrd31
      have hexec := execute_rtypew_subw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
              - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.SUBW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .subw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | auipc =>
      obtain ⟨hrd1, hrd31⟩ :=
        (hkok : KindOK dom .auipc ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (apc + sign_extend (m := 64)
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))
        ard hrd1 hrd31
      have hpc₂ : (afterNextPC (afterPrelude σ) apc).regs.get? Register.PC = some apc := by
        rw [get?_afterNextPC σ apc _ (by decide) (by decide)]; exact hpc
      have hexec := execute_utype_auipc_char
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩)
          (gprIdx ard) apc
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (apc + sign_extend (m := 64)
            (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))))
        hpc₂ hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.UTYPE (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩,
            gprIdx ard, uop.AUIPC))
          (gprReg ard) (gprRT ard
            (apc + sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (apc + sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .auipc lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | ori =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .ori ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L ||| sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_ori_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (srcVal ars1 L ||| sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.ORI))
          (gprReg ard) (gprRT ard
            (srcVal ars1 L ||| sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (srcVal ars1 L ||| sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ori, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ori, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .ori lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srai =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .srai ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_right_arith (srcVal ars1 L)
          (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩) 5 0))
        ard hrd1 hrd31
      have hexec := execute_shiftiop_srai_char
          (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_right_arith (srcVal ars1 L)
            (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩) 5 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIOP (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sop.SRAI))
          (gprReg ard) (gprRT ard
            (shift_bits_right_arith (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_right_arith (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srai, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srai lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | and =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .and ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L &&& srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_and_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L &&& srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.AND))
          (gprReg ard) (gprRT ard (srcVal ars1 L &&& srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .and, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L &&& srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .and, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .and, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .and, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .and lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srl =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .srl ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_right (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0))
        ard hrd1 hrd31
      have hexec := execute_rtype_srl_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_right (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SRL))
          (gprReg ard) (gprRT ard
            (shift_bits_right (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srl, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_right (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srl, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srl, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srl, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srl lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | addw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .addw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
            + Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) ard hrd1 hrd31
      have hexec := execute_rtypew_addw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
              + Sail.BitVec.extractLsb (srcVal ars2 L) 31 0))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.ADDW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                + Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                + Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .addw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srliw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .srliw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
            (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩)))
        ard hrd1 hrd31
      have hexec := execute_shiftiwop_srliw_char
          (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
              (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩)))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIWOP (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sopw.SRLIW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srliw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sraiw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .sraiw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
            (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩)))
        ard hrd1 hrd31
      have hexec := execute_shiftiwop_sraiw_char
          (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
              (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩)))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIWOP (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sopw.SRAIW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sraiw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lui =>
      obtain ⟨hrd1, hrd31⟩ :=
        (hkok : KindOK dom .lui ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))
        ard hrd1 hrd31
      have hexec := execute_utype_lui_char
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩)
          (gprIdx ard)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))))
        hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.UTYPE (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩,
            gprIdx ard, uop.LUI))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ +++ (0x000#12))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ +++ (0x000#12))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lui, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lui lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lhu =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lhu ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0, hp1⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lhu (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lhu_ramv σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lhu (lds.headD []))))
        (srcVal ars1 L) (bytesVal .lhu (lds.headD [])) hG hrx1
        (by simp only [bytesVal]
            exact congrArg (fun w : BitVec (8 * 2) => (zero_extend (m := 64) w : BitVec 64))
              (bytesT2_of_pins hp0 hp1))
        hwx halo hahiram hahtif
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, true, 2))
          (gprReg ard) (gprRT ard (bytesVal .lhu (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lhu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lhu (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lhu, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lhu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lhu, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lhu lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | xor =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .xor ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L ^^^ srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_xor_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (srcVal ars1 L ^^^ srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.XOR))
          (gprReg ard) (gprRT ard
            (srcVal ars1 L ^^^ srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xor, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (srcVal ars1 L ^^^ srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xor, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xor, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xor, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .xor lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sll =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .sll ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_left (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0)) ard hrd1 hrd31
      have hexec := execute_rtype_sll_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_left (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SLL))
          (gprReg ard) (gprRT ard
            (shift_bits_left (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sll, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_left (srcVal ars1 L) (Sail.BitVec.extractLsb (srcVal ars2 L) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sll, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sll, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sll, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sll lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sllw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .sllw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) ard hrd1 hrd31
      have hexec := execute_rtypew_sllw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0)))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.SLLW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sllw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sllw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sllw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sllw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sllw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srlw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .srlw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) ard hrd1 hrd31
      have hexec := execute_rtypew_srlw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0)))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.SRLW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srlw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srlw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srlw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srlw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srlw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sraw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .sraw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) ard hrd1 hrd31
      have hexec := execute_rtypew_sraw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0)))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.SRAW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (srcVal ars2 L) 31 0) 4 0))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sraw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sraw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))

end Vsa.Sim
