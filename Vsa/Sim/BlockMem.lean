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
              (vbase + sign_extend (m := 64) imm).toNat (sbData vdata))) :=
  have hS := siteGood_of_good σ pc hG
  exec_store_w σ pc imm rs2 rs1 1 vbase vdata _ (by decide) hS hrs1 hrs2
    (vmem_write_addr_1 (afterNextPC (afterPrelude σ) pc)
      (vbase + sign_extend (m := 64) imm) (sbData vdata) initMstatus initPmpaddr
      hS.priv hS.mstatus (by decide) hS.pma hS.cfg hS.pmpaddr hS.tohost hlo hhiram hhiwin)

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
              ((vbase + sign_extend (m := 64) imm).toNat + 1) ((shData vdata).extractLsb' 8 8))) :=
  have hS := siteGood_of_good σ pc hG
  exec_store_w σ pc imm rs2 rs1 2 vbase vdata _ (by decide) hS hrs1 hrs2
    (vmem_write_addr_2 (afterNextPC (afterPrelude σ) pc)
      (vbase + sign_extend (m := 64) imm) (shData vdata) initMstatus initPmpaddr
      hS.priv hS.mstatus (by decide) hS.pma hS.cfg hS.pmpaddr hS.tohost hlo hhiram hhiwin halign)

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
    ∀ (w : BitVec 64), gprGet σ n = some w → gprGet σ' n = some w := by
  intro n h1 h31 w h
  gpr_cases n => refine obs_store_other' hobs _ ?_ h; decide

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

/-- The store kinds; every other kind writes `a.rd`. -/
def isStoreM : MKind → Bool
  | .sw | .sd | .sb | .sh => true
  | _ => false

section Family

variable {a : MInstr} {L : GRegs} {bs : List (BitVec 8)} {m : Std.ExtHashMap Nat (BitVec 8)}
  {r : List MInstr} {lds : List (List (BitVec 8))} {dom : List Nat}

/-! The block bookkeeping of one instruction depends on its family only. -/

theorem stepGM_reg (h : isStoreM a.kind = false) :
    stepGM a L bs = (a.rd, wvalM a L bs) :: eraseG a.rd L := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem stepMemM_reg (h : isStoreM a.kind = false) : stepMemM m a L = m := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem wlogM_reg (h : isStoreM a.kind = false) :
    wlogM (a :: r) L lds = wlogM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem wrRegsM_reg (h : isStoreM a.kind = false) : wrRegsM (a :: r) = a.rd :: wrRegsM r := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem domStepM_reg (h : isStoreM a.kind = false) : domStepM a dom = a.rd :: dom := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem stepGM_store (h : isStoreM a.kind = true) : stepGM a L bs = L := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem stepMemM_store (h : isStoreM a.kind = true) : stepMemM m a L = applyW m (wentryM a L) := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem wlogM_store (h : isStoreM a.kind = true) :
    wlogM (a :: r) L lds = wentryM a L :: wlogM r L lds := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem stepLdsM_store (h : isStoreM a.kind = true) : stepLdsM a.kind lds = lds := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem wrRegsM_store (h : isStoreM a.kind = true) : wrRegsM (a :: r) = wrRegsM r := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

theorem domStepM_store (h : isStoreM a.kind = true) : domStepM a dom = dom := by
  obtain ⟨_, _, _, _, _, _, k, _, _, _, _⟩ := a
  cases k <;> first | rfl | cases h

end Family

/-- A source register the block reads holds `srcVal n L` (law L-reg). -/
theorem rX_srcOK {σ : MState} {pc : BitVec 64} {L : GRegs} {dom : List Nat} {n : Nat}
    (hL : GHolds σ L) (hdom : ∀ k ∈ dom, k ∈ keysG L) (h : SrcOK n dom) :
    (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok (srcVal n L) (afterNextPC (afterPrelude σ) pc) :=
  rX_src σ pc n h.1 _ (srcPin_srcVal σ L n (h.2.imp id (hdom n)) hL)

/-- **L-block, register kinds.** The `execute` fact of every non-store kind: it writes
`wvalM a L bs` to `a.rd`. One characterisation per kind; the step is kind-independent. -/
theorem exec_reg_kind (σ : MState) (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (dom : List Nat) (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some a.pc)
    (hL : GHolds σ L) (hdom : ∀ n ∈ dom, n ∈ keysG L)
    (hk : isStoreM a.kind = false) (hkok : KindOK dom a.kind a.rd a.rs1 a.rs2)
    (hextra : MemFacts σ.mem L bs a) :
    (1 ≤ a.rd ∧ a.rd ≤ 31) ∧
    (execute (astOfM a)).run (afterNextPC (afterPrelude σ) a.pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ a.pc (gprReg a.rd) (gprRT a.rd (wvalM a L bs))) := by
  obtain ⟨pc, w, b0, b1, b2, b3, k, rd, rs1, rs2, imm⟩ := a
  have hw : ∀ v, (1 ≤ rd ∧ rd ≤ 31) → (wX_bits (gprIdx rd) v).run (afterNextPC (afterPrelude σ) pc)
      = .ok () {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert (gprReg rd) (gprRT rd v)} :=
    fun v hrd => wX_gpr _ v rd hrd.1 hrd.2
  have hs : ∀ n, SrcOK n dom → (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok (srcVal n L) (afterNextPC (afterPrelude σ) pc) := fun n h => rX_srcOK hL hdom h
  cases k
  -- immediate and register-register arithmetic
  case addi => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_itype_addi_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case slti => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_itype_slti_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case xori => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_itype_xori_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case andi => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_itype_andi_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case ori => obtain ⟨hrd, h1⟩ := hkok
              exact ⟨hrd, execute_itype_ori_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case addiw => obtain ⟨hrd, h1⟩ := hkok
                exact ⟨hrd, execute_addiw_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case slli => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_shiftiop_slli_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case srli => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_shiftiop_srli_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case srai => obtain ⟨hrd, h1⟩ := hkok
               exact ⟨hrd, execute_shiftiop_srai_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case slliw => obtain ⟨hrd, h1⟩ := hkok
                exact ⟨hrd, execute_shiftiwop_slliw_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case srliw => obtain ⟨hrd, h1⟩ := hkok
                exact ⟨hrd, execute_shiftiwop_srliw_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case sraiw => obtain ⟨hrd, h1⟩ := hkok
                exact ⟨hrd, execute_shiftiwop_sraiw_char _ _ _ _ _ _ (hs _ h1) (hw _ hrd)⟩
  case add => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_add_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case sub => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_sub_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case or => obtain ⟨hrd, h1, h2⟩ := hkok
             exact ⟨hrd, execute_rtype_or_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case and => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_and_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case xor => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_xor_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case sll => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_sll_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case srl => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_srl_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case slt => obtain ⟨hrd, h1, h2⟩ := hkok
              exact ⟨hrd, execute_rtype_slt_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case subw => obtain ⟨hrd, h1, h2⟩ := hkok
               exact ⟨hrd, execute_rtypew_subw_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case addw => obtain ⟨hrd, h1, h2⟩ := hkok
               exact ⟨hrd, execute_rtypew_addw_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case sllw => obtain ⟨hrd, h1, h2⟩ := hkok
               exact ⟨hrd, execute_rtypew_sllw_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case srlw => obtain ⟨hrd, h1, h2⟩ := hkok
               exact ⟨hrd, execute_rtypew_srlw_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case sraw => obtain ⟨hrd, h1, h2⟩ := hkok
               exact ⟨hrd, execute_rtypew_sraw_char _ _ _ _ _ _ _ (hs _ h1) (hs _ h2) (hw _ hrd)⟩
  case auipc =>
    have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
      rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
    exact ⟨hkok, execute_utype_auipc_char _ _ _ _ _ hpc₂ (hw _ hkok)⟩
  case lui => exact ⟨hkok, execute_utype_lui_char _ _ _ _ (hw _ hkok)⟩
  -- loads: the loaded value is read through the width layer
  case lw =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0, hp1, hp2, hp3⟩ := hextra
    exact ⟨hrd, exec_lw_ramv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 4) => (sign_extend (m := 64) w : BitVec 64))
        (bytesT4_of_lpins4 ⟨hp0, hp1, hp2, hp3⟩)) (hw _ hrd) hlo hhi hht⟩
  case lwu =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0, hp1, hp2, hp3⟩ := hextra
    exact ⟨hrd, exec_lwu_ramv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 4) => (zero_extend (m := 64) w : BitVec 64))
        (bytesT4_of_lpins4 ⟨hp0, hp1, hp2, hp3⟩)) (hw _ hrd) hlo hhi hht⟩
  case ld =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hextra
    exact ⟨hrd, exec_ld_ramv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 8) => (sign_extend (m := 64) w : BitVec 64))
        (bytesT8_of_lpins8 ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩)) (hw _ hrd) hlo hhi hht⟩
  case lbu =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0⟩ := hextra
    exact ⟨hrd, exec_lbu_totv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 1) => (zero_extend (m := 64) w : BitVec 64))
        (bytesT1_of_pin hp0)) (hw _ hrd) hlo hhi hht⟩
  case lh =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0, hp1⟩ := hextra
    exact ⟨hrd, exec_lh_ramv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 2) => (sign_extend (m := 64) w : BitVec 64))
        (bytesT2_of_pins hp0 hp1)) (hw _ hrd) hlo hhi hht⟩
  case lhu =>
    obtain ⟨hrd, h1⟩ := hkok
    obtain ⟨⟨hlo, hhi, hht⟩, hp0, hp1⟩ := hextra
    exact ⟨hrd, exec_lhu_ramv σ pc imm _ _ _ _ _ hG (hs _ h1)
      (congrArg (fun w : BitVec (8 * 2) => (zero_extend (m := 64) w : BitVec 64))
        (bytesT2_of_pins hp0 hp1)) (hw _ hrd) hlo hhi hht⟩
  all_goals cases hk

/-- **L-block, store kinds.** The `execute` fact of every store kind: it applies the write-log
entry `wentryM a L`, which lies above the code (so below-`tohost` bytes are unchanged). -/
theorem exec_store_kind (σ : MState) (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (dom : List Nat) (hG : GoodState σ) (hL : GHolds σ L) (hdom : ∀ n ∈ dom, n ∈ keysG L)
    (hk : isStoreM a.kind = true) (hkok : KindOK dom a.kind a.rd a.rs1 a.rs2)
    (hextra : MemFacts σ.mem L bs a) :
    (execute (astOfM a)).run (afterNextPC (afterPrelude σ) a.pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ a.pc (applyW σ.mem (wentryM a L))) ∧
    ∀ j, j < tohostAddr → (applyW σ.mem (wentryM a L))[j]? = σ.mem[j]? := by
  obtain ⟨pc, w, b0, b1, b2, b3, k, rd, rs1, rs2, imm⟩ := a
  have hs : ∀ n, SrcOK n dom → (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude σ) pc)
      = .ok (srcVal n L) (afterNextPC (afterPrelude σ) pc) := fun n h => rX_srcOK hL hdom h
  cases k
  case sw =>
    obtain ⟨h1, h2⟩ := hkok
    obtain ⟨hlo, hhi, hwin, hal⟩ := hextra
    exact ⟨exec_sw σ pc imm _ _ _ _ hG (hs _ h1) (hs _ h2) hlo hhi hwin hal,
      fun j hj => writeMap4_low_miss σ.mem (eaddrM ⟨pc, w, b0, b1, b2, b3, .sw, rd, rs1, rs2, imm⟩ L).toNat
        _ j (by omega)⟩
  case sd =>
    obtain ⟨h1, h2⟩ := hkok
    obtain ⟨hlo, hhi, hwin, hal⟩ := hextra
    exact ⟨exec_sd_val σ pc imm _ _ _ _ hG (hs _ h1) (hs _ h2) hlo hhi hwin hal,
      fun j hj => writeMap8_low_miss σ.mem (eaddrM ⟨pc, w, b0, b1, b2, b3, .sd, rd, rs1, rs2, imm⟩ L).toNat
        _ j (by omega)⟩
  case sb =>
    obtain ⟨h1, h2⟩ := hkok
    obtain ⟨hlo, hhi, hwin⟩ := hextra
    exact ⟨exec_sb_bm σ pc imm _ _ _ _ hG (hs _ h1) (hs _ h2) hlo hhi hwin,
      fun j hj => insert_low_miss σ.mem (eaddrM ⟨pc, w, b0, b1, b2, b3, .sb, rd, rs1, rs2, imm⟩ L).toNat
        _ j (by omega)⟩
  case sh =>
    obtain ⟨h1, h2⟩ := hkok
    obtain ⟨hlo, hhi, hwin, hal⟩ := hextra
    exact ⟨exec_sh_bm σ pc imm _ _ _ _ hG (hs _ h1) (hs _ h2) hlo hhi hwin hal,
      fun j hj => writeMap2_low_miss σ.mem (eaddrM ⟨pc, w, b0, b1, b2, b3, .sh, rd, rs1, rs2, imm⟩ L).toNat
        _ j (by omega)⟩
  all_goals cases hk

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
    obtain ⟨⟨hb0, hb1, hb2, hb3⟩, hdec, hextra, hfr⟩ : BytePinsM mc a ∧ DecodeFactM a ∧
        MemFacts σ.mem L (lds.headD []) a ∧
        ProgFactsM mc (stepMemM σ.mem a L) (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) r :=
      hfacts
    obtain ⟨⟨hpcn, hwn, hrvcn, hlo, hhi, halign, hkok⟩, hwfr⟩ :
        InstrOKM pc0 dom a ∧ BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r := hwf
    obtain rfl : pc0 = a.pc := (BitVec.eq_of_toNat_eq hpcn).symm
    have hhi' : a.pc.toNat + 4 ≤ tohostAddr := hhi
    -- the fetch front (law L-front)
    have F : Fetched σ a.pc (astOfM a) :=
      Fetched.of_bytes hG hpc ((hlow _ (by omega)).trans hb0) ((hlow _ (by omega)).trans hb1)
        ((hlow _ (by omega)).trans hb2) ((hlow _ (by omega)).trans hb3) hlo hhi halign
        (BitVec.eq_of_toNat_eq hrvcn) (BitVec.eq_of_toNat_eq hwn)
        (hdec _ (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
          (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
          (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    have hG0 : GoodState (afterNextPC (afterPrelude σ) a.pc) :=
      (hG.insert_nonpinned (r := Register.minstret_increment) (by decide) _).insert_nonpinned
        (r := Register.nextPC) (by decide) _
    have hsteps : ∀ {σ1 σf : MState} {i1 i' : Nat}, Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ →
        Steps ⟨σ1, i1, u + 1⟩ ⟨σf, i', u + 1 + r.length⟩ →
        Steps ⟨σ, i, u⟩ ⟨σf, i', u + (a :: r).length⟩ := fun h1 h2 => by
      have e : u + 1 + r.length = u + (a :: r).length := by simp only [List.length_cons]; omega
      exact e ▸ Steps.head h1 h2
    cases hk : isStoreM a.kind
    · -- register kinds: one commit, one register write
      obtain ⟨hrd, hexec⟩ := exec_reg_kind σ a L (lds.headD []) dom hG hpc hL hdom hk hkok hextra
      obtain ⟨hnpc, hinc, hms, hhart, hnp⟩ := gpr_rd_ok a.rd (by omega) hrd.1
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ := stepObs_retire (u := u)
        (try_step_retire F hexec
          ⟨by reg_reads [hhart, hG.hart_state], by reg_reads [hnpc], by reg_reads [hinc],
           by reg_reads [hms, hmi]⟩)
        hG ((hG0.insert_nonpinned hnp _).retirePost _ _) hi
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      rw [stepMemM_reg hk, stepGM_reg hk] at hfr
      rw [domStepM_reg hk] at hwfr
      obtain ⟨σf, i', hs, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt a.pc 4) vm1 ((a.rd, wvalM a L (lds.headD [])) :: eraseG a.rd L)
          _ mc σ.mem (a.rd :: dom)
          hG1 (obs_alu_pc hobs1) hmi1 hmem1 hlow
          ⟨obs_gpr_rd a.rd hrd.1 hrd.2 _ hobs1, gholds_eraseG hobs1 hrd.1 hrd.2 L hkeys hL⟩
          (keysOK_cons_erase hrd.1 hrd.2 L hkeys) (dom_cons_erase hdom) hfr hwfr hi1
      refine ⟨σf, i', hsteps hs1 hs, hi', hGf, ?_, houtf.trans hobs1.2, hpcf, hmif, ?_, ?_⟩
      · rw [wlogM_reg hk, stepGM_reg hk]; exact hmemf
      · simp only [runGM, stepGM_reg hk]; exact hGHf
      · intro R hn hrds
        rw [wrRegsM_reg hk] at hrds
        exact (hframef R hn fun n hn' => hrds n (List.mem_cons_of_mem _ hn')).trans
          (frame_step_alu hobs1 R hn (hrds _ List.mem_cons_self))
    · -- store kinds: one commit, one write-log entry
      obtain ⟨hexec, hlow1⟩ := exec_store_kind σ a L (lds.headD []) dom hG hL hdom hk hkok hextra
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ := stepObs_retire (u := u)
        (try_step_retire F hexec
          ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hmi]⟩)
        hG ((GoodState.of_regs_eq (σ := afterNextPC (afterPrelude σ) a.pc)
          (σ' := sigma3_store σ a.pc (applyW σ.mem (wentryM a L))) rfl hG0).retirePost _ _) hi
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      rw [stepMemM_store hk, stepGM_store hk] at hfr
      rw [domStepM_store hk] at hwfr
      obtain ⟨σf, i', hs, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt a.pc 4) vm1 L _ mc (applyW σ.mem (wentryM a L)) dom
          hG1 (obs_store_pc hobs1) hmi1 hmem1 (fun j hj => (hlow1 j hj).trans (hlow j hj))
          (gholds_store hobs1 L hkeys hL) hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', hsteps hs1 hs, hi', hGf, ?_, houtf.trans hobs1.2, hpcf, hmif, ?_, ?_⟩
      · rw [wlogM_store hk]; rw [stepLdsM_store hk] at hmemf; exact hmemf
      · simp only [runGM, stepGM_store hk]; exact hGHf
      · intro R hn hrds
        rw [wrRegsM_store hk] at hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)

end Vsa.Sim
