import Vsa.Elf
import Vsa.Sim.StateNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem log2_xlen_sub_one : ((Functions.log2_xlen : Int) - 1).toNat = 5 := by decide

theorem execute_itype_addi_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (v + (sign_extend (m := 64) imm))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ADDI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_itype_slti_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v (sign_extend (m := 64) imm))))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.SLTI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_itype_sltiu_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) imm))))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.SLTIU))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_itype_andi_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (v &&& (sign_extend (m := 64) imm))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ANDI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_itype_ori_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (v ||| (sign_extend (m := 64) imm))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.ORI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_itype_xori_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (v ^^^ (sign_extend (m := 64) imm))).run σ = .ok () σ') :
    (execute (instruction.ITYPE (imm, rs1, rd, iop.XORI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_rtype_add_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (v1 + v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.ADD))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_sub_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (v1 - v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SUB))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_slt_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v1 v2)))).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SLT))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_sltu_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v1 v2)))).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SLTU))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_and_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (v1 &&& v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.AND))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_or_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (v1 ||| v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.OR))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_xor_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (v1 ^^^ v2)).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.XOR))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtype_sll_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 5 0))).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SLL))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  rw [log2_xlen_sub_one, hwr]

theorem execute_rtype_srl_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (shift_bits_right v1 (Sail.BitVec.extractLsb v2 5 0))).run σ = .ok () σ') :
    (execute (instruction.RTYPE (rs2, rs1, rd, rop.SRL))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  rw [log2_xlen_sub_one, hwr]

theorem execute_rtypew_addw_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) ((Sail.BitVec.extractLsb v1 31 0) + (Sail.BitVec.extractLsb v2 31 0)))).run σ = .ok () σ') :
    (execute (instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPEW, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtypew_subw_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) ((Sail.BitVec.extractLsb v1 31 0) - (Sail.BitVec.extractLsb v2 31 0)))).run σ = .ok () σ') :
    (execute (instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPEW, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtypew_sllw_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))).run σ = .ok () σ') :
    (execute (instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPEW, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtypew_srlw_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))).run σ = .ok () σ') :
    (execute (instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPEW, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_rtypew_sraw_char (rs2 rs1 rd : regidx) (v1 v2 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))).run σ = .ok () σ') :
    (execute (instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs1 hrs2 hwr ⊢
  simp only [execute, execute_RTYPEW, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2, hwr]

theorem execute_shiftiop_slli_char (shamt : BitVec 6) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt 5 0))).run σ = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure, hrs]
  rw [log2_xlen_sub_one, hwr]

theorem execute_shiftiop_srli_char (shamt : BitVec 6) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (shift_bits_right v (Sail.BitVec.extractLsb shamt 5 0))).run σ = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SRLI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure, hrs]
  rw [log2_xlen_sub_one, hwr]

theorem execute_shiftiop_srai_char (shamt : BitVec 6) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))).run σ = .ok () σ') :
    (execute (instruction.SHIFTIOP (shamt, rs1, rd, sop.SRAI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure, hrs]
  rw [log2_xlen_sub_one, hwr]

theorem execute_shiftiwop_slliw_char (shamt : BitVec 5) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt))).run σ
      = .ok () σ') :
    (execute (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SLLIW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIWOP, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_shiftiwop_srliw_char (shamt : BitVec 5) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))).run σ
      = .ok () σ') :
    (execute (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRLIW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIWOP, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_shiftiwop_sraiw_char (shamt : BitVec 5) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))).run σ
      = .ok () σ') :
    (execute (instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRAIW))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_SHIFTIWOP, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_addiw_char (imm : BitVec 12) (rs1 rd : regidx) (v : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hrs : (rX_bits rs1).run σ = .ok v σ)
    (hwr : (wX_bits rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))).run σ
      = .ok () σ') :
    (execute (instruction.ADDIW (imm, rs1, rd))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hrs hwr ⊢
  simp only [execute, execute_ADDIW, bind, EStateM.bind, pure, EStateM.pure, hrs, hwr]

theorem execute_utype_lui_char (imm : BitVec 20) (rd : regidx)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwr : (wX_bits rd (sign_extend (m := 64) (imm +++ 0x000#12))).run σ = .ok () σ') :
    (execute (instruction.UTYPE (imm, rd, uop.LUI))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hwr ⊢
  simp only [execute, execute_UTYPE, bind, EStateM.bind, pure, EStateM.pure, hwr]

theorem execute_utype_auipc_char (imm : BitVec 20) (rd : regidx) (pc : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hwr : (wX_bits rd (pc + sign_extend (m := 64) (imm +++ 0x000#12))).run σ = .ok () σ') :
    (execute (instruction.UTYPE (imm, rd, uop.AUIPC))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hwr ⊢
  simp only [execute, execute_UTYPE, get_arch_pc, PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, hpc, hwr]

end Vsa.Sim
