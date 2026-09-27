import Vsa.Sim.BlockTerm

namespace Vsa.Sim

def decodeM (w : BitVec 32) : Option (MKind × Nat × Nat × Nat × BitVec 12) :=
  let opcode := (w.extractLsb' 0 7).toNat
  let funct3 := (w.extractLsb' 12 3).toNat
  let funct7 := (w.extractLsb' 25 7).toNat
  let funct6 := (w.extractLsb' 26 6).toNat
  let rd     := (w.extractLsb' 7 5).toNat
  let rs1    := (w.extractLsb' 15 5).toNat
  let rs2    := (w.extractLsb' 20 5).toNat
  let immI   : BitVec 12 := w.extractLsb' 20 12
  let immS   : BitVec 12 := (w.extractLsb' 25 7).append (w.extractLsb' 7 5)
  if opcode = 0x13 then

    (if funct3 = 0 then some (.addi, rd, rs1, 0, immI)
     else if funct3 = 2 then some (.slti, rd, rs1, 0, immI)
     else if funct3 = 1 then some (.slli, rd, rs1, 0, immI)
     else if funct3 = 5 then
       (if funct6 = 0x00 then some (.srli, rd, rs1, 0, immI)
        else if funct6 = 0x10 then some (.srai, rd, rs1, 0, immI)
        else none)
     else if funct3 = 4 then some (.xori, rd, rs1, 0, immI)
     else if funct3 = 7 then some (.andi, rd, rs1, 0, immI)
     else if funct3 = 6 then some (.ori, rd, rs1, 0, immI)
     else none)
  else if opcode = 0x33 then

    (if funct3 = 0 then
      (if funct7 = 0x00 then some (.add, rd, rs1, rs2, 0#12)
       else if funct7 = 0x20 then some (.sub, rd, rs1, rs2, 0#12)
       else none)
     else if funct3 = 2 then some (.slt, rd, rs1, rs2, 0#12)
     else if funct3 = 6 then (if funct7 = 0x00 then some (.or, rd, rs1, rs2, 0#12) else none)
     else if funct3 = 7 then (if funct7 = 0x00 then some (.and, rd, rs1, rs2, 0#12) else none)
     else if funct3 = 5 then (if funct7 = 0x00 then some (.srl, rd, rs1, rs2, 0#12) else none)
     else if funct3 = 4 then (if funct7 = 0x00 then some (.xor, rd, rs1, rs2, 0#12) else none)
     else if funct3 = 1 then (if funct7 = 0x00 then some (.sll, rd, rs1, rs2, 0#12) else none)
     else none)
  else if opcode = 0x03 then

    (if funct3 = 2 then some (.lw, rd, rs1, 0, immI)
     else if funct3 = 3 then some (.ld, rd, rs1, 0, immI)
     else if funct3 = 4 then some (.lbu, rd, rs1, 0, immI)
     else if funct3 = 1 then some (.lh, rd, rs1, 0, immI)
     else if funct3 = 5 then some (.lhu, rd, rs1, 0, immI)
     else if funct3 = 6 then some (.lwu, rd, rs1, 0, immI)
     else none)
  else if opcode = 0x23 then

    (if funct3 = 2 then some (.sw, 0, rs1, rs2, immS)
     else if funct3 = 3 then some (.sd, 0, rs1, rs2, immS)
     else if funct3 = 0 then some (.sb, 0, rs1, rs2, immS)
     else if funct3 = 1 then some (.sh, 0, rs1, rs2, immS)
     else none)
  else if opcode = 0x1b then

    (if funct3 = 0 then some (.addiw, rd, rs1, 0, immI)
     else if funct3 = 1 then some (.slliw, rd, rs1, 0, immI)
     else if funct3 = 5 then
       (if funct7 = 0x00 then some (.srliw, rd, rs1, 0, immI)
        else if funct7 = 0x20 then some (.sraiw, rd, rs1, 0, immI)
        else none)
     else none)
  else if opcode = 0x3b then

    (if funct3 = 0 then
      (if funct7 = 0x00 then some (.addw, rd, rs1, rs2, 0#12)
       else if funct7 = 0x20 then some (.subw, rd, rs1, rs2, 0#12)
       else none)
     else if funct3 = 1 then (if funct7 = 0x00 then some (.sllw, rd, rs1, rs2, 0#12) else none)
     else if funct3 = 5 then
       (if funct7 = 0x00 then some (.srlw, rd, rs1, rs2, 0#12)
        else if funct7 = 0x20 then some (.sraw, rd, rs1, rs2, 0#12)
        else none)
     else none)
  else if opcode = 0x17 then

    some (.auipc, rd, 0, 0, 0#12)
  else if opcode = 0x37 then

    some (.lui, rd, 0, 0, 0#12)
  else none

def mkLine (pc : BitVec 64) (w : BitVec 32) : MInstr :=
  match decodeM w with
  | some (k, rd, rs1, rs2, imm) =>
      { pc := pc, word := w,
        b0 := w.extractLsb' 0 8, b1 := w.extractLsb' 8 8,
        b2 := w.extractLsb' 16 8, b3 := w.extractLsb' 24 8,
        kind := k, rd := rd, rs1 := rs1, rs2 := rs2, imm := imm }
  | none =>
      { pc := pc, word := w,
        b0 := w.extractLsb' 0 8, b1 := w.extractLsb' 8 8,
        b2 := w.extractLsb' 16 8, b3 := w.extractLsb' 24 8,
        kind := .addi, rd := 0, rs1 := 0, rs2 := 0, imm := 0#12 }

end Vsa.Sim
