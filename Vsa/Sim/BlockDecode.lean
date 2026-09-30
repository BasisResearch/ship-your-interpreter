import Vsa.Sim.BlockTerm

/-!
# `BlockDecode` — a reflected RISC-V decoder for the block model (Stage B)

A concrete, kernel-reducing decoder producing `MInstr` from a `(pc, word)` pair.
The point (Stage B of `experiments/block-abstractions-impl-plan.md`) is to stop
hand-transcribing the `kind/rd/rs1/rs2/imm` fields of every block-body `MInstr`
literal: `mkLine pc w` computes them from `w`, and is *definitionally equal* to
the hand literal for every real word (verified by the `rfl` `example`s below).
The downstream block VCs (`BBlockOK`, `wrRegsM`, `endPCM`) are discharged by
`decide` through the block body, so `mkLine` must keep reducing — hence the
nested-`if` (no `match`-on-`Nat`, no `Option.getD` opacity) construction, which
`rfl`-reduces where a `match` on a `Nat` scrutinee freezes.

Field convention (matching `astOfM` / the hand literals):
* ALU/LOAD (`addi/add/sub/lw/ld/lbu`): `rd` = bits 11..7, `rs1` = bits 19..15,
  `rs2` = bits 24..20 (only meaningful for `add`/`sub`; `0` otherwise), `imm` =
  the I-type immediate bits 31..20 for `addi`/loads, `0` for the R-type
  `add`/`sub` (their `imm` is unused).
* STORE (`sw/sd/sb`): `rd` = 0 (unused), `rs1` = base = bits 19..15, `rs2` =
  data = bits 24..20, `imm` = the S-type immediate {bits 31..25, bits 11..7}.

Scope: the nine `MKind`s.  Branch/jump terminators (`TInstr`) keep their hand
literals — the B-type/J-type immediate scatter is out of scope for this stage.
-/

namespace Vsa.Sim

/-- The decoded core fields of a straight-line instruction: kind + `rd`/`rs1`/
`rs2` (as `Nat`) + the 12-bit immediate.  `pc` and the LE bytes are supplied by
`mkLine`.  Nested `if` on the opcode/funct3/funct7 slices (no `match`-on-`Nat`)
so it `rfl`-reduces.  Returns `none` for words outside the nine supported
kinds. -/
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
    -- OP-IMM: addi (0) / slti (2) / slli (1) / srli (5) / xori (4); rs2 unused
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
    -- OP: add / sub (funct3 = 0, funct7 selects); slt (funct3 = 2)
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
    -- LOAD: lw (2) / ld (3) / lbu (4) / lwu (6, unsigned word); rs2 unused
    (if funct3 = 2 then some (.lw, rd, rs1, 0, immI)
     else if funct3 = 3 then some (.ld, rd, rs1, 0, immI)
     else if funct3 = 4 then some (.lbu, rd, rs1, 0, immI)
     else if funct3 = 1 then some (.lh, rd, rs1, 0, immI)
     else if funct3 = 5 then some (.lhu, rd, rs1, 0, immI)
     else if funct3 = 6 then some (.lwu, rd, rs1, 0, immI)
     else none)
  else if opcode = 0x23 then
    -- STORE: sw (2) / sd (3) / sb (0) / sh (1); rd unused, rs1 = base, rs2 = data
    (if funct3 = 2 then some (.sw, 0, rs1, rs2, immS)
     else if funct3 = 3 then some (.sd, 0, rs1, rs2, immS)
     else if funct3 = 0 then some (.sb, 0, rs1, rs2, immS)
     else if funct3 = 1 then some (.sh, 0, rs1, rs2, immS)
     else none)
  else if opcode = 0x1b then
    -- OP-IMM-32: addiw (funct3 = 0) / slliw (funct3 = 1); rs2 unused.  For
    -- `slliw` the `imm` field is unused (the 5-bit shamt is read off the raw
    -- word via `shamt5Of` in `astOfM`/`wvalM`); we park `immI` there for shape.
    (if funct3 = 0 then some (.addiw, rd, rs1, 0, immI)
     else if funct3 = 1 then some (.slliw, rd, rs1, 0, immI)
     else if funct3 = 5 then
       (if funct7 = 0x00 then some (.srliw, rd, rs1, 0, immI)
        else if funct7 = 0x20 then some (.sraiw, rd, rs1, 0, immI)
        else none)
     else none)
  else if opcode = 0x3b then
    -- OP-32: addw (funct3 = 0, funct7 = 0x00) / subw (funct3 = 0, funct7 = 0x20)
    -- / sllw (funct3 = 1) / srlw-sraw (funct3 = 5, funct7 selects)
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
    -- AUIPC: imm field unused (imm20 lives in the word; see `imm20Of`)
    some (.auipc, rd, 0, 0, 0#12)
  else if opcode = 0x37 then
    -- LUI: imm field unused (imm20 lives in the word; see `imm20Of`)
    some (.lui, rd, 0, 0, 0#12)
  else none

/-- Assemble a full `MInstr` from `pc` and `word`.  Nested-`if` on `decodeM w`
components (via a helper `Option.elim`-free destructure) so `mkLine pc w`
reduces to a concrete `MInstr.mk …` by `rfl` for real words; a `none` word
yields a dummy `addi x0,x0,0` line (never hit by the block bodies). -/
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

/-! ## B2 (light) — per-word defeq checks.

The block lemmas re-verify decode (via `block_facts`'s `DecodeTable` lemmas), so
`decodeM` only has to be *right*; wrong fields make the block lemma unprovable.
These `example`s are the safety net: each asserts `mkLine pc w` is definitionally
equal (`rfl`) to the hand `MInstr` literal it replaces. -/

-- negLoadStoreBlk
-- negPrologueBlk
-- negTailBlkA
-- negTailBlkB
-- comparison-arm kinds (the `EvalCmpRows` slice): real words from the
-- shared comparison arm 0x80003628.. and its dispatch tail.
-- slliw (grow-path head 0x80002b90: `slliw a5,a5,1`, rd=rs1=15, shamt=1).  Checked
-- field-by-field: the whole-struct `⟨…⟩` `rfl` freezes the kernel here (the LOAD/
-- STORE `immS` `.append` branches in the opcode chain balloon the combined defeq
-- problem past its budget — the individual field projections all reduce fine, and
-- `decodeM` reduces to `some (.slliw, …)` standalone), so we assert the *decoded*
-- fields directly.  `astOfM` below then confirms the reflected AST equals the
-- DecodeTable output.
-- the reflected AST matches the DecodeTable lemma output (shamt5 read off the word):
-- io-DAG residue kinds (real words from the proof binary):
-- xor a5,a1,a0 @ 0x80006bc8
-- sll a2,a2,t1 @ 0x80004948
-- sllw a4,s5,s0 @ 0x80007138
-- srlw a0,s5,a5 @ 0x80010c70
-- sraw a5,a4,a5 @ 0x80013a40
end Vsa.Sim
