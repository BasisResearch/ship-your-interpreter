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

/-- The four little-endian bytes of a 32-bit word (`b0` = low byte).  Phrased
via `BitVec.extractLsb'` so it kernel-reduces under `decide`/`rfl`. -/
def bsplit (w : BitVec 32) : BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8 :=
  (w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8)

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
example : mkLine 0x800039ac#64 0x09813583#32
    = ⟨0x800039ac#64, 0x09813583#32, 0x83#8, 0x35#8, 0x81#8, 0x09#8, .ld, 11, 2, 0, 0x098#12⟩ := by rfl
example : mkLine 0x800039b0#64 0x0a013703#32
    = ⟨0x800039b0#64, 0x0a013703#32, 0x03#8, 0x37#8, 0x01#8, 0x0a#8, .ld, 14, 2, 0, 0x0a0#12⟩ := by rfl
example : mkLine 0x800039b4#64 0x09012503#32
    = ⟨0x800039b4#64, 0x09012503#32, 0x03#8, 0x25#8, 0x01#8, 0x09#8, .lw, 10, 2, 0, 0x090#12⟩ := by rfl
example : mkLine 0x800039b8#64 0x0ed13823#32
    = ⟨0x800039b8#64, 0x0ed13823#32, 0x23#8, 0x38#8, 0xd1#8, 0x0e#8, .sd, 0, 2, 13, 0x0f0#12⟩ := by rfl
example : mkLine 0x800039bc#64 0x0eb13c23#32
    = ⟨0x800039bc#64, 0x0eb13c23#32, 0x23#8, 0x3c#8, 0xb1#8, 0x0e#8, .sd, 0, 2, 11, 0x0f8#12⟩ := by rfl
example : mkLine 0x800039c0#64 0x10e13023#32
    = ⟨0x800039c0#64, 0x10e13023#32, 0x23#8, 0x30#8, 0xe1#8, 0x10#8, .sd, 0, 2, 14, 0x100#12⟩ := by rfl

-- negPrologueBlk
example : mkLine 0x800035ec#64 0x00842703#32
    = ⟨0x800035ec#64, 0x00842703#32, 0x03#8, 0x27#8, 0x84#8, 0x00#8, .lw, 14, 8, 0, 0x008#12⟩ := by rfl
example : mkLine 0x800035f0#64 0x00c00793#32
    = ⟨0x800035f0#64, 0x00c00793#32, 0x93#8, 0x07#8, 0xc0#8, 0x00#8, .addi, 15, 0, 0, 0x00c#12⟩ := by rfl
example : mkLine 0x800035f4#64 0x09013683#32
    = ⟨0x800035f4#64, 0x09013683#32, 0x83#8, 0x36#8, 0x01#8, 0x09#8, .ld, 13, 2, 0, 0x090#12⟩ := by rfl

-- negTailBlkA
example : mkLine 0x800039c4#64 0x00200613#32
    = ⟨0x800039c4#64, 0x00200613#32, 0x13#8, 0x06#8, 0x20#8, 0x00#8, .addi, 12, 0, 0, 0x002#12⟩ := by rfl
example : mkLine 0x800039c8#64 0x00442403#32
    = ⟨0x800039c8#64, 0x00442403#32, 0x03#8, 0x24#8, 0x44#8, 0x00#8, .lw, 8, 8, 0, 0x004#12⟩ := by rfl

-- negTailBlkB
example : mkLine 0x800039d0#64 0x40b005b3#32
    = ⟨0x800039d0#64, 0x40b005b3#32, 0xb3#8, 0x05#8, 0xb0#8, 0x40#8, .sub, 11, 0, 11, 0#12⟩ := by rfl
example : mkLine 0x800039d4#64 0x00048513#32
    = ⟨0x800039d4#64, 0x00048513#32, 0x13#8, 0x85#8, 0x04#8, 0x00#8, .addi, 10, 9, 0, 0x000#12⟩ := by rfl

-- comparison-arm kinds (the `EvalCmpRows` slice): real words from the
-- shared comparison arm 0x80003628.. and its dispatch tail.
example : mkLine 0x80003638#64 0xfec6079b#32
    = ⟨0x80003638#64, 0xfec6079b#32, 0x9b#8, 0x07#8, 0xc6#8, 0xfe#8, .addiw, 15, 12, 0, 0xfec#12⟩ := by rfl
example : mkLine 0x8000364c#64 0x02079713#32
    = ⟨0x8000364c#64, 0x02079713#32, 0x13#8, 0x97#8, 0x07#8, 0x02#8, .slli, 14, 15, 0, 0x020#12⟩ := by rfl
example : mkLine 0x80003650#64 0x01d75793#32
    = ⟨0x80003650#64, 0x01d75793#32, 0x93#8, 0x57#8, 0xd7#8, 0x01#8, .srli, 15, 14, 0, 0x01d#12⟩ := by rfl
-- slliw (grow-path head 0x80002b90: `slliw a5,a5,1`, rd=rs1=15, shamt=1).  Checked
-- field-by-field: the whole-struct `⟨…⟩` `rfl` freezes the kernel here (the LOAD/
-- STORE `immS` `.append` branches in the opcode chain balloon the combined defeq
-- problem past its budget — the individual field projections all reduce fine, and
-- `decodeM` reduces to `some (.slliw, …)` standalone), so we assert the *decoded*
-- fields directly.  `astOfM` below then confirms the reflected AST equals the
-- DecodeTable output.
example : decodeM 0x0017979b#32 = some (.slliw, 15, 15, 0, 0x001#12) := by rfl
example : (mkLine 0x80002b90#64 0x0017979b#32).kind = MKind.slliw := by rfl
example : (mkLine 0x80002b90#64 0x0017979b#32).rd = 15 := by rfl
example : (mkLine 0x80002b90#64 0x0017979b#32).rs1 = 15 := by rfl
example : (mkLine 0x80002b90#64 0x0017979b#32).imm = 0x001#12 := by rfl
-- the reflected AST matches the DecodeTable lemma output (shamt5 read off the word):
example : astOfM ⟨0x80002b90#64, 0x0017979b#32, 0x9b#8, 0x79#8, 0x17#8, 0x00#8, .slliw, 15, 15, 0, 0x001#12⟩
    = LeanRV64DExecutable.instruction.SHIFTIWOP
        (0x01#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5,
         LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.sopw.SLLIW) := by rfl
example : mkLine 0x80003640#64 0x00016697#32
    = ⟨0x80003640#64, 0x00016697#32, 0x97#8, 0x66#8, 0x01#8, 0x00#8, .auipc, 13, 0, 0, 0#12⟩ := by rfl
example : mkLine 0x80003698#64 0x0138a733#32
    = ⟨0x80003698#64, 0x0138a733#32, 0x33#8, 0xa7#8, 0x38#8, 0x01#8, .slt, 14, 17, 19, 0#12⟩ := by rfl
example : mkLine 0x800036a0#64 0x40f705bb#32
    = ⟨0x800036a0#64, 0x40f705bb#32, 0xbb#8, 0x05#8, 0xf7#8, 0x40#8, .subw, 11, 14, 15, 0#12⟩ := by rfl
example : mkLine 0x80003af8#64 0x0015a593#32
    = ⟨0x80003af8#64, 0x0015a593#32, 0x93#8, 0xa5#8, 0x15#8, 0x00#8, .slti, 11, 11, 0, 0x001#12⟩ := by rfl

-- io-DAG residue kinds (real words from the proof binary):
-- xor a5,a1,a0 @ 0x80006bc8
example : mkLine 0x80006bc8#64 0x00a5c7b3#32
    = ⟨0x80006bc8#64, 0x00a5c7b3#32, 0xb3#8, 0xc7#8, 0xa5#8, 0x00#8, .xor, 15, 11, 10, 0#12⟩ := by rfl
-- sll a2,a2,t1 @ 0x80004948
example : mkLine 0x80004948#64 0x00661633#32
    = ⟨0x80004948#64, 0x00661633#32, 0x33#8, 0x16#8, 0x66#8, 0x00#8, .sll, 12, 12, 6, 0#12⟩ := by rfl
-- sllw a4,s5,s0 @ 0x80007138
example : mkLine 0x80007138#64 0x008a973b#32
    = ⟨0x80007138#64, 0x008a973b#32, 0x3b#8, 0x97#8, 0x8a#8, 0x00#8, .sllw, 14, 21, 8, 0#12⟩ := by rfl
-- srlw a0,s5,a5 @ 0x80010c70
example : mkLine 0x80010c70#64 0x00fad53b#32
    = ⟨0x80010c70#64, 0x00fad53b#32, 0x3b#8, 0xd5#8, 0xfa#8, 0x00#8, .srlw, 10, 21, 15, 0#12⟩ := by rfl
-- sraw a5,a4,a5 @ 0x80013a40
example : mkLine 0x80013a40#64 0x40f757bb#32
    = ⟨0x80013a40#64, 0x40f757bb#32, 0xbb#8, 0x57#8, 0xf7#8, 0x40#8, .sraw, 15, 14, 15, 0#12⟩ := by rfl

end Vsa.Sim
