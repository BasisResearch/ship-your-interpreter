import Vsa.Sim.DecodeTable.DecodeCommon
import Vsa.Sim.BlockTerm

/-!
# Compiler target instructions: encoding and generic decode facts

The WHILE compiler emits a small RV64I subset (`Ins`). Unlike the interpreter
proof, whose code is one fixed binary with a decode lemma per concrete word,
compiled code varies with the source program, so every decode fact here is
stated for symbolic register fields and immediates.

* `Ins.encode` is the standard RV64I encoding (registers taken mod 32).
* `decode_*_gen` are Sail `ext_decode` facts for any word whose opcode/funct
  slices have the stated values; `Ins.toM`/`Ins.toT` package an instruction at
  a PC as the block layer's `MInstr`/`TInstr`, and `decodeFactM_toM` /
  `decodeFactT_toT` discharge `DecodeFactM`/`DecodeFactT` for them. The block
  layer (`block_mem_run`, `term_step_bt`) then supplies the machine step.
-/

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

/-- Branch comparisons used by the compiler. -/
inductive BrOp where
  | eq | ne | lt | ge
  deriving DecidableEq, Repr

/-- The emitted instruction subset. Register fields are GPR indices; memory
accesses have offset `0`; `br`/`jal` offsets are byte offsets. -/
inductive Ins where
  | addi (rd rs1 : Nat) (imm : BitVec 12)
  | ori (rd rs1 : Nat) (imm : BitVec 12)
  | slli (rd rs1 : Nat) (sh : BitVec 6)
  | add (rd rs1 rs2 : Nat)
  | sub (rd rs1 rs2 : Nat)
  | ld (rd rs1 : Nat)
  | sd (rs2 rs1 : Nat)
  | br (op : BrOp) (rs1 rs2 : Nat) (off : BitVec 13)
  | jal (rd : Nat) (off : BitVec 21)
  | jalr (rs1 : Nat)
  deriving DecidableEq, Repr

/-! ## Encoding -/

def encI (imm rs1 f3 rd opc : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc)

def encR (f7 rs2 rs1 f3 rd opc : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (f7 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc)

def encS (imm rs2 rs1 f3 opc : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm % 4096 / 32 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12
    + imm % 32 * 2^7 + opc)

def encB (imm rs2 rs1 f3 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm / 4096 % 2 * 2^31 + imm / 32 % 64 * 2^25 + rs2 % 32 * 2^20
    + rs1 % 32 * 2^15 + f3 * 2^12 + imm / 2 % 16 * 2^8 + imm / 2048 % 2 * 2^7 + 0x63)

def encJ (imm rd : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm / 1048576 % 2 * 2^31 + imm / 2 % 1024 * 2^21 + imm / 2048 % 2 * 2^20
    + imm / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f)

def BrOp.f3 : BrOp → Nat
  | .eq => 0 | .ne => 1 | .lt => 4 | .ge => 5

def BrOp.bop : BrOp → bop
  | .eq => .BEQ | .ne => .BNE | .lt => .BLT | .ge => .BGE

/-- The standard RV64I encoding. -/
def Ins.encode : Ins → BitVec 32
  | .addi rd rs1 imm => encI imm.toNat rs1 0 rd 0x13
  | .ori rd rs1 imm => encI imm.toNat rs1 6 rd 0x13
  | .slli rd rs1 sh => encI sh.toNat rs1 1 rd 0x13
  | .add rd rs1 rs2 => encR 0 rs2 rs1 0 rd 0x33
  | .sub rd rs1 rs2 => encR 0x20 rs2 rs1 0 rd 0x33
  | .ld rd rs1 => encI 0 rs1 3 rd 0x03
  | .sd rs2 rs1 => encS 0 rs2 rs1 3 0x23
  | .br op rs1 rs2 off => encB off.toNat rs2 rs1 op.f3
  | .jal rd off => encJ off.toNat rd
  | .jalr rs1 => encI 0 rs1 0 0 0x67

/-! ## Slices of the encodings -/

theorem xl_toNat (w : BitVec 32) (hi lo : Nat) :
    (Sail.BitVec.extractLsb w hi lo).toNat = w.toNat / 2^lo % 2^(hi - lo + 1) := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem encI_toNat (imm rs1 f3 rd opc : Nat) (h2 : f3 < 8) (h4 : opc < 128) :
    (encI imm rs1 f3 rd opc).toNat =
      imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc := by
  simp only [encI, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem encR_toNat (f7 rs2 rs1 f3 rd opc : Nat) (h1 : f7 < 128) (h2 : f3 < 8) (h4 : opc < 128) :
    (encR f7 rs2 rs1 f3 rd opc).toNat =
      f7 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc := by
  simp only [encR, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem encS_toNat (imm rs2 rs1 f3 opc : Nat) (h2 : f3 < 8) (h4 : opc < 128) :
    (encS imm rs2 rs1 f3 opc).toNat = imm % 4096 / 32 * 2^25 + rs2 % 32 * 2^20
      + rs1 % 32 * 2^15 + f3 * 2^12 + imm % 32 * 2^7 + opc := by
  simp only [encS, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem encB_toNat (imm rs2 rs1 f3 : Nat) (h2 : f3 < 8) :
    (encB imm rs2 rs1 f3).toNat = imm / 4096 % 2 * 2^31 + imm / 32 % 64 * 2^25 + rs2 % 32 * 2^20
      + rs1 % 32 * 2^15 + f3 * 2^12 + imm / 2 % 16 * 2^8 + imm / 2048 % 2 * 2^7 + 0x63 := by
  simp only [encB, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem encJ_toNat (imm rd : Nat) :
    (encJ imm rd).toNat = imm / 1048576 % 2 * 2^31 + imm / 2 % 1024 * 2^21 + imm / 2048 % 2 * 2^20
      + imm / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f := by
  simp only [encJ, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt; omega

theorem BrOp.f3_lt (op : BrOp) : op.f3 < 8 := by cases op <;> decide

/-- Reduce a slice equation to arithmetic on the encoding. -/
theorem xl_eq {w : BitVec 32} {hi lo n : Nat} {x : BitVec n}
    (h : w.toNat / 2^lo % 2^(hi - lo + 1) = x.toNat) (hn : hi - lo + 1 = n) :
    Sail.BitVec.extractLsb w hi lo = hn ▸ x := by
  subst hn
  apply BitVec.eq_of_toNat_eq
  rw [xl_toNat]; exact h

theorem regidx_at7 (n : Nat) (w : BitVec 32)
    (h : w.toNat / 2^7 % 2^5 = n % 32) :
    regidx.Regidx (Sail.BitVec.extractLsb w 11 7) = gprIdx n := by
  have : Sail.BitVec.extractLsb w 11 7 = BitVec.ofNat 5 n := by
    apply BitVec.eq_of_toNat_eq
    rw [xl_toNat]
    simp only [BitVec.toNat_ofNat]
    exact h
  rw [this]

theorem regidx_at15 (n : Nat) (w : BitVec 32)
    (h : w.toNat / 2^15 % 2^5 = n % 32) :
    regidx.Regidx (Sail.BitVec.extractLsb w 19 15) = gprIdx n := by
  have : Sail.BitVec.extractLsb w 19 15 = BitVec.ofNat 5 n := by
    apply BitVec.eq_of_toNat_eq
    rw [xl_toNat]
    simp only [BitVec.toNat_ofNat]
    exact h
  rw [this]

theorem regidx_at20 (n : Nat) (w : BitVec 32)
    (h : w.toNat / 2^20 % 2^5 = n % 32) :
    regidx.Regidx (Sail.BitVec.extractLsb w 24 20) = gprIdx n := by
  have : Sail.BitVec.extractLsb w 24 20 = BitVec.ofNat 5 n := by
    apply BitVec.eq_of_toNat_eq
    rw [xl_toNat]
    simp only [BitVec.toNat_ofNat]
    exact h
  rw [this]

/-! ## Generic decode facts -/

theorem regm (x : BitVec 5) : encdec_reg_backwards_matches x = true := by
  simp [encdec_reg_backwards_matches, Functions.base_E_enabled, Functions.not]

theorem regb (x : BitVec 5) :
    encdec_reg_backwards x = (pure (regidx.Regidx x) : SailM regidx) := by
  simp only [encdec_reg_backwards, Functions.base_E_enabled, Functions.not, Bool.not_false,
    Bool.true_or, ite_true, Sail.BitVec.extractLsb, Functions.regidx_bit_width]
  have : BitVec.extractLsb (((5:Nat):Int) - 1).toNat 0 x = x := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb, BitVec.extractLsb']
  rw [this]

theorem pure_bind' {α β : Type} (a : α)
    (f : α → EStateM (Sail.Error Register) (SequentialState RegisterType trivialChoiceSource) β) :
    (EStateM.pure a).bind f = f a := rfl

/-- The three control-register pins every decode fact assumes. -/
abbrev DecPins (σ : SequentialState RegisterType trivialChoiceSource) : Prop :=
  σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) ∧
  σ.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege) ∧
  σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg)

set_option linter.unusedSimpArgs false

/-- Peel `ext_decode` for a symbolic word whose selecting slices are pinned by
the given equations: every earlier decoder arm fails on the opcode, and the
target arm's field extraction remains symbolic. -/
syntax "decode_gen" "[" term,* "]" : tactic
macro_rules
  | `(tactic| decode_gen [$hs,*]) => `(tactic| (
    simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
      pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
      currentlyEnabled, hartSupports, get_xLPE, $[$hs:term],*]
    simp (config := {decide := true}) only [regm, regb, Bool.and_false, Bool.false_and,
      Bool.and_true, Bool.true_and, ite_false, ite_true, Bool.false_eq_true, pure_bind',
      _get_Seccfg_MLPE, bool_bit_backwards, encdec_iop_backwards, encdec_bop_backwards,
      Functions.xlen, Bool.true_or, beq_self_eq_true, BitVec.reduceBEq,
      bool_bit_backwards_matches, width_enc_backwards_matches, valid_load_encdec,
      width_enc_backwards, encdec_bop_backwards_matches, pure, EStateM.pure, EStateM.bind]))

local notation "X" w:max hi:max lo:max => Sail.BitVec.extractLsb w hi lo

abbrev SSt := SequentialState RegisterType trivialChoiceSource

theorem decode_itype_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ) (op : iop)
    (hop : X w 6 0 = 0x13#7)
    (hf : (X w 14 12 = 0#3 ∧ op = .ADDI) ∨ (X w 14 12 = 6#3 ∧ op = .ORI)) :
    (ext_decode w).run σ = .ok (instruction.ITYPE (X w 31 20,
      regidx.Regidx (X w 19 15), regidx.Regidx (X w 11 7), op)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  rcases hf with ⟨hf3, rfl⟩ | ⟨hf3, rfl⟩
  · decode_gen [h2, h3, hop, hf3]
  · decode_gen [h2, h3, hop, hf3]

theorem decode_slli_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ)
    (hop : X w 6 0 = 0x13#7) (hf3 : X w 14 12 = 1#3) (hf6 : X w 31 26 = 0#6) :
    (ext_decode w).run σ = .ok (instruction.SHIFTIOP (X w 25 20,
      regidx.Regidx (X w 19 15), regidx.Regidx (X w 11 7), sop.SLLI)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  decode_gen [h2, h3, hop, hf3, hf6]

theorem decode_rtype_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ) (op : rop)
    (hop : X w 6 0 = 0x33#7) (hf3 : X w 14 12 = 0#3)
    (hf : (X w 31 25 = 0#7 ∧ op = .ADD) ∨ (X w 31 25 = 0x20#7 ∧ op = .SUB)) :
    (ext_decode w).run σ = .ok (instruction.RTYPE (regidx.Regidx (X w 24 20),
      regidx.Regidx (X w 19 15), regidx.Regidx (X w 11 7), op)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  rcases hf with ⟨hf7, rfl⟩ | ⟨hf7, rfl⟩
  · decode_gen [h2, h3, hop, hf3, hf7]
  · decode_gen [h2, h3, hop, hf3, hf7]

theorem decode_ld_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ)
    (hop : X w 6 0 = 0x03#7) (h14 : X w 14 14 = 0#1) (h12 : X w 13 12 = 3#2) :
    (ext_decode w).run σ = .ok (instruction.LOAD (X w 31 20,
      regidx.Regidx (X w 19 15), regidx.Regidx (X w 11 7), false, 8)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  decode_gen [h2, h3, hop, h14, h12]

theorem decode_sd_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ)
    (hop : X w 6 0 = 0x23#7) (h14 : X w 14 14 = 0#1) (h12 : X w 13 12 = 3#2) :
    (ext_decode w).run σ = .ok (instruction.STORE (X w 31 25 +++ X w 11 7,
      regidx.Regidx (X w 24 20), regidx.Regidx (X w 19 15), 8)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  decode_gen [h2, h3, hop, h14, h12]

theorem decode_btype_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ) (op : BrOp)
    (hop : X w 6 0 = 0x63#7) (hf3 : X w 14 12 = BitVec.ofNat 3 op.f3) :
    (ext_decode w).run σ = .ok (instruction.BTYPE
      (X w 31 31 +++ X w 7 7 +++ X w 30 25 +++ X w 11 8 +++ 0#1,
      regidx.Regidx (X w 24 20), regidx.Regidx (X w 19 15), op.bop)) σ := by
  obtain ⟨_, h2, h3⟩ := h
  cases op
  · decode_gen [h2, h3, hop, hf3, BrOp.f3, BrOp.bop]
  · decode_gen [h2, h3, hop, hf3, BrOp.f3, BrOp.bop]
  · decode_gen [h2, h3, hop, hf3, BrOp.f3, BrOp.bop]
  · decode_gen [h2, h3, hop, hf3, BrOp.f3, BrOp.bop]

theorem decode_jal_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ)
    (hop : X w 6 0 = 0x6f#7) :
    (ext_decode w).run σ = .ok (instruction.JAL
      (X w 31 31 +++ X w 19 12 +++ X w 20 20 +++ X w 30 21 +++ 0#1,
      regidx.Regidx (X w 11 7))) σ := by
  obtain ⟨_, h2, h3⟩ := h
  decode_gen [h2, h3, hop]

theorem decode_jalr_gen (w : BitVec 32) (σ : SSt) (h : DecPins σ)
    (hop : X w 6 0 = 0x67#7) (hf3 : X w 14 12 = 0#3) :
    (ext_decode w).run σ = .ok (instruction.JALR (X w 31 20,
      regidx.Regidx (X w 19 15), regidx.Regidx (X w 11 7))) σ := by
  obtain ⟨_, h2, h3⟩ := h
  decode_gen [h2, h3, hop, hf3]

/-! ## Block-layer packaging -/

theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2^n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- Little-endian bytes of a word. -/
def byte (w : BitVec 32) (k : Nat) : BitVec 8 := w.extractLsb' (8 * k) 8

theorem bytes_word (w : BitVec 32) :
    (((byte w 3).append (byte w 2)).append (byte w 1)).append (byte w 0) = w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.append_eq, toNat_append', byte, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- The branch/jump offset as the decoder reassembles it (bit 0 cleared). -/
def evenB (off : BitVec 13) : BitVec 13 := BitVec.ofNat 13 (off.toNat / 2 * 2)
def evenJ (off : BitVec 21) : BitVec 21 := BitVec.ofNat 21 (off.toNat / 2 * 2)

/-- Straight-line instructions, as the block layer's `MInstr` at `pc`. -/
def Ins.toM (pc : BitVec 64) (i : Ins) : MInstr :=
  let w := i.encode
  let mk (k : MKind) (rd rs1 rs2 : Nat) (imm : BitVec 12) : MInstr :=
    ⟨pc, w, byte w 0, byte w 1, byte w 2, byte w 3, k, rd, rs1, rs2, imm⟩
  match i with
  | .addi rd rs1 imm => mk .addi rd rs1 0 imm
  | .ori rd rs1 imm => mk .ori rd rs1 0 imm
  | .slli rd rs1 sh => mk .slli rd rs1 0 (sh.setWidth 12)
  | .add rd rs1 rs2 => mk .add rd rs1 rs2 0
  | .sub rd rs1 rs2 => mk .sub rd rs1 rs2 0
  | .ld rd rs1 => mk .ld rd rs1 0 0
  | .sd rs2 rs1 => mk .sd 0 rs1 rs2 0
  | _ => mk .addi 0 0 0 0

/-- Control transfers without a link register, as the block layer's `TInstr`
at `pc`; `taken` is the branch polarity. -/
def Ins.toT (pc : BitVec 64) (taken : Bool) (i : Ins) : TInstr :=
  let w := i.encode
  let mk (k : TKind) (rs1 rs2 : Nat) (i13 : BitVec 13) (i21 : BitVec 21) : TInstr :=
    ⟨pc, w, byte w 0, byte w 1, byte w 2, byte w 3, k, rs1, rs2, i13, i21, 0⟩
  match i with
  | .br op rs1 rs2 off => mk (.br op.bop taken) rs1 rs2 (evenB off) 0
  | .jal _ off => mk .j 0 0 0 (evenJ off)
  | .jalr rs1 => mk .jr rs1 0 0 0
  | _ => mk .j 0 0 0 0

/-- The instruction is straight-line (an `MInstr`). -/
def Ins.IsM : Ins → Prop
  | .addi .. | .ori .. | .slli .. | .add .. | .sub .. | .ld .. | .sd .. => True
  | _ => False


theorem decodeFactM_toM (pc : BitVec 64) (i : Ins) (hi : i.IsM) :
    DecodeFactM (i.toM pc) := by
  intro s h1 h2 h3
  have hp : DecPins s := ⟨h1, h2, h3⟩
  cases i with
  | addi rd rs1 imm =>
    have e := encI_toNat imm.toNat rs1 0 rd 0x13 (by omega) (by omega)
    have := imm.isLt
    rw [show (Ins.toM pc (.addi rd rs1 imm)).word = encI imm.toNat rs1 0 rd 0x13 from rfl]
    rw [decode_itype_gen _ s hp .ADDI (xl_eq (by rw [e]; simp; omega) rfl)
      (.inl ⟨xl_eq (by rw [e]; simp; omega) rfl, rfl⟩)]
    rw [xl_eq (x := imm) (by rw [e]; omega) rfl, regidx_at15 rs1 _ (by rw [e]; omega),
      regidx_at7 rd _ (by rw [e]; omega)]
    rfl
  | ori rd rs1 imm =>
    have e := encI_toNat imm.toNat rs1 6 rd 0x13 (by omega) (by omega)
    have := imm.isLt
    rw [show (Ins.toM pc (.ori rd rs1 imm)).word = encI imm.toNat rs1 6 rd 0x13 from rfl]
    rw [decode_itype_gen _ s hp .ORI (xl_eq (by rw [e]; simp; omega) rfl)
      (.inr ⟨xl_eq (by rw [e]; simp; omega) rfl, rfl⟩)]
    rw [xl_eq (x := imm) (by rw [e]; omega) rfl, regidx_at15 rs1 _ (by rw [e]; omega),
      regidx_at7 rd _ (by rw [e]; omega)]
    rfl
  | slli rd rs1 sh =>
    have e := encI_toNat sh.toNat rs1 1 rd 0x13 (by omega) (by omega)
    have := sh.isLt
    rw [show (Ins.toM pc (.slli rd rs1 sh)).word = encI sh.toNat rs1 1 rd 0x13 from rfl]
    rw [decode_slli_gen _ s hp (xl_eq (by rw [e]; simp; omega) rfl)
      (xl_eq (by rw [e]; simp; omega) rfl) (xl_eq (by rw [e]; simp; omega) rfl)]
    rw [regidx_at15 rs1 _ (by rw [e]; omega), regidx_at7 rd _ (by rw [e]; omega)]
    have hs : X (encI sh.toNat rs1 1 rd 0x13) 25 20 = shamtOf (Ins.toM pc (.slli rd rs1 sh)) := by
      apply BitVec.eq_of_toNat_eq
      rw [xl_toNat, e]
      simp only [shamtOf, Ins.toM, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
      omega
    rw [hs]; rfl
  | add rd rs1 rs2 =>
    have e := encR_toNat 0 rs2 rs1 0 rd 0x33 (by omega) (by omega) (by omega)
    rw [show (Ins.toM pc (.add rd rs1 rs2)).word = encR 0 rs2 rs1 0 rd 0x33 from rfl]
    rw [decode_rtype_gen _ s hp .ADD (xl_eq (by rw [e]; simp; omega) rfl)
      (xl_eq (by rw [e]; simp; omega) rfl) (.inl ⟨xl_eq (by rw [e]; simp; omega) rfl, rfl⟩)]
    rw [regidx_at20 rs2 _ (by rw [e]; omega), regidx_at15 rs1 _ (by rw [e]; omega),
      regidx_at7 rd _ (by rw [e]; omega)]
    rfl
  | sub rd rs1 rs2 =>
    have e := encR_toNat 0x20 rs2 rs1 0 rd 0x33 (by omega) (by omega) (by omega)
    rw [show (Ins.toM pc (.sub rd rs1 rs2)).word = encR 0x20 rs2 rs1 0 rd 0x33 from rfl]
    rw [decode_rtype_gen _ s hp .SUB (xl_eq (by rw [e]; simp; omega) rfl)
      (xl_eq (by rw [e]; simp; omega) rfl) (.inr ⟨xl_eq (by rw [e]; simp; omega) rfl, rfl⟩)]
    rw [regidx_at20 rs2 _ (by rw [e]; omega), regidx_at15 rs1 _ (by rw [e]; omega),
      regidx_at7 rd _ (by rw [e]; omega)]
    rfl
  | ld rd rs1 =>
    have e := encI_toNat 0 rs1 3 rd 0x03 (by omega) (by omega)
    rw [show (Ins.toM pc (.ld rd rs1)).word = encI 0 rs1 3 rd 0x03 from rfl]
    rw [decode_ld_gen _ s hp (xl_eq (by rw [e]; simp; omega) rfl)
      (xl_eq (by rw [e]; simp; omega) rfl) (xl_eq (by rw [e]; simp; omega) rfl)]
    rw [xl_eq (x := (0#12)) (by rw [e]; simp; omega) rfl, regidx_at15 rs1 _ (by rw [e]; omega),
      regidx_at7 rd _ (by rw [e]; omega)]
    rfl
  | sd rs2 rs1 =>
    have e := encS_toNat 0 rs2 rs1 3 0x23 (by omega) (by omega)
    rw [show (Ins.toM pc (.sd rs2 rs1)).word = encS 0 rs2 rs1 3 0x23 from rfl]
    rw [decode_sd_gen _ s hp (xl_eq (by rw [e]; simp; omega) rfl)
      (xl_eq (by rw [e]; simp; omega) rfl) (xl_eq (by rw [e]; simp; omega) rfl)]
    rw [xl_eq (x := (0#7)) (by rw [e]; simp; omega) rfl,
      xl_eq (x := (0#5)) (by rw [e]; simp; omega) rfl,
      regidx_at20 rs2 _ (by rw [e]; omega), regidx_at15 rs1 _ (by rw [e]; omega)]
    rfl
  | br => exact hi.elim
  | jal => exact hi.elim
  | jalr => exact hi.elim

/-- A field of a word presented as `(high * 2^m + x) * 2^k + low`. -/
theorem slice_of (q x r k m : Nat) (hr : r < 2^k) (hx : x < 2^m) :
    ((q * 2^m + x) * 2^k + r) / 2^k % 2^m = x := by
  rw [Nat.add_comm _ r, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hr,
    Nat.zero_add, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem encI_fields (imm rs1 f3 rd opc : Nat) (hf : f3 < 8) (ho : opc < 128) :
    let w := (encI imm rs1 f3 rd opc).toNat
    w / 2^0 % 2^7 = opc ∧ w / 2^7 % 2^5 = rd % 32 ∧ w / 2^12 % 2^3 = f3 ∧
      w / 2^15 % 2^5 = rs1 % 32 ∧ w / 2^20 % 2^12 = imm % 4096 := by
  intro w
  have e : w = (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) := encI_toNat imm rs1 f3 rd opc hf ho
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e, show (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) = ((imm % 4096 * 2^13 + rs1 % 32 * 2^8 + f3 * 2^5 + rd % 32) * 2^7 + opc)
        * 2^0 + 0 by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) = ((imm % 4096 * 2^8 + rs1 % 32 * 2^3 + f3) * 2^5 + rd % 32) * 2^7 + opc
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) = ((imm % 4096 * 2^5 + rs1 % 32) * 2^3 + f3) * 2^12 + (rd % 32 * 2^7 + opc)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) = ((imm % 4096) * 2^5 + rs1 % 32) * 2^15 + (f3 * 2^12 + rd % 32 * 2^7 + opc)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (imm % 4096 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + rd % 32 * 2^7 + opc) = (0 * 2^12 + imm % 4096) * 2^20 + (rs1 % 32 * 2^15 + f3 * 2^12
        + rd % 32 * 2^7 + opc) by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)

theorem encB_fields (off rs2 rs1 f3 : Nat) (hf : f3 < 8) :
    let w := (encB off rs2 rs1 f3).toNat
    w / 2^0 % 2^7 = 0x63 ∧ w / 2^12 % 2^3 = f3 ∧ w / 2^15 % 2^5 = rs1 % 32 ∧
      w / 2^20 % 2^5 = rs2 % 32 := by
  intro w
  have e : w = (off / 4096 % 2 * 2^31 + off / 32 % 64 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63) := encB_toNat off rs2 rs1 f3 hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, show (off / 4096 % 2 * 2^31 + off / 32 % 64 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63) = ((off / 4096 % 2 * 2^24 + off / 32 % 64 * 2^18 + rs2 % 32 * 2^13
        + rs1 % 32 * 2^8 + f3 * 2^5 + off / 2 % 16 * 2 + off / 2048 % 2) * 2^7 + 0x63) * 2^0 + 0
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (off / 4096 % 2 * 2^31 + off / 32 % 64 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63) = ((off / 4096 % 2 * 2^16 + off / 32 % 64 * 2^10 + rs2 % 32 * 2^5
        + rs1 % 32) * 2^3 + f3) * 2^12 + (off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (off / 4096 % 2 * 2^31 + off / 32 % 64 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63) = ((off / 4096 % 2 * 2^11 + off / 32 % 64 * 2^5 + rs2 % 32) * 2^5
        + rs1 % 32) * 2^15 + (f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (off / 4096 % 2 * 2^31 + off / 32 % 64 * 2^25 + rs2 % 32 * 2^20 + rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63) = ((off / 4096 % 2 * 2^6 + off / 32 % 64) * 2^5 + rs2 % 32) * 2^20
        + (rs1 % 32 * 2^15 + f3 * 2^12 + off / 2 % 16 * 2^8 + off / 2048 % 2 * 2^7 + 0x63)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)

theorem encJ_fields (off rd : Nat) :
    let w := (encJ off rd).toNat
    w / 2^0 % 2^7 = 0x6f ∧ w / 2^7 % 2^5 = rd % 32 := by
  intro w
  have e : w = (off / 1048576 % 2 * 2^31 + off / 2 % 1024 * 2^21 + off / 2048 % 2 * 2^20 + off / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f) := encJ_toNat off rd
  refine ⟨?_, ?_⟩
  · rw [e, show (off / 1048576 % 2 * 2^31 + off / 2 % 1024 * 2^21 + off / 2048 % 2 * 2^20 + off / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f) = ((off / 1048576 % 2 * 2^24 + off / 2 % 1024 * 2^14 + off / 2048 % 2 * 2^13
        + off / 4096 % 256 * 2^5 + rd % 32) * 2^7 + 0x6f) * 2^0 + 0 by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  · rw [e, show (off / 1048576 % 2 * 2^31 + off / 2 % 1024 * 2^21 + off / 2048 % 2 * 2^20 + off / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f) = ((off / 1048576 % 2 * 2^19 + off / 2 % 1024 * 2^9 + off / 2048 % 2 * 2^8
        + off / 4096 % 256) * 2^5 + rd % 32) * 2^7 + 0x6f by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)

theorem xl_evenB (off : BitVec 13) (rs1 rs2 f3 : Nat) (hf : f3 < 8) :
    (X (encB off.toNat rs2 rs1 f3) 31 31 +++ X (encB off.toNat rs2 rs1 f3) 7 7
      +++ X (encB off.toNat rs2 rs1 f3) 30 25 +++ X (encB off.toNat rs2 rs1 f3) 11 8 +++ 0#1)
      = evenB off := by
  apply BitVec.eq_of_toNat_eq
  have e := encB_toNat off.toNat rs2 rs1 f3 hf
  have := off.isLt
  have a1 : (X (encB off.toNat rs2 rs1 f3) 31 31).toNat = off.toNat / 4096 % 2 := by
    rw [xl_toNat, e, show 31 - 31 + 1 = 1 by rfl,
      show off.toNat / 4096 % 2 * 2^31 + off.toNat / 32 % 64 * 2^25 + rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63
        = (0 * 2^1 + off.toNat / 4096 % 2) * 2^31 + (off.toNat / 32 % 64 * 2^25 + rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a2 : (X (encB off.toNat rs2 rs1 f3) 7 7).toNat = off.toNat / 2048 % 2 := by
    rw [xl_toNat, e, show 7 - 7 + 1 = 1 by rfl,
      show off.toNat / 4096 % 2 * 2^31 + off.toNat / 32 % 64 * 2^25 + rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63
        = ((off.toNat / 4096 % 2 * 2^23 + off.toNat / 32 % 64 * 2^17 + rs2 % 32 * 2^12
        + rs1 % 32 * 2^7 + f3 * 2^4 + off.toNat / 2 % 16) * 2^1 + off.toNat / 2048 % 2) * 2^7
        + 0x63 by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a3 : (X (encB off.toNat rs2 rs1 f3) 30 25).toNat = off.toNat / 32 % 64 := by
    rw [xl_toNat, e, show 30 - 25 + 1 = 6 by rfl,
      show off.toNat / 4096 % 2 * 2^31 + off.toNat / 32 % 64 * 2^25 + rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63
        = (off.toNat / 4096 % 2 * 2^6 + off.toNat / 32 % 64) * 2^25 + (rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a4 : (X (encB off.toNat rs2 rs1 f3) 11 8).toNat = off.toNat / 2 % 16 := by
    rw [xl_toNat, e, show 11 - 8 + 1 = 4 by rfl,
      show off.toNat / 4096 % 2 * 2^31 + off.toNat / 32 % 64 * 2^25 + rs2 % 32 * 2^20
        + rs1 % 32 * 2^15 + f3 * 2^12 + off.toNat / 2 % 16 * 2^8 + off.toNat / 2048 % 2 * 2^7 + 0x63
        = ((off.toNat / 4096 % 2 * 2^19 + off.toNat / 32 % 64 * 2^13 + rs2 % 32 * 2^8
        + rs1 % 32 * 2^3 + f3) * 2^4 + off.toNat / 2 % 16) * 2^8
        + (off.toNat / 2048 % 2 * 2^7 + 0x63) by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  simp only [toNat_append', a1, a2, a3, a4, evenB, BitVec.toNat_ofNat]
  have m1 := Nat.mod_mul (x := off.toNat) (a := 4096) (b := 2)
  have m2 := Nat.mod_mul (x := off.toNat) (a := 2048) (b := 2)
  have m3 := Nat.mod_mul (x := off.toNat) (a := 32) (b := 64)
  have m4 := Nat.mod_mul (x := off.toNat) (a := 2) (b := 16)
  simp only [Nat.reduceMul] at m1 m2 m3 m4
  simp
  omega

theorem xl_evenJ (off : BitVec 21) (rd : Nat) :
    (X (encJ off.toNat rd) 31 31 +++ X (encJ off.toNat rd) 19 12
      +++ X (encJ off.toNat rd) 20 20 +++ X (encJ off.toNat rd) 30 21 +++ 0#1) = evenJ off := by
  apply BitVec.eq_of_toNat_eq
  have e := encJ_toNat off.toNat rd
  have := off.isLt
  have a1 : (X (encJ off.toNat rd) 31 31).toNat = off.toNat / 1048576 % 2 := by
    rw [xl_toNat, e, show 31 - 31 + 1 = 1 by rfl,
      show off.toNat / 1048576 % 2 * 2^31 + off.toNat / 2 % 1024 * 2^21
        + off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f
        = (0 * 2^1 + off.toNat / 1048576 % 2) * 2^31 + (off.toNat / 2 % 1024 * 2^21
        + off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a2 : (X (encJ off.toNat rd) 19 12).toNat = off.toNat / 4096 % 256 := by
    rw [xl_toNat, e, show 19 - 12 + 1 = 8 by rfl,
      show off.toNat / 1048576 % 2 * 2^31 + off.toNat / 2 % 1024 * 2^21
        + off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f
        = ((off.toNat / 1048576 % 2 * 2^11 + off.toNat / 2 % 1024 * 2
        + off.toNat / 2048 % 2) * 2^8 + off.toNat / 4096 % 256) * 2^12 + (rd % 32 * 2^7 + 0x6f)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a3 : (X (encJ off.toNat rd) 20 20).toNat = off.toNat / 2048 % 2 := by
    rw [xl_toNat, e, show 20 - 20 + 1 = 1 by rfl,
      show off.toNat / 1048576 % 2 * 2^31 + off.toNat / 2 % 1024 * 2^21
        + off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f
        = ((off.toNat / 1048576 % 2 * 2^10 + off.toNat / 2 % 1024) * 2^1
        + off.toNat / 2048 % 2) * 2^20 + (off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  have a4 : (X (encJ off.toNat rd) 30 21).toNat = off.toNat / 2 % 1024 := by
    rw [xl_toNat, e, show 30 - 21 + 1 = 10 by rfl,
      show off.toNat / 1048576 % 2 * 2^31 + off.toNat / 2 % 1024 * 2^21
        + off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f
        = (off.toNat / 1048576 % 2 * 2^10 + off.toNat / 2 % 1024) * 2^21
        + (off.toNat / 2048 % 2 * 2^20 + off.toNat / 4096 % 256 * 2^12 + rd % 32 * 2^7 + 0x6f)
        by omega]
    exact slice_of _ _ _ _ _ (by omega) (by omega)
  simp only [toNat_append', a1, a2, a3, a4, evenJ, BitVec.toNat_ofNat]
  have m1 := Nat.mod_mul (x := off.toNat) (a := 1048576) (b := 2)
  have m2 := Nat.mod_mul (x := off.toNat) (a := 4096) (b := 256)
  have m3 := Nat.mod_mul (x := off.toNat) (a := 2048) (b := 2)
  have m4 := Nat.mod_mul (x := off.toNat) (a := 2) (b := 1024)
  simp only [Nat.reduceMul] at m1 m2 m3 m4
  simp
  omega

/-- The instruction transfers control without writing a link register. -/
def Ins.IsT : Ins → Prop
  | .br .. | .jalr .. => True
  | .jal rd _ => rd % 32 = 0
  | _ => False

theorem decodeFactT_toT (pc : BitVec 64) (taken : Bool) (i : Ins) (hi : i.IsT) :
    DecodeFactT (i.toT pc taken) := by
  intro s h1 h2 h3
  have hp : DecPins s := ⟨h1, h2, h3⟩
  cases i with
  | br op rs1 rs2 off =>
    obtain ⟨f1, f2, f3, f4⟩ := encB_fields off.toNat rs2 rs1 op.f3 op.f3_lt
    have := op.f3_lt
    rw [show (Ins.toT pc taken (.br op rs1 rs2 off)).word = encB off.toNat rs2 rs1 op.f3 from rfl]
    rw [decode_btype_gen _ s hp op (xl_eq (by rw [f1]; rfl) rfl)
      (xl_eq (by rw [f2]; simp; omega) rfl)]
    rw [xl_evenB off rs1 rs2 op.f3 op.f3_lt, regidx_at20 rs2 _ f4, regidx_at15 rs1 _ f3]
    rfl
  | jal rd off =>
    obtain ⟨f1, f2⟩ := encJ_fields off.toNat rd
    have hrd : rd % 32 = 0 := hi
    rw [show (Ins.toT pc taken (.jal rd off)).word = encJ off.toNat rd from rfl]
    rw [decode_jal_gen _ s hp (xl_eq (by rw [f1]; rfl) rfl), xl_evenJ off rd,
      xl_eq (x := (0#5)) (by rw [f2, hrd]; rfl) rfl]
    rfl
  | jalr rs1 =>
    obtain ⟨f1, f2, f3, f4, f5⟩ := encI_fields 0 rs1 0 0 0x67 (by omega) (by omega)
    rw [show (Ins.toT pc taken (.jalr rs1)).word = encI 0 rs1 0 0 0x67 from rfl]
    rw [decode_jalr_gen _ s hp (xl_eq (by rw [f1]; rfl) rfl) (xl_eq (by rw [f3]; rfl) rfl)]
    rw [xl_eq (x := (0#12)) (by rw [f5]; rfl) rfl, regidx_at15 rs1 _ f4,
      xl_eq (x := (0#5)) (by rw [f2]; rfl) rfl]
    rfl
  | _ => exact hi.elim

/-- Decode of a linking `jal rd, off`. -/
theorem decode_jal_link (s : SSt) (hp : DecPins s) (rd : Nat) (off : BitVec 21) :
    (ext_decode (Ins.jal rd off).encode).run s
      = .ok (instruction.JAL (evenJ off, gprIdx rd)) s := by
  obtain ⟨f1, f2⟩ := encJ_fields off.toNat rd
  rw [show (Ins.jal rd off).encode = encJ off.toNat rd from rfl,
    decode_jal_gen _ s hp (xl_eq (by rw [f1]; rfl) rfl), xl_evenJ off rd,
    regidx_at7 rd _ f2]

/-- Every emitted word has the non-compressed low bits `0b11`. -/
theorem encode_rvc (i : Ins) :
    Sail.BitVec.extractLsb i.encode 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [xl_toNat]
  cases i with
  | addi rd rs1 imm => rw [Ins.encode, encI_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega
  | ori rd rs1 imm => rw [Ins.encode, encI_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega
  | slli rd rs1 sh => rw [Ins.encode, encI_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega
  | add => rw [Ins.encode, encR_toNat _ _ _ _ _ _ (by omega) (by omega) (by omega)]; simp; omega
  | sub => rw [Ins.encode, encR_toNat _ _ _ _ _ _ (by omega) (by omega) (by omega)]; simp; omega
  | ld => rw [Ins.encode, encI_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega
  | sd => rw [Ins.encode, encS_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega
  | br op rs1 rs2 off =>
    have := (encB_fields off.toNat rs2 rs1 op.f3 op.f3_lt).1
    rw [Ins.encode]; simp only [Nat.pow_zero, Nat.div_one] at this; simp; omega
  | jal rd off =>
    have := (encJ_fields off.toNat rd).1
    rw [Ins.encode]; simp only [Nat.pow_zero, Nat.div_one] at this; simp; omega
  | jalr => rw [Ins.encode, encI_toNat _ _ _ _ _ (by omega) (by omega)]; simp; omega

end Vsa.Compiler
