import Vsa.Elf
import Vsa.Sim.StateNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The general-purpose register file (law L-reg)

`gprReg n` is the architectural register of number `n ∈ [1,31]`; `rX_bits`/`wX_bits` at
`gprIdx n` read and write it (`rX_bits_gpr`, `wX_bits_gpr`, proved once by `gpr_cases`). The
per-register lemmas below are instances. -/

abbrev gprIdx (n : Nat) : regidx := regidx.Regidx (BitVec.ofNat 5 n)

def gprReg : Nat → Register
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | 6 => Register.x6
  | 7 => Register.x7
  | 8 => Register.x8
  | 9 => Register.x9
  | 10 => Register.x10
  | 11 => Register.x11
  | 12 => Register.x12
  | 13 => Register.x13
  | 14 => Register.x14
  | 15 => Register.x15
  | 16 => Register.x16
  | 17 => Register.x17
  | 18 => Register.x18
  | 19 => Register.x19
  | 20 => Register.x20
  | 21 => Register.x21
  | 22 => Register.x22
  | 23 => Register.x23
  | 24 => Register.x24
  | 25 => Register.x25
  | 26 => Register.x26
  | 27 => Register.x27
  | 28 => Register.x28
  | 29 => Register.x29
  | 30 => Register.x30
  | 31 => Register.x31
  | 0 => Register.x1
  | _+32 => Register.x1

def gprGet (σ : SequentialState RegisterType trivialChoiceSource) : Nat → Option (BitVec 64)
  | 1 => σ.regs.get? Register.x1
  | 2 => σ.regs.get? Register.x2
  | 3 => σ.regs.get? Register.x3
  | 4 => σ.regs.get? Register.x4
  | 5 => σ.regs.get? Register.x5
  | 6 => σ.regs.get? Register.x6
  | 7 => σ.regs.get? Register.x7
  | 8 => σ.regs.get? Register.x8
  | 9 => σ.regs.get? Register.x9
  | 10 => σ.regs.get? Register.x10
  | 11 => σ.regs.get? Register.x11
  | 12 => σ.regs.get? Register.x12
  | 13 => σ.regs.get? Register.x13
  | 14 => σ.regs.get? Register.x14
  | 15 => σ.regs.get? Register.x15
  | 16 => σ.regs.get? Register.x16
  | 17 => σ.regs.get? Register.x17
  | 18 => σ.regs.get? Register.x18
  | 19 => σ.regs.get? Register.x19
  | 20 => σ.regs.get? Register.x20
  | 21 => σ.regs.get? Register.x21
  | 22 => σ.regs.get? Register.x22
  | 23 => σ.regs.get? Register.x23
  | 24 => σ.regs.get? Register.x24
  | 25 => σ.regs.get? Register.x25
  | 26 => σ.regs.get? Register.x26
  | 27 => σ.regs.get? Register.x27
  | 28 => σ.regs.get? Register.x28
  | 29 => σ.regs.get? Register.x29
  | 30 => σ.regs.get? Register.x30
  | 31 => σ.regs.get? Register.x31
  | 0 => none
  | _+32 => none

def gprRT : (n : Nat) → BitVec 64 → RegisterType (gprReg n)
  | 1, v => v
  | 2, v => v
  | 3, v => v
  | 4, v => v
  | 5, v => v
  | 6, v => v
  | 7, v => v
  | 8, v => v
  | 9, v => v
  | 10, v => v
  | 11, v => v
  | 12, v => v
  | 13, v => v
  | 14, v => v
  | 15, v => v
  | 16, v => v
  | 17, v => v
  | 18, v => v
  | 19, v => v
  | 20, v => v
  | 21, v => v
  | 22, v => v
  | 23, v => v
  | 24, v => v
  | 25, v => v
  | 26, v => v
  | 27, v => v
  | 28, v => v
  | 29, v => v
  | 30, v => v
  | 31, v => v
  | 0, v => v
  | _+32, v => v

/-- A property of the 31 general-purpose register numbers, checked once per register:
splits `n` into `1, …, 31`, discharges `0` and `n ≥ 32` from the range hypotheses by `omega`,
and runs `tac` on each register. -/
syntax "gpr_cases " ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| gpr_cases $n:ident => $t:tacticSeq) =>
    `(tactic| ((iterate 32 (rcases $n:ident with _ | $n:ident; rotate_left)); all_goals
      ((try simp only [Nat.zero_add, Nat.reduceAdd] at *) <;> first | omega | ($t))))

/-- **L-reg (read).** -/
theorem rX_bits_gpr (σ : SequentialState RegisterType trivialChoiceSource) (n : Nat)
    (h1 : 1 ≤ n) (h31 : n ≤ 31) (v : BitVec 64) (h : gprGet σ n = some v) :
    (rX_bits (gprIdx n)).run σ = .ok v σ := by
  gpr_cases n =>
    simp only [gprGet] at h
    simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
      EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
      regval_from_reg, Sail.BitVec.toNatInt,
      Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-- **L-reg (write).** -/
theorem wX_bits_gpr (σ : SequentialState RegisterType trivialChoiceSource) (d : BitVec 64)
    (n : Nat) (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    (wX_bits (gprIdx n) d).run σ
      = .ok () {σ with regs := σ.regs.insert (gprReg n) (gprRT n d)} := by
  gpr_cases n =>
    simp only [wX_bits, wX, PreSail.writeReg, bind, EStateM.bind, pure, EStateM.pure,
      EStateM.run, regval_into_reg, Sail.BitVec.toNatInt, gprReg, gprRT,
      Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat,
      bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, if_true,
      xreg_write_callback, xreg_full_write_callback, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet,
      reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards_matches,
      Functions.not, Bool.not_false, Bool.false_eq_true, reduceIte]

theorem wX_bits_zero (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x00#5) d).run σ = .ok () σ := by
  simp only [wX_bits, wX, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat,
    bne_self_eq_false, Bool.false_eq_true, if_false]

theorem rX_bits_x1 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x1 = some v) :
    (rX_bits (regidx.Regidx 0x01#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 1 (by decide) (by decide) v h

theorem wX_bits_x1 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x01#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x1 d} :=
  wX_bits_gpr σ d 1 (by decide) (by decide)

theorem rX_bits_x2 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x2 = some v) :
    (rX_bits (regidx.Regidx 0x02#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 2 (by decide) (by decide) v h

theorem wX_bits_x2 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x02#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x2 d} :=
  wX_bits_gpr σ d 2 (by decide) (by decide)

theorem rX_bits_x3 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x3 = some v) :
    (rX_bits (regidx.Regidx 0x03#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 3 (by decide) (by decide) v h

theorem wX_bits_x3 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x03#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x3 d} :=
  wX_bits_gpr σ d 3 (by decide) (by decide)

theorem rX_bits_x4 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x4 = some v) :
    (rX_bits (regidx.Regidx 0x04#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 4 (by decide) (by decide) v h

theorem wX_bits_x4 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x04#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x4 d} :=
  wX_bits_gpr σ d 4 (by decide) (by decide)

theorem rX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x5 = some v) :
    (rX_bits (regidx.Regidx 0x05#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 5 (by decide) (by decide) v h

theorem wX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x05#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x5 d} :=
  wX_bits_gpr σ d 5 (by decide) (by decide)

theorem rX_bits_x6 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x6 = some v) :
    (rX_bits (regidx.Regidx 0x06#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 6 (by decide) (by decide) v h

theorem wX_bits_x6 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x06#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x6 d} :=
  wX_bits_gpr σ d 6 (by decide) (by decide)

theorem rX_bits_x7 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x7 = some v) :
    (rX_bits (regidx.Regidx 0x07#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 7 (by decide) (by decide) v h

theorem wX_bits_x7 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x07#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x7 d} :=
  wX_bits_gpr σ d 7 (by decide) (by decide)

theorem rX_bits_x8 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x8 = some v) :
    (rX_bits (regidx.Regidx 0x08#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 8 (by decide) (by decide) v h

theorem wX_bits_x8 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x08#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x8 d} :=
  wX_bits_gpr σ d 8 (by decide) (by decide)

theorem rX_bits_x9 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x9 = some v) :
    (rX_bits (regidx.Regidx 0x09#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 9 (by decide) (by decide) v h

theorem wX_bits_x9 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x09#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x9 d} :=
  wX_bits_gpr σ d 9 (by decide) (by decide)

theorem rX_bits_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x10 = some v) :
    (rX_bits (regidx.Regidx 0x0a#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 10 (by decide) (by decide) v h

theorem wX_bits_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0a#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x10 d} :=
  wX_bits_gpr σ d 10 (by decide) (by decide)

theorem rX_bits_x11 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x11 = some v) :
    (rX_bits (regidx.Regidx 0x0b#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 11 (by decide) (by decide) v h

theorem wX_bits_x11 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0b#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x11 d} :=
  wX_bits_gpr σ d 11 (by decide) (by decide)

theorem rX_bits_x12 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x12 = some v) :
    (rX_bits (regidx.Regidx 0x0c#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 12 (by decide) (by decide) v h

theorem wX_bits_x12 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0c#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x12 d} :=
  wX_bits_gpr σ d 12 (by decide) (by decide)

theorem rX_bits_x13 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x13 = some v) :
    (rX_bits (regidx.Regidx 0x0d#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 13 (by decide) (by decide) v h

theorem wX_bits_x13 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0d#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x13 d} :=
  wX_bits_gpr σ d 13 (by decide) (by decide)

theorem rX_bits_x14 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x14 = some v) :
    (rX_bits (regidx.Regidx 0x0e#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 14 (by decide) (by decide) v h

theorem wX_bits_x14 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0e#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x14 d} :=
  wX_bits_gpr σ d 14 (by decide) (by decide)

theorem rX_bits_x15 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x15 = some v) :
    (rX_bits (regidx.Regidx 0x0f#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 15 (by decide) (by decide) v h

theorem wX_bits_x15 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0f#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x15 d} :=
  wX_bits_gpr σ d 15 (by decide) (by decide)

theorem rX_bits_x16 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x16 = some v) :
    (rX_bits (regidx.Regidx 0x10#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 16 (by decide) (by decide) v h

theorem wX_bits_x16 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x10#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x16 d} :=
  wX_bits_gpr σ d 16 (by decide) (by decide)

theorem rX_bits_x17 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x17 = some v) :
    (rX_bits (regidx.Regidx 0x11#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 17 (by decide) (by decide) v h

theorem wX_bits_x17 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x11#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x17 d} :=
  wX_bits_gpr σ d 17 (by decide) (by decide)

theorem rX_bits_x18 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x18 = some v) :
    (rX_bits (regidx.Regidx 0x12#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 18 (by decide) (by decide) v h

theorem wX_bits_x18 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x12#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x18 d} :=
  wX_bits_gpr σ d 18 (by decide) (by decide)

theorem rX_bits_x19 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x19 = some v) :
    (rX_bits (regidx.Regidx 0x13#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 19 (by decide) (by decide) v h

theorem wX_bits_x19 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x13#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x19 d} :=
  wX_bits_gpr σ d 19 (by decide) (by decide)

theorem rX_bits_x20 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x20 = some v) :
    (rX_bits (regidx.Regidx 0x14#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 20 (by decide) (by decide) v h

theorem wX_bits_x20 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x14#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x20 d} :=
  wX_bits_gpr σ d 20 (by decide) (by decide)

theorem rX_bits_x21 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x21 = some v) :
    (rX_bits (regidx.Regidx 0x15#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 21 (by decide) (by decide) v h

theorem wX_bits_x21 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x15#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x21 d} :=
  wX_bits_gpr σ d 21 (by decide) (by decide)

theorem rX_bits_x22 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x22 = some v) :
    (rX_bits (regidx.Regidx 0x16#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 22 (by decide) (by decide) v h

theorem wX_bits_x22 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x16#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x22 d} :=
  wX_bits_gpr σ d 22 (by decide) (by decide)

theorem rX_bits_x23 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x23 = some v) :
    (rX_bits (regidx.Regidx 0x17#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 23 (by decide) (by decide) v h

theorem wX_bits_x23 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x17#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x23 d} :=
  wX_bits_gpr σ d 23 (by decide) (by decide)

theorem rX_bits_x24 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x24 = some v) :
    (rX_bits (regidx.Regidx 0x18#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 24 (by decide) (by decide) v h

theorem wX_bits_x24 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x18#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x24 d} :=
  wX_bits_gpr σ d 24 (by decide) (by decide)

theorem rX_bits_x25 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x25 = some v) :
    (rX_bits (regidx.Regidx 0x19#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 25 (by decide) (by decide) v h

theorem wX_bits_x25 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x19#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x25 d} :=
  wX_bits_gpr σ d 25 (by decide) (by decide)

theorem rX_bits_x26 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x26 = some v) :
    (rX_bits (regidx.Regidx 0x1a#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 26 (by decide) (by decide) v h

theorem wX_bits_x26 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1a#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x26 d} :=
  wX_bits_gpr σ d 26 (by decide) (by decide)

theorem rX_bits_x27 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x27 = some v) :
    (rX_bits (regidx.Regidx 0x1b#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 27 (by decide) (by decide) v h

theorem wX_bits_x27 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1b#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x27 d} :=
  wX_bits_gpr σ d 27 (by decide) (by decide)

theorem rX_bits_x28 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x28 = some v) :
    (rX_bits (regidx.Regidx 0x1c#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 28 (by decide) (by decide) v h

theorem wX_bits_x28 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1c#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x28 d} :=
  wX_bits_gpr σ d 28 (by decide) (by decide)

theorem rX_bits_x29 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x29 = some v) :
    (rX_bits (regidx.Regidx 0x1d#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 29 (by decide) (by decide) v h

theorem wX_bits_x29 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1d#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x29 d} :=
  wX_bits_gpr σ d 29 (by decide) (by decide)

theorem rX_bits_x30 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x30 = some v) :
    (rX_bits (regidx.Regidx 0x1e#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 30 (by decide) (by decide) v h

theorem wX_bits_x30 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1e#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x30 d} :=
  wX_bits_gpr σ d 30 (by decide) (by decide)

theorem rX_bits_x31 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x31 = some v) :
    (rX_bits (regidx.Regidx 0x1f#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 31 (by decide) (by decide) v h

theorem wX_bits_x31 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x1f#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x31 d} :=
  wX_bits_gpr σ d 31 (by decide) (by decide)

end Vsa.Sim
