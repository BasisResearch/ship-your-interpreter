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

/-- The register numbers `1, …, 31`, decided once. -/
theorem gpr_range_fin : ∀ n : Fin 32, 1 ≤ n.val →
    n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨ n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 ∨ n.val = 10 ∨ n.val = 11 ∨ n.val = 12 ∨ n.val = 13 ∨ n.val = 14 ∨ n.val = 15 ∨ n.val = 16 ∨ n.val = 17 ∨ n.val = 18 ∨ n.val = 19 ∨ n.val = 20 ∨ n.val = 21 ∨ n.val = 22 ∨ n.val = 23 ∨ n.val = 24 ∨ n.val = 25 ∨ n.val = 26 ∨ n.val = 27 ∨ n.val = 28 ∨ n.val = 29 ∨ n.val = 30 ∨ n.val = 31 := by
  decide

theorem gpr_range (n : Nat) (h32 : n < 32) (h1 : 1 ≤ n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 :=
  gpr_range_fin ⟨n, h32⟩ h1

/-- A property of the 31 general-purpose register numbers, checked once per register:
`gpr_cases n => tac` substitutes each literal `1, …, 31` for `n` (range hypotheses `1 ≤ n` and
`n ≤ 31` must be in context) and runs `tac` on each case. -/
syntax "gpr_cases " ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| gpr_cases $n:ident => $t:tacticSeq) => do
    let r := Lean.mkIdent `rfl
    `(tactic| (rcases gpr_range $n (by omega) (by omega) with $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r <;> ($t)))

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

theorem rX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x5 = some v) :
    (rX_bits (regidx.Regidx 0x05#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 5 (by decide) (by decide) v h

theorem wX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x05#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x5 d} :=
  wX_bits_gpr σ d 5 (by decide) (by decide)

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

theorem wX_bits_x1 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x01#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x1 d} :=
  wX_bits_gpr σ d 1 (by decide) (by decide)

theorem rX_bits_x16 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x16 = some v) :
    (rX_bits (regidx.Regidx 0x10#5)).run σ = .ok v σ :=
  rX_bits_gpr σ 16 (by decide) (by decide) v h

end Vsa.Sim
