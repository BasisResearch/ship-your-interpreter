import Vsa.Sim.rows.ValuePrintArms
import Vsa.Sim.rows.StoreReprPhicRebase
import Vsa.Alloc
import Vsa.Sim.CallExternalContracts

/-!
# Value-print contracts

`value_print` renders one value for the native-print loop. Its six reflected
arms tail-call `fprintf`, `fwrite`, or `fputs`. The caller supplies the IO
contracts from `CallExternalContracts` and the `ValuePrintDispatch` premise
that reaches the selected arm.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.While

namespace Vsa.Sim

/-! ## §1. The handler (arm-entry) address per kind

The `.rodata` jump table at `0x80019f10` (6 signed 32-bit offsets, base
`0x80019f10`, read off the linked image) sends kind `k` to its arm entry. -/

/-- The arm-entry (handler) PC for a value's kind — the target of the computed
`jr a5`.  (kind 0 null→`0x8000295c`, 1 bool→`0x80002974`, 2 int→`0x80002990`,
3 str→`0x800029a4`, 4 closure→`0x80002928`, 5 native→`0x80002948`.) -/
def vpHandler : Value → BitVec 64
  | .null      => 0x8000295c#64
  | .bool _    => 0x80002974#64
  | .int _     => 0x80002990#64
  | .str _     => 0x800029a4#64
  | .closure _ => 0x80002928#64
  | .native _  => 0x80002948#64

/-! Dispatch from `value_print` at `0x800028fc` to `vpHandler v`.
The premise preserves the value representation, stream, memory, output and
ABI frame. `ValueRepr` supplies the kind bound used by the dispatch guard.
IO contracts are defined in `CallExternalContracts`. -/
def ValuePrintDispatch (N : NativeAddrs) (φc : Addr → Nat) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (pv stream ra : BitVec 64)
    (v : Value) (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : String),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x800028fc#64 ∧
        c.σ.regs.get? Register.x10 = some pv ∧
        c.σ.regs.get? Register.x11 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        ValueRepr m0 N φc pv.toNat v ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0 ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R))
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (vpHandler v) ∧
        c.σ.regs.get? Register.x10 = some pv ∧
        c.σ.regs.get? Register.x11 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        ValueRepr m0 N φc pv.toNat v ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0 ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R))

/-! ## §4. Local arm contract and composition

`ValuePrintDispatch` stops at one of the six reflected arm entries.  The only
code below an arm is its reflected straight-line row followed by one external
IO tail call.  `ValuePrintArmsContract` names exactly that local boundary.  It
does not cover the dispatch head or the surrounding native-print loop. -/

/-- The exact state delivered by `ValuePrintDispatch` to a reflected arm. -/
def ValuePrintArmEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (pv stream ra : BitVec 64)
    (v : Value) (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : String)
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (vpHandler v) ∧
  c.σ.regs.get? Register.x10 = some pv ∧
  c.σ.regs.get? Register.x11 = some stream ∧
  c.σ.regs.get? Register.x1 = some ra ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  IsConsoleStdout stream ∧ ConsoleStream m0 ∧
  ValueRepr m0 N φc pv.toNat v ∧
  Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0 ∧
  (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R)

/-- The common return boundary of one value-print arm and its external IO tail
call.  The external callee may mutate its private FILE state and its stack; no
whole-memory preservation is claimed. -/
structure ValuePrintArmExit
    (g : (R : Register) → Option (RegisterType R))
    (SL : Vsa.Alloc.StackLayout) (privFoot : Nat → Prop)
    (ra sp : BitVec 64) (frag out0 : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some ra
  spReg : c.σ.regs.get? Register.x2 = some sp
  console : ConsoleStream c.σ.mem
  frame : ∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R
  out : Vsa.Machine.output c.σ = out0 ++ frag
  memFrame : ∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    c.σ.mem[a]? = m0[a]?

/-- The union of the four external callees' private memory footprints. -/
def CallIOPrivFoot (io : CallIOContracts SL) (a : Nat) : Prop :=
  io.fprintf.privFoot a ∨ io.fwrite.privFoot a ∨
  io.fputs.privFoot a ∨ io.fputc.privFoot a

/-- The remaining value-print machine frontier, localized to one selected arm.
Each instance is discharged by the corresponding `vp*ArmRow` followed by the
matching field of `CallIOContracts`: null uses `fwrite`; bool/string use
`fputs`; integer/native/closure use `fprintf`. -/
structure ValuePrintArmsContract (SL : Vsa.Alloc.StackLayout) where
  run : (io : CallIOContracts SL) →
    ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
      (sStore : Store) (v : Value) (pv stream ra sp : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : String),
    g Register.x2 = some sp →
    StoreRepr m0 N A φf φc sStore →
    ValueClosuresBounded sStore.closures.size v →
    Triple
      (ValuePrintArmEntry g N φc pv stream ra v m0 out0)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp (Value.display sStore v) out0 m0)

/-- Compose the exact dispatch boundary with the selected reflected arm and its
leaf IO contract.  This is the whole `value_print` result, but not a premise:
the only premises are the local dispatch and arm boundaries above. -/
theorem valuePrint_of_dispatch_arms
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : Vsa.Alloc.StackLayout)
    (φf φc : Addr → Nat) (sStore : Store) (v : Value)
    (pv stream ra sp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : String) (hgsp : g Register.x2 = some sp)
    (hStore : StoreRepr m0 N A φf φc sStore)
    (hBound : ValueClosuresBounded sStore.closures.size v)
    (hDispatch : ValuePrintDispatch N φc)
    (hIO : CallIOContracts SL)
    (hArms : ValuePrintArmsContract SL) :
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x800028fc#64 ∧
        c.σ.regs.get? Register.x10 = some pv ∧
        c.σ.regs.get? Register.x11 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        ValueRepr m0 N φc pv.toNat v ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0 ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R))
      (ValuePrintArmExit g SL (CallIOPrivFoot hIO) ra sp
        (Value.display sStore v) out0 m0) := by
  exact Triple.seq
    (hDispatch g pv stream ra v m0 out0)
    (hArms.run hIO g N A φf φc sStore v pv stream ra sp m0 out0 hgsp hStore hBound)

#print axioms valuePrint_of_dispatch_arms

end Vsa.Sim
