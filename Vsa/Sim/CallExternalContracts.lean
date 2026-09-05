import Vsa.Alloc
import Vsa.Triple
import Vsa.Sim.ConsoleStream

/-! Exact external-output contracts carried by the indexed call boundary. -/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Logic

namespace Vsa.Sim

/-- The three `fprintf` formats used by `value_print`, tied to the bytes or
integer actually passed in `a2`. -/
def FprintfGround (m : Std.ExtHashMap Nat (BitVec 8))
    (fmt arg : BitVec 64) (frag : String) : Prop :=
  (fmt = 0x800192c0#64 ∧ frag = Vsa.While.intToString arg.toInt) ∨
  (∃ name, fmt = 0x800192c8#64 ∧ Vsa.MemRepr.CString m arg.toNat name ∧
    frag = "<fn " ++ name ++ ">") ∨
  (∃ name, fmt = 0x800192d8#64 ∧ Vsa.MemRepr.CString m arg.toNat name ∧
    frag = "<native fn " ++ name ++ ">")

/-- The fixed four-byte buffers used by `value_print`'s `fwrite` arms. -/
def FwriteGround (buf size nmemb : BitVec 64) (frag : String) : Prop :=
  size = 1#64 ∧ nmemb = 4#64 ∧
    ((buf = 0x80019018#64 ∧ frag = "null") ∨
     (buf = 0x800192d0#64 ∧ frag = "<fn>"))

/-- `fputs` either receives one of value_print's two fixed literals or a
represented NUL-terminated string. -/
def FputsGround (m : Std.ExtHashMap Nat (BitVec 8))
    (strp : BitVec 64) (frag : String) : Prop :=
  (strp = 0x80019008#64 ∧ frag = "true") ∨
  (strp = 0x80019010#64 ∧ frag = "false") ∨
  (strp ≠ 0x80019008#64 ∧ strp ≠ 0x80019010#64 ∧
    Vsa.MemRepr.CString m strp.toNat frag)

structure FprintfContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
  consoleFoot : ∀ a, ConsoleFoot a → privFoot a
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (stream fmt arg ra sp : BitVec 64) (frag out0 : String)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x800061c0#64 ∧
        c.σ.regs.get? Register.x10 = some stream ∧
        c.σ.regs.get? Register.x11 = some fmt ∧
        c.σ.regs.get? Register.x12 = some arg ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        FprintfGround m0 fmt arg frag ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ConsoleStream c.σ.mem ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

structure FwriteContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
  consoleFoot : ∀ a, ConsoleFoot a → privFoot a
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (buf size nmemb stream ra sp : BitVec 64) (frag out0 : String)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x80005260#64 ∧
        c.σ.regs.get? Register.x10 = some buf ∧
        c.σ.regs.get? Register.x11 = some size ∧
        c.σ.regs.get? Register.x12 = some nmemb ∧
        c.σ.regs.get? Register.x13 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        FwriteGround buf size nmemb frag ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ConsoleStream c.σ.mem ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

structure FputsContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
  consoleFoot : ∀ a, ConsoleFoot a → privFoot a
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (strp stream ra sp : BitVec 64) (frag out0 : String)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x80006500#64 ∧
        c.σ.regs.get? Register.x10 = some strp ∧
        c.σ.regs.get? Register.x11 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        FputsGround m0 strp frag ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ConsoleStream c.σ.mem ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

/-- Exact leaf contract for `fputc`.  The output fragment is fixed by the
actual low byte passed in `a0`; FILE and stack writes are explicitly carved
out instead of claiming whole-memory preservation. -/
structure FputcContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
  consoleFoot : ∀ a, ConsoleFoot a → privFoot a
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (ch : BitVec 8) (stream ra sp : BitVec 64) (out0 : String)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x800062e0#64 ∧
        c.σ.regs.get? Register.x10 = some (zero_extend (m := 64) ch) ∧
        c.σ.regs.get? Register.x11 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        IsConsoleStdout stream ∧ ConsoleStream m0 ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ConsoleStream c.σ.mem ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ =
          out0 ++ toString (Char.ofNat ch.toNat) ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          c.σ.mem[a]? = m0[a]?))

structure CallIOContracts (SL : Vsa.Alloc.StackLayout) where
  fprintf : FprintfContract SL
  fwrite : FwriteContract SL
  fputs : FputsContract SL
  fputc : FputcContract SL

end Vsa.Sim
