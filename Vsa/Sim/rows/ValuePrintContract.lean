import Vsa.Sim.rows.ValuePrintArms
import Vsa.Alloc

/-!
# `ValuePrintContract` — the `value_print` frontier: callee contracts + dispatch residual (wave 44)

`value_print` (`0x800028fc … 0x800029ac`) is the per-value renderer the
`NativePrintInternal` loop (`rows/NativeBodyPrint.lean`) calls once per argument;
its net effect is to append `Value.display sStore v` to the console.  Wave 44
landed the six case arms as `#derive_case` segs (`rows/ValuePrintArms.lean`,
each parked AT its IO callee's entry with the ABI args in `GHolds`).  This file
names the remaining frontier — the pieces with no code image / site battery yet:

* **The three IO callee contracts** (`FprintfLldContract` / `FwriteBufContract`
  / `FputsContract`) — named-field `structure … where` triples (model:
  `Vsa.Alloc.MallocContract`), each an output-append + ABI-return spec parked at
  the newlib fn's entry.  These are the genuine machine frontier (newlib
  `fprintf`/`fwrite`/`fputs` down to the HTIF `tohost` putchar — deep, multi-wave,
  the wave-39 warning).  A `value_print` caller supplies them ONCE.

* **The dispatch-head residual** (`ValuePrintDispatch`) — the entry kind-load +
  `bltu` guard + the `.rodata` jump-table dispatch (`jr a5`, base `0x80019f10`)
  from `value_print`'s entry to the resolved arm entry.  BLOCKED on the SegEval
  block decoder: the jump table's first instruction `lwu a5,0(a0)` has no `MKind`
  (`decodeM` LOAD = lw/ld/lbu only) — observation `lwu-missing-from-block-decoder`.
  Until `.lwu` lands (coordinator, mirrors the wave-38 `xori` add) the dispatch
  head is a NAMED typed premise; its post is exactly the arm entries the landed
  arm rows consume, so the moment `.lwu` exists it is a `#derive_case` seg ending
  in the `jr` terminator (`TKind.jr`, end PC = `handlerAddr v` per kind, the
  `CmpDispatchSeg`/`ValueEqualSpec` jump-table precedent).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
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

/-! ## §2. The IO callee contracts (named typed premises)

Each is stated as a `structure … where`-wrapped `Triple` parked at the callee's
entry PC, appending exactly the rendered fragment to the console and returning to
`ra` (value_print tail-jumps in, so `ra` is value_print's own caller).  ABI
callee-saved registers and `sp`/`gp` are preserved; memory outside the callee's
private FILE/stack footprint is framed.  These abstract over the newlib internals
(no code image exists yet).  The predicates are deliberately minimal — exactly
what the `value_print` output-append contract needs — and can be strengthened
when the internals land. -/

/-- **`fprintf(stream, "%lld"/fmt, arg)` contract** parked at `0x800061c0`.
The console grows by the rendered fragment `frag` (for the int arm,
`frag = intToString n`; for closure/native arms the C fmt string's render), the
function returns to `ra`, ABI frame preserved, memory framed outside the FILE
footprint.  `arg`/`fmt` are the pinned args; `frag` is the caller-supplied
rendered output. -/
structure FprintfContract (SL : Vsa.Alloc.StackLayout) where
  /-- FILE/reent private footprint (newlib `_impure_ptr` state etc.). -/
  privFoot : Nat → Prop
  /-- One `fprintf` call: entry at `0x800061c0`, args `a0=stream a1=fmt a2=arg`,
  console appends `frag`, returns to `ra`, ABI + sp preserved, memory framed. -/
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
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

/-- **`fwrite(buf, size, nmemb, stream)` contract** parked at `0x80005260`
(the `null` arm's `fwrite("null",1,4,stream)`).  Console appends `frag` (the
`nmemb`-byte buffer content — `"null"` for the null arm), returns to `ra`. -/
structure FwriteContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
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
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

/-- **`fputs(str, stream)` contract** parked at `0x80006500` (the `bool` and
`str` arms).  Console appends the NUL-terminated `str` at `a0` (`frag`), returns
to `ra`. -/
structure FputsContract (SL : Vsa.Alloc.StackLayout) where
  privFoot : Nat → Prop
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (strp ra sp : BitVec 64) (frag out0 : String)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x80006500#64 ∧
        c.σ.regs.get? Register.x10 = some strp ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out0 ++ frag ∧
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))

/-! ## §3. The dispatch-head residual (blocked on `.lwu`, named premise)

The entry (`lw a4,0(a0)` kind ; `li a5,5` ; `bltu a5,a4` guard, NOT taken for
`kind ≤ 5`) + the jump-table dispatch (`lwu a5,0(a0)` ; `auipc/addi a4=0x80019f10`
; `slli` ; `add` ; `lw a5,0(a5)` ; `add` ; `jr a5`).  From `value_print`'s entry
`0x800028fc` with `a0 = pv` representing `v` (`ValueRepr`), lands at the arm entry
`vpHandler v` with the arm's entry pins (`a0 = pv`, `a1 = stream`) intact, memory
and console unchanged.  This IS a `#derive_case` seg ending in the `jr`
terminator once `MKind.lwu` exists (the `lwu a5,0(a0)` reload of the kind); until
then it is a named typed premise.  (The kind bound `< 6` — hence the `bltu` NOT
taken — comes from `ValueRepr`; `read32 m a = some (kindTag v)` and `kindTag v < 6`.) -/
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
        ValueRepr m0 N φc pv.toNat v ∧
        Vsa.Machine.output c.σ = out0 ∧ c.σ.mem = m0 ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R))

end Vsa.Sim
