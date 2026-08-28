import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.ValueSpec
import Vsa.Sim.EvalBoolSim

/-!
# `BoxSuffixSeams` — the value-boxing call seams (`value_int` / `value_bool`)

Item 3 of the binary-op wiring ("the box suffix") is a `jal value_int` (div/mod)
or `jal value_bool` (eq/ne) call site.  Structurally it is the SAME Shape-D
`callSeg` splice as the callee seams `divCallSeam`/`modCallSeam`
(`DivDispatchSeg`/`ModDispatchSeg`) and `valueEqualCallSeam` (`EqNeDispatchSeg`) —
only the threaded callee is the value-constructor `value_int`/`value_bool` rather
than `__divdi3`/`__moddi3`/`value_equal`.

`value_int_spec` (`ValueSpec.lean`) and `value_bool_spec_full` (`EvalBoolSim.lean`)
are already genuine `Triple`s, so each box suffix is one `callSeg` line: given the
caller prefix landing the staged buffer/payload at the value-constructor entry
(`Triple P (int_pre …)` / `boxBool_pre`) and the caller return suffix consuming the
produced `ValueRepr` (`Triple (int_post …) Q` / `boxBool_post`), `callSeg` produces
the whole box call site `Triple P Q`.

These are the named bricks the div/mod/eq/ne arms compose on top of their dispatch
rows (`divDispatchRow` etc.) and the callee seam — closing the "then value_int" /
"then value_bool (+ seqz for ne)" leg exactly as `divCallSeam` closes the
`__divdi3` leg.  Pure `Triple.seq`/`callSeg` plumbing — no reflection, no machine
unfolding.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value)
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## The `value_int` box seam (div / mod)

`int_pre`/`int_post` (`ValueSpec.lean`) are the named entry/exit predicates of
`value_int_spec`, so the seam threads it directly. -/

/-- **The `value_int` box seam, via `callSeg` with the real `value_int_spec`.**
Given the caller prefix landing the staged buffer `buf` and payload `pay` at the
`value_int` entry (`Triple P (int_pre g buf pay r m0 out0)`) and the caller return
suffix consuming the produced `.int` value (`Triple (int_post …) Q`), `callSeg`
produces the whole `jal value_int` box site `Triple P Q` — with `value_int_spec`
(not a hand re-derivation) as the threaded callee.  Shared by `div` and `mod`
(they differ only in the payload `pay = a.tdiv b` vs `a.tmod b`, staged by the
prefix, and the spec bridge `binOpSem_div_int`/`binOpSem_mod_int`). -/
theorem valueIntCallSeam {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (pre : Triple P (int_pre g buf pay r m0 out0))
    (suf : Triple (int_post g buf pay r N φc m0 out0) Q) :
    Triple P Q :=
  callSeg pre (value_int_spec g buf pay r N φc m0 out0) suf

#print axioms valueIntCallSeam

/-! ## The `value_bool` box seam (eq / ne)

`value_bool_spec_full`'s entry/exit predicates are inline lambdas; we name them as
`boxBool_pre`/`boxBool_post` (definitionally the spec's own predicates) so the seam
has a clean, referenceable API — exactly mirroring `int_pre`/`int_post`. -/

/-- The `value_bool` box entry predicate: at `0x800027f8` with `x10 = buf` (the
`value_bool` output buffer, `= sret`), `x11 = vb` (the boolean payload word), and
`x1 = r` (return address); the `value_bool` region + return alignment side
conditions.  Definitionally the `value_bool_spec_full` entry predicate. -/
def boxBool_pre (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Value_boolLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800027f8#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some vb ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  BoolRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- The `value_bool` box exit predicate: PC back at `r`, `x10 = buf`, and
`ValueRepr … buf (.bool (vb != 0))` — the boxed boolean, plus the console-output
invariance and the sret-buffer memory frame the epilogue needs.  Definitionally the
`value_bool_spec_full` exit predicate. -/
def boxBool_post (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  ValueRepr c.σ.mem N φc buf.toNat (.bool (vb != 0#64)) ∧
  c.σ.sailOutput = out0 ∧
  (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
  MemExtends m0 c.σ.mem ∧
  (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)

/-- `value_bool_spec_full` restated over the named `boxBool_pre`/`boxBool_post`
predicates (definitional repackaging, so the seam has a clean API). -/
theorem value_bool_box (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple (boxBool_pre g buf vb r m0 out0) (boxBool_post g buf vb r N φc m0 out0) :=
  value_bool_spec_full g buf vb r N φc m0 out0

/-- **The `value_bool` box seam, via `callSeg` with the real `value_bool_spec_full`.**
Given the caller prefix landing the staged buffer `buf` (`= sret`) and boolean word
`vb` at the `value_bool` entry (`Triple P (boxBool_pre …)`) and the caller return
suffix consuming the produced `.bool (vb != 0)` value (`Triple (boxBool_post …) Q`),
`callSeg` produces the whole `jal value_bool` box site `Triple P Q`.  Shared by `eq`
and `ne`: `eq` stages `vb = value_equal(a,b)` (so `.bool (l.equal r)` via
`binOpSem_eq`), `ne` stages `vb = seqz(value_equal(a,b))` (so `.bool (!(l.equal r))`
via `binOpSem_ne`) — the extra `seqz` lives in the prefix, not this seam. -/
theorem valueBoolCallSeam {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R)) (buf vb r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (pre : Triple P (boxBool_pre g buf vb r m0 out0))
    (suf : Triple (boxBool_post g buf vb r N φc m0 out0) Q) :
    Triple P Q :=
  callSeg pre (value_bool_box g buf vb r N φc m0 out0) suf

#print axioms value_bool_box
#print axioms valueBoolCallSeam

end Vsa.Sim
