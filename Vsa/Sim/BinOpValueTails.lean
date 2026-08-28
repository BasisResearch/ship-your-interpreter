import Vsa.Sim.DivDispatchSeg
import Vsa.Sim.ModDispatchSeg
import Vsa.Sim.EqNeDispatchSeg
import Vsa.Sim.BoxSuffixSeams

/-!
# `BinOpValueTails` — the full two-call value tail per binary-op arm

Each remaining binary-op arm produces its result value through TWO spliced call
sites: a *callee* (`__divdi3`/`__moddi3`/`value_equal`) that computes the scalar,
then a *box* (`value_int`/`value_bool`) that materialises the `Value` struct.  The
callee seams (`divCallSeam`/`modCallSeam`/`valueEqualCallSeam`) and the box seams
(`valueIntCallSeam`/`valueBoolCallSeam`, `BoxSuffixSeams`) each thread ONE real
callee contract via `callSeg`.  This file composes the two into a single named
value-tail theorem per arm, so the whole item-2 + item-3 splice for an arm is one
`callSeg ∘ callSeg` with BOTH real specs threaded.

What each tail leaves as residual is exactly the three concrete machine bridges the
arm still needs (mirroring the by-hand `blockC_ge`, which does all three inline):

* **`pre`** — the caller prefix: the dispatch row (`divDispatchRow` etc., staging
  the callee args) followed by the `jal <callee>` link, landing the callee's own
  entry predicate (`divdi3_pre` / `ve_pre ∧ x2=sp`).  Item 1 (entry linkage from
  the eval-expr dispatch into `SegPre`) feeds this.
* **`stage`** — the inter-call staging: from the callee's exit (`divdi3_post` /
  `ve_str_post`) across the `mv` argument shuffles and the `jal <box>` link to the
  box's entry (`int_pre` / `boxBool_pre`).  For `ne` this is where the extra `seqz`
  negates the `value_equal` result before boxing.
* **`suf`** — the box return suffix: from the box's exit (`int_post` /
  `boxBool_post`) through the epilogue to the arm's post `Q` (`PreEpilogueVD`, fed
  to `blockD_v_rec`).

Pure `callSeg` plumbing over the two real callee contracts — no reflection, no
machine unfolding, so it elaborates in constant time and is axiom-clean.  The
concrete bridges are the honest remaining work; these tails lock the composition so
each bridge can be built in isolation and dropped in.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (NativeFn)
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

/-! ## `div` / `mod` value tails (`__divdi3`/`__moddi3` ≫ `value_int`) -/

/-- **The full `div` value tail.**  `dispatch+jal __divdi3 ≫ __divdi3 ≫
stage(mv+jal value_int) ≫ value_int ≫ epilogue`, with `divdi3_spec` and
`value_int_spec` BOTH threaded as real callees.  `pay` is the staged payload word
(`= Wl.tdiv Wr`, i.e. `wrap64 (a.tdiv b)` via `binOpSem_div_int`); the residual is
exactly the three concrete bridges `pre`/`stage`/`suf`. -/
theorem divValueTail {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R))
    (Wl Wr rC sret pay rB : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (mA mB : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (pre : Triple P (divdi3_pre Wl Wr rC mA))
    (stage : Triple (divdi3_post Wl Wr rC mA) (int_pre g sret pay rB mB out0))
    (suf : Triple (int_post g sret pay rB N φc mB out0) Q) :
    Triple P Q :=
  valueIntCallSeam g sret pay rB N φc mB out0
    (divCallSeam Wl Wr rC mA pre stage) suf

/-- **The full `mod` value tail.**  Sibling of `divValueTail`, threading
`moddi3_spec` (`Wl.tmod Wr`, `wrap64 (a.tmod b)` via `binOpSem_mod_int`) then
`value_int_spec`. -/
theorem modValueTail {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R))
    (Wl Wr rC sret pay rB : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (mA mB : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (pre : Triple P (moddi3_pre Wl Wr rC mA))
    (stage : Triple (moddi3_post Wl Wr rC mA) (int_pre g sret pay rB mB out0))
    (suf : Triple (int_post g sret pay rB N φc mB out0) Q) :
    Triple P Q :=
  valueIntCallSeam g sret pay rB N φc mB out0
    (modCallSeam Wl Wr rC mA pre stage) suf

#print axioms divValueTail
#print axioms modValueTail

/-! ## `eq` / `ne` value tails (`value_equal` ≫ `value_bool`) -/

/-- **The full `eq`/`ne` value tail.**  `spill-setup+jal value_equal ≫ value_equal
≫ stage(+seqz for ne, mv+jal value_bool) ≫ value_bool ≫ epilogue`, with
`value_equal_spec_full` and `value_bool_spec_full` BOTH threaded as real callees.
`bw` is the staged boolean word fed to `value_bool` (`= value_equal(a,b)` for `eq`,
its `seqz` for `ne`); the produced value is `.bool (bw != 0)` (`binOpSem_eq` /
`binOpSem_ne`).  Residual = the three concrete bridges `pre`/`stage`/`suf`; `eq`
and `ne` share this theorem, differing only in `stage`. -/
theorem eqNeValueTail {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R))
    (bufa bufb rC sp sret bw rB : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Vsa.While.Value)
    (mA mB : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
    (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
    (hstrc : StrcmpLoaded mA) (hmask : MaskPinned mA) (hraln4 : rC.toNat % 4 = 0)
    (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
      ∃ (pa' pb' : Nat) (csa csb : List Char),
        read64 mA (bufa.toNat + 8) = some pa' ∧ read64 mA (bufb.toNat + 8) = some pb' ∧
        CStr mA pa' csa ∧ CStr mA pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
        StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
        VEStrRegions sp pa' pb' csa.length csb.length)
    (pre : Triple P (fun c => ve_pre g bufa bufb rC N φc va vb mA c ∧
              c.σ.regs.get? Register.x2 = some sp))
    (stage : Triple (ve_str_post g rC sp va vb mA) (boxBool_pre g sret bw rB mB out0))
    (suf : Triple (boxBool_post g sret bw rB N φc mB out0) Q) :
    Triple P Q :=
  valueBoolCallSeam g sret bw rB N φc mB out0
    (valueEqualCallSeam g bufa bufb rC sp N φc va vb mA
      hφc hN hstrc hmask hraln4 hstrwit pre stage) suf

#print axioms eqNeValueTail

end Vsa.Sim
