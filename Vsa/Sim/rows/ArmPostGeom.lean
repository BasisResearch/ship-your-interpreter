import Vsa.Sim.rows.EvalAddRow
import Vsa.Sim.rows.EvalSubRow

/-!
# `ArmPostGeom` — the shared post-`TwoSubReturn` binary residual (step-1 alias)

The ten binary `Eval<Op>SimGoal` theorems each carry a per-op residual structure
(`AddResid`/`SubResid`/`GtResid`/…) describing the machine config `c'` reached
after both operand sub-calls return (the `TwoSubReturn` landing).  As MEASURED
against the landed sources, `AddResid` and `SubResid` are byte-identical modulo
exactly TWO fields:

* `opTok` — the operator token read at `aExpr+8` (`11` for `.add`, `12` for `.sub`);
* `slot`  — the operator jump-table slot pin (`AddSlotPinned` / `SubSlotPinned`).

Every remaining field is a function of `(gpre,N,A,SL,sp,r,sret,aExpr,Wl,c')` alone.
`ArmPostGeom` factors that shared tail into ONE structure parameterised by the two
per-op data (`opTok : Nat`, `slotDef : Mem → Prop`).  The per-op residual is then a
DEF-alias (`AddResid = ArmPostGeom 11 AddSlotPinned`, up to the thin reassociation
adapters below), collapsing the shared geometry list.

This is a pure interface layer: the adapters are field projections and injections only;
no landed proof is touched, and the per-op `Eval<Op>SimGoal` statements are unchanged.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable
open Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.Alloc Vsa.Sim.Code
open Register

namespace Vsa.Sim

/-- The shared post-`TwoSubReturn` binary residual, parameterised by the two per-op
data (`opTok`, `slotDef`).  Its non-`opTok`/`slot` fields are exactly the shared
tail of every `Eval<Op>SimGoal`'s per-op residual. -/
structure ArmPostGeom
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (opTok : Nat) (slotDef : Mem → Prop)
    (sp r sret aExpr : BitVec 64) (Wl : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTokRead : read32 c'.σ.mem (aExpr.toNat + 8) = some opTok
  slot : slotDef c'.σ.mem
  fullpop : ∀ k : Nat, ∃ w : BitVec 8, c'.σ.mem[k]? = some w
  x19 : c'.σ.regs.get? Register.x19 = some Wl
  wlbuf : read64 c'.σ.mem (sp.toNat - 960) = some Wl.toNat
  kindresp : read64 c'.σ.mem (sp.toNat - 1088) = some (2#64 : BitVec 64).toNat
  exprAl : aExpr.toNat % 4 = 0
  exprLo : 0x80000000 ≤ aExpr.toNat
  exprHi : aExpr.toNat + 16 ≤ 0x100000000
  exprWin : tohostAddr + 8 ≤ aExpr.toNat
  exprSL : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  sretAl : sret.toNat % 8 = 0
  sretLo : 0x80000000 ≤ sret.toNat
  sretHi : sret.toNat + 24 ≤ 0x100000000
  sretWin : tohostAddr + 16 ≤ sret.toNat
  sretVi : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  sretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  raAl : r.toNat % 4 = 0
  vint : Value_intLoaded c'.σ.mem
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo
  tableStk : opTableBase + 4 ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ## Add adapters (`AddResid ↔ ArmPostGeom 11 AddSlotPinned`). -/

theorem armPostGeom_of_addResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : AddResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeom gpre N A SL 11 AddSlotPinned sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem addResid_of_armPostGeom
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeom gpre N A SL 11 AddSlotPinned sp r sret aExpr Wl c') :
    AddResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

/-! ## Sub adapters (`SubResid ↔ ArmPostGeom 12 SubSlotPinned`). -/

theorem armPostGeom_of_subResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : SubResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeom gpre N A SL 12 SubSlotPinned sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem subResid_of_armPostGeom
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeom gpre N A SL 12 SubSlotPinned sp r sret aExpr Wl c') :
    SubResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

#print axioms armPostGeom_of_addResid
#print axioms addResid_of_armPostGeom
#print axioms armPostGeom_of_subResid
#print axioms subResid_of_armPostGeom

end Vsa.Sim
