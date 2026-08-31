import Vsa.Sim.rows.EvalAddRow
import Vsa.Sim.rows.EvalSubRow
import Vsa.Sim.rows.EvalLtRow
import Vsa.Sim.rows.EvalLeRow
import Vsa.Sim.rows.EvalGtRow
import Vsa.Sim.rows.EvalGeRow
import Vsa.Sim.rows.EvalMulRow
import Vsa.Sim.rows.EvalDivRow
import Vsa.Sim.rows.EvalModRow

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

/-!
## `ArmPostGeomV` — the value-form-and-`tableStk`-parameterised shared residual

`ArmPostGeom` (above) is the int/`tableStk+4` instance used by add/sub.  The other
seven `structure`-shaped op residuals (`Lt/Le/Gt/Ge/Mul/Div/Mod`) share the SAME shared
geometry tail, but vary in THREE further pieces the add/sub base fixes:

* **value-form** — the value-image region + its loaded predicate.  Int ops carry
  `vint : Value_intLoaded` with box `[0x8000280c, 0x8000281c)`; the comparison ops
  (`Lt/Le/Gt/Ge`) carry `vbool : Value_boolLoaded` with box `[0x800027f8, 0x8000280c)`.
  Captured by `(valLoaded : Mem → Prop, viLo viHi : Nat)`.
* **`tableStk` offset** — the op-jump-table slot's byte offset: `4` (add/sub, cmp),
  `12` (mul), `20` (div/mod).  Captured by `tblOff : Nat`.

The op-specific libgcc-callee-loaded facts (`muldi3`/`divdi3`/…/`<op>Stk`) are NOT
shared geometry — per the T1.1 discipline note ("the extra fields belong in
`TermGuards`, not `ImageGeom`; keep them separate") they stay OUT of `ArmPostGeomV`
and are threaded as explicit hypotheses on the reverse (`<op>Resid_of_…`) direction.

`ArmPostGeomV` generalises `ArmPostGeom`: `ArmPostGeom o s = ArmPostGeomV o s
Value_intLoaded 0x8000280c 0x8000281c 4` field-for-field (kept separate so the landed
add/sub adapters are untouched; the two are inter-derivable by `⟨…⟩` projection). -/
structure ArmPostGeomV
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (opTok : Nat) (slotDef : Mem → Prop)
    (valLoaded : Mem → Prop) (viLo viHi : Nat) (tblOff : Nat)
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
  sretVi : sret.toNat + 24 ≤ viLo ∨ viHi ≤ sret.toNat
  sretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  raAl : r.toNat % 4 = 0
  vloaded : valLoaded c'.σ.mem
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ viLo ∨ viHi ≤ SL.lo
  tableStk : opTableBase + tblOff ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ### `ArmPostGeom` ↔ `ArmPostGeomV` (the int/`tblOff=4` instance, for add/sub reuse). -/

theorem armPostGeomV_of_armPostGeom
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {opTok : Nat} {slotDef : Mem → Prop}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeom gpre N A SL opTok slotDef sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL opTok slotDef Value_intLoaded 0x8000280c 0x8000281c 4
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

/-! ## Comparison adapters (`vbool`, box `[0x800027f8,0x8000280c)`, `tblOff=4`).

`Lt/Le/Gt/Ge` differ from one another only in `opTok`/`slotDef`; all four are the
bool-value instance of `ArmPostGeomV`.  Clean isos (no op-specific extras). -/

theorem armPostGeomV_of_ltResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : LtResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vbool, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem ltResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c') :
    LtResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem armPostGeomV_of_leResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : LeResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 21 LeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vbool, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem leResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 21 LeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c') :
    LeResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem armPostGeomV_of_gtResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : GtResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 22 GtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vbool, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem gtResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 22 GtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c') :
    GtResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem armPostGeomV_of_geResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : GeResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 23 GeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vbool, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem geResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 23 GeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr Wl c') :
    GeResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

/-! ## Int libgcc-seam adapters (`vint`, int box, op-specific `tblOff` + callee extras).

`Mul`/`Div`/`Mod` are the int-value instance of `ArmPostGeomV` (box `[0x8000280c,
0x8000281c)`) at their own `tblOff` (`12`/`20`/`20`), PLUS op-specific libgcc-callee
`…Loaded` facts and a `<op>Stk` disjointness that are NOT shared geometry.  The
FORWARD adapter projects the shared core (extras discarded); the REVERSE adapter
reconstructs the residual from `ArmPostGeomV` + those extras threaded explicitly. -/

theorem armPostGeomV_of_mulResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : MulResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 13 MulSlotPinned Value_intLoaded 0x8000280c 0x8000281c 12
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem mulResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 13 MulSlotPinned Value_intLoaded 0x8000280c 0x8000281c 12
      sp r sret aExpr Wl c')
    (muldi3 : Vsa.Sim.Code.__muldi3Loaded c'.σ.mem)
    (muldiStk : sp.toNat ≤ 0x80004640 ∨ 0x80004664 ≤ SL.lo) :
    MulResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, muldi3, muldiStk, h.codeStk, h.viStk, h.tableStk, h.sretInSL,
   h.SLloSp, h.SLlo, h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem armPostGeomV_of_divResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : DivResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 14 DivSlotPinned Value_intLoaded 0x8000280c 0x8000281c 20
      sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem divResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 14 DivSlotPinned Value_intLoaded 0x8000280c 0x8000281c 20
      sp r sret aExpr Wl c')
    (divdi3 : Vsa.Sim.Code.__divdi3Loaded c'.σ.mem)
    (umoddi3 : Vsa.Sim.Code.__umoddi3Loaded c'.σ.mem)
    (udivdi3 : __hidden___udivdi3Loaded c'.σ.mem)
    (divStk : sp.toNat ≤ 0x800046a4 ∨ 0x80004728 ≤ SL.lo) :
    DivResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, divdi3, umoddi3, udivdi3, divStk, h.codeStk, h.viStk,
   h.tableStk, h.sretInSL, h.SLloSp, h.SLlo, h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem armPostGeomV_of_modResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ModResid gpre N A SL sp r sret aExpr Wl c') :
    ArmPostGeomV gpre N A SL 15 (SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8)
      Value_intLoaded 0x8000280c 0x8000281c 20 sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTok, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vint, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

theorem modResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 15 (SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8)
      Value_intLoaded 0x8000280c 0x8000281c 20 sp r sret aExpr Wl c')
    (moddi3 : Vsa.Sim.Code.__moddi3Loaded c'.σ.mem)
    (udivdi3 : __hidden___udivdi3Loaded c'.σ.mem)
    (modStk : sp.toNat ≤ 0x800046ac ∨ 0x80004764 ≤ SL.lo) :
    ModResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, moddi3, udivdi3, modStk, h.codeStk, h.viStk, h.tableStk,
   h.sretInSL, h.SLloSp, h.SLlo, h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

/-!
## `EqResid` — RESISTS the `ArmPostGeom(V)` shape (documented, no adapter)

`EqResid` (in `Vsa/Sim/rows/EvalEqNeFront.lean`) is NOT a per-config geometry
`structure` sharing the `ArmPostGeom` fields — it is a `def` `∃ Wl, EqNeDispatchInput
∧ … ∧ ∀ cD lds, op.DispatchPost … → ∃ φ…, EqFrontDataNoRepr ∧ EqNeBoxPre`.  It carries
the eq/ne front's dispatch-run / `DispatchPost` / `PhiExtends` / operand-`ValueRepr`
obligations, NOT the ~30-conjunct disjointness/alignment/RAM/window tower.  That shared
geometry lives DOWNSTREAM of `EqResid`, inside its `EqNeBoxPre` tail (which is where an
`ArmPostGeomV`/`ImageGeom` collapse would eventually land) — there is no
`ArmPostGeom`-shaped core here to alias.  So eq/ne is (correctly) already off the
inline-geometry list; no adapter is written for it, and forcing one would fabricate a
false correspondence.  If/when `EqNeBoxPre` is itself refactored onto `ImageGeom`, the
collapse happens there, not via an `EqResid` adapter. -/

#print axioms armPostGeomV_of_armPostGeom
#print axioms armPostGeomV_of_ltResid
#print axioms ltResid_of_armPostGeomV
#print axioms armPostGeomV_of_leResid
#print axioms leResid_of_armPostGeomV
#print axioms armPostGeomV_of_gtResid
#print axioms gtResid_of_armPostGeomV
#print axioms armPostGeomV_of_geResid
#print axioms geResid_of_armPostGeomV
#print axioms armPostGeomV_of_mulResid
#print axioms mulResid_of_armPostGeomV
#print axioms armPostGeomV_of_divResid
#print axioms divResid_of_armPostGeomV
#print axioms armPostGeomV_of_modResid
#print axioms modResid_of_armPostGeomV

end Vsa.Sim
