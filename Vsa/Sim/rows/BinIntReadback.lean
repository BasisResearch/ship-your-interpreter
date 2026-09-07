import Vsa.Sim.rows.ArmPostGeom
import Vsa.Sim.rows.BinDispatchRow

/-!
# Integer operand readback and tail suppliers

`IntOperandsStaged` exposes represented integer tags and payloads after both
children return. The nine staged adapters supply the remaining operator-tail
geometry. Binary entry facts are derived by `EvalEntry.binaryExtras` in the
generated rows.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.Machine (MState Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While
open Vsa.Alloc
open Vsa.Logic
open Vsa.Sim.Code
open Register

namespace Vsa.Sim

/-! ## The kind-2 operand bundle -/

/-- **`IntOperandsStaged`** — what an `.int`/`.int` `TwoSubReturn` exposes about its two
operand value boxes (`sp-944` = right, `sp-968` = left).  Each box carries an `.int`
`ValueRepr`, so each yields:

* a kind tag `read32 = some 2` — the `Value.int` tag (`RuntimeRepr.lean:81`);
* a payload WORD `readI64 (box+8) = some n` — the signed 64-bit operand value (`b` right, `a`
  left), the int the arm feeds the operator dispatch / libgcc seam.

Named-field structure per CLAUDE.md (never an anonymous ∃/∧ tower); modelled field-for-field
on the str sibling `StrOperandsStaged`, with the pointer/`CString` fields replaced by the two
int payload words. -/
structure IntOperandsStaged
    (m : Mem) (spN : Nat) (a b : Int) : Prop where
  /-- RIGHT operand box (`sp-944`) kind tag = 2 (`int`). -/
  rKind : read32 m (spN - 944) = some 2
  /-- RIGHT operand payload word = `b` (the right sub-value's `Int`). -/
  rPay : readI64 m (spN - 944 + 8) = some b
  /-- LEFT operand box (`sp-968`) kind tag = 2 (`int`). -/
  lKind : read32 m (spN - 968) = some 2
  /-- LEFT operand payload word = `a` (the left sub-value's `Int`). -/
  lPay : readI64 m (spN - 968 + 8) = some a

/-- **The kind-2 readback.**  From a `TwoSubReturn` whose two sub-values are `.int b` (right,
at `sp-944`) and `.int a` (left, at `sp-968`), project out the `IntOperandsStaged` bundle: the
two kind tags (= 2) and the two payload words (`b` right, `a` left).

`spN` is `sp.toNat`; the boxes sit at `spN-944` (right) / `spN-968` (left), exactly
`TwoSubReturn`'s staging addresses.  Consumed by the int arms to feed the operator dispatch and
(for mul/div/mod) the libgcc seam.  Destructures the LANDED `TwoSubReturn` def through a single
`obtain` (no positional chains), mirroring `strOperandsStaged_of_twoSubReturn`. -/
theorem intOperandsStaged_of_twoSubReturn
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (m0 : Mem) (c : Config)
    (hTSR : TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b)
      sp r sret v8 v9 v18 m0 c) :
    IntOperandsStaged c.σ.mem sp.toNat a b := by
  -- Peel the tower down to the two sub-value `ValueRepr`s (one `obtain`, no positional chains).
  obtain ⟨_hG, _htick, _hpc, _hra, _hs9, _hsp, _hmi, _hout, _hframe, _hs3spill,
    ⟨_φfm, _φcm, _hpf, _hpc0,
      ⟨_φcr, _hpcr, hvalR⟩, ⟨_φcl, hvalL⟩, _hstoreBundle⟩,
    _hcode, _hslotRa, _hslot8, _hslot9, _hslot18, _hMemExt, _hmemframe⟩ := hTSR
  -- `ValueRepr … (.int n)` is definitionally the `read32 = some 2 ∧ readI64 (·+8) = some n` pair.
  obtain ⟨hrKind, hrPay⟩ := hvalR
  obtain ⟨hlKind, hlPay⟩ := hvalL
  exact
    { rKind := hrKind
      rPay := hrPay
      lKind := hlKind
      lPay := hlPay }

#print axioms intOperandsStaged_of_twoSubReturn

/-! ## Making the readback LOAD-BEARING: the `ArmPostGeomV`-shaped `.add` cell

`AddResid` (`rows/EvalAddRow.lean:688`) is — as MEASURED — byte-identical to
`ArmPostGeom 11 AddSlotPinned`, i.e. `ArmPostGeomV 11 AddSlotPinned Value_intLoaded
0x8000280c 0x8000281c 4`.  The landed forward adapters (`armPostGeom_of_addResid`,
`armPostGeomV_of_armPostGeom`) go `AddResid → ArmPostGeomV`; the reverse iso is not yet
landed for add.  We land it here (clean iso, all fields present — no op-specific extras, since
`.add` has no libgcc callee) so the demo can produce `AddResid` from an `ArmPostGeomV` instance. -/

/-- **`addResid_of_armPostGeomV`** — the reverse iso for the `.add` cell.  `ArmPostGeomV 11
AddSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4` is definitionally `AddResid` (no
op-specific extras).  Mirrors `ltResid_of_armPostGeomV`. -/
theorem addResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 11 AddSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
      sp r sret aExpr c') :
    AddResid gpre N A SL sp r sret aExpr c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

#print axioms addResid_of_armPostGeomV

/-! ## Integer cell from staged geometry

`ArmPostGeomV` supplies the reached result geometry and register frame.
The dispatcher derives source-store facts from the actual left execution. -/
theorem binIntCellResid_add_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 11 AddSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
          sp r sret aExpr c') :
    BinIntCellResid .add AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => addResid_of_armPostGeomV (hResid c' hTSR)

#print axioms binIntCellResid_add_ofStaged

/-! ## Fan-out: the other 8 int cells (they differ ONLY in the `ArmPostGeomV` params + reverse iso)

Each `binIntCellResid_<op>_ofStaged` is the `.add` demo re-instantiated at that op's `ArmPostGeomV`
parameters (`opTok`/`slotDef`/`valLoaded`/`viLo/viHi`/`tblOff`) and reverse iso `<op>Resid_of_…`.
The comparison ops (`lt/le/gt/ge`) use the landed clean reverse isos; the libgcc-seam ops
(`mul/div/mod`) additionally thread their callee-`…Loaded` + `<op>Stk` extras (NOT shared geometry,
per the T1.1 discipline) as explicit hypotheses on the reverse iso.  `.sub` needs its reverse iso,
landed just below (mirror of `addResid_of_armPostGeomV`). -/

/-- Reverse iso for `.sub` (mirror of `addResid_of_armPostGeomV`; clean, no op-specific extras). -/
theorem subResid_of_armPostGeomV
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 12 SubSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
      sp r sret aExpr c') :
    SubResid gpre N A SL sp r sret aExpr c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

#print axioms subResid_of_armPostGeomV

/-- `.sub` cell — `ArmPostGeomV 12 SubSlotPinned` instance. -/
theorem binIntCellResid_sub_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 12 SubSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
          sp r sret aExpr c') :
    BinIntCellResid .sub SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => subResid_of_armPostGeomV (hResid c' hTSR)

/-- `.lt` cell — `ArmPostGeomV 20 LtSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_lt_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr c') :
    BinIntCellResid .lt LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => ltResid_of_armPostGeomV (hResid c' hTSR)

/-- `.le` cell — `ArmPostGeomV 21 LeSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_le_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 21 LeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr c') :
    BinIntCellResid .le LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => leResid_of_armPostGeomV (hResid c' hTSR)

/-- `.gt` cell — `ArmPostGeomV 22 GtSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_gt_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 22 GtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr c') :
    BinIntCellResid .gt GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => gtResid_of_armPostGeomV (hResid c' hTSR)

/-- `.ge` cell — `ArmPostGeomV 23 GeSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_ge_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 23 GeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr c') :
    BinIntCellResid .ge GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  exact fun c' hTSR => geResid_of_armPostGeomV (hResid c' hTSR)

/-- `.mul` cell — `ArmPostGeomV 13 MulSlotPinned Value_intLoaded … 12` + the `__muldi3Loaded` +
`muldiStk` libgcc extras threaded (per-`c'`) into the reverse iso. -/
theorem binIntCellResid_mul_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 13 MulSlotPinned Value_intLoaded 0x8000280c 0x8000281c 12
          sp r sret aExpr c' ∧ __muldi3Loaded c'.σ.mem ∧
          (sp.toNat ≤ 0x80004640 ∨ 0x80004664 ≤ SL.lo)) :
    BinIntCellResid .mul MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  intro c' hTSR
  obtain ⟨hG, hmuldi3, hmuldiStk⟩ := hResid c' hTSR
  exact mulResid_of_armPostGeomV hG hmuldi3 hmuldiStk

/-- `.div` cell — `ArmPostGeomV 14 DivSlotPinned Value_intLoaded … 20` + `__divdi3`/`__umoddi3`/
`__udivdi3`Loaded + `divStk` extras threaded per-`c'`. -/
theorem binIntCellResid_div_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 14 DivSlotPinned Value_intLoaded 0x8000280c 0x8000281c 20
          sp r sret aExpr c' ∧ __divdi3Loaded c'.σ.mem ∧ __umoddi3Loaded c'.σ.mem ∧
          __hidden___udivdi3Loaded c'.σ.mem ∧ (sp.toNat ≤ 0x800046a4 ∨ 0x80004728 ≤ SL.lo)) :
    BinIntCellResid .div DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  intro c' hTSR
  obtain ⟨hG, hdivdi3, humoddi3, hudivdi3, hdivStk⟩ := hResid c' hTSR
  exact divResid_of_armPostGeomV hG hdivdi3 humoddi3 hudivdi3 hdivStk

/-- `.mod` cell — `ArmPostGeomV 15 (SlotPinned …) Value_intLoaded … 20` + `__moddi3`/`__udivdi3`
Loaded + `modStk` extras threaded per-`c'`. -/
theorem binIntCellResid_mod_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 15 (SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8)
          Value_intLoaded 0x8000280c 0x8000281c 20 sp r sret aExpr c' ∧
          __moddi3Loaded c'.σ.mem ∧ __hidden___udivdi3Loaded c'.σ.mem ∧
          (sp.toNat ≤ 0x800046ac ∨ 0x80004764 ≤ SL.lo)) :
    BinIntCellResid .mod ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  intro gpre v8 v9 v18 v19 hFrame
  have hResid := hGeom gpre v8 v9 v18 v19 hFrame
  intro c' hTSR
  obtain ⟨hG, hmoddi3, hudivdi3, hmodStk⟩ := hResid c' hTSR
  exact modResid_of_armPostGeomV hG hmoddi3 hudivdi3 hmodStk

#print axioms binIntCellResid_sub_ofStaged
#print axioms binIntCellResid_lt_ofStaged
#print axioms binIntCellResid_le_ofStaged
#print axioms binIntCellResid_gt_ofStaged
#print axioms binIntCellResid_ge_ofStaged
#print axioms binIntCellResid_mul_ofStaged
#print axioms binIntCellResid_div_ofStaged
#print axioms binIntCellResid_mod_ofStaged

end Vsa.Sim
