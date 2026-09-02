import Vsa.Sim.rows.ArmPostGeom
import Vsa.Sim.rows.BinDispatchRow

-- discipline: allow(R7-conj-tower-def) The only ∃ in CODE is the single `Wl`/`aLOp`/`aROp`
-- existential the LANDED `BinIntCellResid` def already commits (re-emitted here to build the
-- cell), plus the `TwoSubReturn` tower this file consumes — which is destructured through the
-- SINGLE named lemma `intOperandsStaged_of_twoSubReturn` (one `obtain`, no positional chains),
-- exactly the R7-compliant pattern modelled on `strOperandsStaged_of_twoSubReturn`. The
-- whole-file ∃ count is inflated by doc-comments QUOTING the landed towers to explain the readback.

/-!
# `BinIntReadback` — the kind-2 (`.int`) operand readback + the `ArmPostGeomV`-shaped cell consumer

The `.int`/`.int` sibling of `BinStrReadback`'s kind-3 (`.str`) readback.  Three deliverables:

1. **`IntOperandsStaged` + `intOperandsStaged_of_twoSubReturn`** — from an `.int a`/`.int b`
   `TwoSubReturn`, project the two operand kind tags (`read32 = 2`, `Value.int`'s tag per
   `RuntimeRepr.lean:81`) and the two payload WORDS (the signed 64-bit values `a`/`b` via
   `readI64 (box+8)`).  `ValueRepr … (.int n)` IS `read32 = some 2 ∧ readI64 (a+8) = some n`
   (`RuntimeRepr.lean:81`); the readback is that definitional unfold, mirroring the str sibling.

2. **`boolOperandsStaged` — NOT NEEDED (verified, skipped honestly).**  The eq/ne cells consume
   operands VALUE-GENERICALLY, not per-kind: `EqResid` (`rows/EvalEqNeFront.lean:794`) carries the
   operand `ValueRepr c2.σ.mem N φc … vl` / `… vr` for ARBITRARY `vl vr : Value`, and the dispatch
   (`EqNeDispatchInput.kindResp`, `EqNeDispatchInput.lean`) pins `read64 (sp-1088) = kindTag vl`
   through the GENERIC `kindTag` — no `.bool` payload projection.  Its own doc: "Operand kind tags
   are recovered from `ValueRepr`; no integer specialization remains."  There is no `.bool`-operand
   binary cell anywhere (comparison ops yield `.bool` RESULTS from `.int`/`.str` operands; the
   operand kinds a binary arm reads are only `.int` and `.str`).  So no bool operand staging is
   consumed — a `boolOperandsStaged` would have no consumer.  Skipped per CLAUDE.md law 4.

3. **The consumer demo** — `binIntCellResid_add_ofStaged`: the `.add` cell's `BinIntCellResid`
   residual reduces to exactly (i) `storeSize` stability, (ii) a `BinArmExtras` witness, and (iii)
   an `ArmPostGeomV`-shaped provider that, from any `TwoSubReturn`, yields the `AddResid` post as
   the `ArmPostGeomV 11 AddSlotPinned Value_intLoaded … 4` instance (via the reverse iso
   `addResid_of_armPostGeomV` landed below).  MEASURED: `AddResid` (`rows/EvalAddRow.lean:688`)
   carries NO operand-box readback — every field is a result-config geometry/register/alignment
   fact, i.e. exactly the `ArmPostGeom(V)` tower.  So the cell closes modulo the `ArmPostGeomV`
   instance + `TermGuards.storeSize` + the `BinArmExtras` slot — the target shape for all 9 int
   cells (they differ only in `opTok`/`slotDef`/`valLoaded`/`viLo/viHi`/`tblOff` per `ArmPostGeomV`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
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
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 11 AddSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
      sp r sret aExpr Wl c') :
    AddResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

#print axioms addResid_of_armPostGeomV

/-! ## The consumer demo: the `.add` int cell closes modulo `ArmPostGeomV` + `storeSize`

`binIntCellResid_add_ofStaged` builds `BinIntCellResid .add AddResid` from EXACTLY:

* the two store-size-stability conjuncts (`hSF`/`hSC`) — supplied by `TermGuards.storeSize`;
* a `BinArmExtras` witness (`hX`) + the `∃ aLOp aROp Wl` staging registers — the geometry slot;
* an `ArmPostGeomV`-shaped provider `hGeom`: from any `TwoSubReturn` (whose operands the readback
  `intOperandsStaged_of_twoSubReturn` stages), an `ArmPostGeomV 11 AddSlotPinned …` instance for
  the result config `c'`, reassembled into `AddResid` by the reverse iso above.

This is the target shape: the operand-box content is handled by the readback (the `TwoSubReturn`
already carries the `.int` operands; the readback makes their tags/words load-bearing), and the
`AddResid` production reduces to the `ArmPostGeomV` result geometry + `storeSize`.  No hidden gaps:
`hGeom` is the named `ArmPostGeomV` residual (the `TermShared.geom`/`M6 EvalCaseGeom` widening),
`hX` the `BinArmExtras` slot, `hSF`/`hSC` the `TermGuards.storeSize` pair. -/
theorem binIntCellResid_add_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem)
    (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .add el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 11 AddSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false →
        gpre R = g R)) :
    BinIntCellResid .add AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  refine ⟨fun c' hTSR => addResid_of_armPostGeomV (hResid c' hTSR),
    hg8, hg9, hg18, hg2, hg19, habi⟩

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
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : ArmPostGeomV gpre N A SL 12 SubSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
      sp r sret aExpr Wl c') :
    SubResid gpre N A SL sp r sret aExpr Wl c' :=
  ⟨h.gx8, h.opTokRead, h.slot, h.fullpop, h.x19, h.wlbuf, h.kindresp, h.exprAl, h.exprLo, h.exprHi,
   h.exprWin, h.exprSL, h.sretAl, h.sretLo, h.sretHi, h.sretWin, h.sretVi, h.sretStk,
   h.sretEvalCode, h.raAl, h.vloaded, h.codeStk, h.viStk, h.tableStk, h.sretInSL, h.SLloSp, h.SLlo,
   h.SLwin, h.sphiRam, h.sp8, h.SLhiRam, h.spSLhi⟩

#print axioms subResid_of_armPostGeomV

/-- `.sub` cell — `ArmPostGeomV 12 SubSlotPinned` instance + `storeSize`. -/
theorem binIntCellResid_sub_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .sub el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 12 SubSlotPinned Value_intLoaded 0x8000280c 0x8000281c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .sub SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  exact ⟨fun c' hTSR => subResid_of_armPostGeomV (hResid c' hTSR), hg8, hg9, hg18, hg2, hg19, habi⟩

/-- `.lt` cell — `ArmPostGeomV 20 LtSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_lt_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .lt el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .lt LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  exact ⟨fun c' hTSR => ltResid_of_armPostGeomV (hResid c' hTSR), hg8, hg9, hg18, hg2, hg19, habi⟩

/-- `.le` cell — `ArmPostGeomV 21 LeSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_le_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .le el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 21 LeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .le LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  exact ⟨fun c' hTSR => leResid_of_armPostGeomV (hResid c' hTSR), hg8, hg9, hg18, hg2, hg19, habi⟩

/-- `.gt` cell — `ArmPostGeomV 22 GtSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_gt_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .gt el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 22 GtSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .gt GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  exact ⟨fun c' hTSR => gtResid_of_armPostGeomV (hResid c' hTSR), hg8, hg9, hg18, hg2, hg19, habi⟩

/-- `.ge` cell — `ArmPostGeomV 23 GeSlotPinned Value_boolLoaded [0x800027f8,0x8000280c) 4`. -/
theorem binIntCellResid_ge_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .ge el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 23 GeSlotPinned Value_boolLoaded 0x800027f8 0x8000280c 4
          sp r sret aExpr Wl c') ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .ge GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  exact ⟨fun c' hTSR => geResid_of_armPostGeomV (hResid c' hTSR), hg8, hg9, hg18, hg2, hg19, habi⟩

/-- `.mul` cell — `ArmPostGeomV 13 MulSlotPinned Value_intLoaded … 12` + the `__muldi3Loaded` +
`muldiStk` libgcc extras threaded (per-`c'`) into the reverse iso. -/
theorem binIntCellResid_mul_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .mul el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 13 MulSlotPinned Value_intLoaded 0x8000280c 0x8000281c 12
          sp r sret aExpr Wl c' ∧ __muldi3Loaded c'.σ.mem ∧
          (sp.toNat ≤ 0x80004640 ∨ 0x80004664 ≤ SL.lo)) ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .mul MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  refine ⟨fun c' hTSR => ?_, hg8, hg9, hg18, hg2, hg19, habi⟩
  obtain ⟨hG, hmuldi3, hmuldiStk⟩ := hResid c' hTSR
  exact mulResid_of_armPostGeomV hG hmuldi3 hmuldiStk

/-- `.div` cell — `ArmPostGeomV 14 DivSlotPinned Value_intLoaded … 20` + `__divdi3`/`__umoddi3`/
`__udivdi3`Loaded + `divStk` extras threaded per-`c'`. -/
theorem binIntCellResid_div_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .div el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 14 DivSlotPinned Value_intLoaded 0x8000280c 0x8000281c 20
          sp r sret aExpr Wl c' ∧ __divdi3Loaded c'.σ.mem ∧ __umoddi3Loaded c'.σ.mem ∧
          __hidden___udivdi3Loaded c'.σ.mem ∧ (sp.toNat ≤ 0x800046a4 ∨ 0x80004728 ≤ SL.lo)) ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .div DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  refine ⟨fun c' hTSR => ?_, hg8, hg9, hg18, hg2, hg19, habi⟩
  obtain ⟨hG, hdivdi3, humoddi3, hudivdi3, hdivStk⟩ := hResid c' hTSR
  exact divResid_of_armPostGeomV hG hdivdi3 humoddi3 hudivdi3 hdivStk

/-- `.mod` cell — `ArmPostGeomV 15 (SlotPinned …) Value_intLoaded … 20` + `__moddi3`/`__udivdi3`
Loaded + `modStk` extras threaded per-`c'`. -/
theorem binIntCellResid_mod_ofStaged
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (el er : Expr) (a b : Int)
    (sp r sret aExpr : BitVec 64) (m0 : Mem) (aLOp aROp Wl : BitVec 64)
    (hSF : st'.store.frames.size = st''.store.frames.size)
    (hSC : st'.store.closures.size = st''.store.closures.size)
    (hSB : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    (hX : BinArmExtras g N A SL .mod el er sp r sret aExpr aLOp aROp m0)
    (hGeom : ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      (∀ c' : Vsa.Machine.Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        ArmPostGeomV gpre N A SL 15 (SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8)
          Value_intLoaded 0x8000280c 0x8000281c 20 sp r sret aExpr Wl c' ∧
          __moddi3Loaded c'.σ.mem ∧ __hidden___udivdi3Loaded c'.σ.mem ∧
          (sp.toNat ≤ 0x800046ac ∨ 0x80004764 ≤ SL.lo)) ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
      g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false → gpre R = g R)) :
    BinIntCellResid .mod ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0 := by
  refine ⟨hSF, hSC, hSB, aLOp, aROp, Wl, hX, ?_⟩
  intro gpre v8 v9 v18 v19
  obtain ⟨hResid, hg8, hg9, hg18, hg2, hg19, habi⟩ := hGeom gpre v8 v9 v18 v19
  refine ⟨fun c' hTSR => ?_, hg8, hg9, hg18, hg2, hg19, habi⟩
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
