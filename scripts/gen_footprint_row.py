#!/usr/bin/env python3
"""Generate one footprint-row module per `scripts/footprint_rows.tsv` line.

A footprint row is the footprint-carrying sibling of a landed recursor row (IH
tower, Level 1): the SAME execution, returning `EvalExitF F` instead of
`EvalExitD`, plus the arm's `EvalIHF noArenaFoot` supplier.  For the arm `<arm>`
the module `Vsa/Sim/rows/Eval<Arm>RowFootprint.lean` holds

* `<arm>NodeFoot` and `<arm>NodeFoot_noArena` (families that do not share a node
  footprint with a sibling arm);
* `eval<Arm>SimF` — the landed sim composed from the footprint-carrying blocks
  (`blockB_*_footprint` / `blockC_*_footprint` / `blockD_v_rec_footprint`);
* the row at `EvalEntry` (`binRow_<op>F` / `<arm>RowF`);
* the arm's contract and supplier (`Bin<Op>CellF` + `bin<Op>CellF_of` for the
  integer cells, `eval<Arm>IHF` for the one-child arms).

Emission is per FAMILY: one template (verbatim from the landed modules) plus the
arm's slot values.  Scalar slots — result value, residual, guards, cell/node
footprints, supplier, per-arm extras — come from the TSV; the per-arm proof
fragments that differ structurally between two arms of the same family (block
calls, callee-pin transports, argument lists) live in `ARM_FRAGMENTS`.

Adding a NEW ARM of an existing family is a TSV line (plus its `ARM_FRAGMENTS`
entry when the family's proof text is arm-shaped).  Adding a NEW FAMILY (e.g.
the allocating `allocFoot` family for `fn`/`call`/string-`add`, or an exec-side
arm) is: one `TEMPLATES` entry — the landed module with its per-arm names
replaced by `%%SLOT%%` — one `SLOTS_FROM_TSV` entry naming the slots the TSV
fills, and one TSV line per arm.  `--check` fails on any drift.
"""

from __future__ import annotations

import argparse
import difflib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TSV = ROOT / "scripts/footprint_rows.tsv"
OUTPUT_DIR = ROOT / "Vsa/Sim/rows"
COLUMNS = ["arm", "family", "module", "result", "resid", "guard", "guardfn", "guardpf",
           "cell", "shared", "node", "box", "supplier", "extras", "notes"]
ARM_RE = re.compile(r"^[a-z][A-Za-z]*$")

TEMPLATES: dict[str, str] = {
    'int': r'''import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.rows.Eval%%OPC%%Row
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.BinaryPostEntry
import Vsa.Sim.BinaryArmFrame
import Vsa.Sim.BinaryHeadFootprint

/-!
# `Eval%%OPC%%RowFootprint` — the footprint-carrying exit of the `.%%OP%%` integer cell (IH tower, Level 1)

The footprint sibling of the `.%%OP%%` integer row (`rows/Eval%%OPC%%Row.lean`), in the
shape of pilot B (`rows/EvalLtRowFootprint.lean`): the same execution as
`eval%%OPC%%Sim` / `binRow_%%OP%%`, returning `EvalExitF` instead of `EvalExitD`.
```
m0   ─ head (BinaryHeadFootprintSupply) ─▸  mret   binaryHeadFoot Fl Fr
mret ─ blockC_%%OP%%_footprint             ─▸  mpre   %%OP%%CellFoot (three temporaries ∪ box)
mpre ─ blockD_v_rec_footprint            ─▸  exit   inherited
```
For two non-allocating children the node is non-allocating (`noArenaFoot`).
`Bin%%OPC%%CellF` is the cell contract at `EvalIHF noArenaFoot`; `bin%%OPC%%CellF_of`
discharges it from the head footprint premise and the landed `BinIntCell .%%OP%%`
residual supplier (`ScaffoldRows.field_hI%%OPC%%`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- The `.%%OP%%` node's footprint: the head's plus the cell's. -/
def %%OP%%NodeFoot (Fl Fr : FootFam) : FootFam := fun SL A sp sret k =>
  binaryHeadFoot Fl Fr SL A sp k ∨ %%OP%%CellFoot sp sret k

/-- Two non-allocating children make a non-allocating node. -/
theorem %%OP%%NodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : %%OP%%NodeFoot noArenaFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (binaryHeadFoot_noArena h k hh)
  · exact %%SHAREDNOARENA%% h k hc

/-- **`eval%%OPC%%SimF`** — `eval%%OPC%%Sim` with the node's footprint retained:
`head ≫ blockC_%%OP%%_footprint ≫ blockD_v_rec_footprint`. -/
theorem eval%%OPC%%SimF (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
%%GUARDBINDERS%%    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF Fl st d env el st' (.int a))
    (hIHr : EvalIHF Fr st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .%%OP%% el er) st'' %%RESULT%%)
    (hResid : ∀ c' : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
      %%RESID%% gpre N A SL sp r sret aExpr c') :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .%%OP%% el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary .%%OP%% el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitF (%%OP%%NodeFoot Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' %%RESULT%% sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  -- the head, with its footprint
  obtain ⟨c2, hs2, hReturned⟩ :=
    hHead gouter gpre N A SL φf φc st st' st'' d env .%%OP%% el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr
      (intLeftSurvives a hBE.sproom hBE.arenaStk)
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  obtain ⟨hData, hHeadFoot⟩ := hReturned.extra
  have hR : %%RESID%% gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c2 hTS).p8
  -- the cell, with its footprint from the actual return memory
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD, hCellFoot⟩ :=
    blockC_%%OP%%_footprint gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0 c2.σ.mem%%GUARDARGS%%
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hData,
        hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode,
        hR.raAl, %%VFIELDS%%, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge, rfl⟩
  -- the epilogue inherits the composed footprint
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (%%OP%%NodeFoot Fl Fr SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' %%RESULT%% sp r sret v8 v9 v18
      c2.σ.sailOutput m0 c3 ⟨mpre, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono hEvalE
  have hleftMono := evalE_store_mono hLeft
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hleftMono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hleftMono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size :=
    hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' %%RESULT%% sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  refine ⟨c4, ((hs2.trans hs3).trans hs4), ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- **`binRow_%%OP%%F`** — `binRow_%%OP%%` at two non-allocating children: the node is
non-allocating (`EvalExitF noArenaFoot`).  The residual is taken at the actual entry
config (`BinIntCellResid`, the shape `BinIntCell .%%OP%%` supplies). -/
theorem binRow_%%OP%%F (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
%%GUARDBINDERS%%    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF noArenaFoot st d env el st' (.int a))
    (hIHr : EvalIHF noArenaFoot st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .%%OP%% el er) st'' %%RESULT%%)
    (hPost : ∀ c : Config,
      EvalEntry g N A SL φf φc st d env (.binary .%%OP%% el er) sp r sret aEnv aExpr m0 c →
      BinIntCellResid .%%OP%% %%RESID%% g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .%%OP%% el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' %%RESULT%% sp r sret m0) := by
  intro c hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env .%%OP%% el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    eval%%OPC%%SimF noArenaFoot noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env
      el er a b sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' c1.σ.sailOutput m0
%%GUARDPASS%%      hLeft hIHl hIHr hEvalE (hPost c hc gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR,
        hArmFrame.saved8, hArmFrame.saved9, hArmFrame.saved18, hArmFrame.savedSp,
        hArmFrame.saved19, hArmFrame.bridge⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result,
    hExitF.extra.mono (%%OP%%NodeFoot_noArena hsproom)⟩

/-- The footprint-carrying `.%%OP%%` integer cell contract: `EvalIHF noArenaFoot` for the
node from `EvalIHF noArenaFoot` children (the `EvalIHF` form of `BinIntCell .%%OP%%`). -/
def Bin%%OPC%%CellF : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (st' st'' : Vsa.While.St) (a b : Int),
%%GUARDPROPS%%    EvalE st d env el st' (.int a) →
    EvalE st' d env er st'' (.int b) →
    EvalIHF noArenaFoot st d env el st' (.int a) →
    EvalIHF noArenaFoot st' d env er st'' (.int b) →
    EvalE st d env (.binary .%%OP%% el er) st'' %%RESULT%% →
    EvalIHF noArenaFoot st d env (.binary .%%OP%% el er) st'' %%RESULT%%

/-- **The footprint-carrying cell supplier.**  The `.%%OP%%` integer cell at
`EvalIHF noArenaFoot`, from the head footprint premise and the landed residual
supplier `BinIntCell .%%OP%% %%RESID%% %%GUARDFN%%` (`ScaffoldRows.field_hI%%OPC%%`). -/
theorem bin%%OPC%%CellF_of (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (hCell : BinIntCell .%%OP%% %%RESID%% %%GUARDFN%%) : Bin%%OPC%%CellF := by
  intro st d env el er st' st'' a b %%GUARDNAMES%%hEl hEr ihL ihR hEvalE
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  exact binRow_%%OP%%F hHead g N A SL φf φc st st' st'' d env el er a b
    sp r sret aEnv aExpr m0 %%GUARDNAMES%%hEl ihL ihR hEvalE
    (fun c hc => hCell g N A SL φf φc st st' st'' d env el er a b hEl hEr ihL.forget ihR.forget
      %%GUARDPF%% sp r sret aEnv aExpr m0 c hc)

#print axioms %%OP%%NodeFoot_noArena
#print axioms eval%%OPC%%SimF
#print axioms binRow_%%OP%%F
#print axioms bin%%OPC%%CellF_of

end Vsa.Sim
''',
    'intPilot': r'''import Vsa.While.StoreBodiesBoundPreservation
import %%ROWMOD%%
import Vsa.Sim.BinaryPostEntry
import Vsa.Sim.BinaryArmFrame
import Vsa.Sim.BinaryHeadFootprint

/-!
# `%%MODULE%%` — pilot B of the footprint-carrying exit (IH tower, Level 1)

The footprint sibling of the `.%%OP%%` integer row (`rows/EvalLtRow.lean`): the same
execution as `%%SIM%%` / `%%ROW%%`, returning `EvalExitF` instead of
`EvalExitD`.  The node's footprint is derived from the layer exactly as in
pilot A (`StrCmpCellFootprint.lean`):
```
m0  ─ head (BinaryHeadFootprintSupply) ─▸  mret   binaryHeadFoot Fl Fr
mret ─ %%CELL%%              ─▸  mpre   %%CELLFOOT%% (three temporaries ∪ box)
mpre ─ blockD_v_rec_footprint           ─▸  exit   inherited
```
For two non-allocating children the node is non-allocating (`noArenaFoot`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- The `.%%OP%%` node's footprint: the head's plus the cell's. -/
def %%NODEFOOT%% (Fl Fr : FootFam) : FootFam := fun SL A sp sret k =>
  binaryHeadFoot Fl Fr SL A sp k ∨ %%CELLFOOT%% sp sret k

/-- Two non-allocating children make a non-allocating node. -/
theorem %%NODEFOOT%%_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : %%NODEFOOT%% noArenaFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (binaryHeadFoot_noArena h k hh)
  · exact %%SHAREDNOARENA%% h k hc

/-- **`%%SIMF%%`** — `%%SIM%%` with the node's footprint retained:
`head ≫ %%CELL%% ≫ blockD_v_rec_footprint`. -/
theorem %%SIMF%% (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF Fl st d env el st' (.int a))
    (hIHr : EvalIHF Fr st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .%%OP%% el er) st'' %%RESULT%%)
    (hResid : ∀ c' : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
      %%RESID%% gpre N A SL sp r sret aExpr c') :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .%%OP%% el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary .%%OP%% el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitF (%%NODEFOOT%% Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' %%RESULT%% sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  -- the head, with its footprint
  obtain ⟨c2, hs2, hReturned⟩ :=
    hHead gouter gpre N A SL φf φc st st' st'' d env .%%OP%% el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr
      (intLeftSurvives a hBE.sproom hBE.arenaStk)
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  obtain ⟨hData, hHeadFoot⟩ := hReturned.extra
  have hR : %%RESID%% gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c2 hTS).p8
  -- the cell, with its footprint from the actual return memory
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD, hCellFoot⟩ :=
    %%CELL%% gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0 c2.σ.mem
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hData,
        hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode,
        hR.raAl, %%VFIELDS%%, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge, rfl⟩
  -- the epilogue inherits the composed footprint
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (%%NODEFOOT%% Fl Fr SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' %%RESULT%% sp r sret v8 v9 v18
      c2.σ.sailOutput m0 c3 ⟨mpre, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono hEvalE
  have hleftMono := evalE_store_mono hLeft
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hleftMono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hleftMono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size :=
    hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' %%RESULT%% sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  refine ⟨c4, ((hs2.trans hs3).trans hs4), ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- **`%%ROWF%%`** — `%%ROW%%` at two non-allocating children: the node is
non-allocating (`EvalExitF noArenaFoot`). -/
theorem %%ROWF%% (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF noArenaFoot st d env el st' (.int a))
    (hIHr : EvalIHF noArenaFoot st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .%%OP%% el er) st'' %%RESULT%%)
    (hPost : ∀ (gpre : (R : Register) → Option (RegisterType R))
        (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        %%RESID%% gpre N A SL sp r sret aExpr c') :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .%%OP%% el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' %%RESULT%% sp r sret m0) := by
  intro c hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env .%%OP%% el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    %%SIMF%% noArenaFoot noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env
      el er a b sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE (hPost gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR,
        hArmFrame.saved8, hArmFrame.saved9, hArmFrame.saved18, hArmFrame.savedSp,
        hArmFrame.saved19, hArmFrame.bridge⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result,
    hExitF.extra.mono (%%NODEFOOT%%_noArena hsproom)⟩

#print axioms %%NODEFOOT%%_noArena
#print axioms %%SIMF%%
#print axioms %%ROWF%%

end Vsa.Sim
''',
    'unary': r'''import %%SIMMOD%%
import Vsa.Sim.UnaryHeadFootprint

/-!
# `%%MODULE%%` — the footprint sibling of %%ARMDESC%% (IH tower, Level 1)

%%DOCINTRO%%
```
m0   ─ blockB_unary_footprint    ─▸  mret   unaryHeadFoot F  (stack window ∪ child)
%%DIAGCELL%%
mpre ─ blockD_v_rec_footprint    ─▸  exit   inherited
```
For a non-allocating child the node is non-allocating (`noArenaFoot`), and the
`EvalIHF noArenaFoot` supplier `%%IHF%%` closes the arm at that family.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- %%NODEDESC%%: the head's plus the cell's. -/
def %%NODEFOOT%% (F : FootFam) : FootFam := fun SL A sp sret k =>
  unaryHeadFoot F SL A sp k ∨ %%CELLFOOT%% sp sret k

/-- A non-allocating child makes a non-allocating node. -/
theorem %%NODEFOOT%%_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : %%NODEFOOT%% noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (unaryHeadFoot_noArena h k hh)
  · exact %%SHAREDNOARENA%% h k hc

/-- **`%%SIMF%%`** — `%%SIM%%` with the node's footprint retained:
`blockA_k ≫ blockB_unary_footprint ≫ %%CELL%% ≫ blockD_v_rec_footprint`. -/
theorem %%SIMF%% (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) %%VALBINDER%%
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem)
    %%SIMEVALBINDER%%
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0 c ∧
        %%EXTRASTY%%)
      (EvalExitF (%%NODEFOOT%% F) g N A SL φf φc st.store.frames.size st.store.closures.size
        st' %%RESULT%% sp r sret m0) := by
  intro c ⟨hc, hx⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0 ===
  have hkm0 : read32 m0 aExpr.toNat = some 8 := %%KINDLEMMA%% (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, hx13c1⟩ :=
    blockA_k g N A SL φf φc st env %%EXPR%% 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl, hnb⟩ := hcl
        have hvicodeD := hc.vicode_stack_disjoint
        have htableD := hc.table_stack_disjoint
        refine ⟨loaded_int_writeMap8 mem a8 dd (by omega) hvi, ?_, ?_⟩
        · exact intSlot_writeMap8 mem a8 dd (by simp only [jumpTableBase]; omega) hsl
        · exact nbsPins_writeMap8 mem a8 dd (by omega) (by omega) hnb)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.envReg⟩⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat %%EXPR%% :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (%%OPTOK%%) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some aOperand.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aOperand.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hpeq : p = aOperand.toNat := by
    have := hpayMent.symm.trans hpayMent'; exact Option.some.inj this
  subst hpeq
  have hOperandReprMent : ExprRepr ment aOperand.toNat esub := hsubReprMent
%%GROUNDNOTE%%  have hsp1088N : 1088 ≤ sp.toNat := by
    have := hx.sp_headroom; have := hc.stack_ram.1; omega
  have hspsubN : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsubsretN : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat
      = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088N
  have hgroundChild : EvalGround ment SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub :=
    (hc.mem ▸ hc.ground).child_at
      (fun lo hi hin => exprIn_unary_child hin aOperand.toNat hpayMent')
      hMentM0 ((hc.mem ▸ hc.ground).stack_bytes_extend _hpresM)
      hc.table_stack_disjoint hx.sp_SLhi
      (by omega)
      (by rw [hsubsretN]; have := hx.sp_headroom; have := hc.stack_ram.1; omega)
      (by rw [hsubsretN]; omega)
%%BLOCKB%%      hc.env_valid (hc.envset_defined_frame hbridge) hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hpayMent', hOperandReprMent, hgroundChild, hx.expr24,
        hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega), hx.arena_stk, hx.arena_code,
%%BUDGETNOTE%%        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.unary %%UNOP%% esub).stackNeed
                = evalFrame + esub.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            simp only [h1, h2, evalFrame]; omega),
        Expr.bodiesBound_unary hc.expr_bodies,
        hc.store_bodies, _hpresM⟩
  obtain ⟨mcall, hSubR, hCallMemory⟩ := hReturned.result
  have hHeadFoot := hReturned.extra
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hCallMemory.outside
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1  -- discipline: allow(R6-anon-projection-tower) the landed `SubEvalReturn` tower has no named destructurer; same projection as `%%SIM%%`
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
%%TRANSPORTS%%  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hMemExtM0mc : MemExtends m0 mcall := hCallMemory.presence
  have hExprMcall : ExprRepr mcall aExpr.toNat %%EXPR%% :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
%%CPRE%%  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD, hCellFoot⟩ :=
%%BLOCKCHEAD%%      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hMemExtM0mc,
        hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
%%CARGS1%%        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
%%CARGS2%%        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge, rfl⟩
%%DCOMMENT%%  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (%%NODEFOOT%% F SL A sp.toNat sret.toNat)
      g N A SL φfe φce st' %%RESULT%% sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := %%HEVALUSE%%
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' %%RESULT%% sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

/-- **`%%ROWF%%`** — %%ROWFDESC%% -/
theorem %%ROWF%%
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) %%VALBINDER%%
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hIH : EvalIHF noArenaFoot st d env esub st' %%CHILDVAL%%)
    (hEvalE : EvalE st d env %%EXPR%% st' %%RESULT%%) :
    Triple
      (EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st' %%RESULT%% sp r sret m0) := by
  intro c hc
  obtain ⟨aOperand, hx⟩ := %%EXTRASGET%%
  obtain ⟨c', hs, hExitF⟩ :=
    %%SIMF%% noArenaFoot g N A SL φf φc st st' d env %%SIMCALLARGS%%
      aOperand m0 hIH hEvalE c ⟨hc, hx⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hx.sp_headroom; omega
  exact ⟨c', hs, hExitF.result, hExitF.extra.mono (%%NODEFOOT%%_noArena hsproom)⟩

/-- **The `EvalIHF noArenaFoot` supplier for %%ARMDESC%%**: a non-allocating
child derivation yields a non-allocating parent. -/
theorem %%IHF%% (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) %%VALBINDER%%
    (hE : EvalE st d env esub st' %%CHILDVAL%%)
    (hIH : EvalIHF noArenaFoot st d env esub st' %%CHILDVAL%%) :
    EvalIHF noArenaFoot st d env %%EXPR%% st' %%RESULT%% :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    %%ROWF%% g N A SL φf φc st st' d env %%SIMCALLARGS%% m0 hIH
      (%%CTOR%% %%CTORARGS%%))

#print axioms %%NODEFOOT%%_noArena
#print axioms %%SIMF%%
#print axioms %%ROWF%%
#print axioms %%IHF%%

end Vsa.Sim
''',
    'logicalShort': r'''import %%SIMMOD%%
import Vsa.Sim.LogicalHeadFootprint
import Vsa.Sim.LogicalShortEntry

/-!
# `%%MODULE%%` — the footprint sibling of %%ARMDESC%% (IH tower, Level 1)

The same execution as %%SIMSRC%%, returning `EvalExitF` instead
of `EvalExitD`:
```
m0   ─ blockB_logical_footprint  ─▸  mret   logicalHeadFoot F  (stack window ∪ left child)
mret ─ %%CELL%%  ─▸  mpre   truthyCellFoot     (24-byte argument copy ∪ box)
mpre ─ blockD_v_rec_footprint    ─▸  exit   inherited
```
For a non-allocating left child the node is non-allocating (`noArenaFoot`), and the
`EvalIHF noArenaFoot` supplier `%%IHF%%` closes the arm at that family.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- **`%%SIMF%%`** — `%%SIM%%` with the node's footprint retained:
`blockA_k ≫ blockB_logical_footprint ≫ %%CELL%% ≫ blockD_v_rec_footprint`. -/
theorem %%SIMF%% (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (sp r sret aEnv aExpr aLeft : BitVec 64)
    (m0 : Mem)
    (%%HVL%% : %%TRUTHYEQ%%)
    (hIH : EvalIHF F st d env el st' vl)
    (_hEvalE : EvalE st d env %%EXPR%% st' %%RESULT%%) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0 c ∧
        %%EXTRASTY%% N A SL el er vl sp sret aExpr aLeft m0)
      (EvalExitF (logShortNodeFoot F) g N A SL φf φc st.store.frames.size
        st.store.closures.size st' %%RESULT%% sp r sret m0) := by
  intro c ⟨hc, hx⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  have hkm0 : read32 m0 aExpr.toNat = some 7 := %%KINDLEMMA%% (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, _hx13⟩ :=
    blockA_k g N A SL φf φc st env %%EXPR%% 7 (0x8000355c#64) LogicalArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot7
      ⟨hx.int_loaded, hx.intslot, hx.truthy_loaded, hx.bool_loaded, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl =>
        logicalCallee_writeMap8 mem a8 dd
          (by have := hx.vicode_stk; omega)
          (by simp only [jumpTableBase]; have := hx.table_stk; omega)
          (by have := hx.truthy_stk; omega)
          (by have := hx.boolcode_stk; omega)
          (by have := hx.vicode_stk; omega)
          (by have := hx.table_stk; omega) hcl)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.envReg⟩⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
%%X13NOTE%%  have hx13c1 : c1.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) := _hx13
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat %%EXPR%% :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (%%OPTOK%%) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hlptrM' : read64 ment (aExpr.toNat + 16) = some aLeft.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aLeft.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  -- === block B: arm head + LEFT recursive call ⋈ IH → SubEvalReturn @0x8000356c ===
  obtain ⟨c2, hs2, hReturned⟩ :=
    blockB_logical_footprint F g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env %%LOGARGS%% vl
      sp r sret aExpr aEnv aLeft v8 v9 v18 c.σ.sailOutput m0
      hc.env_valid (hc.envset_defined_frame hbridge) hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hlptrM',
        (fun m' hag => hx.left_survives m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))),
        -- WAVE 47i: the parent ground at the arm entry (ONE kit call).
        ((hc.mem ▸ hc.ground).transport_offstack hc.table_stack_disjoint
          hx.sp_SLhi ((hc.mem ▸ hc.ground).stack_bytes_extend _hpresM) hMentM0),
        hx.expr24,
        hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code,
        -- ITEM ZERO B1: the LEFT child budget, DERIVED from the entry's
        -- budgeted fields (`StackOK.child` + `bodiesBound_logical`).
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.logical LogOp%%LOGARGS%%).stackNeed
                = evalFrame + max el.stackNeed er.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            have hm := Nat.le_max_left el.stackNeed er.stackNeed
            simp only [h1, h2, evalFrame]; omega),
        (Expr.bodiesBound_logical hc.expr_bodies).1,
        hc.store_bodies⟩
  obtain ⟨mcall, hSubR, _hEnvSlot, hMemExtM0mc, hMcallM0stk⟩ := hReturned.result
  have hHeadFoot := hReturned.extra
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1  -- discipline: allow(R6-anon-projection-tower) the landed `SubEvalReturn` tower has no named destructurer; same projection as `%%SIM%%`
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hExprMcall : ExprRepr mcall aExpr.toNat %%EXPR%% :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  have hBufExtras : LogicalBufExtras sp :=
    ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega)⟩
  -- === block C: %%CBLOCKDESC%% → PreEpilogueVD %%RESULTV%% @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD, hCellFoot⟩ :=
    %%CELL%% (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size
      st.store.closures.size st' vl sp r sret aExpr v8 v9 v18
      c2.σ.sailOutput el er m0 c2.σ.mem (hc.mem ▸ hc.sret_words) %%HVL%%
      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hMemExtM0mc,
        hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVtruthyMcall, hVboolMcall, hBufExtras,
        hx.truthy_stk, hx.boolcode_stk, hx.sret_boolcode, hx.truthy_arena, hx.bool_arena,
        hx.code_stk, hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge, rfl⟩
  -- === block D: shared epilogue → EvalExitD %%RESULTV%% (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (logShortNodeFoot F SL A sp.toNat sret.toNat)
      g N A SL φfe φce st' %%RESULT%% sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := evalE_store_mono _hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' %%RESULT%% sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

/-- **`%%ROWF%%`** — %%ARMDESC%% from `EvalEntry` at a non-allocating left child:
the node is non-allocating (`EvalExitF noArenaFoot`). -/
theorem %%ROWF%%
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (%%HVL%% : %%TRUTHYEQ%%)
    (hIH : EvalIHF noArenaFoot st d env el st' vl)
    (hEvalE : EvalE st d env %%EXPR%% st' %%RESULT%%) :
    Triple
      (EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st' %%RESULT%% sp r sret m0) := by
  intro c hc
  obtain ⟨aLeft, hx⟩ := hc.logicalShortExtras vl
  obtain ⟨c', hs, hExitF⟩ :=
    %%SIMF%% noArenaFoot g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr
      aLeft m0 %%HVL%% hIH hEvalE c ⟨hc, hx⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hx.sp_headroom; omega
  exact ⟨c', hs, hExitF.result, hExitF.extra.mono (logShortNodeFoot_noArena hsproom)⟩

/-- **The `EvalIHF noArenaFoot` supplier for %%ARMDESC%%**: a non-allocating
left child derivation yields a non-allocating parent. -/
theorem %%IHF%% (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (hE : EvalE st d env el st' vl) (%%HVL%% : %%TRUTHYEQ%%)
    (hIH : EvalIHF noArenaFoot st d env el st' vl) :
    EvalIHF noArenaFoot st d env %%EXPR%% st' %%RESULT%% :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    %%ROWF%% g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr m0 %%HVL%% hIH
      (%%CTOR%% st d env el er st' vl hE %%HVL%%))

#print axioms %%SIMF%%
#print axioms %%ROWF%%
#print axioms %%IHF%%

end Vsa.Sim
''',
    'logicalFall': r'''import %%SIMMOD%%
import Vsa.Sim.LogicalHeadFootprint
import Vsa.Sim.LogicalFallthroughEntry

/-!
# `%%MODULE%%` — the footprint sibling of %%ARMDESC%% (IH tower, Level 1)

The same execution as %%SIMSRC%%, returning `EvalExitF` instead
of `EvalExitD`:
```
m0   ─ blockB_logical_footprint  ─▸  mret   logicalHeadFoot Fl        (stack window ∪ left child)
mret ─ %%CELL%%  ─▸  mpre   logFallCellFoot Fr %%OFF%%   (argument copies ∪ right child ∪ box)
mpre ─ blockD_v_rec_footprint    ─▸  exit   inherited
```
For two non-allocating children the node is non-allocating (`noArenaFoot`), and the
`EvalIHF noArenaFoot` supplier `%%IHF%%` closes the arm at that family.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-- **`%%SIMF%%`** — `%%SIM%%` with the node's footprint retained:
`blockA_k ≫ blockB_logical_footprint ≫ %%CELL%% ≫ blockD_v_rec_footprint`. -/
theorem %%SIMF%% (Fl Fr : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aEnv aExpr aLeft aRight : BitVec 64)
    (m0 : Mem)
    (%%HVL%% : %%TRUTHYEQ%%)
    (hEl : EvalE st d env el st' vl)
    (hIH : EvalIHF Fl st d env el st' vl)
    (hIHr : EvalIHF Fr st' d env er st'' vr)
    (_hEvalE : EvalE st d env %%EXPR%% st'' (.bool vr.truthy)) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0 c ∧
        %%EXTRASTY%% N A SL st' st'' el er vl vr sp sret aExpr aLeft aRight m0)
      (EvalExitF (logFallNodeFoot Fl Fr %%OFF%%) g N A SL φf φc st.store.frames.size
        st.store.closures.size st'' (.bool vr.truthy) sp r sret m0) := by
  intro c ⟨hc, hx⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  have hkm0 : read32 m0 aExpr.toNat = some 7 := %%KINDLEMMA%% (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, _hx13⟩ :=
    blockA_k g N A SL φf φc st env %%EXPR%% 7 (0x8000355c#64) LogicalArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot7
      ⟨hx.int_loaded, hx.intslot, hx.truthy_loaded, hx.bool_loaded, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl =>
        logicalCallee_writeMap8 mem a8 dd
          (by have := hx.vicode_stk; omega)
          (by simp only [jumpTableBase]; have := hx.table_stk; omega)
          (by have := hx.truthy_stk; omega)
          (by have := hx.boolcode_stk; omega)
          (by have := hx.vicode_stk; omega)
          (by have := hx.table_stk; omega) hcl)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.envReg⟩⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  have hx13c1 : c1.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) := _hx13
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat %%EXPR%% :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (%%OPTOK%%) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hlptrM' : read64 ment (aExpr.toNat + 16) = some aLeft.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aLeft.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  -- === block B: arm head + LEFT recursive call ⋈ IH → SubEvalReturn @0x8000356c ===
  obtain ⟨c2, hs2, hReturned⟩ :=
    blockB_logical_footprint Fl g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env %%LOGARGS%% vl
      sp r sret aExpr aEnv aLeft v8 v9 v18 c.σ.sailOutput m0
      hc.env_valid (hc.envset_defined_frame hbridge) hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hlptrM',
        (fun m' hag => hx.left_survives m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))),
        -- WAVE 47i: the parent ground at the arm entry (ONE kit call).
        ((hc.mem ▸ hc.ground).transport_offstack hc.table_stack_disjoint
          hx.sp_SLhi ((hc.mem ▸ hc.ground).stack_bytes_extend _hpresM) hMentM0),
        hx.expr24,
        hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code,
        -- ITEM ZERO B1: the LEFT child budget, DERIVED from the entry's
        -- budgeted fields (`StackOK.child` + `bodiesBound_logical`).
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.logical LogOp%%LOGARGS%%).stackNeed
                = evalFrame + max el.stackNeed er.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            have hm := Nat.le_max_left el.stackNeed er.stackNeed
            simp only [h1, h2, evalFrame]; omega),
        (Expr.bodiesBound_logical hc.expr_bodies).1,
        hc.store_bodies⟩
  obtain ⟨mcall, hSubR, hEnvSlotMcall, hMemExtM0mc, hMcallM0stk⟩ := hReturned.result
  have hHeadFoot := hReturned.extra
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1  -- discipline: allow(R6-anon-projection-tower) the landed `SubEvalReturn` tower has no named destructurer; same projection as `%%SIM%%`
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hViIntMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.vicode_stk; omega)).symm) hx.int_loaded
  have hViSlotMcall : IntSlotPinned mcall := by
    obtain ⟨q0, q1, q2, q3⟩ := hx.intslot
    have ag : ∀ i : Nat, i < 4 → m0[jumpTableBase + i]? = mcall[jumpTableBase + i]? :=
      fun i hi => (hAgM0 (jumpTableBase + i)
        (by simp only [jumpTableBase]; have := hx.table_stk; omega)).symm
    exact ⟨(ag 0 (by omega)).symm.trans q0, (ag 1 (by omega)).symm.trans q1,
      (ag 2 (by omega)).symm.trans q2, (ag 3 (by omega)).symm.trans q3⟩
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hNbsMcallC : NBSPins mcall :=
    (hc.mem ▸ hc.nbs_pins : NBSPins m0).transport
      (fun a ha => (hAgM0 a (by have := hx.vicode_stk; omega)).symm)
      (fun a ha => (hAgM0 a (by have := hx.table_stk; omega)).symm)
  have hExprMcall : ExprRepr mcall aExpr.toNat %%EXPR%% :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  have hPayRightMcall : read64 mcall (aExpr.toNat + 24) = some aRight.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 24) aRight.toNat hx.pay_right
    have hstk := hx.expr32_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [(hAgM0 (aExpr.toNat + 24) (by omega)), (hAgM0 (aExpr.toNat + 24 + 1) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 2) (by omega)), (hAgM0 (aExpr.toNat + 24 + 3) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 4) (by omega)), (hAgM0 (aExpr.toNat + 24 + 5) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 6) (by omega)), (hAgM0 (aExpr.toNat + 24 + 7) (by omega)),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hRightSurvMcall : ∀ m' : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        mcall[a]? = m'[a]?) → ExprRepr m' aRight.toNat er :=
    fun m' hag => hx.right_survives m'
      (fun a ha1 ha2 => (hAgM0 a ha1).symm.trans (hag a ha1 ha2))
  have hBufExtras : LogicalBufExtras sp :=
    ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega)⟩
%%MONOPRE%%  -- === block C: post-call two-eval tail → PreEpilogueVD .bool vr.truthy @0x800033ec ===
%%MONOPOST%%  obtain ⟨c3, hs3, mpreC, φfe, φce, outF, hpfe, hpce, hPreD, hCellFoot⟩ :=
%%CELLCALLHEAD%%      sp r sret aExpr aEnv aRight v8 v9 v18 c2.σ.sailOutput el er m0 c2.σ.mem %%HVL%% hIHr
      (hc.env_valid.mono (evalE_store_mono hEl).1)
      (hc.envset_defined_frame hbridge)
      hc.env_valid
%%CELLMONOARG%%      c2 ⟨mcall, hSubR, hEnvSlotMcall, hgpre_x8, hAEx18, hExprMcall, hPayRightMcall, hMemExtM0mc,
        -- WAVE 47i: the parent ground at the pre-call memory (ONE kit call).
        ((hc.mem ▸ hc.ground).transport_offstack hc.table_stack_disjoint
          hx.sp_SLhi ((hc.mem ▸ hc.ground).stack_bytes_extend hMemExtM0mc) hAgM0),
        hc.expr_ram.1, hc.expr_ram.2, hx.expr32, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr32_stk, hx.expr_A, hx.expr_A32, hx.expr_sub,
        hRightSurvMcall, hx.rop_lo, hx.rop_hi, hx.rop_win, hx.rop_stk,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hx.sret_boolcode,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVtruthyMcall, hVboolMcall, hViIntMcall, hViSlotMcall, hNbsMcallC, hBufExtras,
        hx.truthy_stk, hx.boolcode_stk, hx.truthy_arena, hx.bool_arena,
        hx.code_stk, (by have := hx.vicode_stk; omega), (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code, hx.arena_vi, hx.arena_table, hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.sp16, hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge,
        -- ITEM ZERO B1: the RIGHT child budget — StackOK/bodiesBound DERIVED
        -- from the entry's budgeted fields; store-bodies from the extras field.
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.logical LogOp%%LOGARGS%%).stackNeed
                = evalFrame + max el.stackNeed er.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            have hm := Nat.le_max_right el.stackNeed er.stackNeed
            simp only [h1, h2, evalFrame]; omega),
        (Expr.bodiesBound_logical hc.expr_bodies).2,
        hx.store_bodiesR, rfl⟩
  -- === block D: shared epilogue → EvalExitD .bool vr.truthy (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (logFallNodeFoot Fl Fr %%OFF%% SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' (.bool vr.truthy) sp r sret v8 v9 v18 outF m0
      c3 ⟨mpreC, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
%%STORELE%%  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.bool vr.truthy) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE %%STORELEREF%%.1 %%STORELEREF%%.2
  refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfe.trans (PhiExtends.mono %%STORELEREF%%.1 hpf'),
    hpce.trans (PhiExtends.mono %%STORELEREF%%.2 hpc'), hSurv⟩

/-- **`%%ROWF%%`** — %%ARMDESC%% from `EvalEntry` at two non-allocating children:
the node is non-allocating (`EvalExitF noArenaFoot`). -/
theorem %%ROWF%%
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (%%HVL%% : %%TRUTHYEQ%%)
    (hEl : EvalE st d env el st' vl)
    (hIH : EvalIHF noArenaFoot st d env el st' vl)
    (hIHr : EvalIHF noArenaFoot st' d env er st'' vr)
    (hEvalE : EvalE st d env %%EXPR%% st'' (.bool vr.truthy)) :
    Triple
      (EvalEntry g N A SL φf φc st d env %%EXPR%% sp r sret aEnv aExpr m0)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool vr.truthy) sp r sret m0) := by
  intro c hc
  obtain ⟨aLeft, aRight, hx⟩ := hc.logicalFallthroughExtras st'' vr hEl
  obtain ⟨c', hs, hExitF⟩ :=
    %%SIMF%% noArenaFoot noArenaFoot g N A SL φf φc st st' st'' d env el er vl vr
      sp r sret aEnv aExpr aLeft aRight m0 %%HVL%% hEl hIH hIHr hEvalE c ⟨hc, hx⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hx.sp_headroom; omega
  exact ⟨c', hs, hExitF.result,
    hExitF.extra.mono (logFallNodeFoot_noArena hsproom ⟨by omega, by omega⟩)⟩

/-- **The `EvalIHF noArenaFoot` supplier for %%ARMDESC%%**: two non-allocating
child derivations yield a non-allocating parent. -/
theorem %%IHF%% (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (vl vr : Value)
    (hEl : EvalE st d env el st' vl) (%%HVL%% : %%TRUTHYEQ%%)
    (hEr : EvalE st' d env er st'' vr)
    (hIH : EvalIHF noArenaFoot st d env el st' vl)
    (hIHr : EvalIHF noArenaFoot st' d env er st'' vr) :
    EvalIHF noArenaFoot st d env %%EXPR%% st'' (.bool vr.truthy) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    %%ROWF%% g N A SL φf φc st st' st'' d env el er vl vr sp r sret aEnv aExpr m0
      %%HVL%% hEl hIH hIHr (%%CTOR%% st d env el er st' st'' vl vr hEl %%HVL%% hEr))

#print axioms %%SIMF%%
#print axioms %%ROWF%%
#print axioms %%IHF%%

end Vsa.Sim
''',
}

ARM_FRAGMENTS: dict[str, dict[str, str]] = {
    'neg': {
        'SIMMOD': 'Vsa.Sim.EvalNegSim3',
        'ARMDESC': 'the `neg` arm',
        'DOCINTRO': "The same execution as `evalNegSim` (`EvalNegSim3.lean`), returning `EvalExitF`\ninstead of `EvalExitD`.  The node's footprint is derived from the layer:",
        'DIAGCELL': 'mret ─ blockC_neg_footprint      ─▸  mpre   negCellFoot      (three temporaries ∪ box)',
        'NODEDESC': "The `neg` node's footprint",
        'SIM': 'evalNegSim',
        'VALBINDER': '(n : Int)',
        'CHILDVAL': '(.int n)',
        'SIMEVALBINDER': "(hIH : EvalIHF F st d env esub st' (.int n))\n    (hEvalE : EvalE st d env (.unary .neg esub) st' (.int (wrap64 (-n)))) :",
        'HEVALUSE': 'evalE_store_mono hEvalE',
        'EXTRASTY': 'NegExtras N A SL st esub sp sret aExpr aOperand m0',
        'EXTRASGET': 'hc.unaryExtras',
        'KINDLEMMA': 'exprRepr_unary_kind',
        'EXPR': '(.unary .neg esub)',
        'UNOP': 'UnOp.neg',
        'OPTOK': 'unOpTok .neg',
        'CTOR': '.neg',
        'CTORARGS': "st d env esub st' n hE",
        'SIMCALLARGS': 'esub n sp r sret aEnv aExpr',
        'ROWFDESC': 'the `neg` arm from `EvalEntry` at a non-allocating child: the\nnode is non-allocating (`EvalExitF noArenaFoot`).',
        'IHFDESC': 'the `neg` arm',
        'GROUNDNOTE': '',
        'BLOCKB': "  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec, with footprint ===\n  obtain ⟨c2, hs2, hReturned⟩ :=\n    blockB_unary_footprint F g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .neg esub\n      (.int n) sp r sret aExpr aEnv aOperand v8 v9 v18 c.σ.sailOutput m0\n",
        'BUDGETNOTE': '',
        'TRANSPORTS': '  have hVintM0 : Value_intLoaded m0 := hc.mem ▸ hc.value_int_code\n  have hVintMcall : Value_intLoaded mcall :=\n    loaded_value_int_agreeP m0 mcall\n      (fun a ha => (hAgM0 a (by have := hc.vicode_stack_disjoint; omega)).symm) hVintM0\n',
        'CPRE': '  -- === block C: post-call neg tail → PreEpilogueVD .int(wrap64 -n), with footprint ===\n',
        'BLOCKCHEAD': "    blockC_neg_footprint (fun R => c1.σ.regs.get? R) g N A SL φf φc\n      st.store.frames.size st.store.closures.size\n      st' n sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0 c2.σ.mem\n      (hc.mem ▸ hc.sret_words)\n",
        'CARGS1': '        hc.sret_vicode_disjoint_int, hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,\n',
        'CARGS2': '        rfl, hVintMcall, hx.code_stk, (by have := hx.vicode_stk; omega), hx.vi_arena,\n        hx.sret_inSL, hMcallM0,\n',
        'DCOMMENT': '  -- === block D: shared epilogue → EvalExitD, inheriting the composed footprint ===\n',
    },
    'not': {
        'SIMMOD': 'Vsa.Sim.EvalNotSim',
        'ARMDESC': 'the logical-not arm',
        'DOCINTRO': 'The same execution as `evalNotSim` (`EvalNotSim.lean`), returning `EvalExitF`\ninstead of `EvalExitD`:',
        'DIAGCELL': 'mret ─ blockC_not_footprint      ─▸  mpre   truthyCellFoot   (24-byte argument copy ∪ box)',
        'NODEDESC': "The logical-not node's footprint",
        'SIM': 'evalNotSim',
        'VALBINDER': '(vsub : Value)',
        'CHILDVAL': 'vsub',
        'SIMEVALBINDER': "(hIH : EvalIHF F st d env esub st' vsub)\n    (_hEvalE : EvalE st d env (.unary .not esub) st' (.bool (!vsub.truthy))) :",
        'HEVALUSE': 'evalE_store_mono _hEvalE',
        'EXTRASTY': 'NotSimExtras N A SL esub sp sret aExpr aOperand m0',
        'EXTRASGET': 'hc.notExtras',
        'KINDLEMMA': 'exprRepr_not_kind',
        'EXPR': '(.unary .not esub)',
        'UNOP': 'UnOp.not',
        'OPTOK': 'unOpTok .not',
        'CTOR': '.not',
        'CTORARGS': "st d env esub st' vsub hE",
        'SIMCALLARGS': 'esub vsub sp r sret aEnv aExpr',
        'ROWFDESC': 'the logical-not arm from `EvalEntry` at a non-allocating child:\nthe node is non-allocating (`EvalExitF noArenaFoot`).',
        'IHFDESC': 'the logical-not arm',
        'GROUNDNOTE': "  -- WAVE 47i: the child's entry-ground bundle from `hc.ground` (ONE kit call).\n",
        'BLOCKB': "  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec ===\n  obtain ⟨c2, hs2, hReturned⟩ :=\n    blockB_unary_footprint F g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .not esub vsub\n      sp r sret aExpr aEnv aOperand v8 v9 v18 c.σ.sailOutput m0\n",
        'BUDGETNOTE': "        -- ITEM ZERO B1: the operand's child budget, DERIVED from the entry's\n        -- budgeted fields (`StackOK.child` + the `.unary` pass-through).\n",
        'TRANSPORTS': '  -- transport the two callee-code pins from `m0` to `mcall`\n  have hVtruthyMcall : Value_truthyLoaded mcall :=\n    loaded_truthy_agreeP m0 mcall\n      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded\n  have hVboolMcall : Value_boolLoaded mcall :=\n    loaded_bool_agreeP m0 mcall\n      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded\n',
        'CPRE': '  have hNotExtras : NotExtras sp :=\n    ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),\n      (by have := hx.sp_headroom; omega)⟩\n  -- === block C: post-call not tail → PreEpilogueVD .bool(!truthy) @0x800033ec ===\n',
        'BLOCKCHEAD': "    blockC_not_footprint (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size\n      st.store.closures.size st' vsub sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0\n      c2.σ.mem (hc.mem ▸ hc.sret_words)\n",
        'CARGS1': '        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,\n',
        'CARGS2': '        rfl, hVtruthyMcall, hVboolMcall, hNotExtras,\n        hx.truthy_stk, hx.boolcode_stk, hx.sret_boolcode, hx.truthy_arena, hx.bool_arena,\n        hx.code_stk, hx.sret_inSL, hMcallM0,\n',
        'DCOMMENT': '  -- === block D: shared epilogue → EvalExitD .bool(!truthy) (via blockD_v_rec) ===\n',
    },
    'orTrue': {
        'SIMMOD': 'Vsa.Sim.EvalOrSim',
        'ARMDESC': 'the or-true (short-circuit) arm',
        'SIMSRC': '`evalOrTrueSim` (`Vsa/Sim/EvalOrSim.lean`)',
        'SIM': 'evalOrTrueSim',
        'HVL': 'hvltrue',
        'TRUTHYEQ': 'vl.truthy = true',
        'KINDLEMMA': 'exprRepr_logical_or_kind',
        'EXPR': '(.logical .or el er)',
        'LOGOP': 'LogOp.or',
        'LOGARGS': '.or el er',
        'OPTOK': 'logOpTok .or',
        'CTOR': '.orTrue',
        'ARMSHORT': 'or-true (short-circuit)',
        'CBLOCKDESC': 'post-call OR short-circuit tail',
        'X13NOTE': '',
    },
    'andFalse': {
        'SIMMOD': 'Vsa.Sim.EvalAndSim',
        'ARMDESC': 'the and-false (short-circuit) arm',
        'SIMSRC': '`evalAndSim` (`Vsa/Sim/EvalAndSim.lean`)',
        'SIM': 'evalAndSim',
        'HVL': 'hvlfalse',
        'TRUTHYEQ': 'vl.truthy = false',
        'KINDLEMMA': 'exprRepr_logical_kind',
        'EXPR': '(.logical .and el er)',
        'LOGOP': 'LogOp.and',
        'LOGARGS': '.and el er',
        'OPTOK': 'logOpTok .and',
        'CTOR': '.andFalse',
        'ARMSHORT': 'and-false (short-circuit)',
        'CBLOCKDESC': 'post-call short-circuit tail',
        'X13NOTE': '  -- blockA_k pins x13 to the canonical frame-map address.\n',
    },
    'andTrue': {
        'SIMMOD': 'Vsa.Sim.EvalLogical3',
        'ARMDESC': 'the and-true (two-eval) arm',
        'SIMSRC': '`evalAndTrueSim` (`Vsa/Sim/EvalLogical3.lean`)',
        'SIM': 'evalAndTrueSim',
        'HVL': 'hvltrue',
        'TRUTHYEQ': 'vl.truthy = true',
        'KINDLEMMA': 'exprRepr_logical_kind',
        'EXPR': '(.logical .and el er)',
        'LOGOP': 'LogOp.and',
        'LOGARGS': '.and el er',
        'OPTOK': 'logOpTok .and',
        'CTOR': '.andTrue',
        'ARMSHORT': 'and-true (two-eval)',
        'MONOPRE': '  have hmono := evalE_store_mono hEl\n',
        'MONOPOST': '',
        'CELLCALLHEAD': "    blockC_andTrue_footprint Fr (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size\n      st.store.closures.size st' st'' d env vl vr\n",
        'CELLMONOARG': '      hmono\n',
        'STORELE': '  have hStoreLe := evalE_store_mono _hEvalE\n',
        'STORELEREF': 'hStoreLe',
    },
    'orFalse': {
        'SIMMOD': 'Vsa.Sim.EvalLogical4',
        'ARMDESC': 'the or-false (two-eval) arm',
        'SIMSRC': '`evalOrFalseSim` (`Vsa/Sim/EvalLogical4.lean`)',
        'SIM': 'evalOrFalseSim',
        'HVL': 'hvlfalse',
        'TRUTHYEQ': 'vl.truthy = false',
        'KINDLEMMA': 'exprRepr_logical_kind',
        'EXPR': '(.logical .or el er)',
        'LOGOP': 'LogOp.or',
        'LOGARGS': '.or el er',
        'OPTOK': 'logOpTok .or',
        'CTOR': '.orFalse',
        'ARMSHORT': 'or-false (two-eval)',
        'MONOPRE': '',
        'MONOPOST': '  have hleftMono := evalE_store_mono hEl\n  have hmono := evalE_store_mono _hEvalE\n',
        'CELLCALLHEAD': "    blockC_orFalse_footprint Fr (fun R => c1.σ.regs.get? R) g N A SL φf φc\n      st.store.frames.size st.store.closures.size st' st'' d env vl vr\n",
        'CELLMONOARG': '      hleftMono\n',
        'STORELE': '',
        'STORELEREF': 'hmono',
    },
}

"""Slots each family takes from the TSV row (everything else is a fragment)."""
SLOTS_FROM_TSV: dict[str, set[str]] = {
    "int": {"OP", "OPC", "RESULT", "RESID", "VFIELDS", "GUARDFN", "GUARDPF",
            "GUARDBINDERS", "GUARDARGS", "GUARDPASS", "GUARDPROPS", "GUARDNAMES",
            "SHAREDNOARENA"},
    "intPilot": {"OP", "MODULE", "ROWMOD", "SIMF", "SIM", "CELL", "ROWF", "ROW",
                 "NODEFOOT", "CELLFOOT", "RESID", "VFIELDS", "RESULT",
                 "SHAREDNOARENA"},
    "unary": {"MODULE", "RESULT", "CELLFOOT", "NODEFOOT", "IHF", "SIMF", "CELL", "ROWF",
              "SHAREDNOARENA"},
    "logicalShort": {"MODULE", "RESULT", "RESULTV", "IHF", "EXTRASTY", "SIMF", "CELL", "ROWF"},
    "logicalFall": {"MODULE", "IHF", "EXTRASTY", "OFF", "SIMF", "CELL", "ROWF"},
}


class Row:
    """One arm of the footprint layer."""

    def __init__(self, cells: dict[str, str]) -> None:
        for column in COLUMNS:
            setattr(self, column, cells[column].strip())
        if not ARM_RE.match(self.arm):
            raise ValueError(f"bad arm name {self.arm!r} (lower camel case expected)")
        if self.family not in TEMPLATES:
            raise ValueError(f"{self.arm}: unknown family {self.family!r} "
                             f"(known: {', '.join(sorted(TEMPLATES))})")
        self.guards  # validated eagerly
        if self.module != f"Eval{self.cap}RowFootprint":
            raise ValueError(f"{self.arm}: module {self.module!r} does not match the arm "
                             f"(expected Eval{self.cap}RowFootprint)")

    @property
    def cap(self) -> str:
        return self.arm[0].upper() + self.arm[1:]

    @property
    def guards(self) -> list[tuple[str, str]]:
        """The cell contract's semantic guards, as (hypothesis name, proposition)."""
        if self.guard in ("", "-"):
            return []
        out = []
        for item in self.guard.split(";"):
            name, sep, prop = item.partition("=")
            if not sep or not name.strip() or not prop.strip():
                raise ValueError(f"{self.arm}: guard entry {item!r} is not name=prop")
            out.append((name.strip(), prop.strip()))
        return out

    @property
    def path(self) -> pathlib.Path:
        return OUTPUT_DIR / f"{self.module}.lean"


def load_rows(tsv: pathlib.Path = TSV) -> list[Row]:
    """Read the row table; validate names, families and uniqueness."""
    rows: list[Row] = []
    columns: list[str] | None = None
    for number, line in enumerate(tsv.read_text().splitlines(), start=1):
        if not line.strip() or line.startswith("#"):
            continue
        if line.startswith("arm\t"):
            columns = [c.strip() for c in line.split("\t")]
            if columns != COLUMNS:
                raise ValueError(f"{tsv.name}:{number}: bad header columns {columns}")
            continue
        if columns is None:
            raise ValueError(f"{tsv.name}:{number}: a header row (arm\t…) must precede rows")
        cells = line.split("\t")
        if len(cells) != len(columns):
            raise ValueError(f"{tsv.name}:{number}: expected {len(columns)} columns, "
                             f"got {len(cells)}")
        try:
            rows.append(Row(dict(zip(columns, cells))))
        except ValueError as error:
            raise ValueError(f"{tsv.name}:{number}: {error}") from None
    arms = [row.arm for row in rows]
    duplicates = sorted({a for a in arms if arms.count(a) > 1})
    if duplicates:
        raise ValueError(f"duplicate arms: {', '.join(duplicates)}")
    return rows


def tsv_slots(row: Row) -> dict[str, str]:
    """The slot values the TSV row supplies, per family."""
    names = dict(OP=row.arm, OPC=row.cap, MODULE=row.module, RESULT=row.result,
                 RESID=row.resid, VFIELDS=row.extras, EXTRASTY=row.extras,
                 CELLFOOT=row.cell, NODEFOOT=row.node, IHF=row.supplier,
                 GUARDFN=row.guardfn, GUARDPF=row.guardpf,
                 SIMF=f"eval{row.cap}SimF", SIM=f"eval{row.cap}Sim",
                 CELL=f"blockC_{row.arm}_footprint", ROWF=f"{row.arm}RowF",
                 ROW=f"binRow_{row.arm}", ROWMOD=f"Vsa.Sim.rows.Eval{row.cap}Row",
                 RESULTV=row.result.strip("()"), OFF=row.node.split()[-1],
                 SHAREDNOARENA=f"{row.shared}_noArena")
    if row.family in ("int", "intPilot"):
        names["ROWF"] = f"binRow_{row.arm}F"
    guards = row.guards
    names["GUARDBINDERS"] = "".join(f"    ({n} : {t})\n" for n, t in guards)
    names["GUARDARGS"] = "".join(f" {n}" for n, _ in guards)
    names["GUARDPASS"] = ("      " + " ".join(n for n, _ in guards) + "\n") if guards else ""
    names["GUARDPROPS"] = "".join(f"    {t} →\n" for _, t in guards)
    names["GUARDNAMES"] = "".join(f"{n} " for n, _ in guards)
    return {key: names[key] for key in SLOTS_FROM_TSV[row.family]}


def render_row(row: Row) -> str:
    """The emitted module: the family template at this arm's slots."""
    slots = dict(tsv_slots(row))
    fragments = ARM_FRAGMENTS.get(row.arm, {})
    overlap = sorted(set(fragments) & set(slots))
    if overlap:
        raise ValueError(f"{row.arm}: fragments repeat TSV slots {overlap}")
    slots.update(fragments)
    template = TEMPLATES[row.family]
    needed = {chunk for chunk in template.split("%%")[1::2]}
    missing = sorted(needed - set(slots))
    if missing:
        raise ValueError(f"{row.arm}: no value for slot(s) {missing} "
                         f"(add them to ARM_FRAGMENTS[{row.arm!r}])")
    text = template
    for key, value in sorted(slots.items(), key=lambda kv: -len(kv[0])):
        text = text.replace(f"%%{key}%%", value)
    if "%%" in text:
        raise ValueError(f"{row.arm}: unexpanded slot marker in the emitted module")
    for what, value in [("module", row.module), ("result", row.result),
                        ("cell", row.cell.split()[0]), ("node", row.node.split()[0]),
                        ("supplier", row.supplier)]:
        if value != "-" and value not in text:
            raise ValueError(f"{row.arm}: TSV {what} {value!r} does not occur in the "
                             f"emitted module (table and template disagree)")
    return text


def render_all(tsv: pathlib.Path = TSV) -> dict[str, str]:
    return {row.arm: render_row(row) for row in load_rows(tsv)}


def relative(path: pathlib.Path) -> pathlib.Path:
    try:
        return path.relative_to(ROOT)
    except ValueError:
        return path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tsv", type=pathlib.Path, default=TSV)
    parser.add_argument("--output-dir", type=pathlib.Path, default=OUTPUT_DIR)
    parser.add_argument("--arm", action="append", default=[],
                        help="restrict to these arms")
    parser.add_argument("--check", action="store_true",
                        help="report stale or missing generated modules; exit 1 on drift")
    parser.add_argument("--stdout", action="store_true", help="print instead of writing")
    args = parser.parse_args(argv)
    try:
        rows = {row.arm: row for row in load_rows(args.tsv)}
        rendered = {arm: render_row(row) for arm, row in rows.items()}
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        return 2
    unknown = sorted(set(args.arm) - set(rendered))
    if unknown:
        print(f"unknown arm(s): {', '.join(unknown)}", file=sys.stderr)
        return 2
    selected = {a: t for a, t in rendered.items() if not args.arm or a in args.arm}
    stale = 0
    for arm, text in selected.items():
        target = args.output_dir / f"{rows[arm].module}.lean"
        if args.stdout:
            sys.stdout.write(text)
            continue
        if args.check:
            current = target.read_text() if target.exists() else ""
            if current != text:
                stale += 1
                print(f"{relative(target)} is stale", file=sys.stderr)
                sys.stderr.writelines(difflib.unified_diff(
                    current.splitlines(True), text.splitlines(True),
                    fromfile=str(relative(target)), tofile="generated"))
            else:
                print(f"{relative(target)}: up to date")
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        print(f"wrote {relative(target)}")
    return 1 if stale else 0


if __name__ == "__main__":
    raise SystemExit(main())
