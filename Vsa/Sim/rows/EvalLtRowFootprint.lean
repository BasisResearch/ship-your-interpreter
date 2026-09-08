import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.rows.EvalLtRow
import Vsa.Sim.BinaryPostEntry
import Vsa.Sim.BinaryArmFrame
import Vsa.Sim.BinaryHeadFootprint

/-!
# `EvalLtRowFootprint` — pilot B of the footprint-carrying exit (IH tower, Level 1)

The footprint sibling of the `.lt` integer row (`rows/EvalLtRow.lean`): the same
execution as `evalLtSim` / `binRow_lt`, returning `EvalExitF` instead of
`EvalExitD`.  The node's footprint is derived from the layer exactly as in
pilot A (`StrCmpCellFootprint.lean`):
```
m0  ─ head (BinaryHeadFootprintSupply) ─▸  mret   binaryHeadFoot Fl Fr
mret ─ blockC_lt_footprint              ─▸  mpre   ltCellFoot (three temporaries ∪ box)
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

/-- The `.lt` node's footprint: the head's plus the cell's. -/
def ltNodeFoot (Fl Fr : FootFam) : FootFam := fun SL A sp sret k =>
  binaryHeadFoot Fl Fr SL A sp k ∨ ltCellFoot sp sret k

/-- Two non-allocating children make a non-allocating node. -/
theorem ltNodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : ltNodeFoot noArenaFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (binaryHeadFoot_noArena h k hh)
  · unfold ltCellFoot word8 resultSlot at hc
    unfold noArenaFoot stackWin resultSlot
    omega

/-- **`evalLtSimF`** — `evalLtSim` with the node's footprint retained:
`head ≫ blockC_lt_footprint ≫ blockD_v_rec_footprint`. -/
theorem evalLtSimF (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF Fl st d env el st' (.int a))
    (hIHr : EvalIHF Fr st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .lt el er) st'' (.bool (a < b)))
    (hResid : ∀ c' : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
      LtResid gpre N A SL sp r sret aExpr c') :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .lt el er)
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
        EvalGround ment SL A sp sret aExpr.toNat (.binary .lt el er) ∧
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
      (EvalExitF (ltNodeFoot Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' (.bool (a < b)) sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  -- the head, with its footprint
  obtain ⟨c2, hs2, hReturned⟩ :=
    hHead gouter gpre N A SL φf φc st st' st'' d env .lt el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr
      (intLeftSurvives a hBE.sproom hBE.arenaStk)
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  obtain ⟨hData, hHeadFoot⟩ := hReturned.extra
  have hR : LtResid gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c2 hTS).p8
  -- the cell, with its footprint from the actual return memory
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD, hCellFoot⟩ :=
    blockC_lt_footprint gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0 c2.σ.mem
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hData,
        hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode,
        hR.raAl, hR.vbool, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge, rfl⟩
  -- the epilogue inherits the composed footprint
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (ltNodeFoot Fl Fr SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' (.bool (a < b)) sp r sret v8 v9 v18
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
      st'' (.bool (a < b)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  refine ⟨c4, ((hs2.trans hs3).trans hs4), ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- **`binRow_ltF`** — `binRow_lt` at two non-allocating children: the node is
non-allocating (`EvalExitF noArenaFoot`). -/
theorem binRow_ltF (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.int a))
    (hIHl : EvalIHF noArenaFoot st d env el st' (.int a))
    (hIHr : EvalIHF noArenaFoot st' d env er st'' (.int b))
    (hEvalE : EvalE st d env (.binary .lt el er) st'' (.bool (a < b)))
    (hPost : ∀ (gpre : (R : Register) → Option (RegisterType R))
        (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c' : Config,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
        LtResid gpre N A SL sp r sret aExpr c') :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .lt el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (a < b)) sp r sret m0) := by
  intro c hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env .lt el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    evalLtSimF noArenaFoot noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env
      el er a b sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE (hPost gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR,
        hArmFrame.saved8, hArmFrame.saved9, hArmFrame.saved18, hArmFrame.savedSp,
        hArmFrame.saved19, hArmFrame.bridge⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result,
    hExitF.extra.mono (ltNodeFoot_noArena hsproom)⟩

#print axioms ltNodeFoot_noArena
#print axioms evalLtSimF
#print axioms binRow_ltF

end Vsa.Sim
