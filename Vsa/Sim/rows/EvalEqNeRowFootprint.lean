import Vsa.While.StoreBodiesBoundPreservation
import Vsa.Sim.rows.EvalEqNeFront
import Vsa.Sim.BinaryPostEntry
import Vsa.Sim.BinaryArmFrame
import Vsa.Sim.BinaryHeadFootprint
import Vsa.Sim.IHClauseGeneric

/-!
# `EvalEqNeRowFootprint` — the footprint siblings of the `.eq` / `.ne` rows (IH tower, Level 1)

The same executions as `evalEqSimD` / `evalNeSimD` (`rows/EvalEqNeFront.lean`),
returning `EvalExitF` instead of `EvalExitD`.  The node's footprint is composed
from the layer, exactly as the integer pilot (`rows/EvalLtRowFootprint.lean`):

```
m0   ─ head (BinaryHeadFootprintSupply)  ─▸ mret   binaryHeadFoot Fl Fr
mret ─ eq/ne dispatch (reflected chain)  ─▸ mA     [sp-1088, sp-824)
mA   ─ value_equal                       ─▸ mVe    [sp-1104, sp-1088)   (VeReturn.hmemframe)
mVe  ─ blockC_eq/ne_footprint (box)      ─▸ mpre   [sret, sret+24)
mpre ─ blockD_v_rec_footprint            ─▸ exit   inherited
```

`value_equal` writes only its own 16-byte scratch window below the caller frame
base (`ve_str_post`'s memory clause; its `strcmp` call writes nothing), and the
reflected dispatch's stores are all `x2`-relative inside `[base, base + 0x108)`
(`eqDispatch_mem_frame` / `neDispatch_mem_frame`), so for two non-allocating
children the node is non-allocating (`noArenaFoot`).

The cells `EqCellF .eq` / `EqCellF .ne` (`IHClauseGeneric.lean`) are produced from
the SAME landed residual suppliers the base row takes (`BinEqCell`, which packages
the left-survival residual and `EqResid`), so `hBinary` closes on exactly
`eval_binary_row`'s hypotheses.

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

-- discipline: allow(R7-conj-tower-def) every ∃ here is a RESTATEMENT of a landed
-- post the eq/ne layer already ships (`blockC_eq/ne_footprint`'s epilogue tower and
-- `eqBlockC_bridge`'s bridge tower); the new facts this file adds are the named
-- `MemFootprint` conjunct and the named `eqneCellFoot`/`eqneNodeFoot` families.
namespace Vsa.Sim

/-- The eq/ne cell's footprint, relative to the memory at the return of both
children: the reflected dispatch's stores `[sp-1088, sp-824)`, `value_equal`'s
scratch window `[sp-1104, sp-1088)`, and the `value_bool` box `[sret, sret+24)`. -/
def eqneCellFoot (sp sret : Nat) (k : Nat) : Prop :=
  (sp - 1104 ≤ k ∧ k < sp - 824) ∨ resultSlot sret k

/-- The `.eq`/`.ne` node's footprint: the head's plus the cell's. -/
def eqneNodeFoot (Fl Fr : FootFam) : FootFam := fun SL A sp sret k =>
  binaryHeadFoot Fl Fr SL A sp k ∨ eqneCellFoot sp sret k

/-- Two non-allocating children make a non-allocating node. -/
theorem eqneNodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1104 ≤ sp) (k : Nat)
    (hk : eqneNodeFoot noArenaFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (binaryHeadFoot_noArena (by omega) k hh)
  · unfold eqneCellFoot resultSlot at hc
    unfold noArenaFoot stackWin resultSlot
    omega

/-- **The reflected dispatch's memory footprint**: every `eq`/`ne` dispatch store is
`x2`-relative at offset `< 0x108` (`eqDispatch_mem_frame`/`neDispatch_mem_frame`). -/
theorem eqneDispatch_footprint (op : EqNeOp) {base : BitVec 64}
    {lds : List (List (BitVec 8))} {m0 : Mem} {c : Config}
    (hrb : EqNeOp.DispatchReadback op base lds m0 c) (fb : FrameBundle m0 base) :
    MemFootprint (fun k => base.toNat ≤ k ∧ k < base.toNat + 0x108) m0 c.σ.mem := by
  cases op with
  | eq =>
    refine ⟨fun k hk => ?_⟩
    have hm : c.σ.mem = writeLog m0
        (evalBlocks eqDispatch (SegEvalState.init (eqDispL base) lds)).log := hrb.memory
    rw [hm]
    exact eqDispatch_mem_frame base lds m0 fb k hk
  | ne =>
    refine ⟨fun k hk => ?_⟩
    have hm : c.σ.mem = writeLog m0
        (evalBlocks neDispatch (SegEvalState.init (eqDispL base) lds)).log := hrb.memory
    rw [hm]
    exact neDispatch_mem_frame base lds m0 fb k hk

/-- **`eqBlockC_bridge_footprint`** — `eqBlockC_bridge` with the cell footprint
retained: the dispatch chain, `value_equal`'s scratch window and the box compose
into `eqneCellFoot`. -/
theorem eqBlockC_bridge_footprint
    (op : EqNeOp)
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (resVal : Value) (link jalPC : BitVec 64) (jImm : BitVec 21)
    (out0 : Array String) (m0 : Mem) (c2 : Config)
    (hEntryLeft : nf ≤ st'.store.frames.size ∧ nc ≤ st'.store.closures.size)
    (hEntryFinal : nf ≤ st''.store.frames.size ∧ nc ≤ st''.store.closures.size)
    (hOut0 : c2.σ.sailOutput = out0)
    (hTS : TwoSubReturn gpre N A SL φf φc nf nc st' st'' vl vr
      sp r sret v8 v9 v18 m0 c2)
    (hLoads : BinaryReturnLoads sp c2)
    (blockCsel : ∀ (φfa φca φfma φcma φf'a φc'a : Addr → Nat)
      (mEnt : Mem) (cR : Config),
      PhiExtends φfa φfma st'.store.frames.size → PhiExtends φca φcma st'.store.closures.size →
      PhiExtends φfma φf'a st''.store.frames.size → PhiExtends φcma φc'a st''.store.closures.size →
      VeReturn g (sp - 1088#64) sret vl vr link out0 mEnt cR →
      EqNeBoxPre g N A SL φf'a φc'a st'' sp r sret v8 v9 v18 v19 w19 out0 m0 mEnt →
      ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat) (cfin : Config),
        Steps cR cfin ∧
        PhiExtends φfa φfm' st'.store.frames.size ∧
        PhiExtends φca φcm' st'.store.closures.size ∧
        PhiExtends φfm' φfe st''.store.frames.size ∧
        PhiExtends φcm' φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 out0 m0 mpre cfin ∧
        MemFootprint (resultSlot sret.toNat) cR.σ.mem mpre)
    (hResid : EqResid op gpre g N A SL φf φc nf nc st' st''
      sp r sret aExpr v8 v9 v18 v19 w19 vl vr link jalPC jImm out0 m0 c2) :
    ∃ (c3 : Config) (mpre : Mem) (φfe φce : Addr → Nat),
      Steps c2 c3 ∧
      PhiExtends φf φfe nf ∧
      PhiExtends φc φce nc ∧
      PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3 ∧
      MemFootprint (eqneCellFoot sp.toNat sret.toNat) c2.σ.mem mpre := by
  obtain ⟨cD, lds, hStepsD, hDispatchPost⟩ :=
    evalEqNeChain_dispatch_of_twoSubReturn op gpre
      N A SL φf φc nf nc st' st'' vl vr sp r sret aExpr v8 v9 v18 m0 c2 hTS hLoads hResid.dispatch
  obtain ⟨resultF, resultC, hTail⟩ := hResid.tail cD lds hDispatchPost
  have hReadback := hDispatchPost.readback
  have hFront : EqFrontData g N resultC (sp - 1088#64) sret vl vr link jalPC jImm
      cD.σ.mem out0 cD :=
    eqFrontData_of_readback op g N resultC (sp - 1088#64) sret vl vr link jalPC jImm
      c2.σ.mem out0 cD lds hResid.base hReadback.memory hReadback.pins
      hResid.leftPayload hResid.rightPayload
      (hTail.returned.values _ _ (by simp)) (hTail.returned.values _ _ (by simp)) hTail.front
  obtain ⟨cR, hStepsFront, hVeReturn⟩ :=
    blockC_eqne_front g N resultC (sp - 1088#64) sret vl vr link jalPC jImm
      cD.σ.mem out0 cD hFront
  obtain ⟨mpre, φfm', φcm', φfe, φce, cfin, hStepsBox, hp1, hp2, hp3, hp4, hPre, hFootBox⟩ :=
    blockCsel resultF resultC resultF resultC resultF resultC cD.σ.mem cR
      (PhiExtends.refl _ _) (PhiExtends.refl _ _)
      (PhiExtends.refl _ _) (PhiExtends.refl _ _) hVeReturn hTail.box
  -- the cell footprint: dispatch ≫ value_equal scratch ≫ box
  have hSB := hResid.dispatch.stack
  have hsp1088 : 1088 ≤ sp.toNat := by have := hSB.SLloSp; have := hSB.SLlo; omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have hFootD : MemFootprint
      (fun k => (sp - 1088#64).toNat ≤ k ∧ k < (sp - 1088#64).toNat + 0x108)
      c2.σ.mem cD.σ.mem :=
    eqneDispatch_footprint op hReadback (frameBundle_of_stackBounds hSB)
  have hFootV : MemFootprint
      (fun k => (sp - 1088#64).toNat - 16 ≤ k ∧ k < (sp - 1088#64).toNat)
      cD.σ.mem cR.σ.mem := ⟨hVeReturn.hmemframe⟩
  refine ⟨cfin, mpre, φfe, φce, (hStepsD.trans hStepsFront).trans hStepsBox, ?_, ?_, ?_, ?_⟩
  · exact hTail.returned.frames.trans
      ((PhiExtends.mono hEntryLeft.1 hp1).trans (PhiExtends.mono hEntryFinal.1 hp3))
  · exact hTail.returned.closures.trans
      ((PhiExtends.mono hEntryLeft.2 hp2).trans (PhiExtends.mono hEntryFinal.2 hp4))
  · rw [hOut0]; exact hPre
  · refine ((hFootD.trans hFootV).trans hFootBox).mono (fun k hk => ?_)
    rcases hk with (h | h) | h
    · rw [hspsub] at h
      exact Or.inl ⟨by omega, by omega⟩
    · rw [hspsub] at h
      exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr h

theorem evalEqNeSimF (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (op : BinOp) (vl vr : Value) (resVal : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' vl)
    (hIHl : EvalIHF Fl st d env el st' vl)
    (hIHr : EvalIHF Fr st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary op el er) st'' resVal)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    -- the op-specific `blockC` bridge (dispatch + value_equal + box) WITH its
    -- memory footprint: the dispatch stores, `value_equal`'s scratch window, the box.
    (hblockC : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      BinaryReturnLoads sp c2 →
      String.join c2.σ.sailOutput.toList = st''.out →
      ∃ (c3 : Vsa.Machine.Config) (mpre : Mem) (φfe φce : Addr → Nat),
        Steps c2 c3 ∧
        PhiExtends φf φfe st.store.frames.size ∧
        PhiExtends φc φce st.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3 ∧
        MemFootprint (eqneCellFoot sp.toNat sret.toNat) c2.σ.mem mpre) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
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
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry.
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`) --
        -- forwarded to `blockB_binary`'s amended pre.
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (EvalExitF (eqneNodeFoot Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' resVal sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩ := hpre
  -- === block B: two-operand head + IHs → TwoSubReturn, with the head footprint ===
  obtain ⟨c2, hs2, hReturned⟩ :=
    hHead gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  obtain ⟨hData, hHeadFoot⟩ := hReturned.extra
  have hLoads : BinaryReturnLoads sp c2 := hData.toBinaryReturnLoads
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' vl vr sp r sret v8 v9 v18 m0 c2 hTS).p8
  -- === block C: dispatch + value_equal + box, with the cell footprint ===
  obtain ⟨c3, mpre, φfe, φce, hs3, hpfe, hpce, hPre, hCellFoot⟩ := hblockC c2 hTS hLoads hOutC2
  -- === block D: the shared epilogue inherits the composed footprint ===
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (eqneNodeFoot Fl Fr SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPre, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono _hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' resVal sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hmono.1 hmono.2
  refine ⟨c4, ((hs2.trans hs3).trans hs4), ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords, φf', φc',
    hpfe.trans (PhiExtends.mono hmono.1 hpf'), hpce.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

theorem evalEqSimF (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' vl)
    (hIHl : EvalIHF Fl st d env el st' vl)
    (hIHr : EvalIHF Fr st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary .eq el er) st'' (.bool (vl.equal vr)))
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    -- the op's front residual (dispatch input, operand payload windows, reached
    -- tail), exactly as the landed `evalEqSimD`/`evalNeSimD` carry it.
    (hResid : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      EqResid .eq gpre g N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' sp r sret aExpr v8 v9 v18 v19 w19 vl vr
        (0x80003720#64) (0x8000371c#64) (0x1ff140#21) c2.σ.sailOutput m0 c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .eq el er)
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
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry.
        EvalGround ment SL A sp sret aExpr.toNat (.binary .eq el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`) --
        -- forwarded to `blockB_binary`'s amended pre.
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (EvalExitF (eqneNodeFoot Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' (.bool (vl.equal vr)) sp r sret m0) :=
  evalEqNeSimF Fl Fr hHead gouter gpre g N A SL φf φc st st' st'' d env el er .eq vl vr
    (.bool (vl.equal vr)) sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hLeft hIHl hIHr _hEvalE hVlSurv
    (fun c2 hTS hLoads _hOut2 =>
      eqBlockC_bridge_footprint .eq gpre g N A SL φf φc
        st.store.frames.size st.store.closures.size st' st'' sp r sret aExpr
        v8 v9 v18 v19 w19 vl vr (.bool (vl.equal vr)) (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
        c2.σ.sailOutput m0 c2 (evalE_store_mono hLeft) (evalE_store_mono _hEvalE) rfl
        hTS hLoads
        (fun φfa φca φfma φcma φf'a φc'a mEnt cR hp1 hp2 hp3 hp4 hVe hBox =>
          blockC_eq_footprint g N A SL φfa φca φfma φcma φf'a φc'a st' st''
            sp r sret v8 v9 v18 v19 w19 vl vr c2.σ.sailOutput m0 mEnt cR
            hp1 hp2 hp3 hp4 hVe hBox)
        (hResid c2 hTS))

theorem evalNeSimF (Fl Fr : FootFam) (hHead : BinaryHeadFootprintSupply Fl Fr)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' vl)
    (hIHl : EvalIHF Fl st d env el st' vl)
    (hIHr : EvalIHF Fr st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary .ne el er) st'' (.bool (!(vl.equal vr))))
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    -- the op's front residual (dispatch input, operand payload windows, reached
    -- tail), exactly as the landed `evalEqSimD`/`evalNeSimD` carry it.
    (hResid : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      EqResid .ne gpre g N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' sp r sret aExpr v8 v9 v18 v19 w19 vl vr
        (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21) c2.σ.sailOutput m0 c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .ne el er)
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
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry.
        EvalGround ment SL A sp sret aExpr.toNat (.binary .ne el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`) --
        -- forwarded to `blockB_binary`'s amended pre.
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (EvalExitF (eqneNodeFoot Fl Fr) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' (.bool (!(vl.equal vr))) sp r sret m0) :=
  evalEqNeSimF Fl Fr hHead gouter gpre g N A SL φf φc st st' st'' d env el er .ne vl vr
    (.bool (!(vl.equal vr))) sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hLeft hIHl hIHr _hEvalE hVlSurv
    (fun c2 hTS hLoads _hOut2 =>
      eqBlockC_bridge_footprint .ne gpre g N A SL φf φc
        st.store.frames.size st.store.closures.size st' st'' sp r sret aExpr
        v8 v9 v18 v19 w19 vl vr (.bool (!(vl.equal vr))) (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
        c2.σ.sailOutput m0 c2 (evalE_store_mono hLeft) (evalE_store_mono _hEvalE) rfl
        hTS hLoads
        (fun φfa φca φfma φcma φf'a φc'a mEnt cR hp1 hp2 hp3 hp4 hVe hBox =>
          blockC_ne_footprint g N A SL φfa φca φfma φcma φf'a φc'a st' st''
            sp r sret v8 v9 v18 v19 w19 vl vr c2.σ.sailOutput m0 mEnt cR
            hp1 hp2 hp3 hp4 hVe hBox)
        (hResid c2 hTS))

/-- **`binRow_eqF`** — the `.eq` cell from the recursor entry at two non-allocating
children, from the SAME landed residual supplier the base row takes. -/
theorem binRow_eqF (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (hCell : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' vl) (hRight : EvalE st' d env er st'' vr)
    (hIHl : EvalIHF noArenaFoot st d env el st' vl)
    (hIHr : EvalIHF noArenaFoot st' d env er st'' vr)
    (hEvalE : EvalE st d env (.binary .eq el er) st'' (.bool (vl.equal vr))) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .eq el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (vl.equal vr)) sp r sret m0) := by
  intro c hc
  obtain ⟨w19, hVl, hRes⟩ :=
    hCell g N A SL φf φc st st' st'' d env el er vl vr sp r sret aEnv aExpr m0 c
      hLeft hRight hIHl.forget hIHr.forget hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env .eq el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    evalEqSimF noArenaFoot noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' w19 c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE hVl (hRes gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩
  have hsproom : SL.lo + 1104 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result, hExitF.extra.mono (eqneNodeFoot_noArena hsproom)⟩

/-- **`binRow_neF`** — the `.ne` cell (the `seqz` clone of `binRow_eqF`). -/
theorem binRow_neF (hHead : BinaryHeadFootprintSupply noArenaFoot noArenaFoot)
    (hCell : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' vl) (hRight : EvalE st' d env er st'' vr)
    (hIHl : EvalIHF noArenaFoot st d env el st' vl)
    (hIHr : EvalIHF noArenaFoot st' d env er st'' vr)
    (hEvalE : EvalE st d env (.binary .ne el er) st'' (.bool (!(vl.equal vr)))) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .ne el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (!(vl.equal vr))) sp r sret m0) := by
  intro c hc
  obtain ⟨w19, hVl, hRes⟩ :=
    hCell g N A SL φf φc st st' st'' d env el er vl vr sp r sret aEnv aExpr m0 c
      hLeft hRight hIHl.forget hIHr.forget hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env .ne el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    evalNeSimF noArenaFoot noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' w19 c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE hVl (hRes gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩
  have hsproom : SL.lo + 1104 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result, hExitF.extra.mono (eqneNodeFoot_noArena hsproom)⟩

/-- **The `.eq` cell at `EvalIHF noArenaFoot`** (`IHClauseGeneric.EqCellF`), from the
landed residual supplier `BinEqCell .eq …` — the SAME hypothesis `eval_binary_row`
takes for its `hEq` field. -/
theorem eqCellF_of (hCell : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)) :
    EqCellF .eq (fun l r => .bool (l.equal r)) := by
  intro st d env el er st' st'' lv rv hEl hEr ihL ihR
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  exact binRow_eqF (binaryHeadFootprintSupply noArenaFoot noArenaFoot) hCell
    g N A SL φf φc st st' st'' d env el er lv rv sp r sret aEnv aExpr m0 hEl hEr ihL ihR
    (EvalE.binary st d env .eq el er st' st'' lv rv _ hEl hEr (by simp [binOpSem]))

/-- **The `.ne` cell at `EvalIHF noArenaFoot`** (`IHClauseGeneric.EqCellF`). -/
theorem neCellF_of (hCell : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)) :
    EqCellF .ne (fun l r => .bool (!(l.equal r))) := by
  intro st d env el er st' st'' lv rv hEl hEr ihL ihR
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  exact binRow_neF (binaryHeadFootprintSupply noArenaFoot noArenaFoot) hCell
    g N A SL φf φc st st' st'' d env el er lv rv sp r sret aEnv aExpr m0 hEl hEr ihL ihR
    (EvalE.binary st d env .ne el er st' st'' lv rv _ hEl hEr (by simp [binOpSem]))

#print axioms eqneNodeFoot_noArena
#print axioms eqneDispatch_footprint
#print axioms eqBlockC_bridge_footprint
#print axioms evalEqNeSimF
#print axioms evalEqSimF
#print axioms evalNeSimF
#print axioms binRow_eqF
#print axioms binRow_neF
#print axioms eqCellF_of
#print axioms neCellF_of

end Vsa.Sim
