import Vsa.Sim.EvalOrSim
import Vsa.Sim.LogicalHeadFootprint
import Vsa.Sim.LogicalShortEntry

/-!
# `EvalOrTrueRowFootprint` — the footprint sibling of the or-true (short-circuit) arm (IH tower, Level 1)

The same execution as `evalOrTrueSim` (`Vsa/Sim/EvalOrSim.lean`), returning `EvalExitF` instead
of `EvalExitD`:
```
m0   ─ blockB_logical_footprint  ─▸  mret   logicalHeadFoot F  (stack window ∪ left child)
mret ─ blockC_orTrue_footprint  ─▸  mpre   truthyCellFoot     (24-byte argument copy ∪ box)
mpre ─ blockD_v_rec_footprint    ─▸  exit   inherited
```
For a non-allocating left child the node is non-allocating (`noArenaFoot`), and the
`EvalIHF noArenaFoot` supplier `evalOrTrueIHF` closes the arm at that family.

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

/-- **`evalOrTrueSimF`** — `evalOrTrueSim` with the node's footprint retained:
`blockA_k ≫ blockB_logical_footprint ≫ blockC_orTrue_footprint ≫ blockD_v_rec_footprint`. -/
theorem evalOrTrueSimF (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (sp r sret aEnv aExpr aLeft : BitVec 64)
    (m0 : Mem)
    (hvltrue : vl.truthy = true)
    (hIH : EvalIHF F st d env el st' vl)
    (_hEvalE : EvalE st d env (.logical .or el er) st' (.bool true)) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.logical .or el er) sp r sret aEnv aExpr m0 c ∧
        OrTrueExtras N A SL el er vl sp sret aExpr aLeft m0)
      (EvalExitF (logShortNodeFoot F) g N A SL φf φc st.store.frames.size
        st.store.closures.size st' (.bool true) sp r sret m0) := by
  intro c ⟨hc, hx⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  have hkm0 : read32 m0 aExpr.toNat = some 7 := exprRepr_logical_or_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, _hx13⟩ :=
    blockA_k g N A SL φf φc st env (.logical .or el er) 7 (0x8000355c#64) LogicalArmCallee
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
  have hExprMent : ExprRepr ment aExpr.toNat (.logical .or el er) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (logOpTok .or) ∧
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
    blockB_logical_footprint F g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .or el er vl
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
            have h1 : (Expr.logical LogOp.or el er).stackNeed
                = evalFrame + max el.stackNeed er.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            have hm := Nat.le_max_left el.stackNeed er.stackNeed
            simp only [h1, h2, evalFrame]; omega),
        (Expr.bodiesBound_logical hc.expr_bodies).1,
        hc.store_bodies⟩
  obtain ⟨mcall, hSubR, _hEnvSlot, hMemExtM0mc, hMcallM0stk⟩ := hReturned.result
  have hHeadFoot := hReturned.extra
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1  -- discipline: allow(R6-anon-projection-tower) the landed `SubEvalReturn` tower has no named destructurer; same projection as `evalOrTrueSim`
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hExprMcall : ExprRepr mcall aExpr.toNat (.logical .or el er) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  have hBufExtras : LogicalBufExtras sp :=
    ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega)⟩
  -- === block C: post-call OR short-circuit tail → PreEpilogueVD .bool true @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD, hCellFoot⟩ :=
    blockC_orTrue_footprint (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size
      st.store.closures.size st' vl sp r sret aExpr v8 v9 v18
      c2.σ.sailOutput el er m0 c2.σ.mem (hc.mem ▸ hc.sret_words) hvltrue
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
  -- === block D: shared epilogue → EvalExitD .bool true (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (logShortNodeFoot F SL A sp.toNat sret.toNat)
      g N A SL φfe φce st' (.bool true) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := evalE_store_mono _hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' (.bool true) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

/-- **`orTrueRowF`** — the or-true (short-circuit) arm from `EvalEntry` at a non-allocating left child:
the node is non-allocating (`EvalExitF noArenaFoot`). -/
theorem orTrueRowF
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hvltrue : vl.truthy = true)
    (hIH : EvalIHF noArenaFoot st d env el st' vl)
    (hEvalE : EvalE st d env (.logical .or el er) st' (.bool true)) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.logical .or el er) sp r sret aEnv aExpr m0)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.bool true) sp r sret m0) := by
  intro c hc
  obtain ⟨aLeft, hx⟩ := hc.logicalShortExtras vl
  obtain ⟨c', hs, hExitF⟩ :=
    evalOrTrueSimF noArenaFoot g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr
      aLeft m0 hvltrue hIH hEvalE c ⟨hc, hx⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hx.sp_headroom; omega
  exact ⟨c', hs, hExitF.result, hExitF.extra.mono (logShortNodeFoot_noArena hsproom)⟩

/-- **The `EvalIHF noArenaFoot` supplier for the or-true (short-circuit) arm**: a non-allocating
left child derivation yields a non-allocating parent. -/
theorem evalOrTrueIHF (st st' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl : Value)
    (hE : EvalE st d env el st' vl) (hvltrue : vl.truthy = true)
    (hIH : EvalIHF noArenaFoot st d env el st' vl) :
    EvalIHF noArenaFoot st d env (.logical .or el er) st' (.bool true) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    orTrueRowF g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr m0 hvltrue hIH
      (.orTrue st d env el er st' vl hE hvltrue))

#print axioms evalOrTrueSimF
#print axioms orTrueRowF
#print axioms evalOrTrueIHF

end Vsa.Sim
