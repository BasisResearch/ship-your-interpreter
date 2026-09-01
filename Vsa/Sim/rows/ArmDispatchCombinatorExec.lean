import Vsa.Sim.ExecBrkCont
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.ReprSurvival

/-!
# `ArmDispatchCombinatorExec` — the ONE parametric exec arm-dispatch bridge (wave 44)

Group B of the `*ArmDispatch` residual class (`StmtExprArmDispatch` /
`StmtRetArmDispatch` / `StmtVarInitArmDispatch` / `StmtIfCondArmDispatch` /
`StmtWhileCondArmDispatch`, all `rows/Stmt*ArmStagePre.lean`): each demands the
dispatch run `ExecEntry (kind s) → ` the arm-head entry bundle (an
`ExecArmEntryK` at the arm's jump-table landing PC plus child-payload /
eval-code / wide-window-survival / enlarged-frame-geometry conjuncts).  The
machine content is `execBlockA` (`ExecBrkCont.lean`) — landed, case-independent
— so the ONLY honest residual is the entry-side extras record
`ExecArmHeadExtras` below (the statement-side twin of `EvalArmHeadExtras`,
`rows/ArmDispatchCombinator.lean`).

`execArmDispatch_of_slot` is the parametric combinator: for ANY
`(k, armPC, s, ce, payOff, nodeHi)` it runs `execBlockA` off the extras and
produces EXACTLY the Mid tower the `Stmt*ArmDispatch` defs quantify (α/defeq at
each instantiation — see `rows/ArmDispatchInstancesExec.lean`).  No `x13`
residual here: the exec Mids never read `a3` past the prologue (`mv s2,a3` is
IN `execBlockA`).

`jsp := (sp - 176) + 1088` is the frame-shift ghost (the arm lowers by 176,
then the staged `jal eval_expr` callee lowers by 1088); the wide-window
`StoreRepr` survival and the `jsp`-form geometry are genuine M6/payload facts —
they stay named fields, shared across all five arms.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
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

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ExecArmHeadExtras` — the shared Group-B dispatch residual

Everything `execBlockA`'s dispatch + the arm-head Mid demand that `ExecEntry`
does not carry, stated over the ENTRY memory `m0` (threadable by an M6 Layout /
`ExecCaseGeom` widening).  `aChild` is the arm's one payload pointer (the
sub-expression node), read off the `Stmt` node at `aStmt + payOff`; `nodeHi` is
the node span consumed by the arm (`16` for expr/ret/if/while, `24` for
varInit). -/
structure ExecArmHeadExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St)
    (k : Nat) (armPC : BitVec 64) (ce : Expr) (payOff nodeHi : Nat)
    (sp aInterp aStmt aChild : BitVec 64)
    (m0 : Mem) : Prop where
  /-- The tag-`k` statement jump-table slot pin (static image fact). -/
  slot : StmtSlotPinned k armPC m0
  /-- The tag-`k` slot's stack-disjointness (the `execBlockA` `jr` read), as the
  projected `StackDisjoint` record `execBlockA` consumes. -/
  tableGeom : StackDisjoint (stmtJumpTableBase + 4 * k) 4 SL sp.toNat
  /-- The child payload pointer, read off the `Stmt` node at the entry memory. -/
  pay : read64 m0 (aStmt.toNat + payOff) = some aChild.toNat
  /-- The child node's `ExprRepr` survives any change confined to the stack
  window (the prologue spills). -/
  child_surv : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aChild.toNat ce
  node_hi : aStmt.toNat + nodeHi ≤ 0x100000000
  /-- The consumed node span is disjoint from the stack window (transports the
  payload read `m0 → ment`). -/
  node_stk : aStmt.toNat + nodeHi ≤ SL.lo ∨ sp.toNat ≤ aStmt.toNat
  /-- `eval_expr` + `value_int` loaded and the int jump-table slot pinned at the
  entry memory — the arm stages a `jal eval_expr`, so these must reach `ment`. -/
  evalCode : Eval_exprLoaded m0
  viInt : Value_intLoaded m0
  viSlot : IntSlotPinned m0
  /-- **The wide-window `StoreRepr` survival** — genuine M6/payload fact: the
  store survives any change confined to the ENLARGED window
  `[SL.lo, (sp-176)+1088)` (the arm frame + the staged callee frame) minus the
  interp buffer hole.  Strictly wider than `ExecEntry.store_survives`. -/
  wide_surv : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < (sp.toNat - 176) + 1088) →
      ¬ (aInterp.toNat ≤ a ∧ a < aInterp.toNat + 24) →
      m0[a]? = m'[a]?) →
    StoreRepr m' N A φf φc st.store
  child_align : aChild.toNat % 8 = 0
  child_lo : 0x80000000 ≤ aChild.toNat
  child_hi : aChild.toNat + 16 ≤ 0x100000000
  child_win : tohostAddr + 16 ≤ aChild.toNat
  child_stk : aChild.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aChild.toNat
  /-- Deep-recursion headroom below the LOWERED frame (`sp - 176`). -/
  sproom : SL.lo + 3264 ≤ sp.toNat - 176
  sp16 : sp.toNat % 16 = 0
  /-- The `jsp`-form geometry (`jsp := (sp - 176) + 1088`, the staged callee's
  entry sp is `sp - 176` and IT lowers by 1088). -/
  jspSLhi : (sp.toNat - 176) + 1088 ≤ SL.hi
  codeStkJ : ((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStkJ : (0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c
  tableStkJ : (0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58
  arenaStkJ : A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo
  arenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo

/-! ## `execArmDispatch_of_slot` — the parametric Group-B combinator

Runs `execBlockA` off the extras, transports the payload / eval-code /
survival facts across the prologue spills, and assembles the arm-head Mid
tower the `Stmt*ArmDispatch` residuals demand.  `gpre := c1.σ.regs.get?` (the
reached frame — ghost frame conjunct `rfl`; `∃ x8`/`∃ x18` off
`ExecArmEntryK`'s `s0 = aStmt`/`s2 = aRet`). -/
theorem execArmDispatch_of_slot
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (k : Nat) (armPC : BitVec 64) (ce : Expr) (payOff nodeHi : Nat)
    (sp r aInterp aStmt aEnv aRet aChild : BitVec 64) (m0 : Mem) (c : Config)
    (hkle : k ≤ 8) (hklt : k < 128) (harmAl : armPC.toNat % 4 = 0)
    (hpayHi : payOff + 8 ≤ nodeHi)
    (hkind : read32 m0 aStmt.toNat = some k)
    (hX : ExecArmHeadExtras N A SL φf φc st k armPC ce payOff nodeHi sp aInterp aStmt aChild m0)
    (hE : ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c) :
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aCh : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ExecArmEntryK g N A SL φf φc st armPC
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 c'.σ.sailOutput m0 ment c' ∧
        read64 ment (aStmt.toNat + payOff) = some aCh.toNat ∧
        ExprRepr ment aCh.toNat ce ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + nodeHi ≤ 0x100000000 ∧
        (aStmt.toNat + nodeHi ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧
        (∀ m' : Mem,
          (∀ a, ¬ (SL.lo ≤ a ∧ a < (sp.toNat - 176) + 1088) →
            ¬ (aInterp.toNat ≤ a ∧ a < aInterp.toNat + 24) →
            ment[a]? = m'[a]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aCh.toNat % 8 = 0 ∧
        0x80000000 ≤ aCh.toNat ∧ aCh.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aCh.toNat ∧
        (aCh.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aCh.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat - 176 ∧ sp.toNat % 16 = 0 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((sp.toNat - 176) + 1088 ≤ SL.hi) ∧
        (((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) := by
  intro c'' heq
  subst heq
  -- === execBlockA: prologue + jump-table dispatch → ExecArmEntryK @armPC ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, v19, hArm⟩ :=
    execBlockA g N A SL φf φc st d env s k armPC
      sp r aInterp aStmt aEnv aRet m0 c''.σ.sailOutput
      hkle hklt hkind hX.slot harmAl hX.tableGeom
      c'' ⟨hE, rfl⟩
  -- Destructure a COPY of the `ExecArmEntryK` (keep `hArm` intact for output).
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, hAx8, _hAx9, _hAx19, hAx18, _hAsp, _hAra, _hAmi,
    hAout, _hAoutStr, _hAmem, _hAcode, _hAstore,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, _hAslotS3,
    _hAg8, _hAg9, _hAg18, _hAg19, _hAg2, _hAframe, hArmMemM0,
    hAsp176, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hAraAl⟩ := hArmCopy
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hAgP : AgreeP (fun a => ¬ (SL.lo ≤ a ∧ a < sp.toNat)) ment m0 := hMentM0
  -- Transport the payload read from `m0` (extras) to the arm-entry `ment`.
  have hpayMent : read64 ment (aStmt.toNat + payOff) = some aChild.toNat := by
    rw [read64_agreeP hAgP (fun kk hk => by rcases hX.node_stk with h | h <;> omega)]
    exact hX.pay
  -- The child `ExprRepr` at `ment` (extras' survival closure at the memframe).
  have hChildMent : ExprRepr ment aChild.toNat ce :=
    hX.child_surv ment (fun a ha => (hMentM0 a ha).symm)
  -- `eval_expr`/`value_int` loaded + int slot pinned at `ment` (the code/rodata
  -- regions are disjoint from the stack window — `jsp`-form geometry + 176 ≤ sp).
  have hEvalMent : Eval_exprLoaded ment :=
    loaded_eval_expr_agreeP m0 ment
      (fun a ha => (hMentM0 a (by rcases hX.codeStkJ with h | h <;> omega)).symm)
      hX.evalCode
  have hViIntMent : Value_intLoaded ment :=
    loaded_value_int_agreeP m0 ment
      (fun a ha => (hMentM0 a (by rcases hX.viStkJ with h | h <;> omega)).symm)
      hX.viInt
  have hViSlotMent : IntSlotPinned ment := by
    obtain ⟨q0, q1, q2, q3⟩ := hX.viSlot
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hMentM0 _ (by
        simp only [jumpTableBase]; rcases hX.tableStkJ with h | h <;> omega)];
       assumption)
  -- The wide-window survival at `ment` (compose the extras' `m0`-closure with
  -- the memframe; outside the ENLARGED window is outside the spill window).
  have hWideMent : ∀ m' : Mem,
      (∀ a, ¬ (SL.lo ≤ a ∧ a < (sp.toNat - 176) + 1088) →
        ¬ (aInterp.toNat ≤ a ∧ a < aInterp.toNat + 24) →
        ment[a]? = m'[a]?) →
      StoreRepr m' N A φf φc st.store :=
    fun m' hag =>
      hX.wide_surv m' (fun a h1 h2 => ((hMentM0 a (by omega)).symm).trans (hag a h1 h2))
  -- Realign the `ExecArmEntryK` `out0` to the reached `c1.σ.sailOutput`.
  have hArm' : ExecArmEntryK g N A SL φf φc st armPC
      sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 c1.σ.sailOutput m0 ment c1 :=
    hAout.symm ▸ hArm
  exact ⟨c1, hs1, (fun R => c1.σ.regs.get? R), aChild, v8, v9, v18, v19, ment,
    hArm', hpayMent, hChildMent,
    hE.stmt_align, hE.stmt_ram.1, hX.node_hi, Or.inr hE.stmt_win,
    hEvalMent, hViIntMent, hViSlotMent, hWideMent,
    hX.child_align, hX.child_lo, hX.child_hi, hX.child_win, hX.child_stk,
    hX.sproom, hX.sp16, hE.stack_ram.1, hE.stack_ram.2, hE.stack_win,
    hX.jspSLhi, hX.codeStkJ, hX.viStkJ, hX.tableStkJ, hX.arenaStkJ, hX.arenaCode,
    (fun R _ => rfl), ⟨aStmt, hAx8⟩, ⟨aRet, hAx18⟩⟩

#print axioms execArmDispatch_of_slot

end Vsa.Sim
