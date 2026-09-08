import Vsa.Sim.EvalAndSim
import Vsa.Sim.EvalLogical2
import Vsa.Sim.ArmTailFootprint
import Vsa.Sim.DeriveMetaTowers

/-!
# `LogicalHeadFootprint` — the logical arms' head with its footprint (IH tower, Level 1)

`blockB_logical_gen` (`EvalAndSim.lean`) is the `EX_LOGICAL` arm head (`ld a2,16(a2)`,
`sd a3,0(sp)`, `addi a0,sp,120`, `jal eval_expr`) composed with the LEFT child at ANY
retained fact `Q mcall` about the child's actual return.  This file instantiates it
at the footprint-carrying child contract `EvalIHF F`: the head's own write (the env
spill at `sp - 1088`) sits inside the parent's stack window, and the child's
footprint sits at its geometry `sp - 1088` / `subsret = sp - 968`.  The short-circuit
node footprint `logShortNodeFoot` (head ∪ `truthyCellFoot`) is shared by the
or-true and and-false rows.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The logical arm's head footprint from the arm-entry memory to the LEFT child's
return: the parent's own stack window (which holds the env spill) and the child's
footprint at its geometry (`sp - 1088`, buffer `sp - 968`). -/
def logicalHeadFoot (F : FootFam) (SL : StackLayout) (A : Arena) (sp : Nat)
    (k : Nat) : Prop :=
  stackWin SL sp k ∨ F SL A (sp - 1088) (sp - 968) k

/-- A non-allocating child keeps the head inside the parent's stack window. -/
theorem logicalHeadFoot_noArena {SL : StackLayout} {A : Arena} {sp : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : logicalHeadFoot noArenaFoot SL A sp k) : stackWin SL sp k := by
  rcases hk with h1 | h2
  · exact h1
  · unfold noArenaFoot stackWin resultSlot at h2
    unfold stackWin
    omega

/-- The short-circuit logical node's footprint (or-true, and-false): the head's plus
the truthiness cell's. -/
def logShortNodeFoot (F : FootFam) : FootFam := fun SL A sp sret k =>
  logicalHeadFoot F SL A sp k ∨ truthyCellFoot sp sret k

/-- A non-allocating left child makes a non-allocating short-circuit node. -/
theorem logShortNodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : logShortNodeFoot noArenaFoot SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc
  · exact Or.inl (logicalHeadFoot_noArena h k hh)
  · unfold truthyCellFoot word8 resultSlot at hc
    unfold noArenaFoot stackWin resultSlot
    omega

/-- The two-eval logical node's footprint (and-true, or-false): the head's plus the
two-eval cell's (`off = 848` for and-true, `944` for or-false). -/
def logFallNodeFoot (Fl Fr : FootFam) (off : Nat) : FootFam := fun SL A sp sret k =>
  logicalHeadFoot Fl SL A sp k ∨ logFallCellFoot Fr off SL A sp sret k

/-- Two non-allocating children make a non-allocating two-eval node (the RIGHT
buffer `sp - off` lies inside the parent's stack window). -/
theorem logFallNodeFoot_noArena {SL : StackLayout} {A : Arena} {sp sret off : Nat}
    (h : SL.lo + 1088 ≤ sp) (hoff : 24 ≤ off ∧ off ≤ 1088) (k : Nat)
    (hk : logFallNodeFoot noArenaFoot noArenaFoot off SL A sp sret k) :
    noArenaFoot SL A sp sret k := by
  rcases hk with hh | hc | hr
  · exact Or.inl (logicalHeadFoot_noArena h k hh)
  · unfold truthyCellFoot word8 resultSlot at hc
    unfold noArenaFoot stackWin resultSlot
    omega
  · unfold noArenaFoot stackWin resultSlot at hr
    unfold noArenaFoot stackWin resultSlot
    omega

/-- **`blockB_logical_footprint`** — `blockB_logical_gen` at a footprint-carrying
LEFT child: the same precondition and result as `blockB_logical`, and the footprint
`logicalHeadFoot F SL A sp` of the child's return memory relative to `m0`. -/
theorem blockB_logical_footprint (F : FootFam)
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (op : LogOp) (el er : Expr) (vl : Value)
    (sp r sret aExpr aIn aLeft : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (henvValid : EnvValid st env)
    (henvset : ∃ v19 v20 v21 : BitVec 64,
      gpre Register.x19 = some v19 ∧ gpre Register.x20 = some v20 ∧
      gpre Register.x21 = some v21)
    (hIH : EvalIHF F st d env el st' vl) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x8000355c#64) LogicalArmCallee (.logical op el er)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        -- ===== recursive-case extras (mirrors `blockB_unary`) =====
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aLeft.toNat ∧
        -- LEFT-operand `ExprRepr`-survival (mirrors `blockB_binary`'s `lexpr_surv`):
        -- a generic `ExprRepr`-agreeP lemma over an arbitrary sub-tree is not
        -- available, so it is threaded as a survival closure keyed to the stack window.
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aLeft.toNat el) ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry
        -- (the LEFT child is derived inside via the `EntryGroundKit`).
        EvalGround ment SL A sp sret aExpr.toNat (.logical op el er) ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        0x80000000 ≤ aLeft.toNat ∧ aLeft.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aLeft.toNat ∧
        (aLeft.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLeft.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (threaded from
        -- the parent `.logical op el er` node's budget by the arm-entry supplier).
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)
      (ReturnedWith (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' vl sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) (0x8000356c#64)
          v8 v9 v18 mcall c ∧
        read64 mcall (sp.toNat - 1088) = some (BitVec.ofNat 64 (φf env)).toNat ∧
        MemExtends m0 mcall ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?))
        (fun c => MemFootprint (logicalHeadFoot F SL A sp.toNat) m0 c.σ.mem)) := by
  intro c hpre
  obtain ⟨c', hs, mcall, hSub, hEnv, hExt, hAg, hQ⟩ :=
    blockB_logical_gen
      (fun mcall c => MemFootprint (F SL A (sp - 1088#64).toNat
        ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat) mcall c.σ.mem)
      gouter gpre N A SL φf φc st st' d env op el er vl sp r sret aExpr aIn aLeft
      v8 v9 v18 out0 m0 henvValid henvset
      (fun g_sub mcall => hIH.run g_sub N A SL φf φc (sp - 1088#64) (0x8000356c#64)
        ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aIn aLeft mcall)
      c hpre
  obtain ⟨ment, hArm, -⟩ := hpre
  have hsp1088 : 1088 ≤ sp.toNat :=
    (ArmEntryK.destruct gouter N A SL φf φc st (0x8000355c#64) LogicalArmCallee
      (.logical op el er) sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c hArm).spRoom
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  rw [hspsub, hsub968] at hQ
  refine ⟨c', hs, ⟨mcall, hSub, hEnv, hExt, hAg⟩, ⟨fun k hk => ?_⟩⟩
  have hstk : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun h => hk (Or.inl h)
  have hF : ¬ F SL A (sp.toNat - 1088) (sp.toNat - 968) k := fun h => hk (Or.inr h)
  rw [hQ.agree k hF]
  exact hAg k hstk

#print axioms logicalHeadFoot_noArena
#print axioms logShortNodeFoot_noArena
#print axioms logFallNodeFoot_noArena
#print axioms blockB_logical_footprint

end Vsa.Sim
