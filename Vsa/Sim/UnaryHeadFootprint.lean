import Vsa.Sim.EvalNegSim
import Vsa.Sim.ArmTailFootprint
import Vsa.Sim.DeriveMetaTowers

/-!
# `UnaryHeadFootprint` — the single-child arm head with its footprint (IH tower, Level 1)

`blockB_unary_gen` (`EvalNegSim.lean`) is the `EX_UNARY` arm head (`ld a2,16(a2)`,
`addi a0,sp,144`, `jal eval_expr`) composed with the child at ANY retained fact
`Q mcall` about the child's actual return.  This file instantiates it at the
footprint-carrying child contract `EvalIHF F`: from the arm-entry memory `m0`,
the head writes nothing itself (its `mcall = ment` agrees with `m0` outside the
stack window `[SL.lo, sp)` by `ArmEntryK`), and the child's footprint sits at its
geometry `sp - 1088` / `subsret = sp - 944`.

The logical arms' head (`blockB_logical`, `EvalAndSim.lean`) differs only by the
env spill `sd a3,0(sp)` (inside the stack window) and the buffer `sp - 968`; it
is instantiated in `LogicalHeadFootprint.lean`.

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

/-- The single-child arm's head footprint from the arm-entry memory to the child's
return: the parent's own stack window and the child's footprint at its geometry
(`sp - 1088`, buffer `sp - 944`). -/
def unaryHeadFoot (F : FootFam) (SL : StackLayout) (A : Arena) (sp : Nat)
    (k : Nat) : Prop :=
  stackWin SL sp k ∨ F SL A (sp - 1088) (sp - 944) k

/-- A non-allocating child keeps the head inside the parent's stack window. -/
theorem unaryHeadFoot_noArena {SL : StackLayout} {A : Arena} {sp : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : unaryHeadFoot noArenaFoot SL A sp k) : stackWin SL sp k := by
  rcases hk with h1 | h2
  · exact h1
  · unfold noArenaFoot stackWin resultSlot at h2
    unfold stackWin
    omega

/-- **`blockB_unary_footprint`** — `blockB_unary_gen` at a footprint-carrying
child: the same precondition as `blockB_unary_with`, the same result
(`SubEvalReturn` + `UnaryCallMemory`), and the footprint
`unaryHeadFoot F SL A sp` of the child's return memory relative to `m0`. -/
theorem blockB_unary_footprint (F : FootFam)
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (op : UnOp) (esub : Expr) (vsub : Value)
    (sp r sret aExpr aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (henvValid : EnvValid st env)
    (henvset : ∃ v19 v20 v21 : BitVec 64,
      gpre Register.x19 = some v19 ∧ gpre Register.x20 = some v20 ∧
      gpre Register.x21 = some v21)
    (hIH : EvalIHF F st d env esub st' vsub) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aOperand.toNat ∧
        ExprRepr ment aOperand.toNat esub ∧
        EvalGround ment SL A (sp - 1088#64)
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        MemExtends m0 ment)
      (ReturnedWith (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' vsub sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) (0x800035ec#64)
          v8 v9 v18 mcall c ∧
        UnaryCallMemory m0 mcall SL sp)
        (fun c => MemFootprint (unaryHeadFoot F SL A sp.toNat) m0 c.σ.mem)) := by
  intro c hpre
  obtain ⟨c', hs, mcall, hSub, hCM, hQ⟩ :=
    blockB_unary_gen
      (fun mcall c => MemFootprint (F SL A (sp - 1088#64).toNat
        ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat) mcall c.σ.mem)
      gouter gpre N A SL φf φc st st' d env op esub vsub sp r sret aExpr aIn aOperand
      v8 v9 v18 out0 m0 henvValid henvset
      (fun g_sub mcall => hIH.run g_sub N A SL φf φc (sp - 1088#64) (0x800035ec#64)
        ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aIn aOperand mcall)
      c hpre
  obtain ⟨ment, hArm, -⟩ := hpre
  have hsp1088 : 1088 ≤ sp.toNat :=
    (ArmEntryK.destruct gouter N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
      sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c hArm).spRoom
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsub944 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  rw [hspsub, hsub944] at hQ
  refine ⟨c', hs, ⟨mcall, hSub, hCM⟩, ⟨fun k hk => ?_⟩⟩
  have hstk : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun h => hk (Or.inl h)
  have hF : ¬ F SL A (sp.toNat - 1088) (sp.toNat - 944) k := fun h => hk (Or.inr h)
  rw [hQ.agree k hF]
  exact hCM.outside k hstk

#print axioms unaryHeadFoot_noArena
#print axioms blockB_unary_footprint

end Vsa.Sim
