import Vsa.Sim.InterpEntry
import Vsa.While.StackNeed

/-!
# ITEM ZERO B1 inhabitation probe

Machine-checked evidence that the additive B1 amendment WORKS: the entry-side
`sp_headroom`-class fact that the fleet proved UNDERIVABLE from the constant
`EvalEntry.stackOK` (falsity #13) now DERIVES from the new budgeted
`EvalEntry.stackBudget` field.

The fleet's `NegExtras.sp_headroom` was `SL.lo + 3264 ≤ sp.toNat`.  For a
`.unary .neg esub` node:

  (.unary .neg esub).stackNeed = evalFrame + esub.stackNeed          -- by rfl
                               = 1088 + esub.stackNeed
                               ≥ 1088 + 1088 = 2176                   -- stackNeed_ge

so the budgeted `stackBudget : StackOK SL sp ((.unary .neg esub).stackNeed
+ (maxCallDepth - d) * perCallBudget + 1088)` gives

  SL.lo + (stackNeed + _ + 1088) ≤ sp.toNat
  ⇒ SL.lo + (2176 + 0 + 1088) = SL.lo + 3264 ≤ sp.toNat.

This is the exact fact the recursive-arm child previously demanded as an
∀-closed oracle premise.  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail
open Vsa.Sim Vsa.While Vsa.Alloc Vsa.RuntimeRepr Vsa.MemRepr
open Vsa.Machine (Config)

/-- **The previously-refuted headroom is now a field consequence.** -/
theorem itemzero_neg_sp_headroom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : St) (d : Nat) (a : Addr) (esub : Expr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config)
    (hc : EvalEntry g N A SL φf φc st d a (.unary .neg esub)
            sp r sret aEnv aExpr m0 c) :
    SL.lo + 3264 ≤ sp.toNat := by
  -- The budgeted headroom, ascribed so no `EvalEntry` projection reaches `omega`
  -- (a raw `omega` here whnf-overflows the large structure — CLAUDE.md law 1).
  have hbud : SL.lo + ((Expr.unary .neg esub).stackNeed
      + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ≤ sp.toNat :=
    hc.stackBudget.1
  -- `esub.stackNeed ≥ evalFrame = 1088`, so the node need `≥ 2176`.
  have hge : evalFrame ≤ esub.stackNeed := esub.stackNeed_ge
  have hstep : (3264 : Nat) ≤ (Expr.unary .neg esub).stackNeed
      + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088 := by
    have h1 : (Expr.unary .neg esub).stackNeed = evalFrame + esub.stackNeed := rfl
    have h2 : (2176 : Nat) ≤ (Expr.unary .neg esub).stackNeed := by
      rw [h1]; exact Nat.add_le_add (Nat.le_refl evalFrame) hge
    calc (3264 : Nat) = 2176 + 1088 := rfl
      _ ≤ (Expr.unary .neg esub).stackNeed + 1088 := Nat.add_le_add_right h2 _
      _ ≤ (Expr.unary .neg esub).stackNeed
            + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088 :=
          Nat.add_le_add_right (Nat.le_add_right _ _) _
  exact Nat.le_trans (Nat.add_le_add_left hstep SL.lo) hbud

#print axioms itemzero_neg_sp_headroom
