import Vsa.Sim.rows.ArmDispatchCombinator
import Vsa.Sim.rows.AssignArmStagePre
import Vsa.Sim.rows.CallArmStagePre

/-!
# `ArmDispatchInstancesEval` — Group-A instantiations (wave 44)

The two eval-side `*ArmDispatch` residuals discharged from the parametric
combinator `evalArmDispatch_of_slot` (`rows/ArmDispatchCombinator.lean`):

* `AssignArmDispatch` (tag 5, arm `0x8000347c`, child = RHS node at `+16`);
* `CallArmDispatch`   (tag 9, arm `0x800031b0`, child = callee node at `+8`).

Each instantiation is the ~10-line pattern: intro the entry, obtain the shared
extras from the ONE named residual `EvalArmDispatchResid`, read the kind tag
off the node's `ExprRepr` (one `cases`), and apply the combinator — the Mid
towers are definitionally the combinator's conclusion at the row parameters.

The remaining premise `EvalArmDispatchResid` is entry-side ONLY (slot pin +
payload/survival/geometry + the `x13_pres` liveness closure): no Triple, no
machine run — the M6 Layout / `EvalCaseGeom` widening supplies it uniformly.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-- **The ONE shared Group-A residual** — for a row `(k, armPC, e, ce, payOff,
nodeHi)`: at every entry instantiation, the extras record holds (with the
node's child payload pointer as the witness).  Entry-side facts only; supplied
by the M6 Layout / `EvalCaseGeom` widening (slot pins from
`LayoutJumpTableGen.groundSlot_<k>`). -/
def EvalArmDispatchResid (k : Nat) (armPC : BitVec 64) (e ce : Expr)
    (payOff nodeHi : Nat) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env e sp r0 sret aEnv aExpr m0 c →
    ∃ aChild : BitVec 64,
      EvalArmHeadExtras g N A SL k armPC e ce payOff nodeHi sp sret aExpr aChild m0

/-- **`AssignArmDispatch` discharged** (tag 5 → `0x8000347c`, RHS at `+16`). -/
theorem assignArmDispatch_of_resid
    (x : String) (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config)
    (hR : EvalArmDispatchResid 5 (0x8000347c#64) (.assign x e) e 16 24 st d env c) :
    AssignArmDispatch x e st d env c := by
  intro g N A SL φf φc sp r0 sret aEnv aExpr m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r0 sret aEnv aExpr m0 hE
  exact evalArmDispatch_of_slot g N A SL φf φc st d env 5 (0x8000347c#64)
    (.assign x e) e 16 24 sp r0 sret aEnv aExpr aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.expr) with | assign hk _ _ _ _ => exact hk)
    hX hE

#print axioms assignArmDispatch_of_resid

/-- **`CallArmDispatch` discharged** (tag 9 → `0x800031b0`, callee at `+8`). -/
theorem callArmDispatch_of_resid
    (f : Expr) (args : List Expr) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (c : Config)
    (hR : EvalArmDispatchResid 9 (0x800031b0#64) (.call f args) f 8 16 st d env c) :
    CallArmDispatch f args st d env c := by
  intro g N A SL φf φc sp r0 sret aEnv aExpr m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r0 sret aEnv aExpr m0 hE
  exact evalArmDispatch_of_slot g N A SL φf φc st d env 9 (0x800031b0#64)
    (.call f args) f 8 16 sp r0 sret aEnv aExpr aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.expr) with | call hk _ _ _ _ _ => exact hk)
    hX hE

#print axioms callArmDispatch_of_resid

end Vsa.Sim
