import Vsa.Sim.rows.ArmDispatchCombinatorExec
import Vsa.Sim.rows.StmtExprArmStagePre
import Vsa.Sim.rows.StmtRetArmStagePre
import Vsa.Sim.rows.StmtVarInitArmStagePre
import Vsa.Sim.rows.StmtIfCondArmStagePre
import Vsa.Sim.rows.StmtWhileCondArmStagePre

/-!
# `ArmDispatchInstancesExec` — Group-B instantiations (wave 44)

The five `ExecEntry`-headed `Stmt*ArmDispatch` residuals discharged from the
parametric combinator `execArmDispatch_of_slot`
(`rows/ArmDispatchCombinatorExec.lean`):

| residual                   | tag | arm PC       | child payload | node span |
|----------------------------|-----|--------------|---------------|-----------|
| `StmtExprArmDispatch`      | 0   | `0x80004170` | `+8`          | 16        |
| `StmtVarInitArmDispatch`   | 1   | `0x800040d8` | `+16`         | 24        |
| `StmtIfCondArmDispatch`    | 3   | `0x800041e8` | `+8`          | 16        |
| `StmtWhileCondArmDispatch` | 4   | `0x8000403c` | `+8`          | 16        |
| `StmtRetArmDispatch`       | 6   | `0x80004120` | `+8`          | 16        |

Each instantiation is the ~10-line pattern: intro the entry, obtain the shared
extras from the ONE named residual `ExecArmDispatchResid`, read the kind tag
off the node's `StmtRepr` (one `cases`), and apply the combinator.

NOT instantiable here (different class, see `experiments/observations.md`
`armdispatch-class-split`): `FlCondArmDispatch` + the Group-C loop-body
dispatches (`FlBody`/`WhileBody`/`ForInit`) + `ArgsHeadDispatch` — their
entries are `FEntryC`/`AEntryC`-style `SegEntry` ∃-packs at GHOST interior PCs
(no `ExecEntry`, no jump-table run to consume), so no slot combinator applies.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-- **The ONE shared Group-B residual** — for a row `(k, armPC, s, ce, payOff,
nodeHi)`: at every entry instantiation, the extras record holds (with the
node's child payload pointer as the witness).  Entry-side facts only (slot pin
+ payload/survival + wide-window store survival + `jsp`-form geometry);
supplied by the M6 Layout / `ExecCaseGeom` widening. -/
def ExecArmDispatchResid (k : Nat) (armPC : BitVec 64) (s : Stmt) (ce : Expr)
    (payOff nodeHi : Nat) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c →
    ∃ aChild : BitVec 64,
      ExecArmHeadExtras N A SL φf φc st k armPC ce payOff nodeHi
        sp aInterp aStmt aChild m0

/-- **`StmtExprArmDispatch` discharged** (tag 0 → `0x80004170`, child at `+8`). -/
theorem stmtExprArmDispatch_of_resid
    (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config)
    (hR : ExecArmDispatchResid 0 (0x80004170#64) (.expr e) e 8 16 st d env c) :
    StmtExprArmDispatch e st d env c := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  exact execArmDispatch_of_slot g N A SL φf φc st d env (.expr e) 0 (0x80004170#64)
    e 8 16 sp r aInterp aStmt aEnv aRet aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.stmt) with | expr hk _ _ => exact hk)
    (Vsa.Alloc.StackOK.child (by decide) (by
      have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
      simp only [Stmt.stackNeed, execFrame, h176]; omega) hE.stackBudget)
    (by exact hE.stmt_bodies)
    hX hE

#print axioms stmtExprArmDispatch_of_resid

/-- **`StmtRetArmDispatch` discharged** (tag 6 → `0x80004120`, child at `+8`). -/
theorem stmtRetArmDispatch_of_resid
    (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config)
    (hR : ExecArmDispatchResid 6 (0x80004120#64) (.ret (some e)) e 8 16 st d env c) :
    StmtRetArmDispatch e st d env c := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  exact execArmDispatch_of_slot g N A SL φf φc st d env (.ret (some e)) 6
    (0x80004120#64) e 8 16 sp r aInterp aStmt aEnv aRet aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.stmt) with | retSome hk _ _ _ => exact hk)
    (Vsa.Alloc.StackOK.child (by decide) (by
      have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
      simp only [Stmt.stackNeed, execFrame, h176]; omega) hE.stackBudget)
    (by exact hE.stmt_bodies)
    hX hE

#print axioms stmtRetArmDispatch_of_resid

/-- **`StmtVarInitArmDispatch` discharged** (tag 1 → `0x800040d8`, init at `+16`). -/
theorem stmtVarInitArmDispatch_of_resid
    (x : String) (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config)
    (hR : ExecArmDispatchResid 1 (0x800040d8#64) (.varDecl x (some e)) e 16 24
      st d env c) :
    StmtVarInitArmDispatch x e st d env c := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  exact execArmDispatch_of_slot g N A SL φf φc st d env (.varDecl x (some e)) 1
    (0x800040d8#64) e 16 24 sp r aInterp aStmt aEnv aRet aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.stmt) with | varInit hk _ _ _ _ _ => exact hk)
    (Vsa.Alloc.StackOK.child (by decide) (by
      have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
      simp only [Stmt.stackNeed, execFrame, h176]; omega) hE.stackBudget)
    (by exact hE.stmt_bodies)
    hX hE

#print axioms stmtVarInitArmDispatch_of_resid

/-- **`StmtIfCondArmDispatch` discharged** (tag 3 → `0x800041e8`, cond at `+8`;
both the `some`- and `none`-else node shapes carry the same tag). -/
theorem stmtIfCondArmDispatch_of_resid
    (cnd : Expr) (t : Stmt) (els : Option Stmt) (st : Vsa.While.St) (d : Nat)
    (env : Addr) (c : Config)
    (hR : ExecArmDispatchResid 3 (0x800041e8#64) (.ifStmt cnd t els) cnd 8 16
      st d env c) :
    StmtIfCondArmDispatch cnd t els st d env c := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  exact execArmDispatch_of_slot g N A SL φf φc st d env (.ifStmt cnd t els) 3
    (0x800041e8#64) cnd 8 16 sp r aInterp aStmt aEnv aRet aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.stmt) with
      | ifElse hk _ _ _ _ _ _ _ => exact hk
      | ifNoElse hk _ _ _ _ _ => exact hk)
    (by
      have hB := hE.stackBudget
      have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
      rcases els with _ | e2
      · refine Vsa.Alloc.StackOK.child (by decide) ?_ hB
        have hm := Nat.le_max_left cnd.stackNeed t.stackNeed
        simp only [Stmt.stackNeed, execFrame, h176]; omega
      · refine Vsa.Alloc.StackOK.child (by decide) ?_ hB
        have hm := Nat.le_max_left cnd.stackNeed (max t.stackNeed e2.stackNeed)
        simp only [Stmt.stackNeed, execFrame, h176]; omega)
    (by
      have h := hE.stmt_bodies
      rcases els with _ | e2 <;>
        simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
      · exact h.1
      · exact h.1.1)
    hX hE

#print axioms stmtIfCondArmDispatch_of_resid

/-- **`StmtWhileCondArmDispatch` discharged** (tag 4 → `0x8000403c`, cond at `+8`). -/
theorem stmtWhileCondArmDispatch_of_resid
    (cnd : Expr) (b : Stmt) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config)
    (hR : ExecArmDispatchResid 4 (0x8000403c#64) (.whileStmt cnd b) cnd 8 16
      st d env c) :
    StmtWhileCondArmDispatch cnd b st d env c := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  obtain ⟨aChild, hX⟩ := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hE
  exact execArmDispatch_of_slot g N A SL φf φc st d env (.whileStmt cnd b) 4
    (0x8000403c#64) cnd 8 16 sp r aInterp aStmt aEnv aRet aChild m0 c
    (by omega) (by omega) (by decide) (by omega)
    (by cases (hE.mem ▸ hE.stmt) with | whileS hk _ _ _ _ => exact hk)
    (by
      refine Vsa.Alloc.StackOK.child (by decide) ?_ hE.stackBudget
      have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
      have hm := Nat.le_max_left cnd.stackNeed b.stackNeed
      simp only [Stmt.stackNeed, execFrame, h176]; omega)
    (by
      have h := hE.stmt_bodies
      simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
      exact h.1)
    hX hE

#print axioms stmtWhileCondArmDispatch_of_resid

end Vsa.Sim
