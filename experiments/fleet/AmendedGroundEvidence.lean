import Vsa.Sim.rows.AssemblySkeleton

/-!
# ITEM ZERO — positive evidence that the falsity-#12 witnesses are CLOSED

Task-(d) companion to re-running the three obstruction files (which now FAIL to
elaborate).  Each lemma here shows the fleet's refuting instantiation now
CONTRADICTS the new entry-side hypothesis of the amended residual:

* B5's `m0 = ∅` witness: no config satisfies `ExecEntry … ∅` (the `code` field
  demands `Exec_stmtLoaded ∅`, whose first byte lookup is `none`);
* B2's `sp = 0` witness: no config satisfies `EvalEntry` at `SL = ⟨0,0⟩`,
  `sp = 0` (the `stackOK` field demands `SL.lo + 2176 ≤ 0`);
* B1's `sret`-in-code window witness (`m0 = ∅`): no config satisfies
  `EvalEntry … ∅` (same `code` route via `InterpCodeLoaded = Eval_exprLoaded`).

So every amended `*Resid` is VACUOUSLY satisfied at the fleet's witnesses — the
refutation routes are closed, and the remaining content of each field is the
honest geometry/glue conditioned on a REAL entry.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.Rows
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

namespace Vsa.Sim.AmendedGroundEvidence

/-- The empty spec state (the fleet's shared witness). -/
def st0 : SpecSt := ⟨⟨#[], #[]⟩, ""⟩

/-- **The B5 route is closed**: the amended `BrkResid`'s hypothesis
`ExecEntry … ∅ cfg` is unsatisfiable — `code : Exec_stmtLoaded ∅` fails at its
first byte pin. -/
theorem execEntry_empty_unsat
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (cfg : Config) :
    ¬ Vsa.Sim.ExecEntry g N A SL φf φc st d env s
        sp r aInterp aStmt aEnv aRet (∅ : Mem) cfg := by
  intro h
  have hcode := h.code
  rw [h.mem] at hcode
  have h0 := hcode.1.1
  simp at h0

/-- **The B1 route is closed**: the amended leaf residuals' hypothesis
`EvalEntry … ∅ cfg` is unsatisfiable — `code : InterpCodeLoaded ∅`
(= `Eval_exprLoaded ∅`) fails at its first byte pin.  (B1's witnesses put
`sret` inside the `value_*` code windows with `m0 = ∅`.) -/
theorem evalEntry_empty_unsat
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (sp r sret aEnv aExpr : BitVec 64) (cfg : Config) :
    ¬ Vsa.Sim.EvalEntry g N A SL φf φc st d env e
        sp r sret aEnv aExpr (∅ : Mem) cfg := by
  intro h
  have hcode := h.code
  rw [h.mem] at hcode
  have h0 := hcode.1.1
  simp at h0

/-- **The B2 route is closed**: the amended unary/logical residuals' hypothesis
`EvalEntry` at the fleet's `SL = ⟨0,0⟩`, `sp = 0#64` witness is unsatisfiable —
`stackOK : StackOK ⟨0,0⟩ 0 (1088+1088)` demands `2176 ≤ 0`.  (Independent of
the witness memory, so it also closes the `b2WitMem` instantiations.) -/
theorem evalEntry_spZero_unsat
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (r sret aEnv aExpr : BitVec 64) (m0 : Mem) (cfg : Config) :
    ¬ Vsa.Sim.EvalEntry g N A ⟨0, 0⟩ φf φc st d env e
        (0#64) r sret aEnv aExpr m0 cfg := by
  intro h
  exact absurd h.stackOK.1 (by decide)

/-- **Smoke-test corollary** (the amended statements are inhabitable at the old
witnesses): each amended B2-shaped residual holds VACUOUSLY at the fleet's
refuting instantiation — e.g. `NegResid` at `sp = 0`, `SL = ⟨0,0⟩`.  (This is
exactly the instantiation `field_hNeg_refuted` used to refute the OLD
statement.) -/
theorem negResid_at_b2_witness_vacuous
    (st : SpecSt) (esub : Expr)
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (g : (R : Register) → Option (RegisterType R))
    (d : Nat) (env : Addr)
    (r sret aEnv aExpr aOperand : BitVec 64) (m0 : Mem) (c : Config) :
    Vsa.Sim.EvalEntry g N A ⟨0, 0⟩ φf φc st d env (.unary .neg esub)
        (0#64) r sret aEnv aExpr m0 c →
    read64 m0 (aExpr.toNat + 16) = some aOperand.toNat →
    ExprRepr m0 aOperand.toNat esub →
    Vsa.Sim.NegExtras N A ⟨0, 0⟩ st esub (0#64) sret aExpr aOperand m0 ∧
    (∀ mcall : Mem,
      (∀ a : Nat, ¬ ((0 : Nat) ≤ a ∧ a < (0#64 : BitVec 64).toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, ∃ b, mcall[a]? = some b) := by
  intro hE
  exact absurd hE (evalEntry_spZero_unsat g N A φf φc st d env _ r sret aEnv aExpr m0 _)

end Vsa.Sim.AmendedGroundEvidence

#print axioms Vsa.Sim.AmendedGroundEvidence.execEntry_empty_unsat
#print axioms Vsa.Sim.AmendedGroundEvidence.evalEntry_empty_unsat
#print axioms Vsa.Sim.AmendedGroundEvidence.evalEntry_spZero_unsat
#print axioms Vsa.Sim.AmendedGroundEvidence.negResid_at_b2_witness_vacuous
