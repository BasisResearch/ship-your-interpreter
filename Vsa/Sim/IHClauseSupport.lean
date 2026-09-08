import Vsa.Sim.EvalReturn
import Vsa.Sim.ExitFootprint

/-!
# Induction-hypothesis clauses — shared support

A clause is an `EvalExtraM` predicate recursed through the mutual family as the
`EvalIHWithM` motive (`Vsa/Sim/ExitFootprint.lean`); an `EvalExtra` clause embeds
through `EvalIHWith.toM`. `scripts/gen_ih_clause.py`
emits one module per declared clause (`scripts/ih_clauses.tsv`) into
`Vsa/Sim/rows/IHClause_<Name>.lean`: the nine clause motives, a named-field
`Residuals` record with one field per recursor case, and the recursor
application `of_residuals`. This module holds the clause-independent pieces the
generated modules and their dischargers share.
-/

namespace Vsa.Sim.IHClause

open Vsa.While

/-- The clause that holds of every child execution. -/
abbrev trueExtra : EvalExtra := fun _ _ _ _ _ _ _ => True

/-- Every recursor case of the trivial clause: the step follows from the old
motive alone (`from_old` discharger of the `Trivial` clause), stated at the
generated motive shape `EvalIHWithM (embedding of trueExtra)`. -/
theorem trivialStep_of_old {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalReturnIH TrivialOwned st d env e st' v) :
    EvalIHWithM (fun N A SL φf φc _ sret _ => trueExtra N A SL φf φc sret.toNat)
      st d env e st' v :=
  (EvalIH.withTrue h.forget).toM

/-- The recursive-eval motive already retains the old motive's selected maps at
the child's actual return; a clause discharger that needs them takes this
projection rather than re-running the child. -/
theorem withMaps_of_old {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalReturnIH TrivialOwned st d env e st' v) :
    EvalIHWith (fun N A SL phiF phiC a =>
      EvalReturnData N A SL phiF phiC st.store.frames.size st.store.closures.size
        st' v a (TrivialOwned N A)) st d env e st' v :=
  h.withMaps

/-- Weaken a retained clause pointwise at the child's actual return. -/
theorem EvalIHWith.mono {P Q : EvalExtra} {st st' : Vsa.While.St} {d env : Nat}
    {e : Expr} {v : Value}
    (h : EvalIHWith P st d env e st' v)
    (hpq : ∀ N A SL phiF phiC a c, P N A SL phiF phiC a c → Q N A SL phiF phiC a c) :
    EvalIHWith Q st d env e st' v where
  run := fun g N A SL phiF phiC sp r sret aEnv aExpr m0 =>
    (h.run g N A SL phiF phiC sp r sret aEnv aExpr m0).conseq
      (fun _ hp => hp) (fun _ hp => ⟨hp.result, hpq _ _ _ _ _ _ _ hp.extra⟩)

#print axioms trivialStep_of_old
#print axioms withMaps_of_old
#print axioms EvalIHWith.mono

end Vsa.Sim.IHClause
