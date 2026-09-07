import Vsa.Sim.EvalNegSim3
import Vsa.Sim.rows.TermRouting

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Specialize shared unary entry geometry to arithmetic negation. -/
theorem EvalEntry.negExtras
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {d env : Nat} {esub : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.unary .neg esub)
      sp r sret aEnv aExpr m0 c) :
    ∃ aOperand, NegExtras N A SL st esub sp sret aExpr aOperand m0 :=
  h.unaryExtras

/-- Closed negation residual, consuming only the actual child derivation and IH. -/
theorem ScaffoldRows.field_hNeg (st : Vsa.While.St) (esub : Expr) :
    Rows.NegResid st esub := by
  intro d env st' n hE hIH g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aOperand, hx⟩ := hc.negExtras
  exact evalNegSim g N A SL phiF phiC st st' d env esub n sp r sret aEnv aExpr
    aOperand m0 hIH (.neg st d env esub st' n hE) c ⟨hc, hx⟩

#print axioms EvalEntry.negExtras
#print axioms ScaffoldRows.field_hNeg

end Vsa.Sim
