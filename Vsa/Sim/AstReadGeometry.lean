import Vsa.Sim.AstReadGeometryCore
import Vsa.Sim.RuntimeOwnershipInitial

namespace Vsa.Sim
open Vsa.MemRepr Vsa.While Vsa.Alloc RuntimeOwnership

/-- Runtime immutable ownership supplies the low-level read-domain contract. -/
theorem SharedReadDomain.of_immutable {SL : StackLayout} {alloc : Allocations}
    {shared : Nat → Prop}
    (h : Immutable alloc shared InitialReadableByte (InitialWriteByte SL)) :
    SharedReadDomain SL shared := by
  refine ⟨h.readable, ?_, ?_⟩
  · intro k hk hin
    apply h.outsideWrites k hk
    left
    change 0x8001ad00 ≤ k ∧ k < 0x8001c168
    change 0x8001ad00 ≤ k ∧ k < 0x8001ad00 + 16 at hin
    omega
  · intro k hk hs
    exact h.outsideWrites k hk (Or.inr hs)

/-- Exact coverage and the existing immutable domain supply read geometry. -/
theorem AstReadGeometry.of_covered {SL : StackLayout} {alloc : Allocations}
    {shared : Nat → Prop} {a width : Nat}
    (h : Immutable alloc shared InitialReadableByte (InitialWriteByte SL))
    (hc : Covers shared a width) (hw : 0 < width) : AstReadGeometry SL a width :=
  .of_domain (.of_immutable h) hc hw

/-- Every represented expression field inherits its own read geometry. -/
theorem AstReadGeometry.expr_field {SL : StackLayout} {alloc : Allocations}
    {shared : Nat → Prop} {m : Mem} {a : Nat} {e : Expr}
    (h : Immutable alloc shared InitialReadableByte (InitialWriteByte SL))
    (hr : ExprReprWithin m shared a e) (f : ReadField) (hf : f ∈ exprReadFields e) :
    AstReadGeometry SL (a + f.offset) f.width :=
  (SharedReadDomain.of_immutable h).expr_field hr f hf

/-- Every represented statement field inherits its own read geometry. -/
theorem AstReadGeometry.stmt_field {SL : StackLayout} {alloc : Allocations}
    {shared : Nat → Prop} {m : Mem} {a : Nat} {s : Stmt}
    (h : Immutable alloc shared InitialReadableByte (InitialWriteByte SL))
    (hr : StmtReprWithin m shared a s) (f : ReadField) (hf : f ∈ stmtReadFields s) :
    AstReadGeometry SL (a + f.offset) f.width :=
  (SharedReadDomain.of_immutable h).stmt_field hr f hf

#print axioms SharedReadDomain.of_immutable
#print axioms AstReadGeometry.of_covered
#print axioms AstReadGeometry.expr_field
#print axioms AstReadGeometry.stmt_field
end Vsa.Sim
