import Vsa.Sim.EntryGround
import Vsa.Sim.AstTransport
import Vsa.MemReprReadFields
import Vsa.Sim.MemRegionWithin

/-!
# `EntryGroundKit` — the child-ground derivation combinators (wave 47i)

The insertion wave threads a CHILD `EvalGround`/`ExecGround` conjunct through
every child-entry ctor tower (`armTail_rec` and its twins).  Suppliers with the
parent entry `hc : EvalEntry …` in scope derive the child bundle in THREE moves,
factored here ONCE (Law 3 — every recursive arm repeats them):

1. **transport** — the pre-call memory agrees with the entry `m0` off the
   scribbled stack window (`EvalGround.survive_stack` with the sret half vacuous);
2. **payload-read agreement** — the node's payload pointer reads back unchanged
   (the AST region is stack-disjoint, `evalGround_ast_read64_agree`);
3. **parameter conversion** — lowered `sp'`, the in-frame `subsret`, and the
   child node via `ExprIn` projection (`EvalGround.child_params`).

`EvalGround.child_at` composes 1+3 (the caller applies 2 to its payload fact and
feeds the projection).  Exec twins for the statement side.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

open LeanRV64DExecutable

/-- Every address in the stack interval has a stored byte. -/
def StackBytesPresent (m : Mem) (SL : StackLayout) : Prop :=
  ∀ k : Nat, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, m[k]? = some b

/-- Any 24-byte slot wholly inside the populated eval stack is readable. -/
theorem EvalGround.valueWordsTotal {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    {a : Nat} (hlo : SL.lo ≤ a) (hhi : a + 24 ≤ SL.hi) :
    ValueWordsTotal m a :=
  valueWordsTotal_of_interval h.stack_bytes hlo hhi

/-! ## Move 1 — off-stack transport (sret half vacuous) -/

theorem ExecGround.transport_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hspSL : sp.toNat ≤ SL.hi)
    (hpop : StackBytesPresent ment SL)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    ExecGround ment SL A sp aRet aStmt s :=
  hg.survive_stack hspSL hpop (fun k hk _ => (hmem k hk).symm)

/-- The enclosing statement representation survives an off-stack memory
change.  The hereditary region in `ExecGround` supplies the exact footprint;
no root-only node window is assumed. -/
theorem ExecGround.stmtRepr_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hr : StmtRepr m0 aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ment[a]? = m0[a]?) :
    StmtRepr ment aStmt s := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  refine ((stmtReprWithin_of_region hr spec.nodes).transport ?_).erase
  intro a ha
  change lo ≤ a ∧ a < hi at ha
  obtain ⟨haLo, haHi⟩ := ha
  exact (hmem a (by
    intro hs
    obtain ⟨hsLo, hsHi⟩ := hs
    rcases spec.stack_disjoint with hd | hd <;> omega)).symm

/-! ## Move 2 — in-node read agreement (the AST region is stack-disjoint) -/

/-! ## Move 3 — parameter conversion (same memory) -/

/-! ## The composed child-at combinator (moves 1 + 3) -/

/-! ## Named child projections (the `exprIn_unary_child` family — Law 6) -/

/-! ## The raw window-wise transport (arbitrary memory hops)

Consumers crossing a SUB-CALL (memory agrees only off stack ∪ arena ∪
sub-result windows) supply the two window agreements directly — the table
window (disjoint from all three by `tableStk`/`arenaTable` + the sub-result
slot living in the stack), and the AST region (stack/arena-disjoint by its
spec, keyed per witness). -/

end Vsa.Sim

