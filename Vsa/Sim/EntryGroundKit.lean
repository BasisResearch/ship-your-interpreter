import Vsa.Sim.AstTransport
import Vsa.MemReprReadFields
import Vsa.Sim.MemRegionWithin
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry

open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

open LeanRV64DExecutable

def StackBytesPresent (m : Mem) (SL : StackLayout) : Prop :=
  ∀ k : Nat, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, m[k]? = some b

theorem EvalGround.valueWordsTotal {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    {a : Nat} (hlo : SL.lo ≤ a) (hhi : a + 24 ≤ SL.hi) :
    ValueWordsTotal m a :=
  valueWordsTotal_of_interval h.stack_bytes hlo hhi

theorem ExecGround.transport_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hspSL : sp.toNat ≤ SL.hi)
    (hpop : StackBytesPresent ment SL)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    ExecGround ment SL A sp aRet aStmt s :=
  hg.survive_stack hspSL hpop (fun k hk _ => (hmem k hk).symm)

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

end Vsa.Sim
