import Vsa.Sim.DriveToLoopHeadSpans

/-! Transport the initial owned AST through the proved prologue memory frame.
The owned-byte predicate remains indexed by the initial snapshot. -/

namespace Vsa.Sim.LayoutInstance

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

theorem InterpRunReadyFacts.prologue_mutable
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft k : Nat}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hk : interpRunWriteFootprint inp k) :
    RuntimeOwnership.InitialWriteByte stackSL k := by
  apply Or.inr
  rcases hk with hs | hj
  · exact hs
  · rw [F.interp_local] at hj
    change 0x87fffe20 ≤ k ∧ k < 0x87fffe90 at hj
    change 0x87800000 ≤ k ∧ k < 0x88000000
    omega

/-- Restrict the actual prologue frame to the initial owned reads. -/
theorem InterpRunReadyFacts.ast_after_prologue
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat} {p : Vsa.While.Program} {m' : Mem}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p)
    (hframe : ∀ k, ¬ interpRunWriteFootprint inp k → c.σ.mem[k]? = m'[k]?) :
    ProgramReprWithin m' (fun k => ¬ RuntimeOwnership.InitialWriteByte stackSL k)
      stmts count p := by
  apply (F.ast_owned p hp).transport
  intro k hk
  exact hframe k (fun hw => hk (F.prologue_mutable hw))

end Vsa.Sim.LayoutInstance

namespace Vsa.Sim

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While

/-- Every reached prefix carrier preserves the initial AST ownership predicate. -/
theorem ReadyPrefixFacts.ast_owned
    {c0 c1 : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {aLeft : Nat} {p : Program}
    (L : ReadyPrefixFacts inp c0 c1)
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (hp : ProgramRepr c0.σ.mem stmts count p) :
    ProgramReprWithin c1.σ.mem
      (fun k => ¬ RuntimeOwnership.InitialWriteByte LayoutInstance.stackSL k)
      stmts count p :=
  F.ast_after_prologue hp L.outside_writes

#print axioms LayoutInstance.InterpRunReadyFacts.prologue_mutable
#print axioms LayoutInstance.InterpRunReadyFacts.ast_after_prologue
#print axioms ReadyPrefixFacts.ast_owned

end Vsa.Sim
