import Vsa.Sim.AstOwnershipPreservation
import Vsa.MemReprWithinInter

/-! Preserve physical readability and ownership through the same actual writes.
The mutable-byte predicate is frozen at the initial memory and region indices. -/

namespace Vsa.MemRepr

/-- Coverage of every byte gives the normal-RAM bounds for a nonempty read. -/
theorem Covers.readable_bounds {a width : Nat}
    (h : Covers (fun k => 0x80000000 ≤ k ∧ k < 0x100000000) a width)
    (hw : 0 < width) : 0x80000000 ≤ a ∧ a + width ≤ 0x100000000 := by
  have first := h 0 hw
  have last := h (width - 1) (by omega)
  omega

end Vsa.MemRepr

namespace Vsa.Sim.LayoutInstance
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

theorem InterpRunReadyFacts.ast_owned_readable
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat} {p : Vsa.While.Program}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p) :
    ProgramReprWithin c.σ.mem
      (fun k => (¬ RuntimeOwnership.InitialWriteByte stackSL k) ∧
        (0x80000000 ≤ k ∧ k < 0x100000000)) stmts count p :=
  (F.ast_owned p hp).inter (F.ast_readable p hp)

theorem InterpRunReadyFacts.ast_owned_readable_after_prologue
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat} {p : Vsa.While.Program} {m' : Mem}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p)
    (hframe : ∀ k, ¬ interpRunWriteFootprint inp k → c.σ.mem[k]? = m'[k]?) :
    ProgramReprWithin m'
      (fun k => (¬ RuntimeOwnership.InitialWriteByte stackSL k) ∧
        (0x80000000 ≤ k ∧ k < 0x100000000)) stmts count p := by
  apply (F.ast_owned_readable hp).transport
  intro k hk
  exact hframe k (fun hw => hk.1 (F.prologue_mutable hw))

end Vsa.Sim.LayoutInstance

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While

theorem ReadyPrefixFacts.ast_owned_readable
    {c0 c1 : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {aLeft : Nat} {p : Program}
    (L : ReadyPrefixFacts inp c0 c1)
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A φf φc aLeft)
    (hp : ProgramRepr c0.σ.mem stmts count p) :
    ProgramReprWithin c1.σ.mem
      (fun k => (¬ RuntimeOwnership.InitialWriteByte LayoutInstance.stackSL k) ∧
        (0x80000000 ≤ k ∧ k < 0x100000000)) stmts count p :=
  F.ast_owned_readable_after_prologue hp L.outside_writes

#print axioms Vsa.MemRepr.Covers.readable_bounds
#print axioms LayoutInstance.InterpRunReadyFacts.ast_owned_readable
#print axioms LayoutInstance.InterpRunReadyFacts.ast_owned_readable_after_prologue
#print axioms ReadyPrefixFacts.ast_owned_readable
end Vsa.Sim
