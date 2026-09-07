import Vsa.Sim.EntryGroundKit

namespace Vsa.Sim

open LeanRV64DExecutable
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

/-- Statement facts needed at every remaining array entry. Register layout,
environment validity, and the current store belong to the sequence carrier. -/
structure SeqStmtGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet : BitVec 64) (d aStmt : Nat) (s : Stmt) : Prop where
  stmt : StmtRepr m aStmt s
  ground : ExecGround m SL A sp aRet aStmt s
  stackBudget : StackOK SL sp
    (s.stackNeed + (maxCallDepth - d) * perCallBudget + 1088)
  bodies : Stmt.bodiesBound perCallBudget s = true

/-- The exact remaining pointer array, with hereditary statement and budget
facts for every element. The empty suffix needs no machine load. -/
inductive SeqSuffixGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet : BitVec 64) (d : Nat) : Nat → List Stmt → Prop where
  | nil {a : Nat} : SeqSuffixGround m SL A sp aRet d a []
  | cons {a p : Nat} {s : Stmt} {ss : List Stmt} :
      read64 m a = some p →
      SeqStmtGround m SL A sp aRet d p s →
      SeqSuffixGround m SL A sp aRet d (a + 8) ss →
      SeqSuffixGround m SL A sp aRet d a (s :: ss)

/-- Pointer-array bytes excluded from every write allowed by a child exit. -/
def SeqArrayReadSafe (SL : StackLayout) (A : Arena) (sp aRet : BitVec 64)
    (a n : Nat) : Prop :=
  ∀ k, a ≤ k ∧ k < a + 8 * n →
    ¬ (SL.lo ≤ k ∧ k < sp.toNat) ∧ ¬ (A.lo ≤ k ∧ k < A.hi) ∧
      ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24)

theorem SeqArrayReadSafe.tail
    {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64} {a n : Nat}
    (h : SeqArrayReadSafe SL A sp aRet a (n + 1)) :
    SeqArrayReadSafe SL A sp aRet (a + 8) n := by
  intro k hk
  exact h k ⟨by omega, by omega⟩

theorem SeqSuffixGround.head
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {d a : Nat} {s : Stmt} {ss : List Stmt}
    (h : SeqSuffixGround m SL A sp aRet d a (s :: ss)) :
    ∃ p, read64 m a = some p ∧ SeqStmtGround m SL A sp aRet d p s := by
  cases h with
  | cons hread hstmt _ => exact ⟨_, hread, hstmt⟩

theorem SeqSuffixGround.tail
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {d a : Nat} {s : Stmt} {ss : List Stmt}
    (h : SeqSuffixGround m SL A sp aRet d a (s :: ss)) :
    SeqSuffixGround m SL A sp aRet d (a + 8) ss := by
  cases h with
  | cons _ _ htail => exact htail

theorem SeqSuffixGround.array
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet : BitVec 64}
    {d a : Nat} {ss : List Stmt}
    (h : SeqSuffixGround m SL A sp aRet d a ss) :
    StmtArrayRepr m a ss.length ss := by
  induction h with
  | nil => exact .nil
  | cons hread hstmt _ ih => exact .cons hread hstmt.stmt ih

/-- Transport a statement using the actual child's frame and presence facts.
An `ExecExitD` supplies these arguments as `.1` and `.2.1`. Keeping that
wrapper out of this module avoids an import cycle with `ExecSimCommon`. -/
theorem SeqStmtGround.transport_execExit
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet r : BitVec 64}
    {d aStmt : Nat} {s : Stmt}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {φf φc : Addr → Nat} {nf nc : Nat} {st' : Vsa.While.St} {status : Status}
    {cfg : Config}
    (h : SeqStmtGround m SL A sp aRet d aStmt s)
    (hExit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m cfg)
    (hExt : MemExtends m cfg.σ.mem) :
    SeqStmtGround cfg.σ.mem SL A sp aRet d aStmt s := by
  exact
    { stmt := h.ground.stmtRepr_execExit h.stmt h.stackBudget.2.1 hExit.memFrame
      ground := h.ground.transport_execExit h.stackBudget.2.1
        (fun k hlo hhi => by
          obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
          exact hExt k b hb) hExit.memFrame
      stackBudget := h.stackBudget
      bodies := h.bodies }

theorem SeqArrayReadSafe.agree_execExit
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet r : BitVec 64}
    {a n : Nat} {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {φf φc : Addr → Nat} {nf nc : Nat}
    {st' : Vsa.While.St} {status : Status} {cfg : Config}
    (h : SeqArrayReadSafe SL A sp aRet a n)
    (hExit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m cfg) :
    AgreeP (fun k => a ≤ k ∧ k < a + 8 * n) m cfg.σ.mem := by
  intro k hk
  obtain ⟨hstack, hArena, hret⟩ := h k hk
  exact ((hExit.memFrame k hstack hArena).resolve_left hret).symm

/-- Every remaining head survives the recursive statement, together with its
pointer-array read. Presence and byte preservation are separate premises. -/
theorem SeqSuffixGround.transport_execExit
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet r : BitVec 64}
    {d a : Nat} {ss : List Stmt}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {φf φc : Addr → Nat} {nf nc : Nat} {st' : Vsa.While.St} {status : Status}
    {cfg : Config}
    (h : SeqSuffixGround m SL A sp aRet d a ss)
    (hExit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m cfg)
    (hExt : MemExtends m cfg.σ.mem) :
    SeqArrayReadSafe SL A sp aRet a ss.length →
      SeqSuffixGround cfg.σ.mem SL A sp aRet d a ss := by
  induction h with
  | nil =>
      intro _
      exact .nil
  | @cons a p s ss hread hstmt _ ih =>
      intro hsafe
      have hread' : read64 cfg.σ.mem a = some p := by
        rw [← read64_agreeP (hsafe.agree_execExit hExit)
          (fun k hk => ⟨by omega, by simp only [List.length_cons]; omega⟩)]
        exact hread
      exact .cons hread' (hstmt.transport_execExit hExit hExt) (ih hsafe.tail)

#print axioms SeqSuffixGround.head
#print axioms SeqSuffixGround.tail
#print axioms SeqSuffixGround.array
#print axioms SeqSuffixGround.transport_execExit

end Vsa.Sim
