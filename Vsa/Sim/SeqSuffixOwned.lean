import Vsa.Sim.ExecGroundOwned
import Vsa.MemReprReadArrays

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

/-- The remaining statement array carries both shared reads and child entry facts. -/
structure SeqSuffixOwned (m : Mem) (shared : Nat → Prop) (SL : StackLayout) (A : Arena)
    (sp aRet : BitVec 64) (d a : Nat) (ss : List Stmt) : Prop where
  reads : StmtArrayReprWithin m shared a ss.length ss
  ground : SeqSuffixGround m SL A sp aRet d a ss

/-- Shared pointer cells survive the actual child; its exit transports each ground. -/
theorem SeqSuffixGround.transport_shared
    {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp aRet r : BitVec 64} {d a : Nat} {ss : List Stmt}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {nf nc : Nat} {st' : Vsa.While.St} {status : Status}
    {cfg : Config}
    (h : SeqSuffixGround m SL A sp aRet d a ss)
    (reads : PointerArrayWithin m shared (StmtReprWithin m shared) a ss)
    (exit : ExecExit g N A SL phiF phiC nf nc st' status sp r aRet m cfg)
    (presence : MemExtends m cfg.σ.mem) (agreement : AgreeP shared m cfg.σ.mem) :
    SeqSuffixGround cfg.σ.mem SL A sp aRet d a ss := by
  induction h with
  | nil => exact .nil
  | @cons a p s ss hread hstmt _ ih =>
    cases reads with
    | cons cell tail =>
      have pointer := Option.some.inj (cell.read.symm.trans hread)
      exact .cons ((read64_agreeP agreement cell.covered).symm.trans hread)
        (hstmt.transport_owned_execExit (pointer ▸ cell.target) agreement exit presence)
        (ih tail)

variable {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {A : Arena}
  {sp aRet : BitVec 64} {d a : Nat} {s : Stmt} {ss : List Stmt}

theorem SeqSuffixOwned.tail
    (h : SeqSuffixOwned m shared SL A sp aRet d a (s :: ss)) :
    SeqSuffixOwned m shared SL A sp aRet d (a + 8) ss := by
  refine ⟨?_, h.ground.tail⟩
  cases h.reads with
  | cons _ _ _ tail => exact tail

/-- Select the same owned statement pointer as the hereditary ground array. -/
theorem SeqSuffixOwned.head
    (h : SeqSuffixOwned m shared SL A sp aRet d a (s :: ss)) :
    ∃ p, PointerReadWithin m shared (StmtReprWithin m shared) a p s ∧
      SeqStmtGround m SL A sp aRet d p s := by
  obtain ⟨p, cell⟩ := h.reads.pointers.get 0 (by simp)
  obtain ⟨q, read, ground⟩ := h.ground.head
  have eq : p = q := Option.some.inj (cell.read.symm.trans read)
  subst q
  exact ⟨p, cell, ground⟩

/-- Retain the suffix at the actual return's expanded shared domain. -/
theorem SeqSuffixOwned.transport_execExit
    {r : BitVec 64} {returnedShared : Nat → Prop}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {nf nc : Nat} {st' : Vsa.While.St} {status : Status}
    {cfg : Config} (h : SeqSuffixOwned m shared SL A sp aRet d a ss)
    (exit : ExecExit g N A SL phiF phiC nf nc st' status sp r aRet m cfg)
    (presence : MemExtends m cfg.σ.mem) (agreement : AgreeP shared m cfg.σ.mem)
    (includes : ∀ k, shared k → returnedShared k) :
    SeqSuffixOwned cfg.σ.mem returnedShared SL A sp aRet d a ss :=
  ⟨(h.reads.transport agreement).mono includes,
    h.ground.transport_shared h.reads.pointers exit presence agreement⟩

#print axioms SeqSuffixGround.transport_shared
#print axioms SeqSuffixOwned.tail
#print axioms SeqSuffixOwned.head
#print axioms SeqSuffixOwned.transport_execExit

end Vsa.Sim
