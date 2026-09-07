import Vsa.Sim.SeparationLogicFrame
import Vsa.Sim.SeparationLogicEffect
import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.RuntimeOwnershipEnvNew
import Vsa.MemReprWithin

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

namespace Vsa.Sim.SeparationLogic

/-- Runtime writes consist of mutable allocation roles and the separately
proved stack/runtime/allocator write footprint. Immutable live extents are
not converted into writable permissions. -/
def runtimeWrites (alloc : RuntimeOwnership.Allocations) (extra : Nat → Prop)
    (k : Nat) : Prop :=
  extra k ∨ ∃ role p n, RuntimeOwnership.Role.mutable role ∧
    RuntimeOwnership.Allocated alloc role p n ∧ RuntimeOwnership.ExtentByte (p, n) k

theorem runtime_compatible {alloc : RuntimeOwnership.Allocations}
    {shared readable writes : Nat → Prop}
    (h : RuntimeOwnership.Immutable alloc shared readable writes) :
    Compatible (Resource.exclusive (runtimeWrites alloc writes)) (Resource.shared shared) := by
  refine ⟨fun _ _ h => h.elim, ?_, fun _ h => h.elim⟩
  intro k hw hr
  rcases hw with hw | ⟨role, p, n, hm, ha, hk⟩
  · exact h.outsideWrites k hr hw
  · exact h.outsideMutable role p n hm ha k hr hk

/-- Interpret the runtime ownership ledger in the separating-conjunction calculus.
Reservation and allocator metadata remain additional runtime invariants. -/
theorem heap_owned_sep {A : Arena} {exts : List Extent} {m : Mem}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : RuntimeOwnership.Allocations}
    {shared readable writes : Nat → Prop} {store : Vsa.While.Store}
    (h : RuntimeOwnership.HeapOwned A exts m phiF phiC alloc shared readable writes store) :
    (owns (runtimeWrites alloc writes) ∗ reads shared) m
      ((Resource.exclusive (runtimeWrites alloc writes)).join
        (Resource.shared shared) (runtime_compatible h.immutable)) :=
  ⟨_, _, Split.join (runtime_compatible h.immutable), rfl, rfl⟩

/-- An immutable C string assertion owns read permission for every byte read,
including the NUL. It can carry additional read-only bytes. -/
def cstring (p : Nat) (s : String) : Assertion where
  holds m r := (∀ k, ¬ r.write k) ∧ CString m p s ∧ ∀ k, k ≤ s.length → r.read (p + k)
  stable hag h := by
    obtain ⟨hw, hs, hb⟩ := h
    refine ⟨hw, ?_, hb⟩
    exact cstring_agreeP hag hs (fun k hk => Or.inr (hb k hk))

/-- The existing shared CString relation supplies the local assertion. -/
theorem sharedCString_assertion {m : Mem} {shared : Nat → Prop} {p : Nat} {s : String}
    (h : RuntimeOwnership.SharedCString m shared p s) :
    cstring p s m (Resource.shared shared) :=
  ⟨fun _ h => h.elim, h.repr, h.bytes⟩

theorem runtime_cstring_sep {m : Mem} {alloc : RuntimeOwnership.Allocations}
    {shared readable writes : Nat → Prop} {p : Nat} {s : String}
    (hi : RuntimeOwnership.Immutable alloc shared readable writes)
    (hs : RuntimeOwnership.SharedCString m shared p s) :
    (owns (runtimeWrites alloc writes) ∗ cstring p s) m
      ((Resource.exclusive (runtimeWrites alloc writes)).join
        (Resource.shared shared) (runtime_compatible hi)) :=
  ⟨_, _, Split.join (runtime_compatible hi), rfl, sharedCString_assertion hs⟩

/-- AST representation with read permissions for its complete hereditary graph. -/
def program (a n : Nat) (p : Vsa.While.Program) : Assertion where
  holds m r := (∀ k, ¬ r.write k) ∧ ProgramReprWithin m r.read a n p
  stable hag h :=
    ⟨h.1, h.2.transport (fun k hk => hag k (Or.inr hk))⟩

theorem program_assertion {m : Mem} {shared : Nat → Prop} {a n : Nat}
    {p : Vsa.While.Program} (h : ProgramReprWithin m shared a n p) :
    program a n p m (Resource.shared shared) := ⟨fun _ h => h.elim, h⟩

/-- Apply the separation frame rule to an actual proved machine execution. -/
theorem frame_machine {P R : Assertion} {before after : Config}
    {left right whole : Resource} {effect : FrameEffect}
    (hs : Split left right whole) (hp : P after.σ.mem left) (hr : R before.σ.mem right)
    (hsteps : FramedSteps effect before after)
    (hprotected : ∀ k, ¬ left.write k → effect.mem k) :
    (P ∗ R) after.σ.mem whole :=
  ⟨left, right, hs, hp,
    StableUnder.separated hs R hprotected before after hr hsteps.frame⟩

/-- Initialized frame and arbitrary framed assertion at the reached endpoint. -/
structure EnvNewFramedPost (esp p par ra savedS0 : BitVec 64) (before after : Config)
    (R : Assertion) (whole : Resource) : Prop where
  initialized : EnvNewSuccessPost esp p par ra savedS0 before after
  run : FramedSteps (envNewSuccessEffect p) before after
  preserved : (owns (RuntimeOwnership.ExtentByte (p.toNat, 32)) ∗ R) after.σ.mem whole

/-- The actual nine-instruction env_new initialization preserves every disjoint
assertion. It neither assumes nor proves the preceding malloc succeeds. -/
theorem envNewSuccess_frame {esp p par ra savedS0 : BitVec 64} {before : Config}
    {R : Assertion} {whole : Resource}
    (hpre : EnvNewSuccessPre esp p par ra savedS0 before)
    (hsep : (owns (RuntimeOwnership.ExtentByte (p.toNat, 32)) ∗ R) before.σ.mem whole) :
    ∃ after, EnvNewFramedPost esp p par ra savedS0 before after R whole := by
  obtain ⟨after, hpost, hrun⟩ := envNewSuccess_run hpre
  obtain ⟨left, right, hs, hp, hr⟩ := hsep
  refine ⟨after, hpost, hrun, ?_⟩
  apply frame_machine hs (show owns (RuntimeOwnership.ExtentByte (p.toNat, 32))
    after.σ.mem left from hp) hr hrun
  intro k hk
  change left = Resource.exclusive (RuntimeOwnership.ExtentByte (p.toNat, 32)) at hp
  simpa only [hp, Resource.exclusive, RuntimeOwnership.ExtentByte, envNewSuccessEffect] using hk

#print axioms runtime_compatible
#print axioms heap_owned_sep
#print axioms sharedCString_assertion
#print axioms runtime_cstring_sep
#print axioms program_assertion
#print axioms frame_machine
#print axioms envNewSuccess_frame

end Vsa.Sim.SeparationLogic
