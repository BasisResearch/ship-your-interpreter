import Vsa.Sim.EnvDefSpec2

/-!
# `ReallocSpec` — corrected allocator-operation interface

The earlier `ReallocContract` cannot express `realloc(NULL,n)` and its public
memory frame omits the returned extent. This module supplies the operation
interface used by `HeapOps`. It is parameterized by one allocator invariant and
one private footprint, so malloc and realloc share the same ledger.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.Sim Vsa.Alloc

namespace Vsa.Sim

abbrev Extent := Nat × Nat

/-- A public-memory frame. Bytes in allocator-private memory, the active stack,
or an explicitly listed extent may change. -/
def HeapPublicFrame (privFoot : Nat → Prop) (SL : StackLayout) (sp : BitVec 64)
    (except : List Extent) (m0 m : Vsa.MemRepr.Mem) : Prop :=
  ∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    (∀ e ∈ except, a < e.1 ∨ e.1 + e.2 ≤ a) → m[a]? = m0[a]?

/-- The old bytes preserved by a successful grow. -/
def ReallocCopies (m0 m : Vsa.MemRepr.Mem) (pOld pNew nOld : Nat) : Prop :=
  ∀ k, k < nOld → m[pNew + k]? = m0[pOld + k]?

/-- Correct result relation for growing one live extent. Failure preserves all
public memory and leaves the old extent live. Success replaces it, copies its
contents, and frames both old and new extents. -/
def ReallocGrowResult (A : Arena) (SL : StackLayout) (privFoot : Nat → Prop)
    (AInv : MState → List Extent → Prop) (exts : List Extent)
    (pOld nOld nNew : Nat) (sp : BitVec 64) (m0 : Vsa.MemRepr.Mem)
    (sigma : MState) : Prop :=
  (sigma.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
    AInv sigma exts ∧ HeapPublicFrame privFoot SL sp [] m0 sigma.mem) ∨
  (∃ pNew,
    sigma.regs.get? Register.x10 = some (BitVec.ofNat 64 pNew) ∧
    pNew ≠ 0 ∧ pNew % 16 = 0 ∧ A.contains pNew nNew ∧
    (∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e) ∧
    ReallocCopies m0 sigma.mem pOld pNew nOld ∧
    AInv sigma ((pNew, nNew) :: exts.erase (pOld, nOld)) ∧
    HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 sigma.mem)

/-- Result relation for `realloc(NULL,n)`. This is allocation, with no old
extent. -/
def ReallocNullResult (A : Arena) (SL : StackLayout) (privFoot : Nat → Prop)
    (AInv : MState → List Extent → Prop) (exts : List Extent)
    (n : Nat) (sp : BitVec 64) (m0 : Vsa.MemRepr.Mem) (sigma : MState) : Prop :=
  (sigma.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
    AInv sigma exts ∧ HeapPublicFrame privFoot SL sp [] m0 sigma.mem) ∨
  (∃ pNew,
    sigma.regs.get? Register.x10 = some (BitVec.ofNat 64 pNew) ∧
    pNew ≠ 0 ∧ pNew % 16 = 0 ∧ A.contains pNew n ∧
    (∀ e ∈ exts, ExtDisjoint (pNew, n) e) ∧
    AInv sigma ((pNew, n) :: exts) ∧
    HeapPublicFrame privFoot SL sp [(pNew, n)] m0 sigma.mem)

/-- Shared precondition for calls to the fixed-binary `realloc`. -/
def ReallocPre (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List Extent → Prop) (exts : List Extent)
    (p n : Nat) (sp r : BitVec 64) (m0 : Vsa.MemRepr.Mem)
    (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) ∧
  c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
  c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 n) ∧
  c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
  c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
  AInv c.σ exts ∧ c.σ.mem = m0

/-- Common ABI postcondition of realloc. -/
def ReallocPost (gpv sp r : BitVec 64)
    (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x2 = some sp ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R)

/-- Total-correctness realloc operations over a shared allocator state. -/
structure ReallocOps (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (AInv : MState → List Extent → Prop)
    (privFoot : Nat → Prop) where
  grow : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List Extent) (pOld nOld nNew : Nat) (sp r : BitVec 64)
      (m0 : Vsa.MemRepr.Mem),
    nNew ≤ maxReq → nOld < nNew → pOld ≠ 0 → (pOld, nOld) ∈ exts →
    Triple
      (ReallocPre SL gpv headroom AInv exts pOld nNew sp r m0 g)
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ)
  null : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List Extent) (n : Nat) (sp r : BitVec 64) (m0 : Vsa.MemRepr.Mem),
    0 < n → n ≤ maxReq →
    Triple
      (ReallocPre SL gpv headroom AInv exts 0 n sp r m0 g)
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocNullResult A SL privFoot AInv exts n sp m0 c.σ)

theorem heapPublicFrame_refl (privFoot : Nat → Prop) (SL : StackLayout)
    (sp : BitVec 64) (m : Vsa.MemRepr.Mem) : HeapPublicFrame privFoot SL sp [] m m :=
  fun _ _ _ _ => rfl

#print axioms heapPublicFrame_refl

end Vsa.Sim
