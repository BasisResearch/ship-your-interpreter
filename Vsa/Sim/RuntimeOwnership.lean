import Vsa.Sim.HeapOwnershipGeometry
import Vsa.Sim.StoreInvariant

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

inductive Role where
  | frame (fa : Addr)
  | names (fa : Addr)
  | values (fa : Addr)
  | binding (fa : Addr) (index : Nat)
  | closure (ca : Addr)
  deriving DecidableEq

def Role.mutable : Role → Prop
  | .binding _ _ => False
  | _ => True

abbrev Allocations := Role → Option Extent

def Allocated (alloc : Allocations) (role : Role) (p n : Nat) : Prop :=
  alloc role = some (p, n)

def ExtentByte (e : Extent) (k : Nat) : Prop := e.1 ≤ k ∧ k < e.1 + e.2

structure Ledger (A : Arena) (exts : List Extent) (alloc : Allocations) : Prop where
  arena : HeapArena A exts
  live : ∀ role p n, Allocated alloc role p n → (p, n) ∈ exts
  separated : ∀ r s p n q size,
    Allocated alloc r p n → Allocated alloc s q size → r ≠ s →
    ExtDisjoint (p, n) (q, size)

structure Immutable (alloc : Allocations) (shared readable writes : Nat → Prop) : Prop where
  readable : ∀ k, shared k → readable k
  outsideWrites : ∀ k, shared k → ¬ writes k
  outsideMutable : ∀ role p n, Role.mutable role → Allocated alloc role p n →
    ∀ k, shared k → ¬ ExtentByte (p, n) k

def ArrayOwned (alloc : Allocations) (role : Role) (p width cap : Nat) : Prop :=
  (cap = 0 ∧ p = 0) ∨ (0 < cap ∧ Allocated alloc role p (width * cap))

structure SharedCString (m : Mem) (shared : Nat → Prop) (p : Nat) (s : String) : Prop where
  repr : CString m p s
  bytes : ∀ k, k ≤ s.length → shared (p + k)

structure CopiedCString (m : Mem) (alloc : Allocations) (shared : Nat → Prop)
    (role : Role) (p : Nat) (s : String) : Prop where
  allocated : Allocated alloc role p (s.length + 1)
  immutable : SharedCString m shared p s

def ValueOwned (m : Mem) (shared : Nat → Prop) (a : Nat) : Value → Prop
  | .str s => ∃ p, read64 m (a + 8) = some p ∧ SharedCString m shared p s
  | .native f => ∃ p, read64 m (a + 8) = some p ∧
      SharedCString m shared p (nativeName f)
  | _ => True

structure ArrayState where
  cap : Nat
  names : Nat
  values : Nat

structure FrameArraysOwned (m : Mem) (phiF : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (fa : Addr) (f : Vsa.While.Frame) (a : ArrayState) : Prop where
  capRead : read32 m (phiF fa + 4) = some a.cap
  namesRead : read64 m (phiF fa + 8) = some a.names
  valuesRead : read64 m (phiF fa + 16) = some a.values
  bound : f.vars.length ≤ a.cap
  names : ArrayOwned alloc (.names fa) a.names 8 a.cap
  values : ArrayOwned alloc (.values fa) a.values 24 a.cap
  keys : ∀ i, (hi : i < f.vars.length) → ∃ q,
    read64 m (a.names + 8 * i) = some q ∧
    CopiedCString m alloc shared (.binding fa i) q f.vars[i].1

structure FrameOwned (m : Mem) (phiF : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (fa : Addr) (f : Vsa.While.Frame) : Prop where
  record : Allocated alloc (.frame fa) (phiF fa) 32
  arrays : ∃ a, FrameArraysOwned m phiF alloc shared fa f a
  values : ∀ pv, read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ValueOwned m shared (pv + 24 * i) f.vars[i].2

structure StoreOwned (m : Mem) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared : Nat → Prop) (s : Store) : Prop where
  frames : ∀ fa, (h : fa < s.frames.size) → FrameOwned m phiF alloc shared fa s.frames[fa]
  closures : ∀ ca, ca < s.closures.size → Allocated alloc (.closure ca) (phiC ca) 16
  valueClosures : StoreClosuresBounded s
  capturedEnvs : ∀ ca, (h : ca < s.closures.size) → s.closures[ca].env < s.frames.size
  closureAsts : ∀ ca, (h : ca < s.closures.size) → ∀ q,
    read64 m (phiC ca) = some q →
    ∀ k, ExprFp m q (.fn s.closures[ca].name s.closures[ca].params
      s.closures[ca].body) k → shared k

end Vsa.Sim.RuntimeOwnership
