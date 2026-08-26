import Vsa.Sim.ReallocSpec

/-!
# `HeapOps` — one allocator ledger for interpreter heap operations

`MallocContract` and `ReallocOps` are packaged here against the same
allocator invariant and private footprint. `HeapRepr` adds the allocation
ownership facts deliberately absent from `StoreRepr`: environment records,
their backing arrays, copied binding names, and closure records all belong to
live extents.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open Vsa.MemRepr

namespace Vsa.Sim

/-- Live extents are nonempty, inside the arena, and pairwise disjoint. -/
def HeapArena (A : Arena) (exts : List Extent) : Prop :=
  (∀ e ∈ exts, 0 < e.2 ∧ A.contains e.1 e.2) ∧
  exts.Pairwise ExtDisjoint

/-- The fixed binary's malloc and realloc obey one allocator ledger. -/
structure HeapOps (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) where
  malloc : MallocContract A SL gpv headroom maxReq
  realloc : ReallocOps A SL gpv headroom maxReq malloc.AInv malloc.privFoot

namespace HeapOps

def AInv {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (H : HeapOps A SL gpv headroom maxReq) :
    MState → List Extent → Prop :=
  H.malloc.AInv

def privFoot {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (H : HeapOps A SL gpv headroom maxReq) : Nat → Prop :=
  H.malloc.privFoot

theorem privFoot_disjoint {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (H : HeapOps A SL gpv headroom maxReq)
    {sigma : MState} {exts : List Extent} (h : H.AInv sigma exts) :
    ∀ e ∈ exts, ∀ k < e.2, ¬ H.privFoot (e.1 + k) :=
  H.malloc.privFoot_disjoint sigma exts h

end HeapOps

/-- Machine allocations owned by one represented environment frame. -/
structure FrameHeapOwned (m : Vsa.MemRepr.Mem) (phiF : Addr → Nat)
    (exts : List Extent) (fa : Addr) (f : Vsa.While.Frame) : Prop where
  record : (phiF fa, 32) ∈ exts
  arrays : ∃ cap pn pv,
    read32 m (phiF fa + 4) = some cap ∧
    read64 m (phiF fa + 8) = some pn ∧
    read64 m (phiF fa + 16) = some pv ∧
    f.vars.length ≤ cap ∧
    (pn, 8 * cap) ∈ exts ∧
    (pv, 24 * cap) ∈ exts ∧
    ∀ i, (hi : i < f.vars.length) →
      ∃ q, read64 m (pn + 8 * i) = some q ∧
        (q, f.vars[i].1.length + 1) ∈ exts

/-- Every spec object and each environment-owned suballocation has a live
extent in the shared allocator ledger. -/
structure StoreHeapOwned (m : Vsa.MemRepr.Mem) (phiF phiC : Addr → Nat)
    (exts : List Extent) (s : Store) : Prop where
  frames : ∀ fa, (h : fa < s.frames.size) →
    FrameHeapOwned m phiF exts fa s.frames[fa]
  closures : ∀ ca, ca < s.closures.size → (phiC ca, 16) ∈ exts

/-- Name uniqueness matches `env_define`, which updates the first matching
binding. It also makes the spec's map-based update observationally identical. -/
def NamesUnique (vars : List (String × Value)) : Prop :=
  ∀ i j, (hi : i < vars.length) → (hj : j < vars.length) →
    vars[i].1 = vars[j].1 → i = j

def StoreUnique (s : Store) : Prop :=
  ∀ fa, (h : fa < s.frames.size) → NamesUnique s.frames[fa].vars

/-- Full heap relation used at heap-operation call sites. -/
structure HeapRepr {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (H : HeapOps A SL gpv headroom maxReq)
    (sigma : MState) (exts : List Extent) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (s : Store) : Prop where
  allocator : H.AInv sigma exts
  arena : HeapArena A exts
  store : StoreRepr sigma.mem N A phiF phiC s
  owned : StoreHeapOwned sigma.mem phiF phiC exts s
  unique : StoreUnique s

#print axioms HeapOps.privFoot_disjoint

end Vsa.Sim
