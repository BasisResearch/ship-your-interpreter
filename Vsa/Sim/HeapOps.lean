import Vsa.Sim.ReallocSpec
import Vsa.Sim.StoreInvariant
import Vsa.Sim.AstTransport
import Vsa.Sim.rows.StoreReprPhicRebase

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
  values : ∀ pv, read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) →
      ValueHeapOwned m exts (pv + 24 * i) f.vars[i].2

/-- Every spec object and each environment-owned suballocation has a live
extent in the shared allocator ledger. -/
structure StoreHeapOwned (m : Vsa.MemRepr.Mem) (phiF phiC : Addr → Nat)
    (exts : List Extent) (s : Store) : Prop where
  frames : ∀ fa, (h : fa < s.frames.size) →
    FrameHeapOwned m phiF exts fa s.frames[fa]
  closures : ∀ ca, ca < s.closures.size → (phiC ca, 16) ∈ exts
  valueClosures : StoreClosuresBounded s
  capturedEnvs : ∀ ca, (h : ca < s.closures.size) →
    s.closures[ca].env < s.frames.size
  closureAsts : ∀ ca, (h : ca < s.closures.size) → ∀ q,
    read64 m (phiC ca) = some q →
    ExprRepr m q (.fn s.closures[ca].name s.closures[ca].params
      s.closures[ca].body) →
    ExtentsCover exts (ExprFp m q (.fn s.closures[ca].name
      s.closures[ca].params s.closures[ca].body))
  appendSeparated : ∀ target, (ht : target < s.frames.size) →
    ∀ cap names vals,
    read32 m (phiF target + 4) = some cap →
    read64 m (phiF target + 8) = some names →
    read64 m (phiF target + 16) = some vals →
    s.frames[target].vars.length < cap →
    (∀ fa, (hf : fa < s.frames.size) → fa ≠ target →
      FrameFootprintCovered m phiF fa s.frames[fa]
        (AppendOutside (phiF target) names vals s.frames[target].vars.length)) ∧
    (∀ ca, (hc : ca < s.closures.size) →
      ClosureFootprintCovered m phiC ca s.closures[ca]
        (AppendOutside (phiF target) names vals s.frames[target].vars.length))
  setSeparated : ∀ target, (ht : target < s.frames.size) →
    ∀ hit, (hhit : hit < s.frames[target].vars.length) → ∀ vals,
    read64 m (phiF target + 16) = some vals →
    let slot := vals + 24 * hit
    TargetFrameFootprintCovered m phiF target s.frames[target] hit
        (SetOutside slot) ∧
      (∀ fa, (hf : fa < s.frames.size) → fa ≠ target →
        FrameFootprintCovered m phiF fa s.frames[fa] (SetOutside slot)) ∧
      (∀ ca, (hc : ca < s.closures.size) →
        ClosureFootprintCovered m phiC ca s.closures[ca] (SetOutside slot))
  payloadAppendSeparated : ∀ target, (ht : target < s.frames.size) →
    ∀ cap names vals,
    read32 m (phiF target + 4) = some cap →
    read64 m (phiF target + 8) = some names →
    read64 m (phiF target + 16) = some vals →
    s.frames[target].vars.length < cap → ∀ a v,
    ValueHeapOwned m exts a v →
    ValuePayloadCovered
      (AppendOutside (phiF target) names vals s.frames[target].vars.length) m a v
  payloadSetSeparated : ∀ target, (ht : target < s.frames.size) →
    ∀ hit, (hhit : hit < s.frames[target].vars.length) → ∀ vals,
    read64 m (phiF target + 16) = some vals → ∀ a v,
    ValueHeapOwned m exts a v →
    ValuePayloadCovered (SetOutside (vals + 24 * hit)) m a v

namespace StoreHeapOwned

theorem valuePayloadOutsideAppend
    {m : Vsa.MemRepr.Mem} {phiF phiC : Addr → Nat} {exts : List Extent}
    {s : Store} (h : StoreHeapOwned m phiF phiC exts s)
    {target : Addr} (ht : target < s.frames.size)
    {cap names vals : Nat}
    (hcap : read32 m (phiF target + 4) = some cap)
    (hnames : read64 m (phiF target + 8) = some names)
    (hvals : read64 m (phiF target + 16) = some vals)
    (happend : s.frames[target].vars.length < cap)
    {a : Nat} {v : Value} (hv : ValueHeapOwned m exts a v) :
    ValuePayloadCovered
      (AppendOutside (phiF target) names vals s.frames[target].vars.length) m a v :=
  h.payloadAppendSeparated target ht cap names vals hcap hnames hvals happend a v hv

theorem valuePayloadOutsideSet
    {m : Vsa.MemRepr.Mem} {phiF phiC : Addr → Nat} {exts : List Extent}
    {s : Store} (h : StoreHeapOwned m phiF phiC exts s)
    {target : Addr} (ht : target < s.frames.size)
    {hit : Nat} (hhit : hit < s.frames[target].vars.length)
    {vals : Nat} (hvals : read64 m (phiF target + 16) = some vals)
    {a : Nat} {v : Value} (hv : ValueHeapOwned m exts a v) :
    ValuePayloadCovered (SetOutside (vals + 24 * hit)) m a v :=
  h.payloadSetSeparated target ht hit hhit vals hvals a v hv

end StoreHeapOwned

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
  parents : StoreParents s

theorem HeapRepr.invariant {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {H : HeapOps A SL gpv headroom maxReq}
    {sigma : MState} {exts : List Extent} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {s : Store}
    (h : HeapRepr H sigma exts N phiF phiC s) : StoreInvariant s :=
  ⟨h.unique, h.parents⟩

#print axioms HeapOps.privFoot_disjoint

end Vsa.Sim
