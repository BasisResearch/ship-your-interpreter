import Vsa.Sim.rows.EnvDefineUpdateExact
import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.RuntimeOwnershipCopy
import Vsa.Sim.RuntimeOwnershipDefine

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Logic Vsa.While

namespace Vsa.Sim

/-- Update result at the epilogue entry, retaining copied-value ownership
and preservation of shared immutable bytes. -/
structure EnvDefineOwnedUpdatePost
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (shared : Nat → Prop) (c : Config) : Prop where
  update : EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c
  shared_agree : AgreeP shared m0 c.σ.mem
  value_owned : RuntimeOwnership.ValueOwned c.σ.mem shared dst.toNat v

/-- Runtime ownership supplies payload separation and preserves shared bytes
through the actual existing-name update instructions. -/
theorem envDefineUpdateFromHit_of_runtime_owned
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp valsBV dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena) (exts : List Extent)
    (alloc : RuntimeOwnership.Allocations) (shared readable writes : Nat → Prop)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (htarget : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hvals : read64 m0 (φf target + 16) = some valsBV.toNat)
    (hdst : dst.toNat = valsBV.toNat + 24 * idx)
    (howned : RuntimeOwnership.HeapOwned A exts m0 φf φc alloc
      shared readable writes store)
    (hsrcOwned : RuntimeOwnership.ValueOwned m0 shared src.toNat v)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src valsBV dst idx m0)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (EnvDefineUpdateHitPre saved env name src count cursor sp idx m0)
      (EnvDefineOwnedUpdatePost saved env src dst sp idx m0 N φc v shared) := by
  have hout : ∀ k, shared k → SetOutside dst.toNat k := by
    simpa only [hdst] using
      (howned.store.frames target htarget).sharedOutsideSet howned.immutable hidx hvals
  intro c hpre
  obtain ⟨after, hsteps, hpost⟩ := envDefineUpdateFromHitCopied saved env name src count
    cursor sp valsBV dst idx m0 N φc v A hcode hword hgeom
    (hsrcOwned.covered hout) hdstArena harenaStack harenaCode c hpre
  have hagree : AgreeP shared m0 after.σ.mem :=
    fun k hk => hpost.update.agree_outside k (hout k hk)
  exact ⟨after, hsteps, hpost.update, hagree, hsrcOwned.copy_total hpost.copied hagree⟩

#print axioms envDefineUpdateFromHit_of_runtime_owned

/-- The reached update post supplies ownership of the exact semantic store.
The source invariant supplies unique bindings and the assigned closure bound. -/
theorem EnvDefineOwnedUpdatePost.heap_owned
    {saved : (R : LeanRV64DExecutable.Register) →
      Option (LeanRV64DExecutable.RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {phiF phiC : Addr → Nat} {v : Value}
    {shared readable writes : Nat → Prop} {c : Vsa.Machine.Config}
    {A : Arena} {exts : List Extent} {alloc : RuntimeOwnership.Allocations}
    {store : Store} {target : Addr} {name : String} {vals : Nat}
    (hp : EnvDefineOwnedUpdatePost saved env src dst sp idx m0 N phiC v shared c)
    (h : RuntimeOwnership.HeapOwned A exts m0 phiF phiC alloc
      shared readable writes store)
    (ht : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hmatch : store.frames[target].vars[idx].1 = name)
    (huniq : FrameUnique store.frames[target])
    (hvals : read64 m0 (phiF target + 16) = some vals)
    (hslot : dst.toNat = vals + 24 * idx)
    (hbounded : ValueClosuresBounded store.closures.size v) :
    RuntimeOwnership.HeapOwned A exts c.σ.mem phiF phiC alloc
      shared readable writes (store.define target name v) := by
  apply h.defineHit ht hidx hmatch huniq hvals
    (hslot ▸ hp.value_owned) hbounded
  simpa only [hslot] using hp.update.agree_outside

#print axioms EnvDefineOwnedUpdatePost.heap_owned

/-- Runtime ownership supplies the exact semantic store advance at the
reached epilogue entry. -/
theorem EnvDefineOwnedUpdatePost.advance
    {saved : (R : Register) → Option (RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {phiF phiC : Addr → Nat} {v : Value}
    {shared readable writes : Nat → Prop} {c : Config}
    {A : Arena} {exts : List Extent} {alloc : RuntimeOwnership.Allocations}
    {store : Store} {target : Addr} {name : String} {vals : Nat}
    (hp : EnvDefineOwnedUpdatePost saved env src dst sp idx m0 N phiC v shared c)
    (h : RuntimeOwnership.HeapOwned A exts m0 phiF phiC alloc
      shared readable writes store)
    (hr : StoreRepr m0 N A phiF phiC store)
    (ht : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hmatch : store.frames[target].vars[idx].1 = name)
    (huniq : FrameUnique store.frames[target])
    (henv : env.toNat = phiF target)
    (hvals : read64 m0 (phiF target + 16) = some vals)
    (hslot : dst.toNat = vals + 24 * idx) :
    StoreDefineAdvance N A phiF phiC store target name v c.σ.mem := by
  have hshell := StoreSetFootprint.target_of_runtime_owned (N := N)
    ht hidx hvals hslot h
  have hframe : FrameRepr m0 N phiF phiC env.toNat store.frames[target] := by
    rw [henv]; exact hr.frames target ht
  have hfoot : EnvDefineUpdateFrameFootprint m0 N phiF phiC env.toNat
      dst.toNat store.frames[target] idx := by
    rw [henv]
    exact ⟨hshell.header, hshell.nameSlots, hshell.names,
      hshell.otherValueHeaders, hshell.otherValueStrings⟩
  have hslotAll : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
      dst.toNat = pv + 24 * idx := by
    intro pv hpv
    rw [henv] at hpv
    have he : pv = vals := Option.some.inj (hpv.symm.trans hvals)
    simpa only [he] using hslot
  have hnew := envDefineUpdateFrameRepr saved env src dst sp idx m0 N phiF phiC
    store.frames[target] name v c hp.update hframe hidx hmatch huniq hslotAll hfoot
  rw [henv] at hnew
  have hget : store.frames[target]? = some store.frames[target] :=
    Array.getElem?_eq_some_iff.mpr ⟨ht, rfl⟩
  exact storeDefineAdvance_of_update hr hget hnew
    (StoreSetFootprint.of_runtime_owned ht hidx hvals hslot h hp.update.agree_outside)

/-- Returned update state with restored registers, the semantic store advance,
whole-store ownership, and agreement on the entry shared domain. -/
structure EnvDefineOwnedReturnPost
    (saved : (R : Register) → Option (RegisterType R)) (sp : BitVec 64)
    (m0 : Mem) (N : NativeAddrs) (A : Arena) (exts : List Extent)
    (phiF phiC : Addr → Nat) (alloc : RuntimeOwnership.Allocations)
    (shared readable writes : Nat → Prop) (store : Store)
    (target : Addr) (name : String) (v : Value) (c : Config) : Prop where
  returned : EnvDefineEpilogueExactPost sp saved c.σ.mem c
  advance : StoreDefineAdvance N A phiF phiC store target name v c.σ.mem
  owned : RuntimeOwnership.HeapOwned A exts c.σ.mem phiF phiC alloc
    shared readable writes (store.define target name v)
  shared_agree : AgreeP shared m0 c.σ.mem

/-- Finish the actual owned update through the memory-preserving epilogue. -/
theorem EnvDefineOwnedUpdatePost.finish
    {saved : (R : Register) → Option (RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {phiF phiC : Addr → Nat} {v : Value}
    {shared readable writes : Nat → Prop} {c : Config}
    {A : Arena} {exts : List Extent} {alloc : RuntimeOwnership.Allocations}
    {store : Store} {target : Addr} {name : String} {vals : Nat}
    (hp : EnvDefineOwnedUpdatePost saved env src dst sp idx m0 N phiC v shared c)
    (h : RuntimeOwnership.HeapOwned A exts m0 phiF phiC alloc
      shared readable writes store)
    (hr : StoreRepr m0 N A phiF phiC store)
    (ht : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hmatch : store.frames[target].vars[idx].1 = name)
    (huniq : FrameUnique store.frames[target])
    (henv : env.toNat = phiF target)
    (hvals : read64 m0 (phiF target + 16) = some vals)
    (hslot : dst.toNat = vals + 24 * idx)
    (hbounded : ValueClosuresBounded store.closures.size v) :
    ∃ after, Steps c after ∧
      EnvDefineOwnedReturnPost saved sp m0 N A exts phiF phiC alloc
        shared readable writes store target name v after := by
  have ho := hp.heap_owned h ht hidx hmatch huniq hvals hslot hbounded
  have ha := hp.advance h hr ht hidx hmatch huniq henv hvals hslot
  obtain ⟨after, hsteps, hret⟩ := hp.update.restore
  refine ⟨after, hsteps, ?_⟩
  have hretSelf : EnvDefineEpilogueExactPost sp saved after.σ.mem after := by
    rw [hret.mem]; exact hret
  refine ⟨hretSelf, ?_, ?_, ?_⟩ <;> rw [hret.mem]
  · exact ha
  · exact ho
  · exact hp.shared_agree

#print axioms EnvDefineOwnedUpdatePost.advance
#print axioms EnvDefineOwnedUpdatePost.finish

end Vsa.Sim
