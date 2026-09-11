import Vsa.Sim.RuntimeArraysDefine
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.MemPresence
import Vsa.Sim.rows.EnvDefineTailFramed

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The existing-name return retains the exact defined store and all allocation credits. -/
structure EnvDefineHitAllocatorPost
    (saved : (R : Register) → Option (RegisterType R)) (sp dst : BitVec 64)
    (m : Mem) (N : NativeAddrs) {A : Arena} {SL : StackLayout}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (store : Store)
    (target : Addr) (name : String) (v : Value) (after : Config) : Prop where
  exit : EnvDefineOwnedReturnPost saved sp m N A exts phiF phiC alloc shared
    InitialReadableByte (InitialWriteByte SL) store target name v after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits
    (store.define target name v) after.σ.mem
  outside : AgreeP (SetOutside dst.toNat) m after.σ.mem
  presence : MemExtends m after.σ.mem
  destination : A.contains dst.toNat 24

/-- An owned hit return and the registers and output preserved by both tail spans. -/
structure EnvDefineHitKeptPost (post : Config → Prop)
    (g : (R : Register) → Option (RegisterType R)) (out : Array String)
    (after : Config) : Prop where
  result : post after
  kept : KeepGhost EnvDefineTailKeep g out after

/-- Run the existing-name copy and return, preserving allocator metadata and reserve. -/
theorem envDefineHitAllocator_run_kept
    {saved : (R : Register) → Option (RegisterType R)}
    {env namePtr src count cursor sp valsBV dst : BitVec 64} {idx : Nat}
    {m : Mem} {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {name : String} {v : Value} {before : Config}
    {g : (R : Register) → Option (RegisterType R)} {out : Array String}
    (keep : KeepGhost EnvDefineTailKeepSp g out before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m)
    (hit : EnvDefineUpdateHitPre saved env namePtr src count cursor sp idx m before)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (ht : target < store.frames.size)
    (hi : idx < store.frames[target].vars.length)
    (matchName : store.frames[target].vars[idx].1 = name)
    (unique : FrameUnique store.frames[target])
    (envAddr : env.toNat = phiF target)
    (values : read64 m (phiF target + 16) = some valsBV.toNat)
    (slot : dst.toNat = valsBV.toNat + 24 * idx)
    (source : ValueOwned m shared src.toNat v)
    (word : ValueWordRepr m N phiC src.toNat v)
    (bounded : ValueClosuresBounded store.closures.size v)
    (code : Code.Env_defineLoaded m)
    (geometry : EnvDefineUpdateGeom env src valsBV dst idx m)
    (dstArena : A.contains dst.toNat 24)
    (arenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (arenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    ∃ after, Steps before after ∧
      EnvDefineHitKeptPost
        (EnvDefineHitAllocatorPost saved sp dst m N M phiF phiC alloc exts shared credits
          store target name v) g out after := by
  have sharedOff : ∀ k, shared k → SetOutside dst.toNat k := by
    simpa only [slot] using (entry.heap.store.frames target ht).sharedOutsideSet
      entry.heap.immutable hi values
  obtain ⟨copied, copySteps, retained⟩ := envDefineUpdateFromHitCopiedKeep
    saved env namePtr src count cursor sp valsBV dst idx m N phiC v A g out
    code word geometry (source.covered sharedOff) dstArena arenaStack arenaCode
    before ⟨hit, keep⟩
  have agreement : AgreeP shared m copied.σ.mem :=
    fun k hk => retained.copy.update.agree_outside k (sharedOff k hk)
  have copyPost : EnvDefineOwnedUpdatePost saved env src dst sp idx m N phiC v shared copied :=
    ⟨retained.copy.update, agreement, source.copy_total retained.copy.copied agreement⟩
  have facts := copyPost.update.destruct
  have advanced := copyPost.advance entry.heap entry.repr ht hi matchName unique
    envAddr values slot
  have owned := copyPost.heap_owned entry.heap ht hi matchName unique values slot bounded
  have ready := entry.arrays.defineHit (N := N) (v := v) entry.heap ht hi matchName values
    (slot ▸ facts.word.words) (by simpa only [slot] using copyPost.update.agree_outside)
  obtain ⟨arrays, arrayFacts⟩ := (entry.heap.store.frames target ht).arrays
  have capPos : 0 < arrays.cap := by have := arrayFacts.bound; omega
  have valuesEq : arrays.values = valsBV.toNat :=
    Option.some.inj (arrayFacts.valuesRead.symm.trans values)
  have live : (valsBV.toNat, 24 * arrays.cap) ∈ exts := by
    rw [← valuesEq]
    exact entry.heap.ledger.live _ _ _ (arrayFacts.values.nonempty capPos)
  have privateOff := AllocLedger.privDisjoint_of_ainvAt entry.ainv before.σ gp
  have invariant : AInvAt M gpv copied.σ.mem exts := by
    apply L.ainvAt_transport entry.ainv
    intro k hk
    apply copyPost.update.agree_outside k
    by_cases inside : SetOutside dst.toNat k
    · exact inside
    exfalso
    have bounds : valsBV.toNat ≤ k ∧ k < valsBV.toNat + 24 * arrays.cap := by
      have := arrayFacts.bound
      unfold SetOutside at inside
      omega
    have noPrivate := privateOff (valsBV.toNat, 24 * arrays.cap) live
      (k - valsBV.toNat) (by dsimp; omega)
    have address : valsBV.toNat + (k - valsBV.toNat) = k := by omega
    exact noPrivate (by simpa only [address] using hk)
  have allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits
      (store.define target name v) copied.σ.mem :=
    { heap := owned, repr := advanced.toStoreRepr, arrays := ready
      geometry := entry.geometry, parents := StoreParents.define store target name v entry.parents
      ainv := invariant, budget := entry.budget
      reserve := entry.reserve.after_live (by
        intro k off
        apply copyPost.update.agree_outside k
        have outside := off (valsBV.toNat, 24 * arrays.cap) live
        have bound := arrayFacts.bound
        unfold SetOutside
        rw [slot]
        omega)
        (fun e he => (entry.heap.ledger.arena.1 e he).2) L.arena_globals }
  obtain ⟨after, returnSteps, returned, kept⟩ := copyPost.update.restoreKeep retained.kept
  refine ⟨after, copySteps.trans returnSteps, ?_, kept⟩
  have returnedSelf : EnvDefineEpilogueExactPost sp saved after.σ.mem after := by
    rw [returned.mem]; exact returned
  refine
    { exit := ⟨returnedSelf, ?_, ?_, ?_⟩
      allocator := ?_, outside := ?_, presence := ?_, destination := dstArena } <;> rw [returned.mem]
  · exact advanced
  · exact owned
  · exact copyPost.shared_agree
  · exact allocator
  · exact copyPost.update.agree_outside
  · exact facts.presence

/-- Run the existing-name copy and return, preserving allocator metadata and reserve. -/
theorem envDefineHitAllocator_run
    {saved : (R : Register) → Option (RegisterType R)}
    {env namePtr src count cursor sp valsBV dst : BitVec 64} {idx : Nat}
    {m : Mem} {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {name : String} {v : Value} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m)
    (hit : EnvDefineUpdateHitPre saved env namePtr src count cursor sp idx m before)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (ht : target < store.frames.size)
    (hi : idx < store.frames[target].vars.length)
    (matchName : store.frames[target].vars[idx].1 = name)
    (unique : FrameUnique store.frames[target])
    (envAddr : env.toNat = phiF target)
    (values : read64 m (phiF target + 16) = some valsBV.toNat)
    (slot : dst.toNat = valsBV.toNat + 24 * idx)
    (source : ValueOwned m shared src.toNat v)
    (word : ValueWordRepr m N phiC src.toNat v)
    (bounded : ValueClosuresBounded store.closures.size v)
    (code : Code.Env_defineLoaded m)
    (geometry : EnvDefineUpdateGeom env src valsBV dst idx m)
    (dstArena : A.contains dst.toNat 24)
    (arenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (arenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    ∃ after, Steps before after ∧
      EnvDefineHitAllocatorPost saved sp dst m N M phiF phiC alloc exts shared credits
        store target name v after := by
  obtain ⟨after, steps, post⟩ := envDefineHitAllocator_run_kept
    (g := fun R => before.σ.regs.get? R) (out := before.σ.sailOutput)
    ⟨fun _ _ => rfl, rfl⟩ L entry hit gp ht hi matchName unique envAddr values slot
    source word bounded code geometry dstArena arenaStack arenaCode
  exact ⟨after, steps, post.result⟩

#print axioms envDefineHitAllocator_run_kept

#print axioms envDefineHitAllocator_run

end Vsa.Sim
