import Vsa.Sim.EnvDefineNameCopyReturn
import Vsa.Sim.EnvDefineAppendInput
import Vsa.Sim.EnvDefineAppendReturn
import Vsa.Sim.EnvDefineAppendInvariant
import Vsa.Sim.RuntimeArraysAppend

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The copied name is installed and env_define has returned to its caller. -/
structure EnvDefineNameAppended
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (target : Addr) (valid : target < st.store.frames.size)
    (name : String) (v : Value) (esp env src r : BitVec 64)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (shared : Nat → Prop) (cap p names vals : Nat) (before after : Config) : Prop where
  returned : EnvDefineAppendReturned (envDefineSaved g r) N A phiF phiC env src (BitVec.ofNat 64 p)
    (esp - 64#64) (st.store.frames[target]'valid).parent (st.store.frames[target]'valid).vars
    name v cap names vals before after
  namesRead : read64 before.σ.mem (phiF target + 8) = some names
  valuesRead : read64 before.σ.mem (phiF target + 16) = some vals
  store : StoreRepr after.σ.mem N A phiF phiC (st.store.define target name v)
  arrays : StoreArraysReady after.σ.mem phiF (st.store.define target name v)
  ainv : M.AInv after.σ ((p, name.length + 1) :: exts)
  agreement : AgreeP shared before.σ.mem after.σ.mem
  support : EvalCallSupport after.σ.mem SL A esp

/-- Join the actual memcpy return to the append stores and the caller epilogue. -/
theorem EnvDefineNameCopied.append
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {name : String} {v : Value}
    {esp env namePtr src r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap p : Nat} {before : Config}
    (h : EnvDefineNameCopied g N A SL phiF phiC st target name v esp env namePtr src r m out M
      alloc exts shared credits cap p before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (sourceAlign : src.toNat % 8 = 0)
    (room : (st.store.frames[target]'h.facts.env_lt).vars.length < cap) :
    ∃ after names vals, Steps before after ∧
      EnvDefineNameAppended g N A SL phiF phiC st target h.facts.env_lt name v esp env src r M
        exts shared cap p names vals before after := by
  have F := h.facts
  have ptrNat := h.block.toNat L.arena_hi
  obtain ⟨a, fields⟩ := (h.baseHeap.store.frames target F.env_lt).arrays
  have namesRead := fields.namesRead
  have valuesRead := fields.valuesRead
  have fresh : ∀ e ∈ exts, ExtDisjoint ((BitVec.ofNat 64 p).toNat, name.length + 1) e := by
    rw [ptrNat]; exact h.block.fresh
  have copiedName : CString before.σ.mem (BitVec.ofNat 64 p).toNat name := by
    rw [ptrNat]; exact h.copiedName
  have input := envDefineAppendInput_of_owned F h.regs L geometry sourceAlign h.pc
    h.savedCopyReg copiedName fresh namesRead valuesRead room
  obtain ⟨after, steps, returned⟩ := input.returned
  have post := returned.toEnvDefineAppendMemory
  have store := post.store_repr h.baseHeap F.store F.env_addr F.cap_read namesRead valuesRead room F.miss
  have footprint := appendFootprint_of_owned h.baseHeap F.env_lt F.cap_read namesRead valuesRead room
    fresh (Nat.le_refl (name.length + 1)) h.owned
  have agreement : AgreeP (AppendOutside (phiF target) a.names a.values
      (st.store.frames[target]'F.env_lt).vars.length) before.σ.mem after.σ.mem := by
    rw [← F.env_addr]
    exact post.agreement
  have newNames : read64 after.σ.mem (phiF target + 8) = some a.names := by
    rw [← F.env_addr]; exact post.readback.namesRead
  have newValues : read64 after.σ.mem (phiF target + 16) = some a.values := by
    rw [← F.env_addr]; exact post.readback.valsRead
  have arrays := h.allocator.arrays.defineAppend (v := v) h.baseHeap F.env_lt F.miss F.cap_read
    namesRead valuesRead room newNames newValues post.word.words agreement footprint.oldValueHeaders
  have invariant : M.AInv after.σ ((p, name.length + 1) :: exts) := by
    have initial : M.AInv before.σ (((BitVec.ofNat 64 p).toNat, name.length + 1) :: exts) := by
      rw [ptrNat]; exact h.regs.ainv
    have result := post.allocatorInvariant h.baseHeap L F.env_addr F.cap_read namesRead valuesRead room
      initial (returned.rest .x3 (by decide) (by decide) (by decide)).symm
    simpa only [ptrNat] using result
  have sharedOff := (h.baseHeap.store.frames target F.env_lt).sharedOutsideAppend
    h.baseHeap.immutable F.cap_read namesRead valuesRead room
  have sharedAgreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => agreement k (sharedOff k hk)
  have support : EvalCallSupport after.σ.mem SL A esp :=
    h.support.transport (fun k hk => (post.outsideArena k (h.support.outsideArena hk)).symm)
  exact ⟨after, a.names, a.values, steps,
    { returned := returned, namesRead := namesRead, valuesRead := valuesRead
      store := store, arrays := arrays, ainv := invariant
      agreement := sharedAgreement, support := support }⟩

#print axioms EnvDefineNameCopied.append

end Vsa.Sim
