import Vsa.Sim.EnvDefineCapacityCaller

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Both capacity arms select the actual append allocations at one reached memory. -/
structure EnvDefineAppendSelected
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (target : Addr) (name : String) (v : Value)
    (esp env namePtr src r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (shared : Nat → Prop)
    (credits : Nat) (after : Config) : Prop where
  selected : ∃ alloc exts cap,
    EnvDefineAppendAllocatorPost g N A SL phiF phiC st target name v esp env namePtr src r m out M
      alloc exts shared credits cap after
  agreement : AgreeP shared m after.σ.mem

/-- Execute a nonempty miss and either capacity arm to the owned append entry. -/
theorem EnvDefinePrologueAllocatorPost.reach_append
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {valid : target < st.store.frames.size} {name : String} {v : Value}
    {esp env namePtr src r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits : Nat} {before : Config}
    (h : EnvDefinePrologueAllocatorPost g esp env namePtr src r m out N M
      phiF phiC alloc exts shared (credits + 3) st.store target valid name v before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (envAddr : env.toNat = phiF target) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0)
    (positive : 0 < (st.store.frames[target]'valid).vars.length)
    (missing : ∀ i (hi : i < (st.store.frames[target]'valid).vars.length),
      ((st.store.frames[target]'valid).vars[i]'hi).1 ≠ name)
    (growRequest : 48 * (st.store.frames[target]'valid).vars.length ≤ maxReq) :
    ∃ after, Steps before after ∧
      EnvDefineAppendSelected g N A SL phiF phiC st target name v esp env namePtr src r m out M
        shared (credits + 1) after := by
  obtain ⟨scanned, pn, scanSteps, scan⟩ := h.scan L envAddr geometry.stack positive
  apply scan.scanned.resolve
  · intro i hi _ hit
    exact False.elim (missing i hi hit.nameEq)
  · intro _ _ miss
    have countEq : (BitVec.ofNat 64 (st.store.frames[target]'valid).vars.length).toNat =
        (st.store.frames[target]'valid).vars.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countSigned; omega)]
    obtain ⟨dispatched, cap, capacitySteps, capacity⟩ := scan.miss_capacity miss L envAddr countEq
    have caller := capacity.caller h geometry envAddr ghostSp retAlign
    have C := capacity.capacity
    have prefixAgreement : AgreeP shared m dispatched.σ.mem := by
      intro k hk; rw [C.memory]; exact h.agreement k hk
    have support : EvalCallSupport dispatched.σ.mem SL A esp :=
      capacity.support.transport (fun _ _ => rfl)
    by_cases room : (st.store.frames[target]'valid).vars.length < cap
    · have ready : EnvDefineAppendAllocatorPost g N A SL phiF phiC st target name v
          esp env namePtr src r m out M alloc exts shared (credits + 1) cap dispatched :=
        { head := { facts := caller.facts, regs := caller.regs
                    pc := by simpa only [if_pos room] using C.pc, room := room }
          allocator := capacity.allocator.credit_mono (by omega)
          owned := capacity.owned, nameOwned := capacity.nameOwned, support := support }
      exact ⟨dispatched, scanSteps.trans capacitySteps,
        { selected := ⟨alloc, exts, cap, ready⟩, agreement := prefixAgreement }⟩
    · have full : (st.store.frames[target]'valid).vars.length = cap := by
        have := C.bound; omega
      obtain ⟨a, fields⟩ := (capacity.allocator.heap.store.frames target valid).arrays
      have kind : EnvDefineGrowKind cap dispatched :=
        .grow (by omega) (by simpa only [if_neg room] using C.pc) C.capacityReg
      have namesReg : dispatched.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn.toNat) := by
        simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using caller.namesReg
      obtain ⟨grown, exts', cap', pn', pvals', growSteps, grownPost, growAgreement⟩ :=
        envDefineGrowAllocator_run g N A SL phiF phiC st target name v esp env namePtr src r m out M
          exts dispatched.σ.mem alloc shared (credits + 1) cap pn.toNat a.values dispatched geometry L
          caller.facts caller.regs capacity.allocator capacity.owned capacity.nameOwned support full
          capacity.namesRead fields.valuesRead (by omega) kind namesReg
      exact ⟨grown, scanSteps.trans (capacitySteps.trans growSteps),
        { selected := ⟨_, exts', cap', grownPost⟩
          agreement := fun k hk => (prefixAgreement k hk).trans (growAgreement k hk) }⟩


#print axioms EnvDefinePrologueAllocatorPost.reach_append

end Vsa.Sim
