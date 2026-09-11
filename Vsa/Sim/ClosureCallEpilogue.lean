import Vsa.Sim.ClosureReturnMemory
import Vsa.Sim.EvalReturn

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Original evaluator-frame facts retained at closure dispatch. -/
structure CallerFrame (g : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp ret sret interp v8 v9 v18 saved5 saved3 saved7 : BitVec 64)
    (depth : Nat) (m0 : Mem) (before : Config) : Prop where
  raRead : read64 before.σ.mem (sp.toNat - 8) = some ret.toNat
  s0Read : read64 before.σ.mem (sp.toNat - 16) = some v8.toNat
  s1Read : read64 before.σ.mem (sp.toNat - 24) = some v9.toNat
  s2Read : read64 before.σ.mem (sp.toNat - 32) = some v18.toNat
  s7Read : read64 before.σ.mem (sp.toNat - 72) = some saved7.toNat
  resultReg : before.σ.regs.get? Register.x9 = some sret
  g8 : g Register.x8 = some v8
  g9 : g Register.x9 = some v9
  g18 : g Register.x18 = some v18
  g2 : g Register.x2 = some sp
  g19 : g Register.x19 = some saved3
  g21 : g Register.x21 = some saved5
  g23 : g Register.x23 = some saved7
  frame : ∀ R, bodyKeep R = true → R ≠ Register.x9 → R ≠ Register.x18 → R ≠ Register.x2 →
    before.σ.regs.get? R = g R
  memoryFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → before.σ.mem[k]? = m0[k]?
  presence : MemExtends m0 before.σ.mem
  words : ValueWordsTotal before.σ.mem sret.toNat
  support : EvalCallSupport before.σ.mem SL A (sp - 1088#64)
  depthRead : read32 before.σ.mem (interp.toNat + 8) = some depth
  depthBound : depth < 1000
  stackSize : 1088 ≤ sp.toNat
  stackHi : sp.toNat ≤ SL.hi
  stackRam : sp.toNat ≤ 0x100000000
  stackLo : 0x80000000 ≤ sp.toNat
  stackHtif : tohostAddr + 16 + 1088 ≤ sp.toNat
  stackAlign : sp.toNat % 8 = 0
  retAlign : ret.toNat % 4 = 0
  retOutside : sret.toNat + 24 ≤ sp.toNat - 72 ∨ sp.toNat ≤ sret.toNat

/-- Marshal the executed return and its selected result into the existing final epilogue. -/
theorem BodyRunAt.epilogue
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC entryF entryC resultF resultC : Addr → Nat} {nf nc reserve : Nat}
    {shared : Nat → Prop} {st final : Vsa.While.St} {env : Nat}
    {cd : ClosureData} {values : List Value} {status : Status} {value : Value}
    {sp call object fn interp parent saved5 saved3 saved7 p sret ret v8 v9 v18 : BitVec 64}
    {depth : Nat} {returns : Bool} {m0 : Mem} {before called head exited after : Config}
    {Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (h : BodyRunAt N M phiF phiC shared reserve st final env cd values status
      (sp - 1088#64) call object fn interp parent saved5 saved3 depth before called head p exited)
    (post : ClosureReturn.Post N phiC (sp - 1088#64) sret interp saved5 saved3 saved7 depth returns exited after)
    (caller : CallerFrame g A SL sp ret sret interp v8 v9 v18 saved5 saved3 saved7 depth m0 before)
    (windows : ClosureReturn.StackWindows SL interp sret)
    (repr : ReturnRepr N A entryF entryC resultF resultC nf nc final.store [(sret.toNat, value)]
      Owned (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem) :
    PreEpilogueOwned g N A SL resultF resultC final value sp ret sret v8 v9 v18
      after.σ.sailOutput m0 Owned after := by
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact caller.stackSize)
  have high := h.caller_stack post caller.depthRead caller.depthBound
  have read (off : Nat) (positive : 8 ≤ off) (bound : off ≤ 32) :
      read64 after.σ.mem (sp.toNat - off) = read64 before.σ.mem (sp.toNat - off) := by
    apply read64_agreeP (P := fun k => (sp - 1088#64).toNat + 1056 ≤ k ∧ k < SL.hi ∧
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24))
      (fun k hk => high k hk.1 hk.2.1 hk.2.2)
    intro k hk
    rw [lowered]
    have := caller.stackSize; have := caller.stackHi; have := caller.retOutside
    exact ⟨by omega, by omega, by omega⟩
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → exited.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply post.outside k
    · have := windows.interpLo; have := windows.interpHi; omega
    · have := windows.retLo; have := windows.retHi; omega
  have exitedSupport : EvalCallSupport exited.σ.mem SL A (sp - 1088#64) := caller.support.transport (fun k hk =>
    (h.memoryFrame k (caller.support.outsideArena hk) (caller.support.outsideStack hk)).symm)
  have support : EvalCallSupport after.σ.mem SL A (sp - 1088#64) :=
    exitedSupport.transport_stack (fun k hk => (stackFrame k hk).symm)
  have presence := caller.presence.trans (h.presence.trans post.presence)
  have frame : ∀ R, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false → after.σ.regs.get? R = g R := by
    intro reg abi h8 h9 h18 h2
    by_cases is19 : reg = Register.x19
    · subst reg
      exact (show after.σ.regs.get? Register.x19 = some saved3 from
        gholds_lookup _ post.regs (show lookupG 19 _ = some saved3 from rfl)).trans caller.g19.symm
    by_cases is21 : reg = Register.x21
    · subst reg
      exact (show after.σ.regs.get? Register.x21 = some saved5 from
        gholds_lookup _ post.regs (show lookupG 21 _ = some saved5 from rfl)).trans caller.g21.symm
    by_cases is23 : reg = Register.x23
    · subst reg
      exact (show after.σ.regs.get? Register.x23 = some saved7 from
        gholds_lookup _ post.regs (show lookupG 23 _ = some saved7 from rfl)).trans caller.g23.symm
    have mask : ∀ R, AbiPreserved R = true → (Register.x8 == R) = false →
        R ≠ Register.x19 → R ≠ Register.x21 → R ≠ Register.x23 → bodyKeep R = true := by
      intro R; cases R <;> decide
    have kept := mask reg abi.1 h8 is19 is21 is23
    have joinMask : ∀ R, bodyKeep R = true → ClosureReturnJoin.keep R = true := by
      intro R; cases R <;> decide
    exact (post.frame reg (joinMask reg kept)).trans ((h.frame reg kept).trans
      (caller.frame reg kept (beq_eq_false_iff_ne.mp h9).symm
        (beq_eq_false_iff_ne.mp h18).symm (beq_eq_false_iff_ne.mp h2).symm))
  have memoryFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      (sret.toNat ≤ k ∧ k < sret.toNat + 24) ∨ after.σ.mem[k]? = m0[k]? := by
    intro k hs ha
    by_cases result : sret.toNat ≤ k ∧ k < sret.toNat + 24
    · exact Or.inl result
    right
    apply Eq.trans _ (caller.memoryFrame k hs ha result)
    by_cases inStack : SL.lo ≤ k ∧ k < SL.hi
    · apply high k _ inStack.2 result
      rw [lowered]
      have := caller.stackSize; omega
    · exact (stackFrame k inStack).symm.trans (h.memoryFrame k ha inStack).symm
  refine ⟨after.σ.mem, ⟨?_, presence, ValueWordsTotal.mono (h.presence.trans post.presence) caller.words,
    repr.survives⟩, repr.owned⟩
  exact ⟨post.good, post.tick, post.pc,
    gholds_lookup _ post.regs (show lookupG 9 _ = some sret from rfl),
    gholds_lookup _ post.regs (show lookupG 2 _ = some (sp - 1088#64) from rfl),
    post.minstret, rfl, by simpa only [OutRepr, Vsa.Machine.output, post.output] using h.exit.out,
    rfl, support.image.text.Eval_exprLoaded, repr.values _ _ (List.mem_singleton_self _),
    repr.storeRepr, frame,
    (read 8 (by decide) (by decide)).trans caller.raRead,
    (read 16 (by decide) (by decide)).trans caller.s0Read,
    (read 24 (by decide) (by decide)).trans caller.s1Read,
    (read 32 (by decide) (by decide)).trans caller.s2Read,
    caller.g8, caller.g9, caller.g18, caller.g2, memoryFrame, caller.stackSize,
    caller.stackRam, caller.stackLo, caller.stackHtif, caller.stackAlign, caller.retAlign⟩

end Vsa.Sim.ClosureCallPrefix
