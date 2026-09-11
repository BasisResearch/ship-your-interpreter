import Vsa.Sim.EnvDefineAppendStoreRun

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Append returns with exact stored data and the restored caller snapshot. -/
structure EnvDefineAppendReturned
    (saved : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (env src copied sp : BitVec 64) (parent : Option Addr) (vars : List (String × Value))
    (name : String) (v : Value) (cap names vals : Nat) (before after : Config) extends
    EnvDefineAppendMemory N A phiF phiC env src copied sp parent vars name v cap names vals before after : Prop where
  returned : EnvDefineEpilogueExactPost sp saved after.σ.mem after
  resultReg : ∃ w, after.σ.regs.get? Register.x10 = some w
  output : after.σ.sailOutput = before.σ.sailOutput
  rest : ∀ R, AbiPreserved R = true → EnvDefineRestored R = false → R ≠ Register.x2 →
    after.σ.regs.get? R = before.σ.regs.get? R

/-- The existing epilogue retains append's exact memory result. -/
theorem EnvDefineAppendStored.restore
    {saved : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {env src copied sp : BitVec 64} {parent : Option Addr} {vars : List (String × Value)}
    {name : String} {v : Value} {cap names vals : Nat} {before stored : Config}
    (h : EnvDefineAppendStored saved N A phiF phiC env src copied sp parent vars
      name v cap names vals before stored) :
    ∃ after, Steps stored after ∧
      EnvDefineAppendReturned saved N A phiF phiC env src copied sp parent vars
        name v cap names vals before after := by
  obtain ⟨lds, facts, values⟩ := h.savedSpills.chainFacts
  have entry : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
      0x80002aec#64 stored.σ.mem stored :=
    ⟨h.good, rfl, h.pc, h.good.minstret, ⟨h.spReg, trivial⟩,
      (by change KeysOK [2]; decide), facts, h.tick⟩
  obtain ⟨after, steps, post, kept⟩ := envDefineEpilogueRowKeep sp lds stored.σ.mem
    (fun R => stored.σ.regs.get? R) before.σ.sailOutput stored
    ⟨entry, fun _ _ => rfl, h.output⟩
  have returned := envDefineEpilogueExact_of_post sp saved lds stored.σ.mem after values post
  have result : ∃ w, after.σ.regs.get? Register.x10 = some w := by
    obtain ⟨w, hw⟩ := h.resultReg
    exact ⟨w, (kept.keep _ (by decide)).trans hw⟩
  refine ⟨after, steps,
    { toEnvDefineAppendMemory := ?_, returned := ?_, resultReg := result
      output := kept.out, rest := ?_ }⟩
  · have memory : EnvDefineAppendMemory N A phiF phiC env src copied sp parent vars
        name v cap names vals before after := by
      have hm := h.toEnvDefineAppendMemory
      cases hm with
      | mk readback word copy nameRead nameString agreement outsideArena presence =>
        constructor <;> rw [returned.mem]
        · exact readback
        · exact word
        · exact copy
        · exact nameRead
        · exact nameString
        · exact agreement
        · exact outsideArena
        · exact presence
    exact memory
  · rw [returned.mem]; exact returned
  · intro R abi notRestored notSp
    have keep := (envDefineRest_facts R abi notRestored notSp).1
    exact (kept.keep R keep).trans (h.frame R abi)

/-- Append's five stores and caller return are one witnessed execution. -/
theorem EnvDefineAppendStoreInput.returned
    {saved : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {env src copied sp : BitVec 64} {parent : Option Addr} {vars : List (String × Value)}
    {name : String} {v : Value} {cap names vals : Nat} {before : Config}
    (h : EnvDefineAppendStoreInput saved N A phiF phiC env src copied sp parent vars
      name v cap names vals before) :
    ∃ after, Steps before after ∧
      EnvDefineAppendReturned saved N A phiF phiC env src copied sp parent vars
        name v cap names vals before after := by
  obtain ⟨stored, storeSteps, post⟩ := h.run
  obtain ⟨after, returnSteps, returned⟩ := post.restore
  exact ⟨after, storeSteps.trans returnSteps, returned⟩

#print axioms EnvDefineAppendStored.restore
#print axioms EnvDefineAppendStoreInput.returned

end Vsa.Sim
