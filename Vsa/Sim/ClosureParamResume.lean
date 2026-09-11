import Vsa.Sim.rows.CallClosureFoldBack
import Vsa.Sim.ClosureEnvNewResume
import Vsa.Sim.HelperCallEnvDefine
import Vsa.Sim.InterpEntry
import Vsa.Sim.Code.FixedImage_Eval_expr

namespace Vsa.Sim.ClosureParamResume

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (more : Bool) : List BBlock :=
  if more then callClosureFoldBackLoopSeg else callClosureFoldBackExitSeg

def exitPC (more : Bool) : BitVec 64 :=
  if more then 0x800032dc#64 else 0x80003324#64

def keep (R : Register) : Bool := AbiPreserved R && !(R == .x22)

def selected (sp savedS6 : BitVec 64) (index count : Nat) (more : Bool) : GRegs :=
  [(2, sp), (15, BitVec.ofNat 64 (8 * (index + 1))),
   (22, if more then BitVec.ofNat 64 (8 * count) else savedS6)]

/-- Saved loop words at the actual env_define return. -/
structure Pre (sp savedS6 : BitVec 64) (index count : Nat) (more : Bool)
    (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80003314#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (callClosureFoldBackL sp (BitVec.ofNat 64 (8 * count)))
  geometry : ClosureEnvNewResume.Geometry sp
  indexRead : read64 before.σ.mem sp.toNat = some (8 * index)
  savedRead : read64 before.σ.mem (sp.toNat + 1024) = some savedS6.toNat
  indexLt : index < count
  countBound : count < 2^31
  branch : decide (index + 1 < count) = more
  code : Code.Eval_exprLoaded before.σ.mem

theorem indexStep (index : Nat) :
    BitVec.ofNat 64 (8 * index) + 8#64 = BitVec.ofNat 64 (8 * (index + 1)) := by
  change BitVec.ofNat 64 (8 * index) + BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_add]
  congr 1

/-- The saved index determines the back edge; the final route restores caller s6. -/
theorem Pre.facts {sp savedS6 : BitVec 64} {index count : Nat} {more : Bool}
    {before : Config} (h : Pre sp savedS6 index count more before) :
    ∃ indexBytes savedBytes,
      ChainFacts before.σ.mem before.σ.mem
        (callClosureFoldBackL sp (BitVec.ofNat 64 (8 * count)))
        [indexBytes, savedBytes] (seg more) ∧
      bytesVal .ld indexBytes = BitVec.ofNat 64 (8 * index) ∧
      bytesVal .ld savedBytes = savedS6 := by
  let L := callClosureFoldBackL sp (BitVec.ofNat 64 (8 * count))
  let ldIndex := mkLine 0x80003314#64 0x00013783#32
  have indexAddr : (eaddrM ldIndex L).toNat = sp.toNat := by
    change (sp + 0#64).toNat = sp.toNat
    rw [BitVec.add_zero]
  have count8 : 8 * count < 2^64 := by have := h.countBound; omega
  have index8 : 8 * index < 2^64 := by have := h.indexLt; omega
  have next8 : 8 * (index + 1) < 2^64 := by have := h.indexLt; omega
  obtain ⟨indexBytes, I⟩ := wordLoadFacts_of_read64 before.σ.mem L ldIndex
    (BitVec.ofNat 64 (8 * index)) rfl
    (by rw [indexAddr]; exact h.geometry.lo)
    (by rw [indexAddr]; have := h.geometry.hi; omega)
    (by rw [indexAddr]; right; have := h.geometry.htif; omega)
    (by rw [indexAddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt index8]; exact h.indexRead)
  let ldSaved := mkLine 0x80003320#64 0x40013b03#32
  have savedAddr : (eaddrM ldSaved L).toNat = sp.toNat + 1024 := h.geometry.spillAddr
  obtain ⟨savedBytes, S⟩ := wordLoadFacts_of_read64 before.σ.mem L ldSaved savedS6 rfl
    (by rw [savedAddr]; have := h.geometry.lo; omega)
    (by rw [savedAddr]; exact h.geometry.hi)
    (by rw [savedAddr]; right; have := h.geometry.htif; omega)
    (by rw [savedAddr]; exact h.savedRead)
  have branch : guardB bop.BNE (BitVec.ofNat 64 (8 * count))
      (bytesVal .ld indexBytes + 8#64) = more := by
    rw [I.value, indexStep]
    by_cases moreParams : index + 1 < count
    · have different : BitVec.ofNat 64 (8 * count) ≠ BitVec.ofNat 64 (8 * (index + 1)) := by
        intro eq
        have eqNat := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt count8, Nat.mod_eq_of_lt next8] at eqNat
        omega
      rw [← h.branch]
      simp [guardB, moreParams, different]
    · have last : count = index + 1 := by have := h.indexLt; omega
      rw [← h.branch]
      simp [guardB, last]
  refine ⟨indexBytes, savedBytes, ?_, I.value, S.value⟩
  cases more <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact I.facts
    · exact branch
    · exact S.facts
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact I.facts
    · exact branch

/-- Both routes preserve memory, output, and every ABI register except restored s6. -/
structure Post (sp savedS6 : BitVec 64) (index count : Nat) (more : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC more)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ (selected sp savedS6 index count more)
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, keep R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem run {sp savedS6 : BitVec 64} {index count : Nat} {more : Bool}
    {before : Config} (h : Pre sp savedS6 index count more before) :
    ∃ after, Steps before after ∧ Post sp savedS6 index count more before after := by
  obtain ⟨indexBytes, savedBytes, facts, indexValue, savedValue⟩ := h.facts
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg more)
    (callClosureFoldBackL sp (BitVec.ofNat 64 (8 * count))) [indexBytes, savedBytes]
    0x80003314#64 vm (fun _ => False) keep (selected sp savedS6 index count more) before
    h.good h.pc hvm h.regs (by change KeysOK [2, 22]; decide) facts
    (by cases more <;> change ChainOK 0x80003314#64 [2, 22] _ <;> decide) h.tick
    (by intro k _; cases more <;> rfl) (by decide) (by cases more <;> decide) (by
      cases more
      · change some sp = some sp ∧ some (bytesVal .ld indexBytes + 8#64) =
          some (BitVec.ofNat 64 (8 * (index + 1))) ∧ some (bytesVal .ld savedBytes) = some savedS6 ∧ True
        simp only [indexValue, savedValue, indexStep, and_true]
      · change some sp = some sp ∧ some (bytesVal .ld indexBytes + 8#64) =
          some (BitVec.ofNat 64 (8 * (index + 1))) ∧
          some (BitVec.ofNat 64 (8 * count)) = some (BitVec.ofNat 64 (8 * count)) ∧ True
        simp only [indexValue, indexStep, and_true])
  exact ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := by cases more <;> exact C.pc
      minstret := C.minstret, regs := C.selected_regs
      memory := by cases more <;> exact C.mem
      output := C.output, frame := C.reg_frame }⟩

#print axioms Pre.facts
#print axioms run

/-- Recover loop words through the actual helper return's arena/stack frame. -/
theorem Pre.of_return
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {st : Vsa.While.St} {env : Vsa.While.Addr} {param : String} {value : Vsa.While.Value}
    {sp savedS6 : BitVec 64} {index count : Nat} {more : Bool}
    {m : Mem} {out : Array String} {returned : Config}
    (h : EnvDefineReturnState g N A SL phiF phiC st env param value
      sp 0x80003314#64 m out returned)
    (geometry : ClosureEnvNewResume.Geometry sp)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (arenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (bound : g Register.x22 = some (BitVec.ofNat 64 (8 * count)))
    (indexRead : read64 m sp.toNat = some (8 * index))
    (savedRead : read64 m (sp.toNat + 1024) = some savedS6.toNat)
    (indexLt : index < count) (countBound : count < 2^31)
    (branch : decide (index + 1 < count) = more)
    (support : EvalCallSupport m SL A sp) :
    Pre sp savedS6 index count more returned := by
  have stackAgreement : AgreeP (fun k => sp.toNat ≤ k ∧ k < SL.hi) returned.σ.mem m := by
    intro k hk
    apply h.mem_frame k
    · omega
    · omega
  have support' : EvalCallSupport returned.σ.mem SL A sp :=
    support.transport (fun k hk => h.mem_frame k (support.outsideArena hk) (by
      have := support.outsideStack hk; omega))
  exact
    { good := h.good, tick := h.tick, pc := h.pc, minstret := h.minstret
      regs := ⟨h.sp, (h.frame .x22 (by decide)).trans bound, trivial⟩
      geometry := geometry
      indexRead := (read64_agreeP stackAgreement (fun _ hk => by omega)).trans indexRead
      savedRead := (read64_agreeP stackAgreement (fun _ hk => by omega)).trans savedRead
      indexLt := indexLt, countBound := countBound, branch := branch
      code := support'.image.text.Eval_exprLoaded }

#print axioms Pre.of_return

end Vsa.Sim.ClosureParamResume
