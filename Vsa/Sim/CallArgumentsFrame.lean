import Vsa.Sim.CallArgumentsComplete
import Vsa.Sim.ClosureCallEpilogue

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Registers preserved by the prologue and every child retain their original values. -/
theorem ArgumentsReady.reg_frame
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {calleeCost argsCost reserve : Nat} {st middle final : Vsa.While.St} {d env : Nat}
    {callee : Expr} {args : List Expr} {calleeValue : Value} {values : List Value}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {after : Config}
    (h : ArgumentsReady g N M phiF phiC alloc exts shared calleeCost argsCost reserve
      st middle final d env callee args calleeValue values sp ret dst node interp saved7 m0 after)
    (R : Register) (hr : AbiPreservedNoise R)
    (h8 : (Register.x8 == R) = false) (h9 : (Register.x9 == R) = false)
    (h18 : (Register.x18 == R) = false) (h2 : (Register.x2 == R) = false) :
    after.σ.regs.get? R = g R := by
  obtain ⟨start, empty, begun⟩ := h.path
  obtain ⟨arm, child, v8, v9, v18, path⟩ := begun.result.path
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800031b0#64 (fun _ => True)
    (.call callee args) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 arm.σ.mem arm path.result.retained.arm
  exact (begun.extra.regs R hr).trans ((path.extra.frame R hr).trans (p.frame R hr h8 h9 h18 h2))

/-- Recover the original caller frame after actual callee and argument evaluation. -/
theorem ArgumentsReady.caller_frame
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {calleeCost argsCost reserve : Nat} {st middle final : Vsa.While.St} {d env : Nat}
    {callee : Expr} {args : List Expr} {calleeValue : Value} {values : List Value}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {before after : Config}
    (h : ArgumentsReady g N M phiF phiC alloc exts shared calleeCost argsCost reserve
      st middle final d env callee args calleeValue values sp ret dst node interp saved7 m0 after)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared (calleeCost + (argsCost + reserve))
      st d env (.call callee args) sp ret dst interp node m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (interpAbove : sp.toNat ≤ interp.toNat) (interpHi : interp.toNat + 12 ≤ SL.hi)
    (depthRead : read32 m0 (interp.toNat + 8) = some d) (depthBound : d < 1000) :
    ∃ v8 v9 v18 saved5 saved3,
      ClosureCallPrefix.CallerFrame g A SL sp ret dst interp v8 v9 v18 saved5 saved3 saved7 d m0 after := by
  obtain ⟨start, empty, begun⟩ := h.path
  obtain ⟨arm, child, v8, v9, v18, path⟩ := begun.result.path
  have ready := path.result
  have arguments := path.extra
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800031b0#64 (fun _ => True)
    (.call callee args) sp ret dst node interp v8 v9 v18 arm.σ.sailOutput m0 arm.σ.mem arm ready.retained.arm
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact p.spRoom)
  have upper := entry.entry.stackOK.2.1
  have bottom := ready.window.lo
  have offArena (k : Nat) (lo : SL.lo ≤ k) (hi : k < SL.hi) : ¬ (A.lo ≤ k ∧ k < A.hi) := by
    have := L.arena_stack
    omega
  have kept : AgreeP (fun k => (sp - 1088#64).toNat + 1024 ≤ k ∧ k < SL.hi) arm.σ.mem after.σ.mem := by
    intro k hk
    have ha := offArena k (by omega) hk.2
    exact (arguments.memoryFrame k (by omega) ha).trans (begun.extra.memory k (by omega) ha)
  have read (off : Nat) (positive : 8 ≤ off) (bound : off ≤ 32) :
      read64 after.σ.mem (sp.toNat - off) = read64 arm.σ.mem (sp.toNat - off) := by
    apply read64_agreeP (fun k hk => (kept k hk).symm)
    intro k hk
    rw [lowered]
    have := p.spRoom
    constructor <;> omega
  have saved7Addr : (sp - 1088#64).toNat + 1016 = sp.toNat - 72 := by rw [lowered]; have := p.spRoom; omega
  have read7 : read64 after.σ.mem ((sp - 1088#64).toNat + 1016) =
      read64 start.σ.mem ((sp - 1088#64).toNat + 1016) := by
    apply read64_agreeP (P := fun k => (sp - 1088#64).toNat + 1016 ≤ k ∧ k < (sp - 1088#64).toNat + 1024)
    · intro k hk
      exact (begun.extra.memory k (by omega) (offArena k (by omega) (by have := ready.window.hi; omega))).symm
    · intro k hk
      constructor <;> omega
  have bridge (R : Register) (hr : AbiPreservedNoise R) : after.σ.regs.get? R = arm.σ.regs.get? R :=
    (begun.extra.regs R hr).trans (arguments.frame R hr)
  have memory : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      after.σ.mem[k]? = m0[k]? := by
    intro k hs ha
    have room := p.spRoom
    apply Eq.trans (begun.extra.memory k (by rw [lowered]; omega) ha).symm
    exact (arguments.memoryFrame k (by rw [lowered]; omega) ha).symm.trans (p.memFrame k hs)
  have presence := ready.retained.presence.trans (arguments.presence.trans begun.extra.presence)
  obtain ⟨saved3, saved4, saved5, r3, _, r5⟩ := entry.entry.envset_defined
  have g19 := (entry.entry.frame .x19 (by decide)).symm.trans r3
  have g21 := (entry.entry.frame .x21 (by decide)).symm.trans r5
  obtain ⟨_, _, s7, _, _, _, _⟩ := arguments.regs
  have g23 : g Register.x23 = some saved7 :=
    (p.frame .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).symm.trans
      ((arguments.frame .x23 (by decide)).symm.trans s7)
  refine ⟨v8, v9, v18, saved5, saved3,
    { raRead := (read 8 (by decide) (by decide)).trans p.slotRa
      s0Read := (read 16 (by decide) (by decide)).trans p.slotS0
      s1Read := (read 24 (by decide) (by decide)).trans p.slotS1
      s2Read := (read 32 (by decide) (by decide)).trans p.slotS2
      s7Read := by rw [← saved7Addr]; exact read7.trans arguments.saved7Read
      resultReg := (bridge .x9 (by decide)).trans p.s1
      g8 := p.saved8, g9 := p.saved9, g18 := p.saved18, g2 := p.savedSp
      g19 := g19, g21 := g21, g23 := g23, frame := ?_
      memoryFrame := fun k hs ha _ => memory k hs ha
      presence := presence
      words := ValueWordsTotal.mono presence (entry.entry.mem ▸ entry.entry.sret_words)
      support := h.loop.ground.ground.eval_call, depthRead := ?_, depthBound := depthBound
      stackSize := p.spRoom, stackHi := upper, stackRam := p.spHi, stackLo := p.spLo
      stackHtif := p.spWin, stackAlign := p.spAlign, retAlign := p.retAlign
      retOutside := by have := p.sretStack; rw [lowered] at bottom; have := p.spRoom; omega }⟩
  · intro R hr h9 h18 h2
    have abi : ∀ R, ClosureCallPrefix.bodyKeep R = true → AbiPreservedNoise R := by intro R; cases R <;> decide
    have mask : ∀ R, ClosureCallPrefix.bodyKeep R = true → (Register.x8 == R) = false := by intro R; cases R <;> decide
    exact (bridge R (abi R hr)).trans (p.frame R (abi R hr) (mask R hr)
      (by exact beq_eq_false_iff_ne.mpr h9.symm) (by exact beq_eq_false_iff_ne.mpr h18.symm)
      (by exact beq_eq_false_iff_ne.mpr h2.symm))
  · apply Eq.trans (read32_agreeP (P := fun k => interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12) _
      (fun k hk => by constructor <;> omega)) depthRead
    intro k hk
    exact memory k (by omega) (offArena k (by have := p.spRoom; rw [lowered] at bottom; omega) (by omega))

end Vsa.Sim.CallCallee
