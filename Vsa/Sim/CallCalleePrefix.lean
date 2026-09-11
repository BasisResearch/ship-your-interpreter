import Vsa.Sim.rows.CallArmCalleeEvalGen
import Vsa.Sim.BinaryPrefixData
import Vsa.Sim.CallEvalSites
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The callee prefix changes only the saved environment word. -/
structure Post (node sp interp env child : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003164#64
  ra : after.σ.regs.get? Register.x1 = some 0x800031c0#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, sp + 96#64), (11, interp), (12, child), (13, env), (2, sp)]
  memory : after.σ.mem = writeLog before.σ.mem [(sp.toNat, 8, env)]
  savedEnv : read64 after.σ.mem sp.toNat = some env.toNat
  outside : ∀ k, ¬ (sp.toNat ≤ k ∧ k < sp.toNat + 8) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Read the actual callee pointer, save the environment, and execute its JAL. -/
theorem run (node sp interp env child : BitVec 64) (before : Config)
    (G : BinaryPrefix.Geometry node sp)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x800031b0#64)
    (pins : GHolds before.σ (callArmCalleeEvalL node sp env))
    (interpReg : before.σ.regs.get? Register.x11 = some interp)
    (code : Code.Eval_exprLoaded before.σ.mem)
    (read : read64 before.σ.mem (node.toNat + 8) = some child.toNat) :
    ∃ after, Steps before after ∧ Post node sp interp env child before after := by
  have address : (eaddrM (mkLine 0x800031b0#64 0x00863603#32)
      (callArmCalleeEvalL node sp env)).toNat = node.toNat + 8 := by
    change (node + 8#64).toNat = node.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.nodeHi; change node.toNat + 8 < 2^64; omega)]
    rfl
  obtain ⟨bs, data⟩ := wordLoadFacts_of_read64 before.σ.mem (callArmCalleeEvalL node sp env)
    (mkLine 0x800031b0#64 0x00863603#32) child rfl
    (by rw [address]; have := G.nodeLo; omega)
    (by rw [address]; have := G.nodeHi; omega)
    (by rw [address]; have := G.nodeHtif; omega) (by rw [address]; exact read)
  have facts : ChainFacts before.σ.mem before.σ.mem (callArmCalleeEvalL node sp env)
      [bs] callArmCalleeEvalSeg := by
    chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
    · exact data.facts
    · exact BinaryPrefix.store_facts G 0 rfl rfl rfl (by decide) (by decide)
  have log : (evalBlocks callArmCalleeEvalSeg
      (SegEvalState.init (callArmCalleeEvalL node sp env) [bs])).log = [(sp.toNat, 8, env)] := by
    change [((sp + 0#64).toNat, 8, env)] = _
    rw [BitVec.add_zero]
  have regs : (evalBlocks callArmCalleeEvalSeg
      (SegEvalState.init (callArmCalleeEvalL node sp env) [bs])).regs =
      [(10, sp + 96#64), (12, child), (2, sp), (13, env)] := by
    change [(10, sp + 96#64), (12, bytesVal .ld bs), (2, sp), (13, env)] = _
    rw [data.value]
  obtain ⟨after, C⟩ := bridgeOfSegFull callArmCalleeEvalSeg (callArmCalleeEvalL node sp env) [bs]
    0x800031b0#64 0x80003164#64 0x800031c0#64 before good pc good.minstret tick pins
    (by change KeysOK [12, 2, 13]; decide) facts
    (by change ChainOK 0x800031b0#64 [12, 2, 13] callArmCalleeEvalSeg; decide)
    (by rw [regs]; change KeysOK [10, 12, 2, 13]; decide)
    (by rw [regs]; change ∀ n ∈ ([10, 12, 2, 13] : List Nat), n ≠ 1; decide)
    (by
      intro middle hg ht hp hm memory _
      have code' : Code.Eval_exprLoaded middle.σ.mem := by
        apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ code
        intro k hk
        rw [memory, log]
        symm
        apply writeLog_out
        simp only [OutL, and_true]
        have := G.stackHtif
        have : 0x80003fe0 ≤ tohostAddr := by decide
        omega
      obtain ⟨vm, hvm⟩ := hm
      obtain ⟨next, parity, step, ht', hg', mem, obs⟩ :=
        site_800031bc_callEval middle.σ middle.tick middle.steps 0x800031bc#64 vm
          hg hp hvm code' rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step ht' hg' mem obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) log)
  have selected : GHolds after.σ [(10, sp + 96#64), (12, child), (2, sp), (13, env)] :=
    regs ▸ C.registers
  obtain ⟨a0, a2, spReg, a3, _⟩ := selected
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      args := ⟨a0, (C.frame .x11 (by decide) (by decide) (by decide)).trans interpReg,
        a2, a3, spReg, trivial⟩
      memory := memory, savedEnv := ?_, outside := ?_, output := C.output, frame := ?_ }⟩
  · rw [memory]
    exact read64_of_writeLog_at before.σ.mem [(sp.toNat, 8, env)] 0 _ _ rfl (by simp [OutLRange])
  · intro k hk
    rw [memory]
    exact (writeLog_out before.σ.mem [(sp.toNat, 8, env)] k (by simp only [OutL, and_true]; omega)).symm
  · intro R hR
    have hn : ∀ r ∈ noiseRegs, (r == R) = false := by
      cases R <;> simp_all [AbiPreserved, noiseRegs]
    have hw : ∀ n ∈ wrChain callArmCalleeEvalSeg, (gprReg n == R) = false := by
      cases R <;> simp_all [AbiPreserved] <;> decide
    have hr : (Register.x1 == R) = false := by cases R <;> simp_all [AbiPreserved]
    exact C.frame R hn hw hr

end Vsa.Sim.CallCallee
