import Vsa.Sim.CallArgStageData
import Vsa.Sim.CallEvalSites
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The loop state reloaded after the recursive argument evaluation. -/
structure Saved (m : Mem) (sp env : BitVec 64) (index count : Nat) : Prop where
  countRead : read64 m (sp.toNat + 24) = some (BitVec.ofNat 64 count).toNat
  indexRead : read64 m (sp.toNat + 16) = some (BitVec.ofNat 64 index).toNat
  envRead : read64 m (sp.toNat + 8) = some env.toNat
  destinationRead : read64 m sp.toNat = some (destination sp index).toNat

/-- Read back all four words of the staging write log. -/
theorem saved (m : Mem) (sp env : BitVec 64) (index count : Nat) :
    Saved (writeLog m (writes sp env index count)) sp env index count := by
  constructor
  · exact read64_of_writeLog_at m (writes sp env index count) 0 _ _ rfl
      (by simp only [writes, List.drop, OutLRange, and_true]; exact ⟨by omega, by omega, by omega⟩)
  · exact read64_of_writeLog_at m (writes sp env index count) 1 _ _ rfl
      (by simp only [writes, List.drop, OutLRange, and_true]; exact ⟨by omega, by omega⟩)
  · exact read64_of_writeLog_at m (writes sp env index count) 2 _ _ rfl
      (by simp only [writes, List.drop, OutLRange, and_true]; omega)
  · exact read64_of_writeLog_at m (writes sp env index count) 3 _ _ rfl
      (by simp [writes, OutLRange])

/-- A child preserving the caller spill window retains the complete loop state. -/
theorem Saved.transport {m m' : Mem} {sp env : BitVec 64} {index count : Nat}
    (h : Saved m sp env index count)
    (agreement : AgreeP (fun k => sp.toNat ≤ k ∧ k < sp.toNat + 32) m m') :
    Saved m' sp env index count := by
  have rd (off : Nat) (bound : off ≤ 24) : read64 m (sp.toNat + off) = read64 m' (sp.toNat + off) :=
    read64_agreeP agreement (fun k hk => by constructor <;> omega)
  exact ⟨(rd 24 (by decide)).symm.trans h.countRead, (rd 16 (by decide)).symm.trans h.indexRead,
    (rd 8 (by decide)).symm.trans h.envRead, (rd 0 (by decide)).symm.trans h.destinationRead⟩

/-- The concrete register calculation at the child call. -/
theorem registers (sp node interp env : BitVec 64) (index count : Nat)
    (bb cb : List (BitVec 8)) (bound : index < 32) :
    (evalBlocks argsHeadBodySeg (SegEvalState.init (input sp node interp env index count) [bb, cb])).regs =
      [(10, sp + 64#64), (11, interp), (14, destination sp index),
       (15, BitVec.ofNat 64 (24 * index) + 976#64), (12, bytesVal .ld cb),
       (2, sp), (8, node), (16, BitVec.ofNat 64 index), (18, interp), (13, env)] := by
  change runGM (argsHeadBodySeg[0].body.drop 8)
    (runGM (argsHeadBodySeg[0].body.take 8) (input sp node interp env index count) [bb, cb]) [] = _
  rw [offset_regs sp node interp env index count bb cb bound]
  change [(10, sp + 64#64), (11, interp + 0#64), (14, destination sp index),
    (15, BitVec.ofNat 64 (24 * index) + 976#64), (12, bytesVal .ld cb),
    (2, sp), (8, node), (16, BitVec.ofNat 64 index), (18, interp), (13, env)] = _
  rw [BitVec.add_zero]

/-- The actual child entry retains the four spill words and the caller frame. -/
structure Post (node sp interp env child : BitVec 64) (index count : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003164#64
  ra : after.σ.regs.get? Register.x1 = some 0x80003224#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, sp + 64#64), (11, interp), (12, child), (13, env), (2, sp)]
  memory : after.σ.mem = writeLog before.σ.mem (writes sp env index count)
  saved : Saved after.σ.mem sp env index count
  outside : ∀ k, ¬ (sp.toNat ≤ k ∧ k < sp.toNat + 32) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the indexed argument staging and its generated recursive-call JAL. -/
theorem run (node sp interp env base child : BitVec 64) (index count : Nat) (before : Config)
    (G : Geometry node base sp index count)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x800031dc#64)
    (pins : GHolds before.σ (input sp node interp env index count))
    (code : Code.Eval_exprLoaded before.σ.mem)
    (baseRead : read64 before.σ.mem (node.toNat + 16) = some base.toNat)
    (childRead : read64 before.σ.mem (base.toNat + 8 * index) = some child.toNat) :
    ∃ after, Steps before after ∧ Post node sp interp env child index count before after := by
  obtain ⟨bb, cb, D⟩ := data before.σ.mem sp node interp env base child index count G code baseRead childRead
  have bound : index < 32 := by have := G.indexBound; have := G.countBound; omega
  have regs := registers sp node interp env index count bb cb bound
  have log := CallArgStage.log sp node interp env index count bb cb bound G.caller.stackHi
  obtain ⟨after, C⟩ := bridgeOfSegFull argsHeadBodySeg (input sp node interp env index count) [bb, cb]
    0x800031dc#64 0x80003164#64 0x80003224#64 before good pc good.minstret tick pins
    (by change KeysOK [2, 8, 16, 15, 18, 13]; decide) D.facts
    (by change ChainOK 0x800031dc#64 [2, 8, 16, 15, 18, 13] argsHeadBodySeg; decide)
    (by rw [regs]; change KeysOK [10, 11, 14, 15, 12, 2, 8, 16, 18, 13]; decide)
    (by rw [regs]; change ∀ n ∈ ([10, 11, 14, 15, 12, 2, 8, 16, 18, 13] : List Nat), n ≠ 1; decide)
    (by
      intro middle hg ht hp hm memory _
      have code' : Code.Eval_exprLoaded middle.σ.mem := by
        apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ code
        intro k hk
        rw [memory, log]
        symm
        apply writeLog_out
        simp only [writes, OutL, and_true]
        have := G.caller.stackHtif
        have : 0x80003fe0 ≤ tohostAddr := by decide
        exact ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨vm, hvm⟩ := hm
      obtain ⟨next, parity, step, ht', hg', mem, obs⟩ :=
        site_80003220_callEval middle.σ middle.tick middle.steps 0x80003220#64 vm
          hg hp hvm code' rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step ht' hg' mem obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) log)
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      args := ?_, memory := memory, saved := by rw [memory]; exact saved _ _ _ _ _
      outside := ?_, output := C.output, frame := ?_ }⟩
  · have selected := regs ▸ C.registers
    apply gholds_selected (hregs := selected)
    change some (sp + 64#64) = some (sp + 64#64) ∧ some interp = some interp ∧
      some (bytesVal .ld cb) = some child ∧ some env = some env ∧ some sp = some sp ∧ True
    simp only [D.childValue, and_self]
  · intro k hk
    rw [memory]
    symm
    apply writeLog_out
    simp only [writes, OutL, and_true]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro R hR
    have hn : ∀ r ∈ noiseRegs, (r == R) = false := by
      cases R <;> simp_all [AbiPreserved, noiseRegs]
    have hw : ∀ n ∈ wrChain argsHeadBodySeg, (gprReg n == R) = false := by
      cases R <;> simp_all [AbiPreserved] <;> decide
    have hr : (Register.x1 == R) = false := by cases R <;> simp_all [AbiPreserved]
    exact C.frame R hn hw hr

end Vsa.Sim.CallArgStage
