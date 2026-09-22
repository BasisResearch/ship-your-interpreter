import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.SegEffect
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.Alloc

#derive_case execRetEpilogueSeg chain
  [(0x80004150#64, 0x0a813083#32),
   (0x80004154#64, 0x0a013403#32),
   (0x80004158#64, 0x09813483#32),
   (0x8000415c#64, 0x09013903#32),
   (0x80004160#64, 0x08813983#32),
   (0x80004164#64, 0x00300513#32),
   (0x80004168#64, 0x0b010113#32)]
    terminator ⟨0x8000416c#64, 0x00008067#32,
      0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0#12⟩

def execRetEpilogueL (esp : BitVec 64) : GRegs := [(2, esp)]

def execRetEpilogueWord (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a+1]?).getD 0, (m[a+2]?).getD 0,
   (m[a+3]?).getD 0, (m[a+4]?).getD 0, (m[a+5]?).getD 0,
   (m[a+6]?).getD 0, (m[a+7]?).getD 0]

def execRetEpilogueLoads (m : Mem) (esp : BitVec 64) : List (List (BitVec 8)) :=
  [execRetEpilogueWord m (esp.toNat + 168),
   execRetEpilogueWord m (esp.toNat + 160),
   execRetEpilogueWord m (esp.toNat + 152),
   execRetEpilogueWord m (esp.toNat + 144),
   execRetEpilogueWord m (esp.toNat + 136)]

theorem execRetEpilogueWord_value (m : Mem) (a : Nat) (value : BitVec 64)
    (h : read64 m a = some value.toNat) :
    bytesVal .ld (execRetEpilogueWord m a) = value := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, _⟩ :=
    read64_bytes m a value.toNat h
  simpa [execRetEpilogueWord, h0, h1, h2, h3, h4, h5, h6, h7, bytesVal] using
    ld_value_eq_read64 m a value.toNat b0 b1 b2 b3 b4 b5 b6 b7
      h h0 h1 h2 h3 h4 h5 h6 h7

private theorem execRetEpilogue_loadFact
    {m : Mem} {L : GRegs} {a : MInstr} (esp : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ esp.toNat) (hhi : esp.toNat + 176 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ esp.toNat) (halign : esp.toNat % 8 = 0)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = esp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 176) (hoff8 : off % 8 = 0) :
    MemFacts m L (execRetEpilogueWord m (esp.toNat + off)) a := by
  have hea : (eaddrM a L).toNat = esp.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  refine ⟨⟨by rw [hea]; omega, by rw [hea]; omega,
    by rw [hea]; right; omega⟩, ?_⟩
  rw [hea]
  simp [LPins8, execRetEpilogueWord]

/-- Inputs to the concrete return suffix. The saved return value remains in memory. -/
structure ExecRetEpiloguePre (esp r v8 v9 v18 v19 : BitVec 64)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004150#64
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  sp : cfg.σ.regs.get? Register.x2 = some esp
  code : Code.Exec_stmtLoaded cfg.σ.mem
  lo : 0x80000000 ≤ esp.toNat
  hi : esp.toNat + 176 ≤ 0x100000000
  win : tohostAddr + 16 ≤ esp.toNat
  align : esp.toNat % 8 = 0
  ret_align : r.toNat % 4 = 0
  saved_ra : read64 cfg.σ.mem (esp.toNat + 168) = some r.toNat
  saved_s0 : read64 cfg.σ.mem (esp.toNat + 160) = some v8.toNat
  saved_s1 : read64 cfg.σ.mem (esp.toNat + 152) = some v9.toNat
  saved_s2 : read64 cfg.σ.mem (esp.toNat + 144) = some v18.toNat
  saved_s3 : read64 cfg.σ.mem (esp.toNat + 136) = some v19.toNat

theorem ExecRetEpiloguePre.facts
    (h : ExecRetEpiloguePre esp r v8 v9 v18 v19 cfg) :
    ChainFacts cfg.σ.mem cfg.σ.mem (execRetEpilogueL esp)
      (execRetEpilogueLoads cfg.σ.mem esp) execRetEpilogueSeg := by
  have hra := execRetEpilogueWord_value _ _ _ h.saved_ra
  unfold execRetEpilogueSeg ChainFacts
  chain_facts h.code with "Vsa.Sim.Code.exec_stmt_at_"
  · exact execRetEpilogue_loadFact esp 168 h.lo h.hi h.win h.align
      (by decide) rfl (by decide) (by decide) (by decide)
  · exact execRetEpilogue_loadFact esp 160 h.lo h.hi h.win h.align
      (by decide) rfl (by decide) (by decide) (by decide)
  · exact execRetEpilogue_loadFact esp 152 h.lo h.hi h.win h.align
      (by decide) rfl (by decide) (by decide) (by decide)
  · exact execRetEpilogue_loadFact esp 144 h.lo h.hi h.win h.align
      (by decide) rfl (by decide) (by decide) (by decide)
  · exact execRetEpilogue_loadFact esp 136 h.lo h.hi h.win h.align
      (by decide) rfl (by decide) (by decide) (by decide)
  · simpa [TermFactsO, TermFactsT, execRetEpilogueL, execRetEpilogueLoads,
      runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
      hra, ret_tgt r h.ret_align] using h.ret_align

/-- The suffix writes only the restored registers and the status register. -/
def execRetEpilogueKeep (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x2 || R == Register.x8 ||
    R == Register.x9 || R == Register.x18 || R == Register.x19)

def execRetEpilogueEffect : FrameEffect where
  regs := fun R => execRetEpilogueKeep R = true
  mem := fun _ => True
  output := True

/-- Exact machine endpoint; memory equality carries arbitrary semantic predicates. -/
structure ExecRetEpiloguePost (esp r v8 v9 v18 v19 : BitVec 64)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (BitVec.update r 0 0#1)
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  sp : after.σ.regs.get? Register.x2 = some (esp + 176#64)
  ra : after.σ.regs.get? Register.x1 = some r
  status : after.σ.regs.get? Register.x10 = some 3#64
  s0 : after.σ.regs.get? Register.x8 = some v8
  s1 : after.σ.regs.get? Register.x9 = some v9
  s2 : after.σ.regs.get? Register.x18 = some v18
  s3 : after.σ.regs.get? Register.x19 = some v19
  mem : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput

theorem execRetEpilogue_run
    (h : ExecRetEpiloguePre esp r v8 v9 v18 v19 cfg) :
    ∃ cfg', ExecRetEpiloguePost esp r v8 v9 v18 v19 cfg cfg' ∧
      FramedSteps execRetEpilogueEffect cfg cfg' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  have hfacts := h.facts
  have hkeys : KeysOK (keysG (execRetEpilogueL esp)) := by
    change KeysOK [2]; decide
  have hwf : ChainOK 0x80004150#64 (keysG (execRetEpilogueL esp))
      execRetEpilogueSeg := by change ChainOK 0x80004150#64 [2] _; decide
  obtain ⟨σ', i', hs, hi, hg, hm, ho, hpc, hmi', hregs, hframe⟩ :=
    segEval_sound execRetEpilogueSeg cfg.σ cfg.tick cfg.steps 0x80004150#64 vm
      (execRetEpilogueL esp) (execRetEpilogueLoads cfg.σ.mem esp)
      h.good h.pc hmi ⟨h.sp, trivial⟩ hkeys hfacts hwf h.tick
  have hra := execRetEpilogueWord_value _ _ _ h.saved_ra
  have hs0 := execRetEpilogueWord_value _ _ _ h.saved_s0
  have hs1 := execRetEpilogueWord_value _ _ _ h.saved_s1
  have hs2 := execRetEpilogueWord_value _ _ _ h.saved_s2
  have hs3 := execRetEpilogueWord_value _ _ _ h.saved_s3
  have hmem : σ'.mem = cfg.σ.mem := by
    simpa +ground [execRetEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
      writeLog, wlogM] using hm
  have reg (n : Nat) (v : BitVec 64)
      (hp : lookupG n (evalBlocks execRetEpilogueSeg (SegEvalState.init
        (execRetEpilogueL esp) (execRetEpilogueLoads cfg.σ.mem esp))).regs = some v) :
      gprGet σ' n = some v := gholds_lookup _ hregs hp
  have selected : GHolds σ' [(2, esp + 176#64), (1, r), (10, 3#64),
      (8, v8), (9, v9), (18, v18), (19, v19)] := by
    repeat' apply And.intro
    all_goals first
      | trivial
      | apply reg
        simp [execRetEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
          runGM, stepGM, stepLdsM, wvalM, srcVal, execRetEpilogueL,
          execRetEpilogueLoads, lookupG, eraseG, mkLine, decodeM,
          hra, hs0, hs1, hs2, hs3,
          show (sign_extend (m := 64) (176#12) : BitVec 64) = 176#64 by decide,
          show (sign_extend (m := 64) (3#12) : BitVec 64) = 3#64 by decide]
  have hpc' : σ'.regs.get? Register.PC = some (BitVec.update r 0 0#1) := by
    rw [hpc]
    simp [execRetEpilogueSeg, evalBlocksPC, chainEndPC,
      endPCB, tgtPCT, SegEvalState.init, runGM, stepGM, stepLdsM, wvalM, srcVal,
      execRetEpilogueL, execRetEpilogueLoads, lookupG, eraseG, mkLine, decodeM, hra,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide]
  let cfg' : Config := ⟨σ', i', cfg.steps + evalBlocksFuel execRetEpilogueSeg⟩
  obtain ⟨hsp, hr, ha0, h8, h9, h18, h19, _⟩ := selected
  refine ⟨cfg', ⟨hg, hi, hpc', hmi', hsp, hr, ha0, h8, h9, h18, h19,
    hmem, ho⟩, hs, ?_⟩
  exact
    { regs := ⟨frame_of_wrChain_avoids
        (by decide : ∀ rr ∈ noiseRegs, execRetEpilogueKeep rr = false)
        (by decide : WrChainAvoids execRetEpilogueKeep execRetEpilogueSeg) hframe⟩
      mem := fun a _ => congrArg (fun m : Mem => m[a]?) hmem
      output := fun _ => ho }

theorem ExecRetEpiloguePost.carry
    (h : ExecRetEpiloguePost esp r v8 v9 v18 v19 before after)
    (Q : Mem → Prop) (hq : Q before.σ.mem) : Q after.σ.mem := by
  rw [h.mem]
  exact hq

#print axioms ExecRetEpiloguePre.facts
#print axioms execRetEpilogue_run

end Vsa.Sim
