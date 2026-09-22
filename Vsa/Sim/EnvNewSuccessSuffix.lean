import Vsa.Sim.ExecRetEpilogue
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.WriteLogNF

/-! The successful env_new suffix, starting at the actual malloc return.
No allocation-success, metadata-invariant, or capacity theorem is claimed here. -/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

#derive_case envNewSuccessSeg chain
  [] terminator ⟨0x80002a14#64, 0x02050263#32,
    0x63#8, 0x02#8, 0x05#8, 0x02#8,
    .br bop.BEQ false, 10, 0, 0x024#13, 0#21, 0#12⟩ ;;
  [(0x80002a18#64, 0x00813083#32),
   (0x80002a1c#64, 0x00853c23#32),
   (0x80002a20#64, 0x00013403#32),
   (0x80002a24#64, 0x00053023#32),
   (0x80002a28#64, 0x00053423#32),
   (0x80002a2c#64, 0x00053823#32),
   (0x80002a30#64, 0x01010113#32)]
  terminator ⟨0x80002a34#64, 0x00008067#32,
    0x67#8, 0x80#8, 0x00#8, 0x00#8,
    .jr, 1, 0, 0#13, 0#21, 0#12⟩

def envNewSuccessL (esp p par : BitVec 64) : GRegs :=
  [(2, esp), (10, p), (8, par)]

def envNewParentMem (m : Mem) (p par : BitVec 64) : Mem :=
  applyW m (p.toNat + 24, 8, par)

def envNewSuccessLoads (m : Mem) (esp p par : BitVec 64) :
    List (List (BitVec 8)) :=
  [execRetEpilogueWord m (esp.toNat + 8),
   execRetEpilogueWord (envNewParentMem m p par) esp.toNat]

def envNewSuccessLog (p par : BitVec 64) : List WEntry :=
  [(p.toNat + 24, 8, par), (p.toNat, 8, 0#64),
   (p.toNat + 8, 8, 0#64), (p.toNat + 16, 8, 0#64)]

/-- Caller frame at the already lowered stack pointer. -/
structure EnvNewCallerGeom (esp r : BitVec 64) : Prop where
  lo : 0x80000000 ≤ esp.toNat
  hi : esp.toNat + 16 ≤ 0x100000000
  win : tohostAddr + 16 ≤ esp.toNat
  align : esp.toNat % 8 = 0
  ret_align : r.toNat % 4 = 0

/-- Geometry of this returned pointer, independently of allocator internals. -/
structure EnvNewFreshGeom (esp p : BitVec 64) : Prop where
  nonzero : p ≠ 0#64
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + 32 ≤ 0x100000000
  win : tohostAddr + 16 ≤ p.toNat
  align : p.toNat % 8 = 0
  stack_disjoint : p.toNat + 32 ≤ esp.toNat ∨ esp.toNat + 16 ≤ p.toNat

/-- Named facts at the actual successful malloc return. -/
structure EnvNewSuccessPre (esp p par r savedS0 : BitVec 64)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80002a14#64
  sp : cfg.σ.regs.get? Register.x2 = some esp
  result : cfg.σ.regs.get? Register.x10 = some p
  parent : cfg.σ.regs.get? Register.x8 = some par
  code : Code.Env_newLoaded cfg.σ.mem
  caller : EnvNewCallerGeom esp r
  fresh : EnvNewFreshGeom esp p
  saved_ra : read64 cfg.σ.mem (esp.toNat + 8) = some r.toNat
  saved_s0 : read64 cfg.σ.mem esp.toNat = some savedS0.toNat

private theorem envNew_loadFact {m : Mem} {L : GRegs} {a : MInstr}
    (base : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ base.toNat)
    (hhi : base.toNat + 16 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ base.toNat)
    (halign : base.toNat % 8 = 0)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = base)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 16) (hoff8 : off % 8 = 0) :
    MemFacts m L (execRetEpilogueWord m (base.toNat + off)) a := by
  have hea : (eaddrM a L).toNat = base.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  refine ⟨⟨by rw [hea]; omega, by rw [hea]; omega,
    by rw [hea]; right; omega⟩, ?_⟩
  rw [hea]
  simp [LPins8, execRetEpilogueWord]

private theorem envNew_storeFact {m : Mem} {L : GRegs} {a : MInstr}
    {bs : List (BitVec 8)} (p : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ p.toNat) (hhi : p.toNat + 32 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ p.toNat) (halign : p.toNat % 8 = 0)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = p)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 32) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = p.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  exact ⟨by rw [hea]; omega, by rw [hea]; omega,
    by rw [hea]; omega, by rw [hea]; omega⟩

theorem EnvNewSuccessPre.saved_s0_after_parent
    (h : EnvNewSuccessPre esp p par r savedS0 cfg) :
    read64 (envNewParentMem cfg.σ.mem p par) esp.toNat = some savedS0.toNat := by
  unfold envNewParentMem
  change read64 (writeMap8 cfg.σ.mem (p.toNat + 24) (sdData_val par))
    esp.toNat = some savedS0.toNat
  rw [read64_writeMap8_disjoint _ _ _ _ (by have := h.fresh.stack_disjoint; omega)]
  exact h.saved_s0

theorem EnvNewSuccessPre.facts
    (h : EnvNewSuccessPre esp p par r savedS0 cfg) :
    ChainFacts cfg.σ.mem cfg.σ.mem (envNewSuccessL esp p par)
      (envNewSuccessLoads cfg.σ.mem esp p par) envNewSuccessSeg := by
  have hret : BitVec.update r 0 0#1 = r := by
    simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      BitVec.add_zero] using ret_tgt r h.caller.ret_align
  have hra := execRetEpilogueWord_value _ _ _ h.saved_ra
  have hp24 : (p + sign_extend (m := 64) (24#12)).toNat = p.toNat + 24 :=
    off24_addr p (by have := h.fresh.hi; omega)
  unfold envNewSuccessSeg ChainFacts
  chain_facts h.code with "Vsa.Sim.Code.env_new_at_"
  · simpa +ground [guardB, envNewSuccessL, srcVal, lookupG, runGM] using
      (beq_eq_false_iff_ne.mpr h.fresh.nonzero)
  · exact envNew_loadFact esp 8 h.caller.lo h.caller.hi h.caller.win
      h.caller.align (by decide) rfl (by decide) (by decide) (by decide)
  · exact envNew_storeFact p 24 h.fresh.lo h.fresh.hi h.fresh.win
      h.fresh.align (by decide) rfl (by decide) (by decide) (by decide)
  · change MemFacts
      (applyW cfg.σ.mem ((p + sign_extend (m := 64) (24#12)).toNat, 8, par))
      _ (execRetEpilogueWord (envNewParentMem cfg.σ.mem p par) esp.toNat) _
    rw [hp24]
    exact envNew_loadFact esp 0 h.caller.lo h.caller.hi h.caller.win
      h.caller.align (by decide) rfl (by decide) (by decide) (by decide)
  · exact envNew_storeFact p 0 h.fresh.lo h.fresh.hi h.fresh.win
      h.fresh.align (by decide) rfl (by decide) (by decide) (by decide)
  · exact envNew_storeFact p 8 h.fresh.lo h.fresh.hi h.fresh.win
      h.fresh.align (by decide) rfl (by decide) (by decide) (by decide)
  · exact envNew_storeFact p 16 h.fresh.lo h.fresh.hi h.fresh.win
      h.fresh.align (by decide) rfl (by decide) (by decide) (by decide)
  · simpa [TermFactsO, TermFactsT, envNewSuccessL, envNewSuccessLoads,
      runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
      hra, hret,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide] using h.caller.ret_align

def envNewSuccessKeep (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x2 || R == Register.x8)

def envNewSuccessEffect (p : BitVec 64) : FrameEffect where
  regs := fun R => envNewSuccessKeep R = true
  mem := fun a => ¬ (p.toNat ≤ a ∧ a < p.toNat + 32)
  output := True

/-- Exact nine-instruction endpoint. The only writes initialize the new frame. -/
structure EnvNewSuccessPost (esp p par r savedS0 : BitVec 64)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some r
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  sp : after.σ.regs.get? Register.x2 = some (esp + 16#64)
  ra : after.σ.regs.get? Register.x1 = some r
  result : after.σ.regs.get? Register.x10 = some p
  s0 : after.σ.regs.get? Register.x8 = some savedS0
  mem : after.σ.mem = writeLog before.σ.mem (envNewSuccessLog p par)
  output : after.σ.sailOutput = before.σ.sailOutput

theorem envNewSuccess_run (h : EnvNewSuccessPre esp p par r savedS0 cfg) :
    ∃ cfg', EnvNewSuccessPost esp p par r savedS0 cfg cfg' ∧
      FramedSteps (envNewSuccessEffect p) cfg cfg' := by
  obtain ⟨vm, hmi⟩ := h.good.minstret
  obtain ⟨σ', i', hs, hi, hg, hm, ho, hpc, hmi', hregs, hframe⟩ :=
    segEval_sound envNewSuccessSeg cfg.σ cfg.tick cfg.steps 0x80002a14#64 vm
      (envNewSuccessL esp p par) (envNewSuccessLoads cfg.σ.mem esp p par)
      h.good h.pc hmi ⟨h.sp, h.result, h.parent, trivial⟩
      (by change KeysOK [2, 10, 8]; decide) h.facts
      (by change ChainOK 0x80002a14#64 [2, 10, 8] _; decide) h.tick
  have hret : BitVec.update r 0 0#1 = r := by
    simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      BitVec.add_zero] using ret_tgt r h.caller.ret_align
  have hra := execRetEpilogueWord_value _ _ _ h.saved_ra
  have hs0 := execRetEpilogueWord_value _ _ _ h.saved_s0_after_parent
  have hp0 := off0_addr p
  have hp8 := off8_addr p (by have := h.fresh.hi; omega)
  have hp16 := off16_addr p (by have := h.fresh.hi; omega)
  have hp24 := off24_addr p (by have := h.fresh.hi; omega)
  have hlog : (evalBlocks envNewSuccessSeg (SegEvalState.init
      (envNewSuccessL esp p par) (envNewSuccessLoads cfg.σ.mem esp p par))).log =
      envNewSuccessLog p par := by
    simp [envNewSuccessSeg, evalBlocks, evalBlock, SegEvalState.init,
      envNewSuccessL, envNewSuccessLoads, envNewSuccessLog, wlogM, wentryM, widthOfM,
      runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG,
      mkLine, decodeM, eaddrM, hp0, hp8, hp16, hp24]
  have hmem : σ'.mem = writeLog cfg.σ.mem (envNewSuccessLog p par) := by
    rw [hlog] at hm
    exact hm
  have reg (n : Nat) (v : BitVec 64)
      (hp : lookupG n (evalBlocks envNewSuccessSeg (SegEvalState.init
        (envNewSuccessL esp p par) (envNewSuccessLoads cfg.σ.mem esp p par))).regs =
          some v) : gprGet σ' n = some v := gholds_lookup _ hregs hp
  have selected : GHolds σ' [(2, esp + 16#64), (1, r), (10, p), (8, savedS0)] := by
    repeat' apply And.intro
    all_goals first
      | trivial
      | apply reg
        simp [envNewSuccessSeg, evalBlocks, evalBlock, SegEvalState.init,
          envNewSuccessL, envNewSuccessLoads, runGM, stepGM, stepLdsM,
          ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, hra, hs0,
          show (sign_extend (m := 64) (16#12) : BitVec 64) = 16#64 by decide]
  have hpc' : σ'.regs.get? Register.PC = some r := by
    rw [hpc]
    simp [envNewSuccessSeg, evalBlocksPC, chainEndPC, endPCB, tgtPCT,
      SegEvalState.init, envNewSuccessL, envNewSuccessLoads, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, hra,
      hret,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide]
  let cfg' : Config := ⟨σ', i', cfg.steps + evalBlocksFuel envNewSuccessSeg⟩
  obtain ⟨hsp, hr, hp, h8, _⟩ := selected
  refine ⟨cfg', ⟨hg, hi, hpc', hmi', hsp, hr, hp, h8, hmem, ho⟩, hs, ?_⟩
  exact
    { regs := ⟨frame_of_wrChain_avoids
        (by decide : ∀ rr ∈ noiseRegs, envNewSuccessKeep rr = false)
        (by decide : WrChainAvoids envNewSuccessKeep envNewSuccessSeg) hframe⟩
      mem := fun a ha => by
        change σ'.mem[a]? = cfg.σ.mem[a]?
        rw [hmem]
        apply writeLog_out
        simp only [envNewSuccessLog, OutL, and_true]
        change ¬ (p.toNat ≤ a ∧ a < p.toNat + 32) at ha
        omega
      output := fun _ => ho }

/-- Exact initialized bytes yield the semantic empty frame, for either parent case. -/
theorem EnvNewSuccessPost.frameRepr
    (h : EnvNewSuccessPost esp p par r savedS0 before after)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (parentSpec : Option Vsa.While.Addr)
    (hparent : match parentSpec with
      | none => par = 0#64
      | some pa => φf pa = par.toNat ∧ par ≠ 0#64) :
    FrameRepr after.σ.mem N φf φc p.toNat ⟨parentSpec, []⟩ := by
  have hm : after.σ.mem = writeMap8 (writeMap8 (writeMap8
      (writeMap8 before.σ.mem (p.toNat + 24) (sdData_val par))
      p.toNat (sdData_val 0#64)) (p.toNat + 8) (sdData_val 0#64))
      (p.toNat + 16) (sdData_val 0#64) := by
    simpa [envNewSuccessLog, writeLog, applyW] using h.mem
  refine ⟨?_, ⟨0, ?_, Nat.le_refl 0⟩, ⟨0, 0, ?_, ?_, ?_⟩, ?_⟩
  · change read32 after.σ.mem p.toNat = some 0
    rw [hm, read32_writeMap8_disjoint _ _ _ _ (by omega),
      read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap8_lo,
      sdData_val_zero_toNat]
  · change read32 after.σ.mem (p.toNat + 4) = some 0
    rw [hm, read32_writeMap8_disjoint _ _ _ _ (by omega),
      read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap8_hi,
      sdData_val_zero_toNat]
  · change read64 after.σ.mem (p.toNat + 8) = some 0
    rw [hm, read64_writeMap8_disjoint _ _ _ _ (by omega),
      read64_writeMap8, sdData_val_zero_toNat]
  · change read64 after.σ.mem (p.toNat + 16) = some 0
    rw [hm, read64_writeMap8, sdData_val_zero_toNat]
  · intro i hi
    exact absurd hi (by simp)
  · have hpar : read64 after.σ.mem (p.toNat + 24) = some par.toNat := by
      rw [hm, read64_writeMap8_disjoint _ _ _ _ (by omega),
        read64_writeMap8_disjoint _ _ _ _ (by omega),
        read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
    cases parentSpec with
    | none => simpa [hparent] using hpar
    | some pa =>
      obtain ⟨hlink, hne⟩ := hparent
      refine ⟨by simpa [hlink] using hpar, ?_⟩
      rw [hlink]
      intro hz
      apply hne
      apply BitVec.eq_of_toNat_eq
      simpa using hz

#print axioms EnvNewSuccessPre.facts
#print axioms envNewSuccess_run
#print axioms EnvNewSuccessPost.frameRepr

end Vsa.Sim
