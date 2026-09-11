import Vsa.Sim.EqCaseEntry
import Vsa.Sim.rows.EvalEqNeRow
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.FrameMeta

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim

#derive_case eqBoolArgSeg chain [(0x80003724#64, 0x00048513#32)]
#derive_case neBoolArgSeg chain [(0x80003774#64, 0x00048513#32)]

namespace EqNeOp

def boolArgSeg : EqNeOp → List BBlock
  | .eq => eqBoolArgSeg
  | .ne => neBoolArgSeg

def boolArgPC : EqNeOp → BitVec 64
  | .eq => 0x80003724#64
  | .ne => 0x80003774#64

def boolJalPC : EqNeOp → BitVec 64
  | .eq => 0x80003728#64
  | .ne => 0x80003778#64

def boolLink : EqNeOp → BitVec 64
  | .eq => 0x8000372c#64
  | .ne => 0x8000377c#64

def boolImm : EqNeOp → BitVec 21
  | .eq => 0x1ff0d0#21
  | .ne => 0x1ff080#21

def boolWord (op : EqNeOp) (w : BitVec 64) : BitVec 64 :=
  match op with
  | .eq => w + sign_extend (m := 64) (0x000#12)
  | .ne => zero_extend (m := 64) (bool_to_bit (zopz0zI_u w
      (sign_extend (m := 64) (0x001#12))))

/-- The existing shuffle sites compute either the equality bit or its negation. -/
theorem boolFirstSite (op : EqNeOp) : EqNeFirstSite op.returnPC op.boolWord := by
  cases op with
  | eq => exact site_80003720_ee
  | ne => exact site_80003770_ee

/-- The boxed word represents the selected source comparison. -/
theorem boolWord_result (op : EqNeOp) (vl vr : Value) :
    (op.boolWord (cond (vl.equal vr) 1#64 0#64) != 0#64) = op.result vl vr := by
  cases op <;> cases h : vl.equal vr <;>
    simp only [boolWord, result, h, cond_true, cond_false] <;> decide

/-- Actual entry to boolean boxing after the comparison result is shuffled. -/
structure BoolCall (op : EqNeOp) (base dst word : BitVec 64)
    (before after : Config) : Prop where
  run : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x800027f8#64
  link : after.σ.regs.get? Register.x1 = some op.boolLink
  result : after.σ.regs.get? Register.x10 = some dst
  value : after.σ.regs.get? Register.x11 = some (op.boolWord word)
  destination : after.σ.regs.get? Register.x9 = some dst
  stack : after.σ.regs.get? Register.x2 = some base
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the result shuffle and reflected argument setup, then call value_bool. -/
theorem boolCall (op : EqNeOp) (base dst word : BitVec 64) (before : Config)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some op.returnPC)
    (value : before.σ.regs.get? Register.x10 = some word)
    (destination : before.σ.regs.get? Register.x9 = some dst)
    (stack : before.σ.regs.get? Register.x2 = some base)
    (code : Eval_exprLoaded before.σ.mem) :
    ∃ after, BoolCall op base dst word before after := by
  obtain ⟨vm, hvm⟩ := good.minstret
  obtain ⟨s, i, step, tickS, goodS, memS, obs⟩ :=
    op.boolFirstSite before.σ before.tick before.steps op.returnPC vm word
      good pc hvm value code rfl tick
  let middle : Config := ⟨s, i, before.steps + 1⟩
  have frameS := StepFrameOut.of_alu obs
  have pcS : s.regs.get? Register.PC = some op.boolArgPC := by
    have h := obs_alu_pc obs
    have next : BitVec.addInt op.returnPC 4 = op.boolArgPC := by cases op <;> decide
    exact next ▸ h
  have valueS : s.regs.get? Register.x11 = some (op.boolWord word) :=
    obs_alu_rd obs (by decide) (by decide) (by decide) (by decide) (by decide)
  have dstS := (frameS.frame Register.x9 (by decide)).trans destination
  have spS := (frameS.frame Register.x2 (by decide)).trans stack
  let inputs : GRegs := [(9, dst), (11, op.boolWord word), (2, base)]
  have pins : GHolds middle.σ inputs := ⟨dstS, valueS, spS, trivial⟩
  have loaded : Eval_exprLoaded middle.σ.mem := memS.symm ▸ code
  have facts : ChainFacts middle.σ.mem middle.σ.mem inputs [] op.boolArgSeg := by
    cases op <;> chain_facts loaded with "Vsa.Sim.Code.eval_expr_at_"
  have emptyLog : writeLog middle.σ.mem
      (evalBlocks op.boolArgSeg (SegEvalState.init inputs [])).log = middle.σ.mem := by
    cases op <;> rfl
  have keys : keysG (evalBlocks op.boolArgSeg (SegEvalState.init inputs [])).regs =
      [10, 9, 11, 2] := by cases op <;> rfl
  obtain ⟨after, call⟩ := bridgeOfSegFull op.boolArgSeg inputs [] op.boolArgPC
    0x800027f8#64 op.boolLink middle goodS pcS goodS.minstret tickS pins
    (by change KeysOK [9, 11, 2]; decide) facts
    (by cases op <;> change ChainOK _ [9, 11, 2] _ <;> decide)
    (by rw [keys]; decide)
    (by change ∀ n ∈ keysG _, n ≠ 1; rw [keys]; decide)
    (by
      intro current hg ht hp hmi hm _
      have memory : current.σ.mem = middle.σ.mem := hm.trans emptyLog
      have pcJ : current.σ.regs.get? Register.PC = some op.boolJalPC := by
        have target : evalBlocksPC op.boolArgPC (SegEvalState.init inputs []) op.boolArgSeg =
            op.boolJalPC := by cases op <;> rfl
        exact target ▸ hp
      obtain ⟨vmi, hvmi⟩ := hmi
      have site : EqNeJalVboolSite op.boolJalPC op.boolImm := by
        cases op with
        | eq => exact site_80003728_ee
        | ne => exact site_80003778_ee
      obtain ⟨s', i', hs, hi, hgood, hmem, hobs⟩ :=
        site current.σ current.tick current.steps op.boolJalPC vmi
          hg pcJ hvmi (memory.symm ▸ loaded) rfl ht
      have link : BitVec.addInt op.boolJalPC 4 = op.boolLink := by cases op <;> decide
      rw [link] at hobs
      exact ⟨⟨s', i', current.steps + 1⟩,
        jalCallFacts_of_obs hs hi hgood hmem hobs (by cases op <;> decide)⟩)
  have result : after.σ.regs.get? Register.x10 = some dst := by
    change gprGet after.σ 10 = some dst
    apply gholds_lookup _ call.registers
    cases op <;> change some (dst + sign_extend (m := 64) (0#12)) = some dst <;>
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide,
        BitVec.add_zero]
  have payload : after.σ.regs.get? Register.x11 = some (op.boolWord word) := by
    change gprGet after.σ 11 = some (op.boolWord word)
    apply gholds_lookup _ call.registers
    cases op <;> rfl
  have frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R := by
    intro R hR
    have suffix := call.frame R (noise_ne_abi hR)
      (wrChain_ne_abi (by cases op <;> decide) hR)
      (abiPreserved_ne hR (by decide))
    exact suffix.trans (frameS.frame R (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact abiPreserved_ne hR (by decide)
      · exact noise_ne_abi hR r hr))
  exact ⟨after,
    { run := (Steps.single step).trans call.run
      good := call.good, tick := call.tick, pc := call.pc, link := call.ra
      result := result, value := payload
      destination := (frame Register.x9 (by decide)).trans destination
      stack := (frame Register.x2 (by decide)).trans stack
      minstret := call.minstret
      memory := (call.mem.trans emptyLog).trans memS
      output := call.output.trans frameS.out
      frame := frame }⟩

#print axioms boolFirstSite
#print axioms boolWord_result
#print axioms boolCall

end EqNeOp
end Vsa.Sim
