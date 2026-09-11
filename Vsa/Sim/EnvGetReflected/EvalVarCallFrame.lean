import Vsa.Sim.EnvGetReflected.EnvGetCallFrame
import Vsa.Sim.EvalVarSim
import Vsa.Sim.WordLoadData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/- The generated variable-call prefix, also present as OutputAliasLoaded.traceSeg015. -/
#derive_case varCallSeg chain
  [(0x80003434#64, 0x00863583#32),
   (0x80003438#64, 0x00068513#32),
   (0x8000343c#64, 0x0f010613#32)]

def varCallInput (expr env sp : BitVec 64) : GRegs :=
  [(12, expr), (13, env), (2, sp)]

/-- Retain the complete reflected register frame at the actual lookup call. -/
theorem var_call_framed (expr env sp : BitVec 64) (bs : List (BitVec 8))
    (c : Config) (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80003434#64)
    (htick : c.tick < 2) (hL : GHolds c.σ (varCallInput expr env sp))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (varCallInput expr env sp) [bs] varCallSeg)
    (hloaded : Code.Eval_exprLoaded c.σ.mem) :
    ∃ after, SegCallFacts varCallSeg (varCallInput expr env sp) [bs]
      0x80002c10#64 0x80003444#64 c after := by
  have hmemLog : writeLog c.σ.mem (evalBlocks varCallSeg
      (SegEvalState.init (varCallInput expr env sp) [bs])).log = c.σ.mem := rfl
  have hkeys : keysG (evalBlocks varCallSeg
      (SegEvalState.init (varCallInput expr env sp) [bs])).regs = [12, 10, 11, 13, 2] := rfl
  apply bridgeOfSegFull varCallSeg (varCallInput expr env sp) [bs]
    0x80003434#64 0x80002c10#64 0x80003444#64 c hG hpc hG.minstret htick hL
    (by show KeysOK [12, 13, 2]; decide) hfacts
    (by show ChainOK 0x80003434#64 [12, 13, 2] varCallSeg; decide)
    (by rw [hkeys]; decide)
    (by show ∀ n ∈ keysG _, n ≠ 1; rw [hkeys]; decide)
  intro middle hGm htm hpcm hmim hmemm _
  obtain ⟨σ, i, u⟩ := middle
  obtain ⟨vm, hvm⟩ := hmim
  have hpcEval : evalBlocksPC 0x80003434#64
      (SegEvalState.init (varCallInput expr env sp) [bs]) varCallSeg = 0x80003440#64 := rfl
  have hloaded' : Code.Eval_exprLoaded σ.mem := by
    change Code.Eval_exprLoaded (⟨σ, i, u⟩ : Config).σ.mem
    rw [hmemm, hmemLog]
    exact hloaded
  obtain ⟨σ', i', hs, hi, hg, hm, ho⟩ :=
    site_80003440_var σ i u 0x80003440#64 vm hGm
      (hpcEval ▸ hpcm) hvm hloaded' rfl (by decide) htm
  have hlink : BitVec.addInt 0x80003440#64 4 = (0x80003444#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at ho
  exact ⟨⟨σ', i', u + 1⟩, jalCallFacts_of_obs hs hi hg hm ho
    (by apply BitVec.eq_of_toNat_eq; decide)⟩

/-- The actual name-field read supplies the prefix, with no byte-presence oracle. -/
theorem var_call_read (m : Mem) (expr env sp name : BitVec 64)
    (hloaded : Code.Eval_exprLoaded m)
    (hlo : 0x80000000 ≤ expr.toNat + 8)
    (hhi : expr.toNat + 16 ≤ 0x100000000)
    (hhtif : expr.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ expr.toNat + 8)
    (hread : read64 m (expr.toNat + 8) = some name.toNat) :
    ∃ bs, WordLoadFacts m (varCallInput expr env sp)
      (mkLine 0x80003434#64 0x00863583#32) name bs ∧
      ChainFacts m m (varCallInput expr env sp) [bs] varCallSeg := by
  have hea : (eaddrM (mkLine 0x80003434#64 0x00863583#32)
      (varCallInput expr env sp)).toNat = expr.toNat + 8 :=
    off_ed_08 expr (by omega)
  obtain ⟨bs, hw⟩ := wordLoadFacts_of_read64 m (varCallInput expr env sp)
    (mkLine 0x80003434#64 0x00863583#32) name (by rfl)
    (by rw [hea]; exact hlo) (by rw [hea]; omega)
    (by rw [hea]; exact hhtif) (by rw [hea]; exact hread)
  refine ⟨bs, hw, ?_⟩
  chain_facts hloaded with "Vsa.Sim.Code.eval_expr_at_"
  exact hw.facts

/-- The prefix's actual name read and execution share one call entry. -/
structure VarCallResult (expr env sp name : BitVec 64) (bs : List (BitVec 8))
    (before after : Config) : Prop extends
    SegCallFacts varCallSeg (varCallInput expr env sp) [bs]
      0x80002c10#64 0x80003444#64 before after where
  nameValue : bytesVal .ld bs = name

def varCallerKeep (R : Register) : Bool :=
  kept R || [Register.x8, .x9, .x18, .x19, .x20, .x21].contains R

theorem VarCallResult.caller
    {expr env sp name : BitVec 64} {bs : List (BitVec 8)} {before after : Config}
    (h : VarCallResult expr env sp name bs before after) :
    ∀ R, varCallerKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R := by
  intro R hR
  exact h.frame R
    (noise_avoids (by decide : ∀ R ∈ noiseRegs, varCallerKeep R = false) hR)
    (wrChain_avoids (by decide : WrChainAvoids varCallerKeep varCallSeg) hR)
    (regAvoids_ne hR (by decide))

theorem VarCallResult.args
    {expr env sp name : BitVec 64} {bs : List (BitVec 8)} {before after : Config}
    (h : VarCallResult expr env sp name bs before after) :
    GHolds after.σ [(10, env), (11, name), (12, sp + 240#64), (2, sp)] := by
  have hp : GProjects (evalBlocks varCallSeg
      (SegEvalState.init (varCallInput expr env sp) [bs])).regs
      [(10, env), (11, name), (12, sp + 240#64), (2, sp)] := by
    change some (env + sign_extend (m := 64) (0#12)) = some env ∧
      some (bytesVal .ld bs) = some name ∧
      some (sp + sign_extend (m := 64) (0x0f0#12)) = some (sp + 240#64) ∧
      some sp = some sp ∧ True
    simp only [h.nameValue,
      show sign_extend (m := 64) (0#12) = 0#64 from by decide,
      show sign_extend (m := 64) (0x0f0#12) = 240#64 from by decide,
      BitVec.add_zero, and_true]
  exact gholds_selected hp h.registers

theorem VarCallResult.memory
    {expr env sp name : BitVec 64} {bs : List (BitVec 8)} {before after : Config}
    (h : VarCallResult expr env sp name bs before after) :
    after.σ.mem = before.σ.mem := h.mem

/-- Execute the prefix from its represented name field and reached registers. -/
theorem var_call (expr env sp name : BitVec 64) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80003434#64)
    (htick : c.tick < 2) (hL : GHolds c.σ (varCallInput expr env sp))
    (hloaded : Code.Eval_exprLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ expr.toNat + 8)
    (hhi : expr.toNat + 16 ≤ 0x100000000)
    (hhtif : expr.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ expr.toNat + 8)
    (hread : read64 c.σ.mem (expr.toNat + 8) = some name.toNat) :
    ∃ bs after, VarCallResult expr env sp name bs c after := by
  obtain ⟨bs, hw, hf⟩ := var_call_read c.σ.mem expr env sp name hloaded hlo hhi hhtif hread
  obtain ⟨after, hc⟩ := var_call_framed expr env sp bs c hG hpc htick hL hf hloaded
  exact ⟨bs, after, { hc with nameValue := hw.value }⟩

#print axioms var_call_framed
#print axioms var_call_read
#print axioms VarCallResult.caller
#print axioms VarCallResult.args
#print axioms VarCallResult.memory
#print axioms var_call

end Vsa.Sim.EnvGetReflected
