import Vsa.Sim.EnvGetReflected.EnvGetSegments
import Vsa.Sim.HelperCall
import Vsa.Sim.Code.Env_get

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- The count test changes s2 and preserves the remaining saved registers. -/
def countKeep (R : Register) : Bool :=
  (Vsa.Alloc.AbiPreserved R && R != Register.x18) || R == Register.x1

theorem countKeep_noise : ∀ R ∈ noiseRegs, countKeep R = false := by decide

def countSeg (empty : Bool) : List BBlock :=
  if empty then env_getX2c40TSeg else env_getX2c40FSeg

def countPC (empty : Bool) : BitVec 64 :=
  if empty then 0x80002cc4#64 else 0x80002c48#64

/-- The actual count load determines the outer frame's next branch. -/
structure CountResult (count : Nat) (empty : Bool) (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (countPC empty)
  count2 : after.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 count)
  mem : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, countKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  empty_iff : empty = true ↔ count = 0

/-- Execute the generated signed count load and test.
Frame ownership supplies the signed length bound and the header read. -/
theorem count_head (env : BitVec 64) (count : Nat) (c : Config)
    (hgood : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c40#64)
    (htick : c.tick < 2)
    (henv : c.σ.regs.get? Register.x20 = some env)
    (hloaded : Vsa.Sim.Code.Env_getLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ env.toNat)
    (hhi : env.toNat + 4 ≤ 0x100000000)
    (hht : env.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat)
    (hread : read32 c.σ.mem env.toNat = some count)
    (hcount : count < 2^31) :
    ∃ after empty, CountResult count empty c after := by
  let L : GRegs := [(20, env)]
  let bs := wordLds4 c.σ.mem env.toNat
  let empty := decide (count = 0)
  have hvalue : bytesVal .lw bs = BitVec.ofNat 64 count :=
    bytesVal_lw_wordLds4 c.σ.mem env.toNat count hcount hread
  have hguard : guardB bop.BGE (0#64) (bytesVal .lw bs) = empty := by
    rw [hvalue]
    by_cases hz : count = 0
    · subst count
      exact blez_guard_zero
    · have hpos : 0 < count := Nat.pos_of_ne_zero hz
      simpa [empty, hz, guardB] using blez_guard_pos count hpos (by omega)
  have hload : MemFacts c.σ.mem L bs (mkLine 0x80002c40#64 0x000a2903#32) := by
    change (0x80000000 ≤ (env + sign_extend (m := 64) (0#12)).toNat ∧
      (env + sign_extend (m := 64) (0#12)).toNat + 4 ≤ 0x100000000 ∧
      ((env + sign_extend (m := 64) (0#12)).toNat + 4 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (env + sign_extend (m := 64) (0#12)).toNat)) ∧
      LPins4 c.σ.mem (env + sign_extend (m := 64) (0#12)).toNat bs
    rw [sext_zero, BitVec.add_zero]
    exact ⟨⟨hlo, hhi, hht⟩, rfl, rfl, rfl, rfl⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [bs] (countSeg empty) := by
    generalize he : empty = b
    cases b <;> chain_facts hloaded with "Vsa.Sim.Code.env_get_at_"
    all_goals first | exact hload | exact hguard.trans he
  have hmemLog : writeLog c.σ.mem
      (evalBlocks (countSeg empty) (SegEvalState.init L [bs])).log = c.σ.mem := by
    generalize empty = b
    cases b <;> rfl
  have hpcEval : evalBlocksPC 0x80002c40#64
      (SegEvalState.init L [bs]) (countSeg empty) = countPC empty := by
    generalize empty = b
    cases b <;> rfl
  have hproj : GProjects
      (evalBlocks (countSeg empty) (SegEvalState.init L [bs])).regs
      [(18, BitVec.ofNat 64 count)] := by
    generalize empty = b
    cases b <;> refine ⟨?_, trivial⟩
    all_goals change some (bytesVal .lw bs) = some (BitVec.ofNat 64 count)
    all_goals rw [hvalue]
  have hL : GHolds c.σ L := ⟨by simpa [gprGet] using henv, trivial⟩
  obtain ⟨vm, hvm⟩ := hgood.minstret
  obtain ⟨after, h⟩ := segEval_selected_framed (countSeg empty) L [bs]
    0x80002c40#64 vm (fun _ => False) countKeep [(18, BitVec.ofNat 64 count)] c
    hgood hpc hvm hL (by show KeysOK [20]; decide) hfacts
    (by generalize empty = b; cases b <;> show ChainOK 0x80002c40#64 [20] _ <;> decide)
    htick (fun _ _ => by rw [hmemLog]) countKeep_noise
    (by generalize empty = b; cases b <;> decide) hproj
  refine ⟨after, empty,
    { steps := h.steps
      good := h.good
      tick := h.tick
      pc := hpcEval ▸ h.pc
      count2 := ?_
      mem := h.mem.trans hmemLog
      output := h.output
      frame := h.reg_frame
      empty_iff := by simp [empty] }⟩
  change gprGet after.σ 18 = _
  exact gholds_lookup [(18, BitVec.ofNat 64 count)] h.selected_regs rfl

#print axioms countKeep_noise
#print axioms count_head

end Vsa.Sim.EnvGetReflected
