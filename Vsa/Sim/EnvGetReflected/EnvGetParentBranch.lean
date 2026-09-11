import Vsa.Sim.EnvGetReflected.EnvGetSegments
import Vsa.Sim.WordLoadData
import Vsa.Sim.Code.Env_get

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- Parent descent changes only s4 among saved registers and preserves ra. -/
def parentKeep (R : Register) : Bool :=
  (Vsa.Alloc.AbiPreserved R && R != Register.x20) || R == Register.x1

theorem parentKeep_noise : ∀ R ∈ noiseRegs, parentKeep R = false := by decide

def parentSeg (present : Bool) : List BBlock :=
  if present then env_getX2cc4TSeg else env_getX2cc4FSeg

def parentPC (present : Bool) : BitVec 64 :=
  if present then 0x80002c40#64 else 0x80002ccc#64

/-- The loaded parent controls the generated branch at the same endpoint. -/
structure ParentResult (parent : BitVec 64) (present : Bool)
    (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (parentPC present)
  env : after.σ.regs.get? Register.x20 = some parent
  mem : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, parentKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  present_iff : present = true ↔ parent ≠ 0#64

/-- Execute the reflected parent load and both branch polarities.
Frame ownership supplies the header read and RAM geometry. -/
theorem parent_branch (env parent : BitVec 64) (c : Config)
    (hgood : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002cc4#64)
    (htick : c.tick < 2)
    (henv : c.σ.regs.get? Register.x20 = some env)
    (hloaded : Vsa.Sim.Code.Env_getLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ env.toNat + 24)
    (hhi : env.toNat + 32 ≤ 0x100000000)
    (hht : env.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 24)
    (hread : read64 c.σ.mem (env.toNat + 24) = some parent.toNat) :
    ∃ after present, ParentResult parent present c after := by
  let L : GRegs := [(20, env)]
  let load := mkLine 0x80002cc4#64 0x018a3a03#32
  have hea : (eaddrM load L).toNat = env.toNat + 24 := by
    change (env + sign_extend (m := 64) (0x018#12)).toNat = _
    rw [show sign_extend (m := 64) (0x018#12) = 24#64 from by decide,
      BitVec.toNat_add]
    change (env.toNat + 24) % 2^64 = env.toNat + 24
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨bs, hword⟩ := wordLoadFacts_of_read64 c.σ.mem L load parent
    (by rfl) (by rw [hea]; exact hlo) (by rw [hea]; exact hhi)
    (by rw [hea]; exact hht) (by rw [hea]; exact hread)
  let present := parent != 0#64
  have hbranch : (bytesVal .ld bs != 0#64) = present := by rw [hword.value]
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [bs] (parentSeg present) := by
    generalize he : present = b
    cases b <;> chain_facts hloaded with "Vsa.Sim.Code.env_get_at_"
    all_goals first | exact hword.facts | exact hbranch.trans he
  have hmemLog : writeLog c.σ.mem
      (evalBlocks (parentSeg present) (SegEvalState.init L [bs])).log = c.σ.mem := by
    generalize present = b
    cases b <;> rfl
  have hpcEval : evalBlocksPC 0x80002cc4#64
      (SegEvalState.init L [bs]) (parentSeg present) = parentPC present := by
    generalize present = b
    cases b <;> rfl
  have hproj : GProjects
      (evalBlocks (parentSeg present) (SegEvalState.init L [bs])).regs [(20, parent)] := by
    generalize present = b
    cases b <;> refine ⟨?_, trivial⟩
    all_goals change some (bytesVal .ld bs) = some parent
    all_goals rw [hword.value]
  have hL : GHolds c.σ L := ⟨by simpa [gprGet] using henv, trivial⟩
  obtain ⟨vm, hvm⟩ := hgood.minstret
  obtain ⟨after, h⟩ := segEval_selected_framed (parentSeg present) L [bs]
    0x80002cc4#64 vm (fun _ => False) parentKeep [(20, parent)] c
    hgood hpc hvm hL (by show KeysOK [20]; decide) hfacts
    (by generalize present = b; cases b <;> show ChainOK 0x80002cc4#64 [20] _ <;> decide)
    htick (fun _ _ => by rw [hmemLog]) parentKeep_noise
    (by generalize present = b; cases b <;> decide) hproj
  refine ⟨after, present,
    { steps := h.steps
      good := h.good
      tick := h.tick
      pc := hpcEval ▸ h.pc
      env := ?_
      mem := h.mem.trans hmemLog
      output := h.output
      frame := h.reg_frame
      present_iff := ?_ }⟩
  · change gprGet after.σ 20 = _
    exact gholds_lookup [(20, parent)] h.selected_regs rfl
  · simp [present, bne]

#print axioms parentKeep_noise
#print axioms parent_branch

end Vsa.Sim.EnvGetReflected
