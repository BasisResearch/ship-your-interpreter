import EnvGetPrologueData
import EnvGetLookupTransport
import TransportEnv_getRange
import Vsa.Sim.EnvGetPrologueHead
import Vsa.Sim.MemPresence

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- One prologue execution retains its saved words, caller frame, and exact
spill agreement at the first count head. -/
structure PrologueResult
    (env name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (before after : Config) : Prop where
  steps : Steps before after
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  registers : FrameRegisters env name out r0 (sp0 - 64#64) after
  pc : after.σ.regs.get? Register.PC = some 0x80002c40#64
  saved : PrologueSaved after.σ.mem (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
  outside : ∀ k, OutsideSpill sp0 k → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the non-null entry branch and the generated spill block.
The actual segment results supply both register framing and saved-word reads. -/
theorem prologue_framed
    (env name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (m0 : Mem) (c : Config)
    (hSt : PrologueHeadSt env name out sp0 r0 r8 r9 r18 r19 r20 r21 len pn m0 c)
    (hstrcmp : Code.StrcmpLoaded c.σ.mem) :
    ∃ after, PrologueResult env name out sp0 r0 r8 r9 r18 r19 r20 r21 c after := by
  let L := env_getX2c14L sp0 r19 r20 r21 r0 r8 r9 r18 env name out
  have hL : GHolds c.σ L :=
    ⟨by simpa [gprGet] using hSt.sp,
     by simpa [gprGet] using hSt.cs19,
     by simpa [gprGet] using hSt.cs20,
     by simpa [gprGet] using hSt.cs21,
     by simpa [gprGet] using hSt.ra,
     by simpa [gprGet] using hSt.cs8,
     by simpa [gprGet] using hSt.cs9,
     by simpa [gprGet] using hSt.cs18,
     by simpa [gprGet] using hSt.a0,
     by simpa [gprGet] using hSt.a1,
     by simpa [gprGet] using hSt.a2, trivial⟩
  have hkeys : KeysOK (keysG L) := by
    show KeysOK [2, 19, 20, 21, 1, 8, 9, 18, 10, 11, 12]
    decide
  have hloaded := hSt.loadedG
  have hbranch : ChainFacts c.σ.mem c.σ.mem L [] env_getX2c10FSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_get_at_"
    exact hSt.envNe
  obtain ⟨vm, hvm⟩ := hSt.minstret
  obtain ⟨head, hb⟩ := segment_framed env_getX2c10FSeg
    (by simp [segments]) L [] 0x80002c10#64 vm (fun _ => False) L c
    hSt.good hSt.pc hvm hL hkeys hbranch
    (by show ChainOK 0x80002c10#64 [2, 19, 20, 21, 1, 8, 9, 18, 10, 11, 12] _; decide)
    hSt.tick (fun _ _ => rfl)
    (by simp [env_getX2c10FSeg, evalBlocks, evalBlock, SegEvalState.init,
      GProjects, L, env_getX2c14L, runGM, lookupG])
  have hheadMem : head.σ.mem = c.σ.mem := hb.mem
  have hheadPC : head.σ.regs.get? Register.PC = some 0x80002c14#64 := hb.pc
  have hheadLoaded : Code.Env_getLoaded head.σ.mem := hheadMem.symm ▸ hSt.loadedG
  have hfoot : ∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64) →
      head.σ.mem[k]? = (writeLog head.σ.mem
        (evalBlocks env_getX2c14Seg (SegEvalState.init L [])).log)[k]? := by
    intro k hk
    rw [prologue_log sp0 env name out r0 r8 r9 r18 r19 r20 r21 hSt.spDrop]
    apply Eq.symm
    apply writeLog_out
    simp only [prologueLog, OutL, and_true]
    omega
  let selected : GRegs := [(20, env), (19, name), (21, out), (1, r0), (2, sp0 - 64#64)]
  have hproj : GProjects (evalBlocks env_getX2c14Seg (SegEvalState.init L [])).regs
      selected := by
    change some (env + sign_extend (m := 64) (0x000#12)) = some env ∧
      some (name + sign_extend (m := 64) (0x000#12)) = some name ∧
      some (out + sign_extend (m := 64) (0x000#12)) = some out ∧
      some r0 = some r0 ∧
      some (sp0 + sign_extend (m := 64) (0xfc0#12)) = some (sp0 - 64#64) ∧ True
    simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, sp_sub64, and_true]
  obtain ⟨vmHead, hvmHead⟩ := hb.minstret
  obtain ⟨after, hp⟩ := segment_framed env_getX2c14Seg
    (by simp [segments]) L [] 0x80002c14#64 vmHead
    (fun k => (sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64)
    selected head hb.good hheadPC hvmHead hb.selected_regs hkeys
    (prologue_facts head.σ.mem sp0 env name out r0 r8 r9 r18 r19 r20 r21
      hheadLoaded hSt.spLo hSt.spHi (by have := hSt.spWin; omega) hSt.spAlign hSt.spDrop)
    (by show ChainOK 0x80002c14#64 [2, 19, 20, 21, 1, 8, 9, 18, 10, 11, 12] _; decide)
    hb.tick hfoot hproj
  have houtside : ∀ k, OutsideSpill sp0 k → after.σ.mem[k]? = c.σ.mem[k]? := by
    intro k hk
    exact (hp.outside k hk).symm.trans (congrArg (fun m : Mem => m[k]?) hheadMem)
  have hbase := sp_sub64_toNat sp0 hSt.spDrop
  have hstack := hSt.spWin
  have hG : Code.Env_getLoaded after.σ.mem := Code.env_getLoaded_of_agree_range
    (fun k hlo hhi => houtside k (by
      unfold OutsideSpill
      have htohost : tohostAddr = 0x8001ad00 := rfl
      omega)) hSt.loadedG
  have hS : Code.StrcmpLoaded after.σ.mem := strcmpLoaded_outsideSpill
    (agreeP_of_prologue houtside) (by
      intro k hlo hhi
      unfold OutsideSpill
      have htohost : tohostAddr = 0x8001ad00 := rfl
      omega) hstrcmp
  have hsaved : PrologueSaved after.σ.mem (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21 := by
    rw [hp.mem, prologue_log sp0 env name out r0 r8 r9 r18 r19 r20 r21 hSt.spDrop]
    exact prologue_saved head.σ.mem sp0 r0 r8 r9 r18 r19 r20 r21
  obtain ⟨henv, hname, hout, hra, hsp, _⟩ := hp.selected_regs
  exact ⟨after,
    { steps := hb.steps.trans hp.steps
      extendsMemory := by
        rw [hp.mem, hheadMem]
        exact memExtends_writeLog _ _
      registers :=
        { good := hp.good, loadedG := hG, loadedS := hS, tick := hp.tick
          env4 := by simpa [gprGet] using henv
          name3 := by simpa [gprGet] using hname
          out5 := by simpa [gprGet] using hout
          ra1 := by simpa [gprGet] using hra
          sp2 := by simpa [gprGet] using hsp }
      pc := hp.pc
      saved := hsaved
      outside := houtside
      output := hp.output.trans hb.output
      kept_frame := fun R hR => (hp.reg_frame R hR).trans (hb.reg_frame R hR) }⟩

#print axioms prologue_framed

end Vsa.Sim.EnvGetReflected
