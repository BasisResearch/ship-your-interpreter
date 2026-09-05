import Vsa.Sim.rows.EnvDefineEpilogueCore
import Vsa.Sim.EnvDefMarshal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 1000000
attribute [local simp] mkLine decodeM envDefLdsHead envDefLdsHeadGetD envDefLdsTail

/-- Exact return state of the reflected restore-and-ret epilogue.  Registers
are stated using the saved image's total defaults; callers rewrite them with
their entry `some` facts. -/
structure EnvDefineEpilogueExactPost
    (sp : BitVec 64) (saved : (R : Register) → Option (RegisterType R))
    (m : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m
  pc : c.σ.regs.get? Register.PC = some
    (BitVec.update ((saved Register.x1).getD 0#64) 0 0#1)
  spReg : c.σ.regs.get? Register.x2 = some (sp + 64#64)
  ra : c.σ.regs.get? Register.x1 = some ((saved Register.x1).getD 0#64)
  s0 : c.σ.regs.get? Register.x8 = some ((saved Register.x8).getD 0#64)
  s1 : c.σ.regs.get? Register.x9 = some ((saved Register.x9).getD 0#64)
  s2 : c.σ.regs.get? Register.x18 = some ((saved Register.x18).getD 0#64)
  s3 : c.σ.regs.get? Register.x19 = some ((saved Register.x19).getD 0#64)
  s4 : c.σ.regs.get? Register.x20 = some ((saved Register.x20).getD 0#64)
  s5 : c.σ.regs.get? Register.x21 = some ((saved Register.x21).getD 0#64)
  s6 : c.σ.regs.get? Register.x22 = some ((saved Register.x22).getD 0#64)

/-- Decode the finite epilogue row into its exact observable return state. -/
theorem envDefineEpilogueExact_of_post
    (sp : BitVec 64) (saved : (R : Register) → Option (RegisterType R))
    (lds : List (List (BitVec 8)))
    (m : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hv : EnvDefineSpillValues saved lds)
    (hp : EnvDefineEpiloguePost sp lds m c) :
    EnvDefineEpilogueExactPost sp saved m c := by
  obtain ⟨hG, hmem, hpc, hregs, htick⟩ := hp
  obtain ⟨hra, hs0, hs1, hs2, hs3, hs4, hs5, hs6⟩ := hv
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineEpilogueSeg
        (SegEvalState.init (envDefineEpilogueL sp) lds)).regs = some w) :
      gprGet c.σ n = some w :=
    gholds_lookup _ hregs hl
  refine ⟨hG, htick, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [envDefineEpilogueSeg, evalBlocks, SegEvalState.init, writeLog] using hmem
  · rw [hpc]
    simp [envDefineEpilogueSeg, evalBlocks, evalBlock, evalBlocksPC, chainEndPC,
      endPCB, tgtPCT, SegEvalState.init, runGM, stepGM, stepLdsM, wvalM, srcVal,
      envDefineEpilogueL, lookupG, eraseG, hra]
    rw [show lds[0]?.getD [] = lds.getD 0 [] by rfl, hra,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      BitVec.add_zero]
  · have h := reg 2 (sp + 64#64) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG,
        show (sign_extend (m := 64) (64#12) : BitVec 64) = 64#64 by decide])
    simpa [gprGet] using h
  · have h := reg 1 (bytesVal .ld (lds.getD 0 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x1 = some (bytesVal .ld (lds.getD 0 [])) at h
    rw [hra] at h
    exact h
  · have h := reg 8 (bytesVal .ld (lds.getD 1 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x8 = some (bytesVal .ld (lds.getD 1 [])) at h
    rw [hs0] at h
    exact h
  · have h := reg 9 (bytesVal .ld (lds.getD 2 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x9 = some (bytesVal .ld (lds.getD 2 [])) at h
    rw [hs1] at h
    exact h
  · have h := reg 18 (bytesVal .ld (lds.getD 3 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x18 = some (bytesVal .ld (lds.getD 3 [])) at h
    rw [hs2] at h
    exact h
  · have h := reg 19 (bytesVal .ld (lds.getD 4 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x19 = some (bytesVal .ld (lds.getD 4 [])) at h
    rw [hs3] at h
    exact h
  · have h := reg 20 (bytesVal .ld (lds.getD 5 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x20 = some (bytesVal .ld (lds.getD 5 [])) at h
    rw [hs4] at h
    exact h
  · have h := reg 21 (bytesVal .ld (lds.getD 6 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x21 = some (bytesVal .ld (lds.getD 6 [])) at h
    rw [hs5] at h
    exact h
  · have h := reg 22 (bytesVal .ld (lds.getD 7 [])) (by
      simp [envDefineEpilogueSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, wvalM, srcVal, envDefineEpilogueL, lookupG, eraseG])
    change c.σ.regs.get? Register.x22 = some (bytesVal .ld (lds.getD 7 [])) at h
    rw [hs6] at h
    exact h

/-- Strengthened append-path epilogue entry. -/
structure AppendedFrameStStrong
    (SL : Vsa.Alloc.StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : Vsa.Machine.MState → List (Nat × Nat) → Prop)
    (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : Vsa.RuntimeRepr.NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value) (c : Config) : Prop where
  base : AppendedFrameSt SL gpv headroom AInv exts sp gm N φf φc
    envAddr parent vars x v c
  spills : EnvDefineSpillFrame sp gm c

/-- Strengthened update-path epilogue entry. -/
structure UpdatedFrameStStrong
    (SL : Vsa.Alloc.StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : Vsa.Machine.MState → List (Nat × Nat) → Prop)
    (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : Vsa.RuntimeRepr.NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (f : Vsa.While.Frame) (name : String) (v : Vsa.While.Value)
    (c : Config) : Prop where
  base : UpdatedFrameSt SL gpv headroom AInv exts sp gm N φf φc
    envAddr f name v c
  spills : EnvDefineSpillFrame sp gm c

/-- Execute the exact epilogue from any strengthened helper carrier.  Only the
final semantic reclassification remains pointwise. -/
theorem envDefineEpilogue_of_spills
    {P Q : Config → Prop} {sp : BitVec 64}
    {gm : (R : Register) → Option (RegisterType R)}
    (hReady : ∀ c, P c →
      GoodState c.σ ∧ c.σ.regs.get? Register.PC = some 0x80002aec#64 ∧
      c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2)
    (hSpills : ∀ c, P c → EnvDefineSpillFrame sp gm c)
    (hLand : ∀ (lds : List (List (BitVec 8)))
      (m : Std.ExtHashMap Nat (BitVec 8)) (c : Config),
      EnvDefineEpiloguePost sp lds m c → Q c) :
    Triple P Q := by
  intro c hc
  obtain ⟨hG, hpc, hsp, htick⟩ := hReady c hc
  obtain ⟨lds, hfacts⟩ :=
    (hSpills c hc).chainFacts
  have hpre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
      0x80002aec#64 c.σ.mem c :=
    ⟨hG, rfl, hpc, hG.minstret, ⟨hsp, trivial⟩,
      (by show KeysOK [2]; decide), hfacts, htick⟩
  obtain ⟨c', hs, hpost⟩ := envDefineEpilogueRow sp lds c.σ.mem c hpre
  exact ⟨c', hs, hLand lds c.σ.mem c' hpost⟩

/-- Exact epilogue execution with the outer-snapshot relation kept separate from
the live helper-register frame. -/
theorem envDefineEpilogue_of_saved
    {P Q : Config → Prop} {sp : BitVec 64}
    {saved : (R : Register) → Option (RegisterType R)}
    (hReady : ∀ c, P c →
      GoodState c.σ ∧ c.σ.regs.get? Register.PC = some 0x80002aec#64 ∧
      c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2)
    (hSaved : ∀ c, P c → EnvDefineSavedSpillFrame sp saved c)
    (hLand : ∀ (lds : List (List (BitVec 8)))
      (m : Std.ExtHashMap Nat (BitVec 8)) (c : Config),
      EnvDefineSpillValues saved lds → EnvDefineEpiloguePost sp lds m c → Q c) :
    Triple P Q := by
  intro c hc
  obtain ⟨hG, hpc, hsp, htick⟩ := hReady c hc
  obtain ⟨lds, hfacts, hvalues⟩ := (hSaved c hc).chainFacts
  have hpre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
      0x80002aec#64 c.σ.mem c :=
    ⟨hG, rfl, hpc, hG.minstret, ⟨hsp, trivial⟩,
      (by show KeysOK [2]; decide), hfacts, htick⟩
  obtain ⟨c', hs, hpost⟩ := envDefineEpilogueRow sp lds c.σ.mem c hpre
  exact ⟨c', hs, hLand lds c.σ.mem c' hvalues hpost⟩

/-- Run the exact epilogue and expose its decoded return state. -/
theorem envDefineEpilogue_exact
    {P : Config → Prop} {sp : BitVec 64}
    {saved : (R : Register) → Option (RegisterType R)}
    (hReady : ∀ c, P c →
      GoodState c.σ ∧ c.σ.regs.get? Register.PC = some 0x80002aec#64 ∧
      c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2)
    (hSaved : ∀ c, P c → EnvDefineSavedSpillFrame sp saved c) :
    Triple P (fun c => ∃ m, EnvDefineEpilogueExactPost sp saved m c) :=
  envDefineEpilogue_of_saved hReady hSaved fun lds m c hv hp =>
    ⟨m, envDefineEpilogueExact_of_post sp saved lds m c hv hp⟩

#print axioms envDefineEpilogue_of_spills
#print axioms envDefineEpilogue_of_saved
#print axioms envDefineEpilogueExact_of_post
#print axioms envDefineEpilogue_exact

end Vsa.Sim
