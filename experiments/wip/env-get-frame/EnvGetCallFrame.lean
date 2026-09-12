import EnvGetSegments
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.EnvGetSites2

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)

namespace Vsa.Sim.EnvGetReflected

/-- The argument block and its call retain the same computed result and frame. -/
structure CallResult (cursor name : BitVec 64) (lds : List (List (BitVec 8)))
    (before after : Config) : Prop extends
    SegCallFacts env_getX2c60Seg (env_getX2c60L cursor name) lds
      0x80006ea0#64 0x80002c6c#64 before after where
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the generated argument block and the observed `jal strcmp` once. -/
theorem call_framed (cursor name : BitVec 64) (lds : List (List (BitVec 8)))
    (c : Config) (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c60#64)
    (htick : c.tick < 2) (hL : GHolds c.σ (env_getX2c60L cursor name))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (env_getX2c60L cursor name) lds env_getX2c60Seg)
    (hloaded : Code.Env_getLoaded c.σ.mem) :
    ∃ after, CallResult cursor name lds c after := by
  have hmemLog : writeLog c.σ.mem (evalBlocks env_getX2c60Seg
      (SegEvalState.init (env_getX2c60L cursor name) lds)).log = c.σ.mem := rfl
  have hkeys : keysG (evalBlocks env_getX2c60Seg
      (SegEvalState.init (env_getX2c60L cursor name) lds)).regs = [11, 10, 9, 19] := rfl
  obtain ⟨after, h⟩ := bridgeOfSegFull env_getX2c60Seg (env_getX2c60L cursor name) lds
    0x80002c60#64 0x80006ea0#64 0x80002c6c#64 c hG hpc hG.minstret htick hL
    (by show KeysOK [9, 19]; decide) hfacts
    (by show ChainOK 0x80002c60#64 [9, 19] env_getX2c60Seg; decide)
    (by rw [hkeys]; decide)
    (by show ∀ n ∈ keysG _, n ≠ 1; rw [hkeys]; decide)
    (by
      intro middle hGm htm hpcm hmim hmemm _
      obtain ⟨σ, i, u⟩ := middle
      obtain ⟨vm, hvm⟩ := hmim
      have hpcEval : evalBlocksPC 0x80002c60#64
          (SegEvalState.init (env_getX2c60L cursor name) lds)
          env_getX2c60Seg = 0x80002c68#64 := rfl
      have hloaded' : Code.Env_getLoaded σ.mem := by
        change Code.Env_getLoaded (⟨σ, i, u⟩ : Config).σ.mem
        rw [hmemm, hmemLog]
        exact hloaded
      obtain ⟨σ', i', hs, hi, hg, hm, ho⟩ :=
        site_80002c68_eg2 σ i u 0x80002c68#64 vm hGm
          (hpcEval ▸ hpcm) hvm hloaded' rfl (by decide) htm
      have hlink : BitVec.addInt 0x80002c68#64 4 = (0x80002c6c#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      rw [hlink] at ho
      exact ⟨⟨σ', i', u + 1⟩, jalCallFacts_of_obs hs hi hg hm ho
        (by apply BitVec.eq_of_toNat_eq; decide)⟩)
  refine ⟨after, { toSegCallFacts := h, kept_frame := ?_ }⟩
  intro R hR
  exact h.frame R (noise_avoids kept_noise hR)
    (wrChain_avoids (kept_segments env_getX2c60Seg (by simp [segments])) hR)
    (regAvoids_ne hR (by decide))

#print axioms call_framed

end Vsa.Sim.EnvGetReflected
