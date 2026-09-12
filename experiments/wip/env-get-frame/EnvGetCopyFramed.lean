import EnvGetCopyData
import TransportEnv_getRange

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The hit copy's actual endpoint, ready for the common restore tail. -/
structure CopyResult (out sp : BitVec 64) (src : Nat) (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  loaded : Code.Env_getLoaded after.σ.mem
  pc : after.σ.regs.get? Register.PC = some 0x80002ca0#64
  stack : after.σ.regs.get? Register.x2 = some sp
  result : after.σ.regs.get? Register.x10 = some 1#64
  mem : after.σ.mem = copy3Log before.σ.mem src out.toNat
  outside : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the copy once, retaining its register frame and exact copied memory. -/
theorem copy_framed (env out sp : BitVec 64) (pv i : Nat) (c : Config)
    (h : CopyGeom env out pv i) (hgood : GoodState c.σ)
    (hcode : Code.Env_getLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c70#64)
    (hregs : GHolds c.σ (env_getX2c70L env (BitVec.ofNat 64 i) out))
    (hsp : c.σ.regs.get? Register.x2 = some sp) (htick : c.tick < 2)
    (hvalues : read64 c.σ.mem (env.toNat + 16) = some pv)
    (hwords : ValueWordsTotal c.σ.mem (pv + 24 * i)) :
    ∃ after, CopyResult out sp (pv + 24 * i) c after := by
  obtain ⟨lds, hd⟩ := copy_data c.σ.mem env out sp pv i h hcode hvalues hwords
  have hL : GHolds c.σ (copyInput env out sp i) := by
    obtain ⟨he, hi, ho, _⟩ := hregs
    exact ⟨he, hi, ho, by simpa [gprGet] using hsp, trivial⟩
  have hfoot : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) →
      c.σ.mem[k]? = (writeLog c.σ.mem (evalBlocks env_getX2c70Seg
        (SegEvalState.init (copyInput env out sp i) lds)).log)[k]? := by
    intro k hk
    rw [hd.log]
    exact (copy3_frame c.σ.mem (pv + 24 * i) out.toNat k hk).symm
  have hproj : GProjects (evalBlocks env_getX2c70Seg
      (SegEvalState.init (copyInput env out sp i) lds)).regs [(2, sp), (10, 1#64)] := by
    exact ⟨rfl, rfl, trivial⟩
  obtain ⟨vm, hvm⟩ := hgood.minstret
  obtain ⟨after, hs⟩ := segment_framed env_getX2c70Seg (by simp [segments])
    (copyInput env out sp i) lds 0x80002c70#64 vm
    (fun k => out.toNat ≤ k ∧ k < out.toNat + 24) [(2, sp), (10, 1#64)] c
    hgood hpc hvm hL (by show KeysOK [20, 8, 21, 2]; decide) hd.facts
    (by show ChainOK 0x80002c70#64 [20, 8, 21, 2] _; decide)
    htick hfoot hproj
  have houtside : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) →
      after.σ.mem[k]? = c.σ.mem[k]? := fun k hk => (hs.outside k hk).symm
  have hloaded : Code.Env_getLoaded after.σ.mem := Code.env_getLoaded_of_agree_range
    (fun k hlo hhi => houtside k (by
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := h.outHtif
      omega)) hcode
  obtain ⟨hsp', ha0', _⟩ := hs.selected_regs
  exact ⟨after,
    { steps := hs.steps, good := hs.good, tick := hs.tick, loaded := hloaded
      pc := hs.pc
      stack := by simpa [gprGet] using hsp'
      result := by simpa [gprGet] using ha0'
      mem := hs.mem.trans hd.log
      outside := houtside, output := hs.output, kept_frame := hs.reg_frame }⟩

#print axioms copy_framed

end Vsa.Sim.EnvGetReflected
