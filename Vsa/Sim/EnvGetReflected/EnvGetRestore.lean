import Vsa.Sim.EnvGetReflected.EnvGetPrologueData
import Vsa.Sim.WordLoadData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- Retain the prologue's saved words through the hit copy's byte frame. -/
theorem PrologueSaved.transport {m m' : Mem} {sp r0 r8 r9 r18 r19 r20 r21 : BitVec 64}
    (h : PrologueSaved m sp r0 r8 r9 r18 r19 r20 r21)
    (ha : ∀ k, sp.toNat ≤ k ∧ k < sp.toNat + 64 → m'[k]? = m[k]?) :
    PrologueSaved m' sp r0 r8 r9 r18 r19 r20 r21 := by
  have hr (off : Nat) (hoff : off + 8 ≤ 64) :
      read64 m' (sp.toNat + off) = read64 m (sp.toNat + off) :=
    read64_agreeP ha (fun k hk => by omega)
  exact
    { ra := (hr 56 (by decide)).trans h.ra
      s0 := (hr 48 (by decide)).trans h.s0
      s1 := (hr 40 (by decide)).trans h.s1
      s2 := (hr 32 (by decide)).trans h.s2
      s3 := (hr 24 (by decide)).trans h.s3
      s4 := (hr 16 (by decide)).trans h.s4
      s5 := (hr 8 (by decide)).trans h.s5 }

/-- One restore load, from its saved word and the actual 64-byte frame. -/
theorem restore_word (m : Mem) (sp v : BitVec 64) (a : MInstr) (off : Nat)
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ sp.toNat)
    (hk : a.kind = .ld) (hrs : a.rs1 = 2)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 64)
    (hread : read64 m (sp.toNat + off) = some v.toNat) :
    ∃ bs, WordLoadFacts m (env_getX2ca0L sp) a v bs := by
  have hea : (eaddrM a (env_getX2ca0L sp)).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hrs]
    change (sp + sign_extend (m := 64) a.imm).toNat = _
    rw [BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  exact wordLoadFacts_of_read64 m (env_getX2ca0L sp) a v hk
    (by rw [hea]; omega) (by rw [hea]; omega)
    (by rw [hea]; right; omega) (by rw [hea]; exact hread)

def restoreRegs (sp a0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64) : GRegs :=
  [(1, r0), (2, sp + 64#64), (8, r8), (9, r9), (18, r18),
   (19, r19), (20, r20), (21, r21), (10, a0)]

/-- The generated restore and return preserve the copy's memory and result. -/
structure RestoreResult (sp a0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some r0
  regs : GHolds after.σ (restoreRegs sp a0 r0 r8 r9 r18 r19 r20 r21)
  mem : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem restore_framed
    (sp a0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (c : Config)
    (hgood : GoodState c.σ) (hcode : Code.Env_getLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002ca0#64)
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (ha0 : c.σ.regs.get? Register.x10 = some a0) (htick : c.tick < 2)
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ sp.toNat) (halign : r0.toNat % 4 = 0)
    (hsaved : PrologueSaved c.σ.mem sp r0 r8 r9 r18 r19 r20 r21) :
    ∃ after, RestoreResult sp a0 r0 r8 r9 r18 r19 r20 r21 c after := by
  obtain ⟨b0, w0⟩ := restore_word c.σ.mem sp r0 (mkLine 0x80002ca0#64 0x03813083#32) 56
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.ra
  obtain ⟨b8, w8⟩ := restore_word c.σ.mem sp r8 (mkLine 0x80002ca4#64 0x03013403#32) 48
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s0
  obtain ⟨b9, w9⟩ := restore_word c.σ.mem sp r9 (mkLine 0x80002ca8#64 0x02813483#32) 40
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s1
  obtain ⟨b18, w18⟩ := restore_word c.σ.mem sp r18 (mkLine 0x80002cac#64 0x02013903#32) 32
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s2
  obtain ⟨b19, w19⟩ := restore_word c.σ.mem sp r19 (mkLine 0x80002cb0#64 0x01813983#32) 24
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s3
  obtain ⟨b20, w20⟩ := restore_word c.σ.mem sp r20 (mkLine 0x80002cb4#64 0x01013a03#32) 16
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s4
  obtain ⟨b21, w21⟩ := restore_word c.σ.mem sp r21 (mkLine 0x80002cb8#64 0x00813a83#32) 8
    hlo hhi hht (by decide) (by decide) (by decide) (by decide) hsaved.s5
  let L : GRegs := [(2, sp), (10, a0)]
  let lds := [b0, b8, b9, b18, b19, b20, b21]
  have hfacts : ChainFacts c.σ.mem c.σ.mem L lds env_getX2ca0Seg := by
    chain_facts hcode with "Vsa.Sim.Code.env_get_at_"
    · exact w0.facts
    · exact w8.facts
    · exact w9.facts
    · exact w18.facts
    · exact w19.facts
    · exact w20.facts
    · exact w21.facts
    · change (Sail.BitVec.update (bytesVal .ld b0 + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [w0.value, ret_tgt r0 halign]
      exact halign
  have hL : GHolds c.σ L :=
    ⟨by simpa [gprGet] using hsp, by simpa [gprGet] using ha0, trivial⟩
  have hproj : GProjects (evalBlocks env_getX2ca0Seg (SegEvalState.init L lds)).regs
      (restoreRegs sp a0 r0 r8 r9 r18 r19 r20 r21) := by
    change some (bytesVal .ld b0) = some r0 ∧
      some (sp + sign_extend (m := 64) (0x040#12)) = some (sp + 64#64) ∧
      some (bytesVal .ld b8) = some r8 ∧ some (bytesVal .ld b9) = some r9 ∧
      some (bytesVal .ld b18) = some r18 ∧ some (bytesVal .ld b19) = some r19 ∧
      some (bytesVal .ld b20) = some r20 ∧ some (bytesVal .ld b21) = some r21 ∧
      some a0 = some a0 ∧ True
    simp only [w0.value, w8.value, w9.value, w18.value, w19.value, w20.value, w21.value,
      show sign_extend (m := 64) (0x040#12) = 64#64 from by decide,
      and_true]
  obtain ⟨vm, hvm⟩ := hgood.minstret
  obtain ⟨after, hs⟩ := segment_framed env_getX2ca0Seg (by simp [segments])
    L lds 0x80002ca0#64 vm (fun _ => False)
    (restoreRegs sp a0 r0 r8 r9 r18 r19 r20 r21) c
    hgood hpc hvm hL (by show KeysOK [2, 10]; decide) hfacts
    (by show ChainOK 0x80002ca0#64 [2, 10] _; decide)
    htick (fun _ _ => rfl) hproj
  have hret : after.σ.regs.get? Register.PC = some r0 := by
    have hp := hs.pc
    change after.σ.regs.get? Register.PC =
      some (Sail.BitVec.update (bytesVal .ld b0 + sign_extend (m := 64) (0#12)) 0 0#1) at hp
    rwa [w0.value, ret_tgt r0 halign] at hp
  exact ⟨after,
    { steps := hs.steps, good := hs.good, tick := hs.tick, pc := hret
      regs := hs.selected_regs, mem := hs.mem, output := hs.output
      kept_frame := hs.reg_frame }⟩

#print axioms PrologueSaved.transport
#print axioms restore_word
#print axioms restore_framed

end Vsa.Sim.EnvGetReflected
