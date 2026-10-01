import VsaIris.Vsa.Console

namespace VsaIris.Inst

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim

structure JalSite where
  pc : Nat
  b0 : BitVec 8
  b1 : BitVec 8
  b2 : BitVec 8
  b3 : BitVec 8
  w : BitVec 32
  imm : BitVec 21
  tgt : BitVec 64

namespace JalSite

abbrev code (S : JalSite) : List (BitVec 8) := [S.b0, S.b1, S.b2, S.b3]

structure Cert (S : JalSite) : Prop where
  word : ((S.b3.append S.b2).append S.b1).append S.b0 = S.w
  notrvc : Sail.BitVec.extractLsb (((S.b3.append S.b2).append S.b1).append S.b0) 1 0 =
    (0b11#2 : BitVec 2)
  dec : ∀ σ : MState,
    σ.regs.get? Register.misa = some ((initMisa) : RegisterType Register.misa) →
    σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege) →
    σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode S.w).run σ = .ok (instruction.JAL (S.imm, regidx.Regidx 0x01#5)) σ
  tgt : BitVec.ofNat 64 S.pc + sign_extend (m := 64) S.imm = S.tgt
  tgt_align : S.tgt.toNat % 4 = 0
  lo : 0x80000000 ≤ S.pc
  hi : S.pc + 4 ≤ tohostAddr
  align : S.pc % 4 = 0

macro "jal_cert" : term => `(
  { word := (by decide), notrvc := (by decide), dec := fun σ h1 h2 h3 => Vsa.Sim.decodeW σ h1 h2 h3,
    tgt := (by decide), tgt_align := (by decide), lo := (by decide), hi := (by decide),
    align := (by decide) })

theorem pc_toNat {S : JalSite} (hS : S.Cert) : (BitVec.ofNat 64 S.pc).toNat = S.pc := by
  have := hS.hi
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by unfold tohostAddr at this; omega)

theorem exec {S : JalSite} (hS : S.Cert) (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    JalExec (vsaModel live) S.pc S.code S.tgt := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have e := pc_toNat hS
  have hb' : ∀ k (b : BitVec 8), (S.pc + k, Iris.DFrac.discard, b) ∈ codeFoot S.pc S.code →
      c.σ.mem[(BitVec.ofNat 64 S.pc).toNat + k]? = some b := fun k b hm => by
    rw [e]; exact hb _ hm
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_exec (u := c.steps) (BitVec.ofNat 64 S.pc + sign_extend (m := 64) S.imm) vm
      (Fetched.of_bytes hG hpc
        (hb' 0 S.b0 (by simp [codeFoot])) (hb' 1 S.b1 (by simp [codeFoot]))
        (hb' 2 S.b2 (by simp [codeFoot])) (hb' 3 S.b3 (by simp [codeFoot]))
        (by rw [e]; exact hS.lo) (by rw [e]; exact hS.hi) (by rw [e]; exact hS.align)
        hS.notrvc hS.word
        (hS.dec _ (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
          (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
          (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg)))
      (execute_jal_char S.imm (regidx.Regidx 0x01#5) _ (BitVec.ofNat 64 S.pc) _ _ _
        (by reg_reads []) (by reg_reads [hpc]) (by reg_reads [hG.misa])
        (by rw [hS.tgt]; exact hS.tgt_align)
        (wX_bits_gpr _ (BitVec.addInt (BitVec.ofNat 64 S.pc) 4) 1 (by decide) (by decide)))
      ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hmi]⟩
      (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi
  have h := jalStep_of_obs (calleeEntry := S.tgt) hs hi' hG' hmem hobs hS.tgt
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [addInt_ofNat_four] at h

end JalSite

end VsaIris.Inst
