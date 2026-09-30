import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000af44 : List BBlock := [{ body := [mkLine 0x8000af44#64 0x0a0a3503#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000af44 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000af48#64 (upd R 10 (ldv .ld Mt ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000af44#64 R Mt :=
  swp_stepD ix_8000af44 [10, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000af44 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 20])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000af48 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000af48 [0xef#8, 0xc0#8, 0x8f#8, 0x89#8], live p.1) :
    JalExec (vsaModel live) 0x8000af48 [0xef#8, 0xc0#8, 0x8f#8, 0x89#8] 0x80006fe0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000af48, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000af49, .discard, 0xc0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000af4a, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000af4b, .discard, 0x89#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000af48#64) vm (0x898fc0ef#32) (0x1fc098#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000af48#64) 4)
      (0xef#8) (0xc0#8) (0x8f#8) (0x89#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x898fc0ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000af48#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006fe0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000af48#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000af48 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000af48 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006fe0#64 (upd R 1 (BitVec.ofNat 64 (0x8000af48 + 4))) Mt) :
    NW live Dt DA S Q 0x8000af48#64 R Mt :=
  swp_jal 0x8000af48 [0xef#8, 0xc0#8, 0x8f#8, 0x89#8] 0x80006fe0#64 (jalx_8000af48 live (fun p hp => hlive _ ((stdio_code (by decide)) p hp)))
    (fun p hp => List.mem_append_left _ ((stdio_code (by decide)) p hp)) (by decide) (by decide) rfl hk

end VsaIris.Sym
