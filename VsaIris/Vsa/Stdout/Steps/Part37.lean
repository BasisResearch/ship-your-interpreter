import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc
import Vsa.Sim.DecodeTable.Batch18

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000e3e4 : List BBlock := [{ body := [mkLine 0x8000e3e4#64 0x000a0513#32], term := none }]
def ixT_8000e3e8 : List BBlock := [⟨[], some (⟨0x8000e3e8#64, 0x01378863#32, 0x63#8, 0x88#8, 0x37#8, 0x01#8, .br bop.BEQ true, 15, 19, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000e3e8 : List BBlock := [⟨[], some (⟨0x8000e3e8#64, 0x01378863#32, 0x63#8, 0x88#8, 0x37#8, 0x01#8, .br bop.BEQ false, 15, 19, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e3f0 : List BBlock := [{ body := [mkLine 0x8000e3f0#64 0x01656b33#32], term := none }]
def ix_8000e3f4 : List BBlock := [{ body := [mkLine 0x8000e3f4#64 0x000b0b1b#32], term := none }]
def ix_8000e3f8 : List BBlock := [{ body := [mkLine 0x8000e3f8#64 0x0b840413#32], term := none }]
def ixT_8000e3fc : List BBlock := [⟨[], some (⟨0x8000e3fc#64, 0xfc941ce3#32, 0xe3#8, 0x1c#8, 0x94#8, 0xfc#8, .br bop.BNE true, 8, 9, 0x1fd8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000e3fc : List BBlock := [⟨[], some (⟨0x8000e3fc#64, 0xfc941ce3#32, 0xe3#8, 0x1c#8, 0x94#8, 0xfc#8, .br bop.BNE false, 8, 9, 0x1fd8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e400 : List BBlock := [{ body := [mkLine 0x8000e400#64 0x00093903#32], term := none }]
def ixT_8000e404 : List BBlock := [⟨[], some (⟨0x8000e404#64, 0xfa0912e3#32, 0xe3#8, 0x12#8, 0x09#8, 0xfa#8, .br bop.BNE true, 18, 0, 0x1fa4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000e404 : List BBlock := [⟨[], some (⟨0x8000e404#64, 0xfa0912e3#32, 0xe3#8, 0x12#8, 0x09#8, 0xfa#8, .br bop.BNE false, 18, 0, 0x1fa4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e408 : List BBlock := [{ body := [mkLine 0x8000e408#64 0x04813083#32], term := none }]
def ix_8000e40c : List BBlock := [{ body := [mkLine 0x8000e40c#64 0x04013403#32], term := none }]
def ix_8000e410 : List BBlock := [{ body := [mkLine 0x8000e410#64 0x03813483#32], term := none }]
def ix_8000e414 : List BBlock := [{ body := [mkLine 0x8000e414#64 0x03013903#32], term := none }]
def ix_8000e418 : List BBlock := [{ body := [mkLine 0x8000e418#64 0x02813983#32], term := none }]
def ix_8000e41c : List BBlock := [{ body := [mkLine 0x8000e41c#64 0x02013a03#32], term := none }]
def ix_8000e420 : List BBlock := [{ body := [mkLine 0x8000e420#64 0x01813a83#32], term := none }]
def ix_8000e424 : List BBlock := [{ body := [mkLine 0x8000e424#64 0x00813b83#32], term := none }]
def ix_8000e428 : List BBlock := [{ body := [mkLine 0x8000e428#64 0x000b0513#32], term := none }]
def ix_8000e42c : List BBlock := [{ body := [mkLine 0x8000e42c#64 0x01013b03#32], term := none }]
def ix_8000e430 : List BBlock := [{ body := [mkLine 0x8000e430#64 0x05010113#32], term := none }]
def ix_8000e434 : List BBlock := [⟨[], some (⟨0x8000e434#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e438 : List BBlock := [{ body := [mkLine 0x8000e438#64 0x01059703#32], term := none }]
def ix_8000e43c : List BBlock := [{ body := [mkLine 0x8000e43c#64 0x00277793#32], term := none }]
def ixT_8000e440 : List BBlock := [⟨[], some (⟨0x8000e440#64, 0x00078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000e440 : List BBlock := [⟨[], some (⟨0x8000e440#64, 0x00078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000e444 : List BBlock := [{ body := [mkLine 0x8000e444#64 0x07758793#32], term := none }]
def ix_8000e448 : List BBlock := [{ body := [mkLine 0x8000e448#64 0x00100713#32], term := none }]
def ix_8000e44c : List BBlock := [{ body := [mkLine 0x8000e44c#64 0x00f5b023#32], term := none }]
def ix_8000e450 : List BBlock := [{ body := [mkLine 0x8000e450#64 0x00f5bc23#32], term := none }]
def ix_8000e454 : List BBlock := [{ body := [mkLine 0x8000e454#64 0x02e5a023#32], term := none }]
def ix_8000e458 : List BBlock := [⟨[], some (⟨0x8000e458#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000e3e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e3e8#64 (upd R 10 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000e3e4#64 R Mt :=
  swp_stepD ix_8000e3e4 [10, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e3e4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 20])))) rfl hk

theorem it_8000e3e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (R 19) → NW live Dt DA S Q 0x8000e3f8#64 R Mt) (hF : ¬ ((R 15) = (R 19)) → NW live Dt DA S Q 0x8000e3ec#64 R Mt) :
    NW live Dt DA S Q 0x8000e3e8#64 R Mt := by
  by_cases hc : (R 15) = (R 19)
  · exact
    swp_stepD ixT_8000e3e8 [15, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000e3e8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000e3e8 [15, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000e3e8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem it_8000e3ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (Sail.BitVec.update (R 21 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hk : NW live Dt DA S Q (Sail.BitVec.update (R 21 + sign_extend (m := 64) (0x000#12)) 0 0#1) (upd R 1 (BitVec.ofNat 64 (0x8000e3ec + 4))) Mt) :
    NW live Dt DA S Q 0x8000e3ec#64 R Mt :=
  swp_jalr 0x8000e3ec [0xe7#8, 0x80#8, 0x0a#8, 0x00#8] [21] (Sail.BitVec.update (R 21 + sign_extend (m := 64) (0x000#12)) 0 0#1)
    (jalrStep_of_obs
      (fun q hq => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact (show ∀ k ∈ [21], 1 ≤ k ∧ k ≤ 31 by decide) k hk)
      (fun p hp => hlive _ (stdio_code_8000e3ec p hp))
      (fun c hG hi hpc hRR hMR => by
      obtain ⟨vm, hmi⟩ := hG.minstret
      have hb0 := hMR (0x8000e3ec, .discard, 0xe7#8) (by simp [codeFoot])
      have hb1 := hMR (0x8000e3ed, .discard, 0x80#8) (by simp [codeFoot])
      have hb2 := hMR (0x8000e3ee, .discard, 0x0a#8) (by simp [codeFoot])
      have hb3 := hMR (0x8000e3ef, .discard, 0x00#8) (by simp [codeFoot])
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        stepObs_jalr c.σ c.tick c.steps (0x8000e3ec#64) vm (R 21) (0x000a80e7#32) (0x000#12)
          (regidx.Regidx 0x15#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000e3ec#64) 4)
          (0xe7#8) (0x80#8) (0x0a#8) (0x00#8)
          hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
          (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
          (Vsa.Sim.DecodeTable.decode_000a80e7 (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
          (rX_bits_x21 _ (R 21) (by rw [get?_afterNextPC c.σ (0x8000e3ec#64) _ (by decide) (by decide)]; exact hRR (21, Iris.DFrac.own 1, R 21) (by simp)))
          hal (by decide) (by decide) (by decide) (by decide) (by decide)
          (wX_bits_x1 _ (BitVec.addInt (0x8000e3ec#64) 4)) hi
      refine ⟨σ', i', vm, hs, hi', hG', hmem, ?_⟩
      rwa [show BitVec.addInt (0x8000e3ec#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000e3ec + 4) from by
        apply BitVec.eq_of_toNat_eq; decide] at hobs))
    (fun p hp => List.mem_append_left _ (stdio_code_8000e3ec p hp))
    (by decide) (by decide) (by decide) rfl hk

theorem it_8000e3f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e3f4#64 (upd R 22 ((R 10) ||| (R 22))) Mt) :
    NW live Dt DA S Q 0x8000e3f0#64 R Mt :=
  swp_stepD ix_8000e3f0 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e3f0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [10, 22])))) rfl hk

theorem it_8000e3f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e3f8#64 (upd R 22 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 22) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000e3f4#64 R Mt :=
  swp_stepD ix_8000e3f4 [22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e3f4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [22])))) rfl hk

theorem it_8000e3f8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e3fc#64 (upd R 8 ((R 8) + sign_extend (m := 64) (0x0b8#12))) Mt) :
    NW live Dt DA S Q 0x8000e3f8#64 R Mt :=
  swp_stepD ix_8000e3f8 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e3f8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem it_8000e3fc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 8) ≠ (R 9) → NW live Dt DA S Q 0x8000e3d4#64 R Mt) (hF : ¬ ((R 8) ≠ (R 9)) → NW live Dt DA S Q 0x8000e400#64 R Mt) :
    NW live Dt DA S Q 0x8000e3fc#64 R Mt := by
  by_cases hc : (R 8) ≠ (R 9)
  · exact
    swp_stepD ixT_8000e3fc [8, 9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000e3fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000e3fc [8, 9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000e3fc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000e400 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 18) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 18) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e404#64 (upd R 18 (ldv .ld Mt ((R 18) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e400#64 R Mt :=
  swp_stepD ix_8000e400 [18] [bytesAt (imgM Mt) ((R 18) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 18) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e400 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [18])))) rfl hk

theorem it_8000e404 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 18) ≠ (0#64) → NW live Dt DA S Q 0x8000e3a8#64 R Mt) (hF : ¬ ((R 18) ≠ (0#64)) → NW live Dt DA S Q 0x8000e408#64 R Mt) :
    NW live Dt DA S Q 0x8000e404#64 R Mt := by
  by_cases hc : (R 18) ≠ (0#64)
  · exact
    swp_stepD ixT_8000e404 [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000e404 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000e404 [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000e404 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000e408 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e40c#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x048#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e408#64 R Mt :=
  swp_stepD ix_8000e408 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x048#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e408 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem it_8000e40c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e410#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x040#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e40c#64 R Mt :=
  swp_stepD ix_8000e40c [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x040#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e40c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem it_8000e410 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e414#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e410#64 R Mt :=
  swp_stepD ix_8000e410 [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e410 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem it_8000e414 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e418#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e414#64 R Mt :=
  swp_stepD ix_8000e414 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e414 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem it_8000e418 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e41c#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e418#64 R Mt :=
  swp_stepD ix_8000e418 [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e418 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem it_8000e41c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e420#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e41c#64 R Mt :=
  swp_stepD ix_8000e41c [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e41c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem it_8000e420 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e424#64 (upd R 21 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e420#64 R Mt :=
  swp_stepD ix_8000e420 [2, 21] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e420 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [2, 21])))) rfl hk

theorem it_8000e424 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e428#64 (upd R 23 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e424#64 R Mt :=
  swp_stepD ix_8000e424 [2, 23] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e424 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 23 ∈ [2, 23])))) rfl hk

theorem it_8000e428 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e42c#64 (upd R 10 ((R 22) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000e428#64 R Mt :=
  swp_stepD ix_8000e428 [10, 22] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e428 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 22])))) rfl hk

theorem it_8000e42c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e430#64 (upd R 22 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e42c#64 R Mt :=
  swp_stepD ix_8000e42c [2, 22] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e42c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 22 ∈ [2, 22])))) rfl hk

theorem it_8000e430 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e434#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x050#12))) Mt) :
    NW live Dt DA S Q 0x8000e430#64 R Mt :=
  swp_stepD ix_8000e430 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e430 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem it_8000e434 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000e434#64 R Mt :=
  swp_stepD ix_8000e434 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e434 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e438 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2)
    (hLDS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2, S b)
    (hk : NW live Dt DA S Q 0x8000e43c#64 (upd R 14 (ldv .lh Mt ((R 11) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000e438#64 R Mt :=
  swp_stepD ix_8000e438 [11, 14] [bytesAt (imgM Mt) ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2] (accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 2) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e438 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins2_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [11, 14])))) rfl hk

theorem it_8000e43c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e440#64 (upd R 15 ((R 14) &&& sign_extend (m := 64) (0x002#12))) Mt) :
    NW live Dt DA S Q 0x8000e43c#64 R Mt :=
  swp_stepD ix_8000e43c [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e43c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem it_8000e440 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 15) = (0#64) → NW live Dt DA S Q 0x8000e45c#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → NW live Dt DA S Q 0x8000e444#64 R Mt) :
    NW live Dt DA S Q 0x8000e440#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    swp_stepD ixT_8000e440 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000e440 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000e440 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000e440 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000e444 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e448#64 (upd R 15 ((R 11) + sign_extend (m := 64) (0x077#12))) Mt) :
    NW live Dt DA S Q 0x8000e444#64 R Mt :=
  swp_stepD ix_8000e444 [11, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e444 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem it_8000e448 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e44c#64 (upd R 14 ((0#64) + sign_extend (m := 64) (0x001#12))) Mt) :
    NW live Dt DA S Q 0x8000e448#64 R Mt :=
  swp_stepD ix_8000e448 [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e448 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem it_8000e44c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e450#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000e44c#64 R Mt :=
  swp_stepD ix_8000e44c [11, 15] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e44c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e450 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000e454#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 15))])) :
    NW live Dt DA S Q 0x8000e450#64 R Mt :=
  swp_stepD ix_8000e450 [11, 15] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e450 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e454 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4, S b)
    (hk : NW live Dt DA S Q 0x8000e458#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x020#12)).toNat, 4, (R 14))])) :
    NW live Dt DA S Q 0x8000e454#64 R Mt :=
  swp_stepD ix_8000e454 [11, 14] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000e454 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000e458 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : NW live Dt DA S Q (R 1) R Mt) :
    NW live Dt DA S Q 0x8000e458#64 R Mt :=
  swp_stepD ix_8000e458 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000e458 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
