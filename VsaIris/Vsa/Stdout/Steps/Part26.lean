import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def ix_8000cf9c : List BBlock := [{ body := [mkLine 0x8000cf9c#64 0x00040513#32], term := none }]
def ix_8000cfa0 : List BBlock := [{ body := [mkLine 0x8000cfa0#64 0x0e010613#32], term := none }]
def ix_8000cfa4 : List BBlock := [{ body := [mkLine 0x8000cfa4#64 0x000a0593#32], term := none }]
def ixT_8000cfac : List BBlock := [⟨[], some (⟨0x8000cfac#64, 0x00051463#32, 0x63#8, 0x14#8, 0x05#8, 0x00#8, .br bop.BNE true, 10, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000cfac : List BBlock := [⟨[], some (⟨0x8000cfac#64, 0x00051463#32, 0x63#8, 0x14#8, 0x05#8, 0x00#8, .br bop.BNE false, 10, 0, 0x8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000cfb0 : List BBlock := [⟨[], some (⟨0x8000cfb0#64, 0xd0dfd06f#32, 0x6f#8, 0xd0#8, 0xdf#8, 0xd0#8, .j, 0, 0, 0x0#13, 0x1fdd0c#21, 0#12⟩ : TInstr)⟩]
def ix_8000cfb8 : List BBlock := [{ body := [mkLine 0x8000cfb8#64 0x000c8513#32], term := none }]
def ix_8000cfbc : List BBlock := [{ body := [mkLine 0x8000cfbc#64 0x02613823#32], term := none }]
def ix_8000cfc0 : List BBlock := [{ body := [mkLine 0x8000cfc0#64 0x03c13023#32], term := none }]
def ix_8000cfc4 : List BBlock := [{ body := [mkLine 0x8000cfc4#64 0x00813c23#32], term := none }]
def ix_8000cfcc : List BBlock := [{ body := [mkLine 0x8000cfcc#64 0x0005069b#32], term := none }]
def ix_8000cfd0 : List BBlock := [{ body := [mkLine 0x8000cfd0#64 0x01813e83#32], term := none }]
def ix_8000cfd4 : List BBlock := [{ body := [mkLine 0x8000cfd4#64 0x02013e03#32], term := none }]
def ix_8000cfd8 : List BBlock := [{ body := [mkLine 0x8000cfd8#64 0x03013303#32], term := none }]
def ix_8000cfdc : List BBlock := [{ body := [mkLine 0x8000cfdc#64 0x00068613#32], term := none }]
def ixT_8000cfe0 : List BBlock := [⟨[], some (⟨0x8000cfe0#64, 0x0606cc63#32, 0x63#8, 0xcc#8, 0x06#8, 0x06#8, .br bop.BLT true, 13, 0, 0x78#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ixF_8000cfe0 : List BBlock := [⟨[], some (⟨0x8000cfe0#64, 0x0606cc63#32, 0x63#8, 0xcc#8, 0x06#8, 0x06#8, .br bop.BLT false, 13, 0, 0x78#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ix_8000cfe4 : List BBlock := [{ body := [mkLine 0x8000cfe4#64 0x0a714583#32], term := none }]
def ix_8000cfe8 : List BBlock := [⟨[], some (⟨0x8000cfe8#64, 0xbccfe06f#32, 0x6f#8, 0xe0#8, 0xcf#8, 0xbc#8, .j, 0, 0, 0x0#13, 0x1fe3cc#21, 0#12⟩ : TInstr)⟩]
def ix_8000cfec : List BBlock := [{ body := [mkLine 0x8000cfec#64 0x0a0a3503#32], term := none }]
def ix_8000cff4 : List BBlock := [⟨[], some (⟨0x8000cff4#64, 0xc1dfd06f#32, 0x6f#8, 0xd0#8, 0xdf#8, 0xc1#8, .j, 0, 0, 0x0#13, 0x1fdc1c#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem it_8000cf9c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfa0#64 (upd R 10 ((R 8) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000cf9c#64 R Mt :=
  swp_stepD ix_8000cf9c [8, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cf9c ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [8, 10])))) rfl hk

theorem it_8000cfa0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfa4#64 (upd R 12 ((R 2) + sign_extend (m := 64) (0x0e0#12))) Mt) :
    NW live Dt DA S Q 0x8000cfa0#64 R Mt :=
  swp_stepD ix_8000cfa0 [2, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfa0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [2, 12])))) rfl hk

theorem it_8000cfa4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfa8#64 (upd R 11 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000cfa4#64 R Mt :=
  swp_stepD ix_8000cfa4 [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfa4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 20])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000cfa8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000cfa8 [0xef#8, 0x10#8, 0x50#8, 0x12#8], live p.1) :
    JalExec (vsaModel live) 0x8000cfa8 [0xef#8, 0x10#8, 0x50#8, 0x12#8] 0x8000e8cc#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000cfa8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000cfa9, .discard, 0x10#8) (by simp [codeFoot])
  have hb2 := hb (0x8000cfaa, .discard, 0x50#8) (by simp [codeFoot])
  have hb3 := hb (0x8000cfab, .discard, 0x12#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000cfa8#64) vm (0x125010ef#32) (0x001924#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000cfa8#64) 4)
      (0xef#8) (0x10#8) (0x50#8) (0x12#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_125010ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000cfa8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000e8cc#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000cfa8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000cfa8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000cfa8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000e8cc#64 (upd R 1 (BitVec.ofNat 64 (0x8000cfa8 + 4))) Mt) :
    NW live Dt DA S Q 0x8000cfa8#64 R Mt :=
  swp_jal 0x8000cfa8 [0xef#8, 0x10#8, 0x50#8, 0x12#8] 0x8000e8cc#64 (jalx_8000cfa8 live (fun p hp => hlive _ (stdio_code_8000cfa8 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000cfa8 p hp)) (by decide) (by decide) rfl hk

theorem it_8000cfac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 10) ≠ (0#64) → NW live Dt DA S Q 0x8000cfb4#64 R Mt) (hF : ¬ ((R 10) ≠ (0#64)) → NW live Dt DA S Q 0x8000cfb0#64 R Mt) :
    NW live Dt DA S Q 0x8000cfac#64 R Mt := by
  by_cases hc : (R 10) ≠ (0#64)
  · exact
    swp_stepD ixT_8000cfac [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000cfac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000cfac [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000cfac ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000cfb0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000acbc#64 R Mt) :
    NW live Dt DA S Q 0x8000cfb0#64 R Mt :=
  swp_stepD ix_8000cfb0 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfb0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cfb8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfbc#64 (upd R 10 ((R 25) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000cfb8#64 R Mt :=
  swp_stepD ix_8000cfb8 [10, 25] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfb8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 25])))) rfl hk

theorem it_8000cfbc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfc0#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 6))])) :
    NW live Dt DA S Q 0x8000cfbc#64 R Mt :=
  swp_stepD ix_8000cfbc [2, 6] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000cfbc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cfc0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfc4#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 28))])) :
    NW live Dt DA S Q 0x8000cfc0#64 R Mt :=
  swp_stepD ix_8000cfc0 [2, 28] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000cfc0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cfc4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfc8#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 8))])) :
    NW live Dt DA S Q 0x8000cfc4#64 R Mt :=
  swp_stepD ix_8000cfc4 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold ix_8000cfc4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000cfc8 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000cfc8 [0xef#8, 0x90#8, 0x9f#8, 0xd2#8], live p.1) :
    JalExec (vsaModel live) 0x8000cfc8 [0xef#8, 0x90#8, 0x9f#8, 0xd2#8] 0x80006cf0#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000cfc8, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000cfc9, .discard, 0x90#8) (by simp [codeFoot])
  have hb2 := hb (0x8000cfca, .discard, 0x9f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000cfcb, .discard, 0xd2#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000cfc8#64) vm (0xd29f90ef#32) (0x1f9d28#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000cfc8#64) 4)
      (0xef#8) (0x90#8) (0x9f#8) (0xd2#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_d29f90ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000cfc8#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006cf0#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000cfc8#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000cfc8 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000cfc8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006cf0#64 (upd R 1 (BitVec.ofNat 64 (0x8000cfc8 + 4))) Mt) :
    NW live Dt DA S Q 0x8000cfc8#64 R Mt :=
  swp_jal 0x8000cfc8 [0xef#8, 0x90#8, 0x9f#8, 0xd2#8] 0x80006cf0#64 (jalx_8000cfc8 live (fun p hp => hlive _ (stdio_code_8000cfc8 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000cfc8 p hp)) (by decide) (by decide) rfl hk

theorem it_8000cfcc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfd0#64 (upd R 13 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 10) + sign_extend (m := 64) (0x000#12)) 31 0))) Mt) :
    NW live Dt DA S Q 0x8000cfcc#64 R Mt :=
  swp_stepD ix_8000cfcc [10, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfcc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [10, 13])))) rfl hk

theorem it_8000cfd0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfd4#64 (upd R 29 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cfd0#64 R Mt :=
  swp_stepD ix_8000cfd0 [2, 29] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfd0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [2, 29])))) rfl hk

theorem it_8000cfd4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfd8#64 (upd R 28 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cfd4#64 R Mt :=
  swp_stepD ix_8000cfd4 [2, 28] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfd4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [2, 28])))) rfl hk

theorem it_8000cfd8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cfdc#64 (upd R 6 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cfd8#64 R Mt :=
  swp_stepD ix_8000cfd8 [2, 6] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfd8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [2, 6])))) rfl hk

theorem it_8000cfdc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000cfe0#64 (upd R 12 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    NW live Dt DA S Q 0x8000cfdc#64 R Mt :=
  swp_stepD ix_8000cfdc [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfdc ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 13])))) rfl hk

theorem it_8000cfe0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hT : (R 13).toInt < (0#64).toInt → NW live Dt DA S Q 0x8000d058#64 R Mt) (hF : ¬ ((R 13).toInt < (0#64).toInt) → NW live Dt DA S Q 0x8000cfe4#64 R Mt) :
    NW live Dt DA S Q 0x8000cfe0#64 R Mt := by
  by_cases hc : (R 13).toInt < (0#64).toInt
  · exact
    swp_stepD ixT_8000cfe0 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixT_8000cfe0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD ixF_8000cfe0 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold ixF_8000cfe0 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem it_8000cfe4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1, S b)
    (hk : NW live Dt DA S Q 0x8000cfe8#64 (upd R 11 (ldv .lbu Mt ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cfe4#64 R Mt :=
  swp_stepD ix_8000cfe4 [2, 11] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1] (accAddrs ((R 2) + sign_extend (m := 64) (0x0a7#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfe4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [2, 11])))) rfl hk

theorem it_8000cfe8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000b3b4#64 R Mt) :
    NW live Dt DA S Q 0x8000cfe8#64 R Mt :=
  swp_stepD ix_8000cfe8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfe8 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem it_8000cfec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hea : LdOK ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8, S b)
    (hk : NW live Dt DA S Q 0x8000cff0#64 (upd R 10 (ldv .ld Mt ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat)) Mt) :
    NW live Dt DA S Q 0x8000cfec#64 R Mt :=
  swp_stepD ix_8000cfec [10, 20] [bytesAt (imgM Mt) ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8] (accAddrs ((R 20) + sign_extend (m := 64) (0x0a0#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cfec ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 20])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000cff0 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000cff0 [0xef#8, 0xa0#8, 0x8f#8, 0x80#8], live p.1) :
    JalExec (vsaModel live) 0x8000cff0 [0xef#8, 0xa0#8, 0x8f#8, 0x80#8] 0x80006ff8#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000cff0, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000cff1, .discard, 0xa0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000cff2, .discard, 0x8f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000cff3, .discard, 0x80#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000cff0#64) vm (0x808fa0ef#32) (0x1fa008#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000cff0#64) 4)
      (0xef#8) (0xa0#8) (0x8f#8) (0x80#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_808fa0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000cff0#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80006ff8#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000cff0#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000cff0 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem it_8000cff0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x80006ff8#64 (upd R 1 (BitVec.ofNat 64 (0x8000cff0 + 4))) Mt) :
    NW live Dt DA S Q 0x8000cff0#64 R Mt :=
  swp_jal 0x8000cff0 [0xef#8, 0xa0#8, 0x8f#8, 0x80#8] 0x80006ff8#64 (jalx_8000cff0 live (fun p hp => hlive _ (stdio_code_8000cff0 p hp)))
    (fun p hp => List.mem_append_left _ (stdio_code_8000cff0 p hp)) (by decide) (by decide) rfl hk

theorem it_8000cff4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ stdioText, live p.1)
    (hk : NW live Dt DA S Q 0x8000ac10#64 R Mt) :
    NW live Dt DA S Q 0x8000cff4#64 R Mt :=
  swp_stepD ix_8000cff4 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold ix_8000cff4 ChainFacts; chain_facts hm with "VsaIris.Sym.stdio_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
