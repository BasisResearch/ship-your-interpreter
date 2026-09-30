import VsaIris.Vsa.SnpRunDef
import VsaIris.Vsa.SymObs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def nx_8000e914 : List BBlock := [{ body := [mkLine 0x8000e914#64 0x02113c23#32], term := none }]
def nx_8000e918 : List BBlock := [{ body := [mkLine 0x8000e918#64 0x00060493#32], term := none }]
def nxT_8000e91c : List BBlock := [⟨[], some (⟨0x8000e91c#64, 0x08070a63#32, 0x63#8, 0x0a#8, 0x07#8, 0x08#8, .br bop.BEQ true, 14, 0, 0x94#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e91c : List BBlock := [⟨[], some (⟨0x8000e91c#64, 0x08070a63#32, 0x63#8, 0x0a#8, 0x07#8, 0x08#8, .br bop.BEQ false, 14, 0, 0x94#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e920 : List BBlock := [{ body := [mkLine 0x8000e920#64 0x02813823#32], term := none }]
def nx_8000e924 : List BBlock := [{ body := [mkLine 0x8000e924#64 0x01313c23#32], term := none }]
def nx_8000e928 : List BBlock := [{ body := [mkLine 0x8000e928#64 0x01413823#32], term := none }]
def nx_8000e92c : List BBlock := [{ body := [mkLine 0x8000e92c#64 0x01513423#32], term := none }]
def nx_8000e930 : List BBlock := [{ body := [mkLine 0x8000e930#64 0x00063403#32], term := none }]
def nx_8000e934 : List BBlock := [{ body := [mkLine 0x8000e934#64 0x03213023#32], term := none }]
def nx_8000e938 : List BBlock := [{ body := [mkLine 0x8000e938#64 0x00050993#32], term := none }]
def nx_8000e93c : List BBlock := [{ body := [mkLine 0x8000e93c#64 0x00058a13#32], term := none }]
def nx_8000e940 : List BBlock := [{ body := [mkLine 0x8000e940#64 0xfff00a93#32], term := none }]
def nx_8000e944 : List BBlock := [⟨[], some (⟨0x8000e944#64, 0x00c0006f#32, 0x6f#8, 0x00#8, 0xc0#8, 0x00#8, .j, 0, 0, 0x0#13, 0xc#21, 0#12⟩ : TInstr)⟩]
def nx_8000e948 : List BBlock := [{ body := [mkLine 0x8000e948#64 0x01040413#32], term := none }]
def nxT_8000e94c : List BBlock := [⟨[], some (⟨0x8000e94c#64, 0x04068863#32, 0x63#8, 0x88#8, 0x06#8, 0x04#8, .br bop.BEQ true, 13, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e94c : List BBlock := [⟨[], some (⟨0x8000e94c#64, 0x04068863#32, 0x63#8, 0x88#8, 0x06#8, 0x04#8, .br bop.BEQ false, 13, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e950 : List BBlock := [{ body := [mkLine 0x8000e950#64 0x0084a783#32], term := none }]
def nx_8000e954 : List BBlock := [{ body := [mkLine 0x8000e954#64 0x00070693#32], term := none }]
def nx_8000e958 : List BBlock := [{ body := [mkLine 0x8000e958#64 0xfff7861b#32], term := none }]
def nx_8000e95c : List BBlock := [{ body := [mkLine 0x8000e95c#64 0x00c4a423#32], term := none }]
def nxT_8000e960 : List BBlock := [⟨[], some (⟨0x8000e960#64, 0x02f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x02#8, .br bop.BGE true, 0, 15, 0x3c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e960 : List BBlock := [⟨[], some (⟨0x8000e960#64, 0x02f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x02#8, .br bop.BGE false, 0, 15, 0x3c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e964 : List BBlock := [{ body := [mkLine 0x8000e964#64 0x00843903#32], term := none }]
def nxT_8000e968 : List BBlock := [⟨[], some (⟨0x8000e968#64, 0xfe0900e3#32, 0xe3#8, 0x00#8, 0x09#8, 0xfe#8, .br bop.BEQ true, 18, 0, 0x1fe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e968 : List BBlock := [⟨[], some (⟨0x8000e968#64, 0xfe0900e3#32, 0xe3#8, 0x00#8, 0x09#8, 0xfe#8, .br bop.BEQ false, 18, 0, 0x1fe0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e96c : List BBlock := [{ body := [mkLine 0x8000e96c#64 0x00043603#32], term := none }]
def nx_8000e970 : List BBlock := [{ body := [mkLine 0x8000e970#64 0x00090693#32], term := none }]
def nx_8000e974 : List BBlock := [{ body := [mkLine 0x8000e974#64 0x000a0593#32], term := none }]
def nx_8000e978 : List BBlock := [{ body := [mkLine 0x8000e978#64 0x00098513#32], term := none }]
def nxT_8000e980 : List BBlock := [⟨[], some (⟨0x8000e980#64, 0x05550663#32, 0x63#8, 0x06#8, 0x55#8, 0x05#8, .br bop.BEQ true, 10, 21, 0x4c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e980 : List BBlock := [⟨[], some (⟨0x8000e980#64, 0x05550663#32, 0x63#8, 0x06#8, 0x55#8, 0x05#8, .br bop.BEQ false, 10, 21, 0x4c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e984 : List BBlock := [{ body := [mkLine 0x8000e984#64 0x0104b703#32], term := none }]
def nx_8000e988 : List BBlock := [{ body := [mkLine 0x8000e988#64 0x01040413#32], term := none }]
def nx_8000e98c : List BBlock := [{ body := [mkLine 0x8000e98c#64 0x41270733#32], term := none }]
def nx_8000e990 : List BBlock := [{ body := [mkLine 0x8000e990#64 0x00e4b823#32], term := none }]
def nx_8000e994 : List BBlock := [{ body := [mkLine 0x8000e994#64 0x00070693#32], term := none }]
def nxT_8000e998 : List BBlock := [⟨[], some (⟨0x8000e998#64, 0xfa069ce3#32, 0xe3#8, 0x9c#8, 0x06#8, 0xfa#8, .br bop.BNE true, 13, 0, 0x1fb8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8000e998 : List BBlock := [⟨[], some (⟨0x8000e998#64, 0xfa069ce3#32, 0xe3#8, 0x9c#8, 0x06#8, 0xfa#8, .br bop.BNE false, 13, 0, 0x1fb8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e99c : List BBlock := [{ body := [mkLine 0x8000e99c#64 0x03013403#32], term := none }]
def nx_8000e9a0 : List BBlock := [{ body := [mkLine 0x8000e9a0#64 0x02013903#32], term := none }]
def nx_8000e9a4 : List BBlock := [{ body := [mkLine 0x8000e9a4#64 0x01813983#32], term := none }]
def nx_8000e9a8 : List BBlock := [{ body := [mkLine 0x8000e9a8#64 0x01013a03#32], term := none }]
def nx_8000e9ac : List BBlock := [{ body := [mkLine 0x8000e9ac#64 0x00813a83#32], term := none }]
def nx_8000e9b0 : List BBlock := [{ body := [mkLine 0x8000e9b0#64 0x03813083#32], term := none }]
def nx_8000e9b4 : List BBlock := [{ body := [mkLine 0x8000e9b4#64 0x0004b823#32], term := none }]
def nx_8000e9b8 : List BBlock := [{ body := [mkLine 0x8000e9b8#64 0x0004a423#32], term := none }]
def nx_8000e9bc : List BBlock := [{ body := [mkLine 0x8000e9bc#64 0x00000513#32], term := none }]
def nx_8000e9c0 : List BBlock := [{ body := [mkLine 0x8000e9c0#64 0x02813483#32], term := none }]
def nx_8000e9c4 : List BBlock := [{ body := [mkLine 0x8000e9c4#64 0x04010113#32], term := none }]
def nx_8000e9c8 : List BBlock := [⟨[], some (⟨0x8000e9c8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_8000e9cc : List BBlock := [{ body := [mkLine 0x8000e9cc#64 0x03013403#32], term := none }]
def nx_8000e9d0 : List BBlock := [{ body := [mkLine 0x8000e9d0#64 0x03813083#32], term := none }]
def nx_8000e9d4 : List BBlock := [{ body := [mkLine 0x8000e9d4#64 0x02013903#32], term := none }]
def nx_8000e9d8 : List BBlock := [{ body := [mkLine 0x8000e9d8#64 0x01813983#32], term := none }]
def nx_8000e9dc : List BBlock := [{ body := [mkLine 0x8000e9dc#64 0x01013a03#32], term := none }]
def nx_8000e9e0 : List BBlock := [{ body := [mkLine 0x8000e9e0#64 0x00813a83#32], term := none }]
def nx_8000e9e4 : List BBlock := [{ body := [mkLine 0x8000e9e4#64 0x0004b823#32], term := none }]
def nx_8000e9e8 : List BBlock := [{ body := [mkLine 0x8000e9e8#64 0x0004a423#32], term := none }]
def nx_8000e9ec : List BBlock := [{ body := [mkLine 0x8000e9ec#64 0x02813483#32], term := none }]
def nx_8000e9f0 : List BBlock := [{ body := [mkLine 0x8000e9f0#64 0x04010113#32], term := none }]
def nx_8000e9f4 : List BBlock := [⟨[], some (⟨0x8000e9f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80010234 : List BBlock := [{ body := [mkLine 0x80010234#64 0x3e81c503#32], term := none }]
def nx_80010238 : List BBlock := [⟨[], some (⟨0x80010238#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80010258 : List BBlock := [{ body := [mkLine 0x80010258#64 0x38818513#32], term := none }]
def nx_8001025c : List BBlock := [⟨[], some (⟨0x8001025c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80012268 : List BBlock := [⟨[], some (⟨0x80012268#64, 0x02058063#32, 0x63#8, 0x80#8, 0x05#8, 0x02#8, .br bop.BEQ true, 11, 0, 0x20#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80012268 : List BBlock := [⟨[], some (⟨0x80012268#64, 0x02058063#32, 0x63#8, 0x80#8, 0x05#8, 0x02#8, .br bop.BEQ false, 11, 0, 0x20#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_8001226c : List BBlock := [⟨[], some (⟨0x8001226c#64, 0x04060263#32, 0x63#8, 0x02#8, 0x06#8, 0x04#8, .br bop.BEQ true, 12, 0, 0x44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_8001226c : List BBlock := [⟨[], some (⟨0x8001226c#64, 0x04060263#32, 0x63#8, 0x02#8, 0x06#8, 0x04#8, .br bop.BEQ false, 12, 0, 0x44#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxT_80012270 : List BBlock := [⟨[], some (⟨0x80012270#64, 0x04068863#32, 0x63#8, 0x88#8, 0x06#8, 0x04#8, .br bop.BEQ true, 13, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nxF_80012270 : List BBlock := [⟨[], some (⟨0x80012270#64, 0x04068863#32, 0x63#8, 0x88#8, 0x06#8, 0x04#8, .br bop.BEQ false, 13, 0, 0x50#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def nx_80012274 : List BBlock := [{ body := [mkLine 0x80012274#64 0x00064783#32], term := none }]
def nx_80012278 : List BBlock := [{ body := [mkLine 0x80012278#64 0x00f5a023#32], term := none }]
def nx_8001227c : List BBlock := [{ body := [mkLine 0x8001227c#64 0x00064503#32], term := none }]
def nx_80012284 : List BBlock := [⟨[], some (⟨0x80012284#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem nt_8000e914 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e918#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x038#12)).toNat, 8, (R 1))])) :
    SnpW live Dt DA S Q 0x8000e914#64 R Mt :=
  swp_stepD nx_8000e914 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e914 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e918 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e91c#64 (upd R 9 ((R 12) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e918#64 R Mt :=
  swp_stepD nx_8000e918 [9, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e918 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 12])))) rfl hk

theorem nt_8000e91c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 14) = (0#64) → SnpW live Dt DA S Q 0x8000e9b0#64 R Mt) (hF : ¬ ((R 14) = (0#64)) → SnpW live Dt DA S Q 0x8000e920#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e91c#64 R Mt := by
  by_cases hc : (R 14) = (0#64)
  · exact
    swp_stepD nxT_8000e91c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e91c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e91c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e91c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e920 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e924#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x030#12)).toNat, 8, (R 8))])) :
    SnpW live Dt DA S Q 0x8000e920#64 R Mt :=
  swp_stepD nx_8000e920 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e920 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e924 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e928#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 19))])) :
    SnpW live Dt DA S Q 0x8000e924#64 R Mt :=
  swp_stepD nx_8000e924 [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e924 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e928 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e92c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 20))])) :
    SnpW live Dt DA S Q 0x8000e928#64 R Mt :=
  swp_stepD nx_8000e928 [2, 20] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e928 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e92c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e930#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 21))])) :
    SnpW live Dt DA S Q 0x8000e92c#64 R Mt :=
  swp_stepD nx_8000e92c [2, 21] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e92c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e930 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e934#64 (upd R 8 (ldv .ld Mt ((R 12) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e930#64 R Mt :=
  swp_stepD nx_8000e930 [8, 12] [bytesAt (imgM Mt) ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e930 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 12])))) rfl hk

theorem nt_8000e934 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e938#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 18))])) :
    SnpW live Dt DA S Q 0x8000e934#64 R Mt :=
  swp_stepD nx_8000e934 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e934 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e938 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e93c#64 (upd R 19 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e938#64 R Mt :=
  swp_stepD nx_8000e938 [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e938 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [10, 19])))) rfl hk

theorem nt_8000e93c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e940#64 (upd R 20 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e93c#64 R Mt :=
  swp_stepD nx_8000e93c [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e93c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [11, 20])))) rfl hk

theorem nt_8000e940 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e944#64 (upd R 21 ((0#64) + sign_extend (m := 64) (0xfff#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e940#64 R Mt :=
  swp_stepD nx_8000e940 [21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e940 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [21])))) rfl hk

theorem nt_8000e944 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e950#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e944#64 R Mt :=
  swp_stepD nx_8000e944 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e944 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e948 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e94c#64 (upd R 8 ((R 8) + sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e948#64 R Mt :=
  swp_stepD nx_8000e948 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e948 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem nt_8000e94c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13) = (0#64) → SnpW live Dt DA S Q 0x8000e99c#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → SnpW live Dt DA S Q 0x8000e950#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e94c#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD nxT_8000e94c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e94c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e94c [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e94c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e950 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8000e954#64 (upd R 15 (ldv .lw Mt ((R 9) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e950#64 R Mt :=
  swp_stepD nx_8000e950 [9, 15] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e950 ChainFacts; chain_facts hm; exact ⟨hea, lpins4_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [9, 15])))) rfl hk

theorem nt_8000e954 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e958#64 (upd R 13 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e954#64 R Mt :=
  swp_stepD nx_8000e954 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e954 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 14])))) rfl hk

theorem nt_8000e958 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e95c#64 (upd R 12 (sign_extend (m := 64) (Sail.BitVec.extractLsb ((R 15) + sign_extend (m := 64) (0xfff#12)) 31 0))) Mt) :
    SnpW live Dt DA S Q 0x8000e958#64 R Mt :=
  swp_stepD nx_8000e958 [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e958 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 15])))) rfl hk

theorem nt_8000e95c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8000e960#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x008#12)).toNat, 4, (R 12))])) :
    SnpW live Dt DA S Q 0x8000e95c#64 R Mt :=
  swp_stepD nx_8000e95c [9, 12] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e95c ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e960 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 15).toInt ≤ (0#64).toInt → SnpW live Dt DA S Q 0x8000e99c#64 R Mt) (hF : ¬ ((R 15).toInt ≤ (0#64).toInt) → SnpW live Dt DA S Q 0x8000e964#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e960#64 R Mt := by
  by_cases hc : (R 15).toInt ≤ (0#64).toInt
  · exact
    swp_stepD nxT_8000e960 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e960 ChainFacts; chain_facts hm; exact (guard_bge _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e960 [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e960 ChainFacts; chain_facts hm; exact (guard_false (guard_bge _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e964 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e968#64 (upd R 18 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e964#64 R Mt :=
  swp_stepD nx_8000e964 [8, 18] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e964 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [8, 18])))) rfl hk

theorem nt_8000e968 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 18) = (0#64) → SnpW live Dt DA S Q 0x8000e948#64 R Mt) (hF : ¬ ((R 18) = (0#64)) → SnpW live Dt DA S Q 0x8000e96c#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e968#64 R Mt := by
  by_cases hc : (R 18) = (0#64)
  · exact
    swp_stepD nxT_8000e968 [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e968 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e968 [18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e968 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e96c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e970#64 (upd R 12 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e96c#64 R Mt :=
  swp_stepD nx_8000e96c [8, 12] [bytesAt (imgM Mt) ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8] (accAddrs ((R 8) + sign_extend (m := 64) (0x000#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e96c ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [8, 12])))) rfl hk

theorem nt_8000e970 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e974#64 (upd R 13 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e970#64 R Mt :=
  swp_stepD nx_8000e970 [13, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e970 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 18])))) rfl hk

theorem nt_8000e974 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e978#64 (upd R 11 ((R 20) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e974#64 R Mt :=
  swp_stepD nx_8000e974 [11, 20] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e974 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 20])))) rfl hk

theorem nt_8000e978 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e97c#64 (upd R 10 ((R 19) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e978#64 R Mt :=
  swp_stepD nx_8000e978 [10, 19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e978 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 19])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalxn_8000e97c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000e97c [0xef#8, 0x50#8, 0x10#8, 0x21#8], live p.1) :
    JalExec (vsaModel live) 0x8000e97c [0xef#8, 0x50#8, 0x10#8, 0x21#8] 0x8001438c#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000e97c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000e97d, .discard, 0x50#8) (by simp [codeFoot])
  have hb2 := hb (0x8000e97e, .discard, 0x10#8) (by simp [codeFoot])
  have hb3 := hb (0x8000e97f, .discard, 0x21#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000e97c#64) vm (0x211050ef#32) (0x005a10#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000e97c#64) 4)
      (0xef#8) (0x50#8) (0x10#8) (0x21#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x211050ef#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000e97c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8001438c#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000e97c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000e97c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem ntC_8000e97c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8001438c#64 (upd R 1 (BitVec.ofNat 64 (0x8000e97c + 4))) Mt) :
    SnpW live Dt DA S Q 0x8000e97c#64 R Mt :=
  swp_jal 0x8000e97c [0xef#8, 0x50#8, 0x10#8, 0x21#8] 0x8001438c#64
    (jalxn_8000e97c live fun p hp => hlive _ ((snp_code (by decide)) p hp))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp)) (by decide) (by decide) rfl hk

theorem nt_8000e980 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 10) = (R 21) → SnpW live Dt DA S Q 0x8000e9cc#64 R Mt) (hF : ¬ ((R 10) = (R 21)) → SnpW live Dt DA S Q 0x8000e984#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e980#64 R Mt := by
  by_cases hc : (R 10) = (R 21)
  · exact
    swp_stepD nxT_8000e980 [10, 21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e980 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e980 [10, 21] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e980 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e984 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e988#64 (upd R 14 (ldv .ld Mt ((R 9) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e984#64 R Mt :=
  swp_stepD nx_8000e984 [9, 14] [bytesAt (imgM Mt) ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e984 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [9, 14])))) rfl hk

theorem nt_8000e988 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e98c#64 (upd R 8 ((R 8) + sign_extend (m := 64) (0x010#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e988#64 R Mt :=
  swp_stepD nx_8000e988 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e988 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem nt_8000e98c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e990#64 (upd R 14 ((R 14) - (R 18))) Mt) :
    SnpW live Dt DA S Q 0x8000e98c#64 R Mt :=
  swp_stepD nx_8000e98c [14, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e98c ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14, 18])))) rfl hk

theorem nt_8000e990 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e994#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 14))])) :
    SnpW live Dt DA S Q 0x8000e990#64 R Mt :=
  swp_stepD nx_8000e990 [9, 14] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e990 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e994 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e998#64 (upd R 13 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e994#64 R Mt :=
  swp_stepD nx_8000e994 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e994 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13, 14])))) rfl hk

theorem nt_8000e998 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13) ≠ (0#64) → SnpW live Dt DA S Q 0x8000e950#64 R Mt) (hF : ¬ ((R 13) ≠ (0#64)) → SnpW live Dt DA S Q 0x8000e99c#64 R Mt) :
    SnpW live Dt DA S Q 0x8000e998#64 R Mt := by
  by_cases hc : (R 13) ≠ (0#64)
  · exact
    swp_stepD nxT_8000e998 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8000e998 ChainFacts; chain_facts hm; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8000e998 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8000e998 ChainFacts; chain_facts hm; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8000e99c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9a0#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e99c#64 R Mt :=
  swp_stepD nx_8000e99c [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e99c ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem nt_8000e9a0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9a4#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9a0#64 R Mt :=
  swp_stepD nx_8000e9a0 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9a0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem nt_8000e9a4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9a8#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9a4#64 R Mt :=
  swp_stepD nx_8000e9a4 [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9a4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem nt_8000e9a8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9ac#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9a8#64 R Mt :=
  swp_stepD nx_8000e9a8 [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9a8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem nt_8000e9ac {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9b0#64 (upd R 21 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9ac#64 R Mt :=
  swp_stepD nx_8000e9ac [2, 21] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9ac ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [2, 21])))) rfl hk

theorem nt_8000e9b0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9b4#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9b0#64 R Mt :=
  swp_stepD nx_8000e9b0 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9b0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem nt_8000e9b4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9b8#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x010#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x8000e9b4#64 R Mt :=
  swp_stepD nx_8000e9b4 [9] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e9b4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e9b8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9bc#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x008#12)).toNat, 4, (0#64))])) :
    SnpW live Dt DA S Q 0x8000e9b8#64 R Mt :=
  swp_stepD nx_8000e9b8 [9] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e9b8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e9bc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e9c0#64 (upd R 10 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e9bc#64 R Mt :=
  swp_stepD nx_8000e9bc [10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9bc ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10])))) rfl hk

theorem nt_8000e9c0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9c4#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9c0#64 R Mt :=
  swp_stepD nx_8000e9c0 [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9c0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem nt_8000e9c4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e9c8#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x040#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e9c4#64 R Mt :=
  swp_stepD nx_8000e9c4 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9c4 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem nt_8000e9c8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x8000e9c8#64 R Mt :=
  swp_stepD nx_8000e9c8 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9c8 ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e9cc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9d0#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9cc#64 R Mt :=
  swp_stepD nx_8000e9cc [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9cc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem nt_8000e9d0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9d4#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9d0#64 R Mt :=
  swp_stepD nx_8000e9d0 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9d0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem nt_8000e9d4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9d8#64 (upd R 18 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9d4#64 R Mt :=
  swp_stepD nx_8000e9d4 [2, 18] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9d4 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [2, 18])))) rfl hk

theorem nt_8000e9d8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9dc#64 (upd R 19 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9d8#64 R Mt :=
  swp_stepD nx_8000e9d8 [2, 19] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9d8 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [2, 19])))) rfl hk

theorem nt_8000e9dc {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9e0#64 (upd R 20 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9dc#64 R Mt :=
  swp_stepD nx_8000e9dc [2, 20] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9dc ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 20 ∈ [2, 20])))) rfl hk

theorem nt_8000e9e0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9e4#64 (upd R 21 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9e0#64 R Mt :=
  swp_stepD nx_8000e9e0 [2, 21] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9e0 ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 21 ∈ [2, 21])))) rfl hk

theorem nt_8000e9e4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9e8#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x010#12)).toNat, 8, (0#64))])) :
    SnpW live Dt DA S Q 0x8000e9e4#64 R Mt :=
  swp_stepD nx_8000e9e4 [9] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e9e4 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e9e8 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9ec#64 R (writeLog Mt [(((R 9) + sign_extend (m := 64) (0x008#12)).toNat, 4, (0#64))])) :
    SnpW live Dt DA S Q 0x8000e9e8#64 R Mt :=
  swp_stepD nx_8000e9e8 [9] [] [] (accAddrs ((R 9) + sign_extend (m := 64) (0x008#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_8000e9e8 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_8000e9ec {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : SnpW live Dt DA S Q 0x8000e9f0#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8000e9ec#64 R Mt :=
  swp_stepD nx_8000e9ec [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9ec ChainFacts; chain_facts hm; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

theorem nt_8000e9f0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8000e9f4#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0x040#12))) Mt) :
    SnpW live Dt DA S Q 0x8000e9f0#64 R Mt :=
  swp_stepD nx_8000e9f0 [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9f0 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem nt_8000e9f4 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x8000e9f4#64 R Mt :=
  swp_stepD nx_8000e9f4 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8000e9f4 ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80010234 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((0x8001b510#64) + sign_extend (m := 64) (0x3e8#12)).toNat 1)
    (hLDS : ∀ b ∈ accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x3e8#12)).toNat 1, S b)
    (hk : SnpW live Dt DA S Q 0x80010238#64 (upd R 10 (ldv .lbu Mt ((0x8001b510#64) + sign_extend (m := 64) (0x3e8#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80010234#64 R Mt :=
  swp_stepD nx_80010234 [3, 10] [bytesAt (imgM Mt) ((0x8001b510#64) + sign_extend (m := 64) (0x3e8#12)).toNat 1] (accAddrs ((0x8001b510#64) + sign_extend (m := 64) (0x3e8#12)).toNat 1) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80010234 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img hLD⟩)
    (by decide) (by decide) (fun _ => rfl) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [3, 10])))) rfl hk

theorem nt_80010238 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x80010238#64 R Mt :=
  swp_stepD nx_80010238 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80010238 ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80010258 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x8001025c#64 (upd R 10 ((0x8001b510#64) + sign_extend (m := 64) (0x388#12))) Mt) :
    SnpW live Dt DA S Q 0x80010258#64 R Mt :=
  swp_stepD nx_80010258 [3, 10] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80010258 ChainFacts; chain_facts hm)
    (by decide) (by decide) (fun _ => rfl) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [3, 10])))) rfl hk

theorem nt_8001025c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x8001025c#64 R Mt :=
  swp_stepD nx_8001025c [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8001025c ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem nt_80012268 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 11) = (0#64) → SnpW live Dt DA S Q 0x80012288#64 R Mt) (hF : ¬ ((R 11) = (0#64)) → SnpW live Dt DA S Q 0x8001226c#64 R Mt) :
    SnpW live Dt DA S Q 0x80012268#64 R Mt := by
  by_cases hc : (R 11) = (0#64)
  · exact
    swp_stepD nxT_80012268 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80012268 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80012268 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80012268 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_8001226c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 12) = (0#64) → SnpW live Dt DA S Q 0x800122b0#64 R Mt) (hF : ¬ ((R 12) = (0#64)) → SnpW live Dt DA S Q 0x80012270#64 R Mt) :
    SnpW live Dt DA S Q 0x8001226c#64 R Mt := by
  by_cases hc : (R 12) = (0#64)
  · exact
    swp_stepD nxT_8001226c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_8001226c ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_8001226c [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_8001226c ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem nt_80012270 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hT : (R 13) = (0#64) → SnpW live Dt DA S Q 0x800122c0#64 R Mt) (hF : ¬ ((R 13) = (0#64)) → SnpW live Dt DA S Q 0x80012274#64 R Mt) :
    SnpW live Dt DA S Q 0x80012270#64 R Mt := by
  by_cases hc : (R 13) = (0#64)
  · exact
    swp_stepD nxT_80012270 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxT_80012270 ChainFacts; chain_facts hm; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_stepD nxF_80012270 [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by unfold nxF_80012270 ChainFacts; chain_facts hm; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem ntD_80012274 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1, b ∈ DA)
    (hk : SnpW live Dt DA S Q 0x80012278#64 (upd R 15 (ldv .lbu Dt ((R 12) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x80012274#64 R Mt :=
  swp_stepD nx_80012274 [12, 15] [bytesAt (imgM Dt) ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80012274 ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [12, 15])))) rfl hk

theorem nt_80012278 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : StOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 4)
    (hS : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 4, S b)
    (hk : SnpW live Dt DA S Q 0x8001227c#64 R (writeLog Mt [(((R 11) + sign_extend (m := 64) (0x000#12)).toNat, 4, (R 15))])) :
    SnpW live Dt DA S Q 0x80012278#64 R Mt :=
  swp_stepD nx_80012278 [11, 15] [] [] (accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 4) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by unfold nx_80012278 ChainFacts; chain_facts hm; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem ntD_8001227c {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hea : LdOK ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hLDD : ∀ b ∈ accAddrs ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1, b ∈ DA)
    (hk : SnpW live Dt DA S Q 0x80012280#64 (upd R 10 (ldv .lbu Dt ((R 12) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    SnpW live Dt DA S Q 0x8001227c#64 R Mt :=
  swp_stepD nx_8001227c [10, 12] [bytesAt (imgM Dt) ((R 12) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_8001227c ChainFacts; chain_facts hm; exact ⟨hea, lpins1_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 12])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem ntO_80012280 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hk : SnpW live Dt DA S Q 0x80012284#64 (upd R 10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (R 10))))) Mt) :
    SnpW live Dt DA S Q 0x80012280#64 R Mt :=
  swp_alu 0x80012280 [0x33#8, 0x35#8, 0xa0#8, 0x00#8] 10 [10] (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (R 10))))
    (aluStep_of_obs (by decide) (by decide)
      (fun q hq => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact (show ∀ k ∈ [10], 1 ≤ k ∧ k ≤ 31 by decide) k hk)
      (fun p hp => hlive _ ((snp_code (by decide)) p hp))
      (fun c hG hi hpc hRR hMR => by
      obtain ⟨vm, hmi⟩ := hG.minstret
      have hb0 := hMR (0x80012280, .discard, 0x33#8) (by simp [codeFoot])
      have hb1 := hMR (0x80012281, .discard, 0x35#8) (by simp [codeFoot])
      have hb2 := hMR (0x80012282, .discard, 0xa0#8) (by simp [codeFoot])
      have hb3 := hMR (0x80012283, .discard, 0x00#8) (by simp [codeFoot])
      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
        stepObs_alu c.σ c.tick c.steps (0x80012280#64) vm (0x00a03533#32)
          (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
          Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (R 10))))
          (0x33#8) (0x35#8) (0xa0#8) (0x00#8)
          hG hpc hmi (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
          (Vsa.Sim.decodeW (w := 0x00a03533#32) (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
          (execute_rtype_sltu_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64) (R 10) (afterNextPC (afterPrelude c.σ) (0x80012280#64)) (sigma3_alu c.σ (0x80012280#64) Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (R 10)))))
        (rX_bits_zero _)
        (rX_bits_x10 _ (R 10) (by rw [get?_afterNextPC c.σ (0x80012280#64) _ (by decide) (by decide)]; exact hRR (10, Iris.DFrac.own 1, R 10) (by simp)))
        (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (R 10))))))
          (by decide) (by decide) (by decide) (by decide) (by decide)
          hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi
      exact ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩))
    (fun p hp => List.mem_append_left _ ((snp_code (by decide)) p hp))
    (by decide) (by decide) (by decide) (by decide) rfl hk

theorem nt_80012284 {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ snpText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : SnpW live Dt DA S Q (R 1) R Mt) :
    SnpW live Dt DA S Q 0x80012284#64 R Mt :=
  swp_stepD nx_80012284 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by unfold nx_80012284 ChainFacts; chain_facts hm; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Sym
