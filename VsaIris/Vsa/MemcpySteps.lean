import VsaIris.Vsa.MemcpyRun
import VsaIris.Vsa.AllocRun

namespace VsaIris.Memcpy

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast VsaIris.Sym
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem mst_80006bc8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bcc#64 (upd R 15 ((R 11) ^^^ (R 10))) Mt) :
    MW live Xs ns img S Q 0x80006bc8#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bc8#64 0x00a5c7b3#32], term := none }] : List BBlock) [10, 11, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [10, 11, 15])))) rfl hk

theorem mst_80006bcc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bd0#64 (upd R 15 ((R 15) &&& sign_extend (m := 64) (0x007#12))) Mt) :
    MW live Xs ns img S Q 0x80006bcc#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bcc#64 0x0077f793#32], term := none }] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem mst_80006bd0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bd4#64 (upd R 17 ((R 10) + (R 12))) Mt) :
    MW live Xs ns img S Q 0x80006bd0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bd0#64 0x00c508b3#32], term := none }] : List BBlock) [10, 12, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 17 ∈ [10, 12, 17])))) rfl hk

theorem mst_80006bd4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15) ≠ (0#64) → MW live Xs ns img S Q 0x80006c40#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → MW live Xs ns img S Q 0x80006bd8#64 R Mt) :
    MW live Xs ns img S Q 0x80006bd4#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    mw_step ([⟨[], some (⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE true, 15, 0, 0x6c#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE false, 15, 0, 0x6c#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006bdc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 12) ≠ (0#64) → MW live Xs ns img S Q 0x80006c40#64 R Mt) (hF : ¬ ((R 12) ≠ (0#64)) → MW live Xs ns img S Q 0x80006be0#64 R Mt) :
    MW live Xs ns img S Q 0x80006bdc#64 R Mt := by
  by_cases hc : (R 12) ≠ (0#64)
  · exact
    mw_step ([⟨[], some (⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8, .br bop.BNE true, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8, .br bop.BNE false, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006be0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006be4#64 (upd R 15 ((R 10) &&& sign_extend (m := 64) (0x007#12))) Mt) :
    MW live Xs ns img S Q 0x80006be0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006be0#64 0x00757793#32], term := none }] : List BBlock) [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [10, 15])))) rfl hk

theorem mst_80006be4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006be8#64 (upd R 14 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    MW live Xs ns img S Q 0x80006be4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006be4#64 0x00050713#32], term := none }] : List BBlock) [10, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [10, 14])))) rfl hk

theorem mst_80006be8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15) ≠ (0#64) → MW live Xs ns img S Q 0x80006cbc#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → MW live Xs ns img S Q 0x80006bec#64 R Mt) :
    MW live Xs ns img S Q 0x80006be8#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    mw_step ([⟨[], some (⟨0x80006be8#64, 0x0c079a63#32, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8, .br bop.BNE true, 15, 0, 0xd4#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006be8#64, 0x0c079a63#32, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8, .br bop.BNE false, 15, 0, 0xd4#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006bec {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bf0#64 (upd R 12 ((R 17) &&& sign_extend (m := 64) (0xff8#12))) Mt) :
    MW live Xs ns img S Q 0x80006bec#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bec#64 0xff88f613#32], term := none }] : List BBlock) [12, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 17])))) rfl hk

theorem mst_80006bf0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bf4#64 (upd R 13 ((R 12) - (R 14))) Mt) :
    MW live Xs ns img S Q 0x80006bf0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bf0#64 0x40e606b3#32], term := none }] : List BBlock) [12, 13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [12, 13, 14])))) rfl hk

theorem mst_80006bf4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bf8#64 (upd R 15 ((0#64) + sign_extend (m := 64) (0x040#12))) Mt) :
    MW live Xs ns img S Q 0x80006bf4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bf4#64 0x04000793#32], term := none }] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem mst_80006bf8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15).toInt < (R 13).toInt → MW live Xs ns img S Q 0x80006c60#64 R Mt) (hF : ¬ ((R 15).toInt < (R 13).toInt) → MW live Xs ns img S Q 0x80006bfc#64 R Mt) :
    MW live Xs ns img S Q 0x80006bf8#64 R Mt := by
  by_cases hc : (R 15).toInt < (R 13).toInt
  · exact
    mw_step ([⟨[], some (⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT true, 15, 13, 0x68#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT false, 15, 13, 0x68#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006bfc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c00#64 (upd R 13 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    MW live Xs ns img S Q 0x80006bfc#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006bfc#64 0x00058693#32], term := none }] : List BBlock) [11, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem mst_80006c00 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c04#64 (upd R 15 ((R 14) + sign_extend (m := 64) (0x000#12))) Mt) :
    MW live Xs ns img S Q 0x80006c00#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c00#64 0x00070793#32], term := none }] : List BBlock) [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem mst_80006c04 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 12).toNat ≤ (R 14).toNat → MW live Xs ns img S Q 0x80006c38#64 R Mt) (hF : ¬ ((R 12).toNat ≤ (R 14).toNat) → MW live Xs ns img S Q 0x80006c08#64 R Mt) :
    MW live Xs ns img S Q 0x80006c04#64 R Mt := by
  by_cases hc : (R 12).toNat ≤ (R 14).toNat
  · exact
    mw_step ([⟨[], some (⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU true, 14, 12, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU false, 14, 12, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006c08 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 13) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 13) + sign_extend (m := 64) (0x000#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c0c#64 (upd R 16 (ldvf .ld img ((R 13) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c08#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c08#64 0x0006b803#32], term := none }] : List BBlock) [13, 16] [bytesAt img ((R 13) + sign_extend (m := 64) (0x000#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [13, 16])))) rfl hk

theorem mst_80006c0c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c10#64 (upd R 15 ((R 15) + sign_extend (m := 64) (0x008#12))) Mt) :
    MW live Xs ns img S Q 0x80006c0c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c0c#64 0x00878793#32], term := none }] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem mst_80006c10 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c14#64 (upd R 13 ((R 13) + sign_extend (m := 64) (0x008#12))) Mt) :
    MW live Xs ns img S Q 0x80006c10#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c10#64 0x00868693#32], term := none }] : List BBlock) [13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [13])))) rfl hk

theorem mst_80006c14 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 15) + sign_extend (m := 64) (0xff8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0xff8#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006c18#64 R (writeLog Mt [(((R 15) + sign_extend (m := 64) (0xff8#12)).toNat, 8, (R 16))])) :
    MW live Xs ns img S Q 0x80006c14#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c14#64 0xff07bc23#32], term := none }] : List BBlock) [15, 16] [] [] (accAddrs ((R 15) + sign_extend (m := 64) (0xff8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c18 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15).toNat < (R 12).toNat → MW live Xs ns img S Q 0x80006c08#64 R Mt) (hF : ¬ ((R 15).toNat < (R 12).toNat) → MW live Xs ns img S Q 0x80006c1c#64 R Mt) :
    MW live Xs ns img S Q 0x80006c18#64 R Mt := by
  by_cases hc : (R 15).toNat < (R 12).toNat
  · exact
    mw_step ([⟨[], some (⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU true, 15, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bltu _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU false, 15, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [12, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bltu _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006c1c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c20#64 (upd R 12 ((R 12) + sign_extend (m := 64) (0xfff#12))) Mt) :
    MW live Xs ns img S Q 0x80006c1c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c1c#64 0xfff60613#32], term := none }] : List BBlock) [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem mst_80006c20 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c24#64 (upd R 12 ((R 12) - (R 14))) Mt) :
    MW live Xs ns img S Q 0x80006c20#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c20#64 0x40e60633#32], term := none }] : List BBlock) [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 14])))) rfl hk

theorem mst_80006c24 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c28#64 (upd R 12 ((R 12) &&& sign_extend (m := 64) (0xff8#12))) Mt) :
    MW live Xs ns img S Q 0x80006c24#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c24#64 0xff867613#32], term := none }] : List BBlock) [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem mst_80006c28 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c2c#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x008#12))) Mt) :
    MW live Xs ns img S Q 0x80006c28#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c28#64 0x00858593#32], term := none }] : List BBlock) [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem mst_80006c2c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c30#64 (upd R 14 ((R 14) + sign_extend (m := 64) (0x008#12))) Mt) :
    MW live Xs ns img S Q 0x80006c2c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c2c#64 0x00870713#32], term := none }] : List BBlock) [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem mst_80006c30 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c34#64 (upd R 11 ((R 11) + (R 12))) Mt) :
    MW live Xs ns img S Q 0x80006c30#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c30#64 0x00c585b3#32], term := none }] : List BBlock) [11, 12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 12])))) rfl hk

theorem mst_80006c34 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c38#64 (upd R 14 ((R 14) + (R 12))) Mt) :
    MW live Xs ns img S Q 0x80006c34#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c34#64 0x00c70733#32], term := none }] : List BBlock) [12, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [12, 14])))) rfl hk

theorem mst_80006c38 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 14).toNat < (R 17).toNat → MW live Xs ns img S Q 0x80006c48#64 R Mt) (hF : ¬ ((R 14).toNat < (R 17).toNat) → MW live Xs ns img S Q 0x80006c3c#64 R Mt) :
    MW live Xs ns img S Q 0x80006c38#64 R Mt := by
  by_cases hc : (R 14).toNat < (R 17).toNat
  · exact
    mw_step ([⟨[], some (⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU true, 14, 17, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bltu _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU false, 14, 17, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bltu _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006c3c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : MW live Xs ns img S Q (R 1) R Mt) :
    MW live Xs ns img S Q 0x80006c3c#64 R Mt :=
  mw_step ([⟨[], some (⟨0x80006c3c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c40 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c44#64 (upd R 14 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    MW live Xs ns img S Q 0x80006c40#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c40#64 0x00050713#32], term := none }] : List BBlock) [10, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [10, 14])))) rfl hk

theorem mst_80006c44 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 17).toNat ≤ (R 10).toNat → MW live Xs ns img S Q 0x80006c3c#64 R Mt) (hF : ¬ ((R 17).toNat ≤ (R 10).toNat) → MW live Xs ns img S Q 0x80006c48#64 R Mt) :
    MW live Xs ns img S Q 0x80006c44#64 R Mt := by
  by_cases hc : (R 17).toNat ≤ (R 10).toNat
  · exact
    mw_step ([⟨[], some (⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU true, 10, 17, 0x1ff8#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [10, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bgeu _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU false, 10, 17, 0x1ff8#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [10, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bgeu _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006c48 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c4c#64 (upd R 15 (ldvf .lbu img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c48#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c48#64 0x0005c783#32], term := none }] : List BBlock) [11, 15] [bytesAt img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins1_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [11, 15])))) rfl hk

theorem mst_80006c4c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c50#64 (upd R 14 ((R 14) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006c4c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c4c#64 0x00170713#32], term := none }] : List BBlock) [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem mst_80006c50 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c54#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006c50#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c50#64 0x00158593#32], term := none }] : List BBlock) [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem mst_80006c54 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOKb ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1, S b)
    (hk : MW live Xs ns img S Q 0x80006c58#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfff#12)).toNat, 1, (R 15))])) :
    MW live Xs ns img S Q 0x80006c54#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c54#64 0xfef70fa3#32], term := none }] : List BBlock) [14, 15] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c58 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 17) ≠ (R 14) → MW live Xs ns img S Q 0x80006c48#64 R Mt) (hF : ¬ ((R 17) ≠ (R 14)) → MW live Xs ns img S Q 0x80006c5c#64 R Mt) :
    MW live Xs ns img S Q 0x80006c58#64 R Mt := by
  by_cases hc : (R 17) ≠ (R 14)
  · exact
    mw_step ([⟨[], some (⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE true, 17, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE false, 17, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [14, 17] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006c5c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : MW live Xs ns img S Q (R 1) R Mt) :
    MW live Xs ns img S Q 0x80006c5c#64 R Mt :=
  mw_step ([⟨[], some (⟨0x80006c5c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c60 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c64#64 (upd R 13 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c60#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c60#64 0x0005b683#32], term := none }] : List BBlock) [11, 13] [bytesAt img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem mst_80006c64 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c68#64 (upd R 5 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c64#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c64#64 0x0085b283#32], term := none }] : List BBlock) [5, 11] [bytesAt img ((R 11) + sign_extend (m := 64) (0x008#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 5 ∈ [5, 11])))) rfl hk

theorem mst_80006c68 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c6c#64 (upd R 31 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c68#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c68#64 0x0105bf83#32], term := none }] : List BBlock) [11, 31] [bytesAt img ((R 11) + sign_extend (m := 64) (0x010#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 31 ∈ [11, 31])))) rfl hk

theorem mst_80006c6c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c70#64 (upd R 30 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c6c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c6c#64 0x0185bf03#32], term := none }] : List BBlock) [11, 30] [bytesAt img ((R 11) + sign_extend (m := 64) (0x018#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 30 ∈ [11, 30])))) rfl hk

theorem mst_80006c70 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c74#64 (upd R 29 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c70#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c70#64 0x0205be83#32], term := none }] : List BBlock) [11, 29] [bytesAt img ((R 11) + sign_extend (m := 64) (0x020#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 29 ∈ [11, 29])))) rfl hk

theorem mst_80006c74 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x028#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c78#64 (upd R 28 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c74#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c74#64 0x0285be03#32], term := none }] : List BBlock) [11, 28] [bytesAt img ((R 11) + sign_extend (m := 64) (0x028#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 28 ∈ [11, 28])))) rfl hk

theorem mst_80006c78 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c7c#64 (upd R 6 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x030#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c78#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c78#64 0x0305b303#32], term := none }] : List BBlock) [6, 11] [bytesAt img ((R 11) + sign_extend (m := 64) (0x030#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 6 ∈ [6, 11])))) rfl hk

theorem mst_80006c7c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x038#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x038#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c80#64 (upd R 16 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x038#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c7c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c7c#64 0x0385b803#32], term := none }] : List BBlock) [11, 16] [bytesAt img ((R 11) + sign_extend (m := 64) (0x038#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 16 ∈ [11, 16])))) rfl hk

theorem mst_80006c80 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006c84#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0x000#12)).toNat, 8, (R 13))])) :
    MW live Xs ns img S Q 0x80006c80#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c80#64 0x00d73023#32], term := none }] : List BBlock) [13, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0x000#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c84 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006c88#64 (upd R 13 (ldvf .ld img ((R 11) + sign_extend (m := 64) (0x040#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006c84#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c84#64 0x0405b683#32], term := none }] : List BBlock) [11, 13] [bytesAt img ((R 11) + sign_extend (m := 64) (0x040#12)).toNat 8] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins8_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem mst_80006c88 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c8c#64 (upd R 14 ((R 14) + sign_extend (m := 64) (0x048#12))) Mt) :
    MW live Xs ns img S Q 0x80006c88#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c88#64 0x04870713#32], term := none }] : List BBlock) [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem mst_80006c8c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfc0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfc0#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006c90#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfc0#12)).toNat, 8, (R 5))])) :
    MW live Xs ns img S Q 0x80006c8c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c8c#64 0xfc573023#32], term := none }] : List BBlock) [5, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfc0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c90 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006c94#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xff8#12)).toNat, 8, (R 13))])) :
    MW live Xs ns img S Q 0x80006c90#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c90#64 0xfed73c23#32], term := none }] : List BBlock) [13, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c94 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfc8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfc8#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006c98#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfc8#12)).toNat, 8, (R 31))])) :
    MW live Xs ns img S Q 0x80006c94#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c94#64 0xfdf73423#32], term := none }] : List BBlock) [14, 31] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfc8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006c98 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006c9c#64 (upd R 13 ((R 12) - (R 14))) Mt) :
    MW live Xs ns img S Q 0x80006c98#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c98#64 0x40e606b3#32], term := none }] : List BBlock) [12, 13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [12, 13, 14])))) rfl hk

theorem mst_80006c9c {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfd0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfd0#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006ca0#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfd0#12)).toNat, 8, (R 30))])) :
    MW live Xs ns img S Q 0x80006c9c#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006c9c#64 0xfde73823#32], term := none }] : List BBlock) [14, 30] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfd0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006ca0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfd8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfd8#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006ca4#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfd8#12)).toNat, 8, (R 29))])) :
    MW live Xs ns img S Q 0x80006ca0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ca0#64 0xfdd73c23#32], term := none }] : List BBlock) [14, 29] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfd8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006ca4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfe0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfe0#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006ca8#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfe0#12)).toNat, 8, (R 28))])) :
    MW live Xs ns img S Q 0x80006ca4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ca4#64 0xffc73023#32], term := none }] : List BBlock) [14, 28] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfe0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006ca8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xfe8#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfe8#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006cac#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfe8#12)).toNat, 8, (R 6))])) :
    MW live Xs ns img S Q 0x80006ca8#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ca8#64 0xfe673423#32], term := none }] : List BBlock) [6, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfe8#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006cac {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOK ((R 14) + sign_extend (m := 64) (0xff0#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xff0#12)).toNat 8, S b)
    (hk : MW live Xs ns img S Q 0x80006cb0#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xff0#12)).toNat, 8, (R 16))])) :
    MW live Xs ns img S Q 0x80006cac#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cac#64 0xff073823#32], term := none }] : List BBlock) [14, 16] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xff0#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006cb0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006cb4#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x048#12))) Mt) :
    MW live Xs ns img S Q 0x80006cb0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cb0#64 0x04858593#32], term := none }] : List BBlock) [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem mst_80006cb4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15).toInt < (R 13).toInt → MW live Xs ns img S Q 0x80006c60#64 R Mt) (hF : ¬ ((R 15).toInt < (R 13).toInt) → MW live Xs ns img S Q 0x80006cb8#64 R Mt) :
    MW live Xs ns img S Q 0x80006cb4#64 R Mt := by
  by_cases hc : (R 15).toInt < (R 13).toInt
  · exact
    mw_step ([⟨[], some (⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT true, 15, 13, 0x1fac#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT false, 15, 13, 0x1fac#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [13, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006cb8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bfc#64 R Mt) :
    MW live Xs ns img S Q 0x80006cb8#64 R Mt :=
  mw_step ([⟨[], some (⟨0x80006cb8#64, 0xf45ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf4#8, .j, 0, 0, 0x0#13, 0x1fff44#21, 0#12⟩ : TInstr)⟩] : List BBlock) [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006cbc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006cc0#64 (upd R 13 (ldvf .lbu img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006cbc#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cbc#64 0x0005c683#32], term := none }] : List BBlock) [11, 13] [bytesAt img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins1_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem mst_80006cc0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006cc4#64 (upd R 14 ((R 14) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006cc0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cc0#64 0x00170713#32], term := none }] : List BBlock) [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem mst_80006cc4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006cc8#64 (upd R 15 ((R 14) &&& sign_extend (m := 64) (0x007#12))) Mt) :
    MW live Xs ns img S Q 0x80006cc4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cc4#64 0x00777793#32], term := none }] : List BBlock) [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem mst_80006cc8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOKb ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1, S b)
    (hk : MW live Xs ns img S Q 0x80006ccc#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfff#12)).toNat, 1, (R 13))])) :
    MW live Xs ns img S Q 0x80006cc8#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cc8#64 0xfed70fa3#32], term := none }] : List BBlock) [13, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006ccc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006cd0#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006ccc#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ccc#64 0x00158593#32], term := none }] : List BBlock) [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem mst_80006cd0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15) = (0#64) → MW live Xs ns img S Q 0x80006bec#64 R Mt) (hF : ¬ ((R 15) = (0#64)) → MW live Xs ns img S Q 0x80006cd4#64 R Mt) :
    MW live Xs ns img S Q 0x80006cd0#64 R Mt := by
  by_cases hc : (R 15) = (0#64)
  · exact
    mw_step ([⟨[], some (⟨0x80006cd0#64, 0xf0078ee3#32, 0xe3#8, 0x8e#8, 0x07#8, 0xf0#8, .br bop.BEQ true, 15, 0, 0x1f1c#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006cd0#64, 0xf0078ee3#32, 0xe3#8, 0x8e#8, 0x07#8, 0xf0#8, .br bop.BEQ false, 15, 0, 0x1f1c#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006cd4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : LdOK ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1)
    (hin : ∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1, Xs ≤ b ∧ b < Xs + ns)
    (hk : MW live Xs ns img S Q 0x80006cd8#64 (upd R 13 (ldvf .lbu img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat)) Mt) :
    MW live Xs ns img S Q 0x80006cd4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cd4#64 0x0005c683#32], term := none }] : List BBlock) [11, 13] [bytesAt img ((R 11) + sign_extend (m := 64) (0x000#12)).toNat 1] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact ⟨hea, lpins1_fn (fun b hb => srcRead hD (hin b hb))⟩)
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 13 ∈ [11, 13])))) rfl hk

theorem mst_80006cd8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006cdc#64 (upd R 14 ((R 14) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006cd8#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cd8#64 0x00170713#32], term := none }] : List BBlock) [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem mst_80006cdc {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006ce0#64 (upd R 15 ((R 14) &&& sign_extend (m := 64) (0x007#12))) Mt) :
    MW live Xs ns img S Q 0x80006cdc#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006cdc#64 0x00777793#32], term := none }] : List BBlock) [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem mst_80006ce0 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hea : StOKb ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat)
    (hS : ∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1, S b)
    (hk : MW live Xs ns img S Q 0x80006ce4#64 R (writeLog Mt [(((R 14) + sign_extend (m := 64) (0xfff#12)).toNat, 1, (R 13))])) :
    MW live Xs ns img S Q 0x80006ce0#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ce0#64 0xfed70fa3#32], term := none }] : List BBlock) [13, 14] [] [] (accAddrs ((R 14) + sign_extend (m := 64) (0xfff#12)).toNat 1) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact hea)
    (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem mst_80006ce4 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006ce8#64 (upd R 11 ((R 11) + sign_extend (m := 64) (0x001#12))) Mt) :
    MW live Xs ns img S Q 0x80006ce4#64 R Mt :=
  mw_step ([{ body := [mkLine 0x80006ce4#64 0x00158593#32], term := none }] : List BBlock) [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem mst_80006ce8 {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hT : (R 15) ≠ (0#64) → MW live Xs ns img S Q 0x80006cbc#64 R Mt) (hF : ¬ ((R 15) ≠ (0#64)) → MW live Xs ns img S Q 0x80006cec#64 R Mt) :
    MW live Xs ns img S Q 0x80006ce8#64 R Mt := by
  by_cases hc : (R 15) ≠ (0#64)
  · exact
    mw_step ([⟨[], some (⟨0x80006ce8#64, 0xfc079ae3#32, 0xe3#8, 0x9a#8, 0x07#8, 0xfc#8, .br bop.BNE true, 15, 0, 0x1fd4#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    mw_step ([⟨[], some (⟨0x80006ce8#64, 0xfc079ae3#32, 0xe3#8, 0x9a#8, 0x07#8, 0xfc#8, .br bop.BNE false, 15, 0, 0x1fd4#13, 0x0#21, 0#12⟩ : TInstr)⟩] : List BBlock) [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem mst_80006cec {live : Nat → Prop} {Xs ns : Nat} {img : Nat → BitVec 8} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ mText, live p.1)
    (hk : MW live Xs ns img S Q 0x80006bec#64 R Mt) :
    MW live Xs ns img S Q 0x80006cec#64 R Mt :=
  mw_step ([⟨[], some (⟨0x80006cec#64, 0xf01ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xf0#8, .j, 0, 0, 0x0#13, 0x1fff00#21, 0#12⟩ : TInstr)⟩] : List BBlock) [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hD hLD => by have hm := memcpyLoaded_of_text hm; unfold ChainFacts; chain_facts hm with "Vsa.Sim.Code.memcpy_at_")
    (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

end VsaIris.Memcpy
