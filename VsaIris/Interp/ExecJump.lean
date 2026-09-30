import VsaIris.Interp.ArmCore
import VsaIris.Interp.ExecDispOf

/-!
`break` and `continue`: one reflected segment each and one Wp-generic core; the total and
partial statement specs follow from the core through `execDispT_of` / `execDispP_of`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr


/-- The reflected `break`/`continue` arm (statement kind `tag`) to the return. -/
def JumpRun (tag : Nat) (status : Status) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s ret v8 v9 v18 v19 : BitVec 64},
    ExecFrameGeom s → 0x80000000 ≤ aS.toNat → aS.toNat + 4 ≤ 0x100000000 →
    aS.toNat + 4 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aS.toNat → ret.toNat % 4 = 0 →
    R 8 = aS → R 16 = 8#64 → R 14 = 0x80019fb8#64 → R 2 = execSP s →
    ldv .lw m aS.toNat = BitVec.ofNat 64 tag → ldv .lwu m aS.toNat = BitVec.ofNat 64 tag →
    ExecSaved Mt s ret v8 v9 v18 v19 →
    (∀ R', R' 1 = ret → ExecRet R R' s v8 v9 v18 v19 status →
      IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q ret R' Mt) →
    IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt

section Segs
open Vsa.Sim

#ix_seg ExecBrk_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 4 ≤ 0x100000000)
    (hx3 : aS.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (hal : ret.toNat % 4 = 0)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 7#64) (hku : ldv .lwu m aS.toNat = 7#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by ix_run hlive using [h8, h16, h14, h2, hk, hku, hRA, hS0, hS1, hS2, hS3, hsf, hal]

#ix_seg ExecCont_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 4 ≤ 0x100000000)
    (hx3 : aS.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (hal : ret.toNat % 4 = 0)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 8#64) (hku : ldv .lwu m aS.toNat = 8#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m (stmtView aS.toNat 4) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by ix_run hlive using [h8, h16, h14, h2, hk, hku, hRA, hS0, hS1, hS2, hS3, hsf, hal]

end Segs

set_option hygiene false in
macro "jump_run " seg:ident : tactic => `(tactic| (
  intro live hlive Q m Mt R aS s ret v8 v9 v18 v19 fg hx1 hx2 hx3 hal h8 h16 h14 h2 hk hku hsv hk'
  have hoff := execSP_offF (s := s) fg.sf (by have := fg.hi; omega)
  refine $seg (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive fg.sf fg.lo fg.hi fg.al
    hx1 hx2 hx3 hal h8 h16 h14 h2 hk hku ?_ ?_ ?_ ?_ ?_
    (fun h => absurd h (by rw [h16]; decide)) ?_
  · rw [hoff _ (by decide)]; exact hsv.ra
  · rw [hoff _ (by decide)]; exact hsv.s0
  · rw [hoff _ (by decide)]; exact hsv.s1
  · rw [hoff _ (by decide)]; exact hsv.s2
  · rw [hoff _ (by decide)]; exact hsv.s3
  intro _
  refine hk' _ (by ix_reg) ⟨by ix_reg; exact execSP_restore s, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg, fun x hx => ?_, by ix_reg; rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg))

theorem jumpRun_brk : JumpRun 7 .brk := by jump_run ExecBrk_run
theorem jumpRun_cont : JumpRun 8 .cont := by jump_run ExecCont_run

/-- `break` and `continue`. -/
inductive JumpK | brk | cont

@[reducible] def JumpK.stmt : JumpK → Stmt | .brk => .brk | .cont => .cont
@[reducible] def JumpK.status : JumpK → Status | .brk => .brk | .cont => .cont
@[reducible] def JumpK.tag : JumpK → Nat | .brk => 7 | .cont => 8
theorem JumpK.run : ∀ j : JumpK, JumpRun j.tag j.status
  | .brk => jumpRun_brk | .cont => jumpRun_cont

theorem JumpK.node {m : Mem} {P : Nat → Prop} {aS : BitVec 64} (j : JumpK)
    (h : StmtReprWithin m P aS.toNat j.stmt) (hg : ∀ k, P k → ReadOK k) :
    StmtNode m P aS j.tag 4 := by
  cases j <;> cases h <;> exact stmtNode_of hg ‹_› ‹_› (by decide) (Or.inl rfl) (fun j h1 h2 => by omega)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem jumpCore (j : JumpK) (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (vsaModel live))
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat}
    (Φ : Nat × String → IProp GF) (ρ : Regime) (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64) :
    execDispPre N L Room inp ρ st d env j.stmt aS aE aRet s R Mt ret v8 v9 v18 v19 ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st d j.stmt j.status aRet s R ret v8 v9 v18 v19 ⊢
      Wp.W Φ := by
  unfold execDispPre
  iintro ⟨⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hn := j.node hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(stackScratch (execSP s) (execNeed j.stmt d - 176) ∗
      slot24 aRet.toNat ∗ world N L Room inp ρ st d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st d j.stmt j.status aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine j.run hlive hfg hn.lo hn.hi hn.off hf.ral hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp
    hn.kind hn.kindu hf.saved fun R' hra hret => swp_closeF Wp ?_
  unfold F'
  refine .trans ?_ (execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) Wp
    (ρ := ρ) (st' := st) (status := j.status) (aRet := aRet) (R := R) (R' := R') (Mt := Mt)
    (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (pc := ret) hf.stack rfl hra hret)
  have hsr : statusRet (GF := GF) N aRet.toNat j.status = slot24 aRet.toNat := by cases j <;> rfl
  rw [hsr]
  iintro ⟨⟨Hst, Hslot, Hw, HK⟩, Hms⟩
  iframe Hms Hst Hw HK Hslot

theorem jumpT (j : JumpK) (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} (D : ExecSCost st d env j.stmt st j.status 0) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env j.stmt st j.status 0 D :=
  execDispT_of (GF := GF) D (jumpCore j hlive (twpW _))

theorem jumpP (j : JumpK) (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat}
    (hE : ExecS st d env j.stmt st j.status) :
    ⊢ execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env j.stmt :=
  execDispP_of (GF := GF) hE (jumpCore j hlive (wpW _))

end

end VsaIris.Interp
