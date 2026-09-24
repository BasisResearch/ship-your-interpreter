import VsaIris.Interp.ExecBlock
import VsaIris.Interp.ExecLoops

/-!
# `{ARM}`, total mode (family `execBlock`, lane E5)

`caseT_{ARM}`: `exec_stmt` on `.block ss` meets its dispatch-point spec
(`execDispT_body`), given `env_new`'s spec and lane G's block loop motive
`blockSeqT_body` for the statements: the dispatch to `jal env_new`
(`BlockArm_run1`), the new frame (`ms_callEnvNewW`), the count test; an empty
block leaves through the shared exit (`BlockArm_runE`, `wp_execEpi`), a
nonempty one runs the loop from its head `0x800041a4` (`BlockArm_runL`,
`blockSeqT_body`) and leaves the same way.
Template: `scripts/iris_arms/templates/execBlock_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

theorem caseT_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {st : St} {d env : Nat} {ss : List Stmt} {store' : Store} {inner : Nat} {st' : St}
    {status : Status} {n : Nat}
    (halloc : st.store.allocFrame (some env) = (store', inner))
    (Dseq : ExecSeqCost ⟨store', st.out⟩ d inner ss st' status n)
    (hseq : blockSeqT_body (GF := GF) live N vsaLayoutP vsaRoomB inp ⟨store', st.out⟩ d inner ss st'
      status n Dseq)
    (hen : ⊢ envNewSpec (GF := GF) (twpW (vsaModel live)) N) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp st d env (.block ss) st'
        status (envBytes + n) (.block st d env ss store' inner st' status n halloc Dseq) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨arr, count, hn, hcnt, hlen, hbn⟩ := blockNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have hsz : st.store.frames.size = inner := congrArg Prod.snd halloc
  have hst' : (st.store.allocFrame (some env)).1 = store' := congrArg Prod.fst halloc
  have hbig : envNewNeed ≤ execNeed (.block ss) d - 176 := by
    have := Stmt.stackNeed_ge (.block ss); unfold execNeed stackBudget evalFrame envNewNeed allocHeadroom
    unfold execFrame at this; omega
  rw [show k + (envBytes + n) = k + n + envBytes by omega]
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.block ss) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp (.counted (k + n + envBytes)) st d ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k) st' d
        (.block ss) status aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine BlockArm_run1 (s := s) hlive hn.lo hn.hi hn.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hn.kind
    hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- env_new
  have h12 : R1 2 = execSP s := by subst hR1; ix_reg; exact hf.regs.sp
  have h110 : R1 10 = aE := by subst hR1; ix_reg; exact hf.regs.s3
  have hle' : execNeed (.block ss) d - 176 ≤ (execSP s).toNat := by
    rw [hfg.sf]; have := hf.stack.le; omega
  ihave ⟨Hsl, Hst⟩ := stackScratch_narrow (s := execSP s) hle' hbig $$ Hst
  rw [← h12]
  ihave Hen := hen
  iapply ms_callEnvNewW (N := N) (twpW _) (i := 0x80004190)
    (jalx_80004190 live (fun p hp => hlive _ (interp_code_80004190 p hp)))
    interp_code_80004190 (by decide) (k := k + n) (st := st) (d := d) (env := env) (R := R1)
    ⟨by rw [h12, hfg.sf]; have := hfg.lo; unfold htifLo envNewNeed allocHeadroom; omega,
      by rw [h12, hfg.sf]; have := hfg.hi; omega, by rw [h12, hfg.sf]; have := hfg.al; omega⟩
  iframe Hen Hcode Hms Hst Hw
  isplitl []
  · imodintro; rw [h110]; iexact Hfb
  iintro %R2 %hk2 Hst Hw #Hnew Hms
  rw [hst', hsz]
  rw [h12]
  ihave Hst := stackScratch_widen (s := execSP s) hle' hbig $$ [Hsl Hst]
  · iframe Hsl Hst
  have hk2' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R2 1 (BitVec.ofNat 64 (0x80004190 + 4))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    subst hR1
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [hk2 _ (by decide) (by decide)]; ix_reg)
  have h22 : upd R2 1 (BitVec.ofNat 64 (0x80004190 + 4)) 2 = execSP s := by
    ix_reg; rw [hk2 _ (by decide) (by decide)]; exact h12
  have h28 : upd R2 1 (BitVec.ofNat 64 (0x80004190 + 4)) 8 = aS := by
    ix_reg; rw [hk2 _ (by decide) (by decide)]; subst hR1; ix_reg; exact hf.regs.s0
  have hsv1 : ExecSaved Mt1 s ret v8 v9 v18 v19 := by rw [hMt1]; exact hf.saved
  rcases Nat.eq_zero_or_pos count with h0 | hpos
  · -- the empty block
    subst h0
    have hss : ss = [] := List.eq_nil_of_length_eq_zero hlen
    subst hss
    cases Dseq
    simp only [Nat.add_zero]
    iapply wp_swpF (twpW _) (text := interpText ++ dataOf m (stmtView aS.toNat 20))
      (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed (.block []) d - 176) ∗
        slot24 aRet.toNat ∗ world N vsaLayoutP vsaRoomB inp (.counted k) ⟨store', st.out⟩ d ∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k)
          ⟨store', st.out⟩ d (.block []) .normal aRet s R ret v8 v9 v18 v19))
    rotate_left
    · iframe Hms Hcode Hst Hslot Hw HK
      iapply roOwn_data hn.view $$ [Hcode Hro]
      iframe Hcode Hro
    intro F'
    refine BlockArm_runE (s := s) hlive hn.lo hn.hi hn.off h28 hcnt ?_
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    have hepi := wp_execEpi (N := N) (L := vsaLayoutP) (Room := vsaRoomB) (inp := inp) hlive (twpW _)
      (Φ := Φ) (ρ := .counted k) (st' := ⟨store', st.out⟩) (d := d) (sm := .block [])
      (status := .normal) (aRet := aRet) (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18)
      (v19 := v19) (R0 := R) (R := R3) (Mt := Mt3) hf.stack hf.ral
      (by subst hR3; ix_reg; exact h22) (by subst hR3; ix_reg; rfl) (by rw [hMt3]; exact hsv1)
      (by subst hR3; repeat (first | exact hk2' | refine KeepRegs.upd ?_ (by decide) _))
    simp only [statusRet] at hepi
    unfold F'
    iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
    iapply hepi
    iframe Hcode Hms Hst Hslot Hw HK
  · -- the statement loop
    have hbn := hbn hpos
    have hne : ss ≠ [] := fun h => by subst h; simp at hlen; omega
    iapply wp_swpF (twpW _) (text := interpText ++ dataOf m (stmtView aS.toNat 20))
      (F := iprop(codeRes ∗ roOn P m ∗ frameAt inner (R2 10).toNat ∗
        stackScratch (execSP s) (execNeed (.block ss) d - 176) ∗
        slot24 aRet.toNat ∗ world N vsaLayoutP vsaRoomB inp (.counted (k + n)) ⟨store', st.out⟩ d ∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k)
          st' d (.block ss) status aRet s R ret v8 v9 v18 v19))
    rotate_left
    · iframe Hms Hcode Hro Hnew Hst Hslot Hw HK
      iapply roOwn_data hn.view $$ [Hcode Hro]
      iframe Hcode Hro
    intro F'
    refine BlockArm_runL (s := s) (count := count) hlive hn.lo hn.hi hn.off h28 hcnt ?_ ?_
    · intro hc
      exfalso
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
      rw [ofNat_toInt_small hbn.small] at hc
      simp at hc; omega
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    have hh : BlockHead R3 s aS (BitVec.ofNat 64 inp) aRet (R2 10) 0 := by
      subst hR3
      refine ⟨by ix_reg; exact h22, by ix_reg; exact h28, ?_, ?_, by ix_reg, by ix_reg; try rfl⟩
      · ix_reg; rw [hk2 _ (by decide) (by decide)]; subst hR1; ix_reg; exact hf.regs.s1
      · ix_reg; rw [hk2 _ (by decide) (by decide)]; subst hR1; ix_reg; exact hf.regs.s2
    have hk3 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R3 := by
      subst hR3; repeat (first | exact hk2' | refine KeepRegs.upd ?_ (by decide) _)
    have hall : ∀ x ∈ ss, execNeed x d ≤ execNeed (.block ss) d - 176 ∧
        x.bodiesBound perCallBudget = true := fun x hx => ⟨by
      have := execNeed_block hx d; unfold execFrame at this; omega,
      Stmt.bodiesBound_of_mem hf.bodies hx⟩
    unfold F'
    refine .trans ?_ (hseq Φ k 0 count aS (BitVec.ofNat 64 arr) aRet (R2 10) s R3 Mt3 m P ss
      (execNeed (.block ss) d - 176) (fun M => ExecSaved M s ret v8 v9 v18 v19)
      (execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ (.counted k)
          st' d (.block ss) status aRet s R ret v8 v9 v18 v19)
      hne List.drop_zero.symm hbn hh hfg (hf.stack.lower hneed hfg.sf) hall hf.slot
      (by rw [hMt3]; exact hsv1)
      (fun M v hM => hM.store v (by have := hfg.lo; omega) (by
        rw [execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega) 8 (by decide)]; omega)))
    iintro ⟨⟨#Hcode, #Hro, #Hnew, Hst, Hslot, Hw, HK⟩, Hms⟩
    iframe HK Hms Hcode Hro Hnew Hst Hslot Hw
    have hsub : ∀ x ∈ [20, 21, 22, 23, 24, 25, 26, 27], x ∈ calleeSaved := by decide
    iintro %R' %Mt' %⟨hk, h10, hinv⟩ HK Hms Hst Hret Hw
    iapply wp_execEpi hlive (twpW _) hf.stack hf.ral ((hk 2 (by decide)).trans hh.sp) h10 hinv
      (fun x hx => (hk x (hsub x hx)).trans (hk3 x hx))
    iframe Hcode Hms Hst Hret Hw HK

end VsaIris.Interp
