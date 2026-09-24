  iapply wp_swpF (twpW _) (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed ({SM}) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted k) st' d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st' d
        ({SM}) ({STATUS}) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hcode Hms Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine {ARM}_run2 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hepi := wp_execEpi (N := N) (L := L) (Room := Room) (inp := inp) hlive (twpW _)
    (Φ := Φ) (ρ := .counted k) (st' := st') (d := d) (sm := {SM}) (status := {STATUS})
    (aRet := aRet) (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (R0 := R)
    (R := R2) (Mt := Mt2) hf.stack hf.ral
    (by subst hR2 hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp)
    (by subst hR2; ix_reg; rfl)
    (by rw [hMt2]; exact hsv1)
    (by subst hR2; repeat (first | exact hk1 | refine KeepRegs.upd ?_ (by decide) _))
  simp only [statusRet] at hepi
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hepi
  iframe Hcode Hms Hst Hslot Hw HK
