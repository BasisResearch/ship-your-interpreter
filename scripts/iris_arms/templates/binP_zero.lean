#ix_piece {ARM}P_{ROW}1 from {ARM}P_p2 at {K} by
  -- the divisor is zero: `runtime_error(in, line, "{MSG}", 0, 0)`
  unfold valOf
  icases Hv1 with %⟨hw0, hw1⟩
  icases Hv2 with %⟨hu0, hu1⟩
  have hu0' : u1 = 0#64 := BitVec.eq_of_toInt_eq (by rw [hu1]; rfl)
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st2 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.binary {OP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗ errCtx inp))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [HE]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iexact HE
  intro F'
  refine {ARM}P_{ROW}_run (aX := aX) (s := s) (sret := sret) (w1 := w1) hlive hsf hs' hs2 hs3
    hx1 hx2 hx3 ?_ ?_ ?_ ?_ hn.op ?_ ?_ ?_ ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd; exact ofNat_lo32 hw0
  · ix_fwd; exact ofNat_lo32 hu0
  · ix_fwd; exact hu0'
  intros
  apply swp_closeM
  intro Mt3 hMt3
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #HE⟩, Hms⟩
  ihave Hk := and_elim_r $$ Hk
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval (wpW _) hE (i := 0x{RT})
    (jalx_{RT} live (fun p hp => hlive _ (interp_code_{RT} p hp))) interp_code_{RT}
    (Sro := rodataDom) (rd := rodataByte) (fmt := 0x{FMT}#64) (x1 := 0#64) (x2 := 0#64)
    (readable_rodata_fmt (fun hro => plain_fmt hro 0x{FMT}#64 {FLEN} (by decide) (by decide) (by decide) _))
    hsg (evalNeed_binary_rtErr {OP} l r d)
  iframe Hcode HE Hrd Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨?_, rfl, by ix_reg, by ix_reg, by ix_reg, by ix_keep [hkeep2, hkeep1]⟩
    ix_keep [hkeep2, hkeep1]
  iintro HA
  iapply Hk
  iframe HA Hslot
