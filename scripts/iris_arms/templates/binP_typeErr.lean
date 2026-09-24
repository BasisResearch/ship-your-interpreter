#ix_piece {ARM}P_{ROW}1 from {ARM}P_p2 at {K} by
  -- {ROWDOC}: the type error's first run, to `value_kind_name`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st2 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.binary {OP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe IH; iexact HE
  intro F'
{REFINE}
  intros
  apply swp_closeM
  intro Mt3 hMt3
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE⟩, Hms⟩

#ix_piece {ARM}P_{ROW}2 from {ARM}P_{ROW}1 by
  -- `value_kind_name` on the operand's copy at `sp + 64`
  have hS64 : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have hw64 : ldv .ld Mt3 (s + 18446744073709550528#64 + 64#64).toNat = {W0} := by
    {HW64}
  iapply ms_callKindName (wpW _) hvk (i := 0x{VKN})
    (jalx_{VKN} live (fun p hp => hlive _ (interp_code_{VKN} p hp)))
    interp_code_{VKN} (by decide) (v := {V}) hS64
    (evalSlotGeom hsg hneed (o := 64) (by decide) (by decide)) hw64 {HTAG}
  iframe Hcode Hms
  isplitl []
  · ipureintro; ix_reg
  iintro %R4 %M4 %hkeep4 %hk4 %hag4 Hms

#ix_piece {ARM}P_{ROW}3 from {ARM}P_{ROW}2 by
  -- stage `runtime_error(in, line, "operand of '%s' must be an int, got %s", op, name)`
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
{RTREFINE}
  intros
  apply swp_closeM
  intro Mt5 hMt5
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #HE⟩, Hms⟩
  ihave Hk := and_elim_r $$ Hk
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval (wpW _) hE (i := 0x{RT})
    (jalx_{RT} live (fun p hp => hlive _ (interp_code_{RT} p hp))) interp_code_{RT}
    (Sro := rodataDom) (rd := rodataByte) (fmt := 0x800193f0#64) (x1 := 0x{OPNAME}#64)
    (x2 := kindNamePtr {V})
    (readable_rodata_fmt (fun hro => operand_fmt hro (rodata_cstrV hro 0x{OPNAME}#64 {OPLEN} (by decide) (by decide))
      (kindName_cstr hro {V})))
    hsg (evalNeed_binary_rtErr {OP} l r d)
  iframe Hcode HE Hrd Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨?_, rfl, by ix_reg, by ix_reg, ?_, by ix_keep [hkeep4, hkeep2, hkeep1]⟩
    · ix_keep [hkeep4, hkeep2, hkeep1]
    · ix_reg; exact hk4
  iintro HA
  iapply Hk
  iframe HA Hslot
