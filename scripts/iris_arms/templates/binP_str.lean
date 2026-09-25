
#ix_piece {ARM}P_{ROW}1 from {ARM}P_p2 at {K} by
  -- run 3: operator dispatch, the string/string test, to `strcmp`
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
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗
      □ valOf N (.str x) w0 w1 w2 ∗ □ valOf N (.str y) u0 u1 u2))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE Hv1 Hv2]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe IH HE Hv1; iexact Hv2
  intro F'
  refine {STRT}_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_ ?_ ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd; exact ofNat_lo32 htl
  · ix_fwd; exact ofNat_lo32 htr
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved Mt3 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt3]; ix_saved hsv2 using hoff
  have hop3 : ldv .ld Mt3 (s.toNat - 1088) = {TOK}#64 := by
    rw [hMt3]; e2_fwd hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE, #Hv1, #Hv2⟩, Hms⟩
  -- `strcmp(l, r)`: the sign class of the result
  ihave #Hsc0 := hsc
  ihave ⟨Hw, #Hbi⟩ := world_binImg N L Room inp _ _ d $$ Hw
  ihave #Hsc := strcmpOrdSpec_at (p := w1) (q := u1) (x := x) (y := y) $$ Hsc0
  unfold valOf
  icases Hv1 with ⟨%hx, #Hx⟩
  icases Hv2 with ⟨%hy, #Hy⟩
  iapply ms_callHelper (wpW _) (i := 0x{JSC})
    (jalx_{JSC} live (fun p hp => hlive _ (interp_code_{JSC} p hp)))
    interp_code_{JSC} (by decide) (clob := callerSaved)
    (pins := fun rv => rv 10 = w1 ∧ rv 11 = u1)
    (Pre := iprop(Newlib.binImg ∗ strAt w1.toNat x ∗ strAt u1.toNat y))
    (Post := fun rv' => iprop(⌜StrcmpSign (rv' 10) x y⌝))
  iframe Hsc Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep2], by ix_reg; ix_fwd⟩
  isplitl []
  · iframe Hbi Hx; iexact Hy
  iintro %R3 %hkeep3 %hsign Hms

#ix_piece {ARM}P_{ROW}2 from {ARM}P_{ROW}1 by
  -- run 4: the operator's bit of the sign, to `value_bool`
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
  refine {STRT}_run4 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_ ?_ ?_
  · ix_keep [hkeep3, hkeep2, hkeep1]
  · ix_keep [hkeep3, hkeep2, hkeep1]
  · exact hop3
  intros
  apply swp_closeM
  intro Mt4 hMt4
  have hsv4 : EvalSaved Mt4 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt4]; ix_saved hsv3 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE⟩, Hms⟩
  -- value_bool
  ihave Hvi := hvb $$ %sret %({ARGW})
  unfold valueBoolSpec
  iapply ms_callHelper (wpW _) (i := 0x{JVB})
    (jalx_{JVB} live (fun p hp => hlive _ (interp_code_{JVB} p hp)))
    interp_code_{JVB} (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep3, hkeep2, hkeep1], by ix_reg⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R5 %hkeep5 Hval Hms
  have hsum : (({ARGW}) != 0#64) = ({SUMB}) := {SUMPF} hsign
  rw [hsum]

#ix_piece {ARM}P_{ROW}3 from {ARM}P_{ROW}2 by
  -- run 5: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (valAt N sret.toNat {RES})
      (world N L Room inp .uncounted st2 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.binary {OP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE]
    · iframe Hcode Hro Hfb Hst Hval Hw; iexact Hk
    · iframe IH; iexact HE
  intro F'
  refine {STRT}_run5 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep5, hkeep3, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv4.ra
  · rw [hoff _ (by decide)]; exact hsv4.s0
  · rw [hoff _ (by decide)]; exact hsv4.s1
  · rw [hoff _ (by decide)]; exact hsv4.s2
  · rw [hoff _ (by decide)]; exact hsv4.s3
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, Hw, Hk⟩, #IH, #HE⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists st2, {RES}
  isplitl []
  · ipureintro; exact EvalE.binary st d env {OP} l r st1 st2 (.str x) (.str y) _ hEl hEr rfl
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep5, hkeep3, hkeep2, hkeep1]
