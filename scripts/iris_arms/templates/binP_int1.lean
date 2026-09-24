#ix_piece {ARM}P_{ROW}1 from {ARM}P_p2 at {K} by
  -- run 3: operator dispatch, int/int checks, the sum
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
  refine {TRUN}_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_ ?_ ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd; exact hk0
  · ix_fwd; exact hk0'
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved Mt3 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt3]; ix_saved hsv2 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE⟩, Hms⟩
  -- {HELPERC}
  ihave Hvi := {HNAME} $$ %sret %({ARGW})
  unfold {HSPEC}
  iapply ms_callHelper (wpW _) (i := 0x{J3})
    (jalx_{J3} live (fun p hp => hlive _ (interp_code_{J3} p hp)))
    interp_code_{J3} (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep2, hkeep1], by ix_reg; ix_fwd⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  have hsum : {SUMEQ} := by {SUMPF}
  rw [hsum]

#ix_piece {ARM}P_{ROW}2 from {ARM}P_{ROW}1 by
  -- run 4: the epilogue
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
  refine {TRUN}_run4 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep3, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv3.ra
  · rw [hoff _ (by decide)]; exact hsv3.s0
  · rw [hoff _ (by decide)]; exact hsv3.s1
  · rw [hoff _ (by decide)]; exact hsv3.s2
  · rw [hoff _ (by decide)]; exact hsv3.s3
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
  · ipureintro; exact EvalE.binary st d env {OP} l r st1 st2 (.int a) (.int b) _ hEl hEr rfl
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3, hkeep2, hkeep1]


