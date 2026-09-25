
#ix_piece {ARM}P_ok1 from {ARM}P_p2 at 1 by
  -- run 3: operator dispatch and the operand copies, to `value_equal`
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
      □ valOf N lv w0 w1 w2 ∗ □ valOf N rv' u0 u1 u2))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE Hv1 Hv2]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe IH HE Hv1; iexact Hv2
  intro F'
  refine {ARM}T_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved Mt3 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt3]; ix_saved hsv2 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE, #Hv1, #Hv2⟩, Hms⟩

#ix_piece {ARM}P_ok2 from {ARM}P_ok1 by
  -- `value_equal(&l, &r)` on the copies at `sp + 64` and `sp + 32`
  have ha0 : ldv .ld Mt3 (s + 18446744073709550528#64 + 64#64).toNat = w0 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  have ha8 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 8) = w1 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  have ha16 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 16) = w2 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  have hb0 : ldv .ld Mt3 (s + 18446744073709550528#64 + 32#64).toNat = u0 := by
    rw [hMt3]; e2_fwd hoff
  have hb8 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 32#64).toNat + 8) = u1 := by
    rw [hMt3]; e2_fwd hoff
  have hb16 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 32#64).toNat + 16) = u2 := by
    rw [hMt3]; e2_fwd hoff
  have hSa : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have hSb : ∀ k, InExt ((s + 18446744073709550528#64 + 32#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 32 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have hab : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      ¬ InExt ((s + 18446744073709550528#64 + 32#64).toNat, 24) k := by
    intro k hk hk'; rw [hoff 64 (by decide)] at hk; rw [hoff 32 (by decide)] at hk'
    simp only [VsaIris.InExt] at hk hk'; omega
  have hne := evalNeed_binary_rtErr {OP} l r d
  unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at hne
  have g16 := evalCallGeom (nc := 16) (o := 0) hsg (by omega) (by decide) (by decide)
  ihave #Hcmp := hsc
  ihave ⟨Hw, #Hbi⟩ := world_binImg N L Room inp _ st2 d $$ Hw
  ihave ⟨%B, Hsto, Hwk⟩ := world_store N L Room inp _ st2 d $$ Hw
  ihave ⟨Hslack, Hs16⟩ := stackScratch_narrow (s := s + 18446744073709550528#64)
    (n := evalNeed (.binary {OP} l r) d - 1088) (m := 16) (by rw [hsf]; omega) (by omega) $$ Hst
  iapply ms_callValueEqual (wpW _) hve (i := 0x{JVE})
    (jalx_{JVE} live (fun p hp => hlive _ (interp_code_{JVE} p hp)))
    interp_code_{JVE} (by decide) (sp := s + 18446744073709550528#64) (st := st2.store) (B := B)
    hSa hSb hab
    (evalSlotGeom hsg hneed (o := 64) (by decide) (by decide))
    (evalSlotGeom hsg hneed (o := 32) (by decide) (by decide)) hni ha0 ha8 ha16 hb0 hb8 hb16
  iframe Hcode Hv1 Hv2 Hms Hsto Hcmp Hbi
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg, by ix_keep [hkeep2, hkeep1]⟩
  isplitl [Hs16]
  · unfold stackAt; iframe Hs16; ipureintro; exact g16.child
  iintro %R4 %M4 %hkeep4 %hr4 %hag4 Hms Hsto ⟨Hs16, -⟩
  ihave Hw := Hwk $$ Hsto
  ihave Hst := stackScratch_widen (s := s + 18446744073709550528#64)
    (n := evalNeed (.binary {OP} l r) d - 1088) (m := 16) (by rw [hsf]; omega) (by omega) $$ [Hslack Hs16]
  · iframe Hslack Hs16
  have hsv4 : EvalSaved M4 s ret (rv 8) (rv 9) (rv 18) (rv 19) := hsv3.agree fun k h1 h2 =>
    hag4 k (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)
      (by rw [hoff 32 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece {ARM}P_ok3 from {ARM}P_ok2 by
  -- run 4: to `value_bool`
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
  refine {ARM}T_run4 (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt5 hMt5
  have hsv5 : EvalSaved Mt5 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by rw [hMt5]; exact hsv4
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
  · ipureintro; exact ⟨by ix_keep [hkeep4, hkeep2, hkeep1], by {PINS}⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R6 %hkeep6 Hval Hms
  have hsum : (({ARGW}) != 0#64) = ({SUMB}) := by
    cases Value.equal lv rv' <;> decide
  rw [hsum]

#ix_piece {ARM}P_ok4 from {ARM}P_ok3 by
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
  refine {ARM}T_run5 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep6, hkeep4, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv5.ra
  · rw [hoff _ (by decide)]; exact hsv5.s0
  · rw [hoff _ (by decide)]; exact hsv5.s1
  · rw [hoff _ (by decide)]; exact hsv5.s2
  · rw [hoff _ (by decide)]; exact hsv5.s3
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
  · ipureintro; exact EvalE.binary st d env {OP} l r st1 st2 lv rv' _ hEl hEr rfl
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep6, hkeep4, hkeep2, hkeep1]

