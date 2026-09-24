#ix_piece {ARM}P_{ROW}1 from {ARM}P_p2 at {K} by
  -- run 3: operator dispatch, int/int checks, the operation
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
    ?_ ?_ ?_ ?_ hn.op ?_ ?_{ZEROHOLE} ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd; exact hk0
  · ix_fwd; exact hk0'{ZEROBULLET}
  intros
  -- the libgcc call, followed inside the run
  refine iw_jal 0x{JL} _ _ (jalx_{JL} live (fun p hp => hlive _ (interp_code_{JL} p hp)))
    interp_code_{JL} rfl ?_
  refine {LIBIW} hlive {LX} {LY} 0x{RETA}#64 _ _ {LIBHY}?_ ?_ ?_ (by decide) (fun R' hq hkeep => ?_)
  · {B10}
  · {B11}
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd]
  have hR'2 : R' 2 = s + 18446744073709550528#64 := by
    rw [hkeep 2 {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1]
  have hR'k : ∀ z ∈ [20, 21, 22, 23, 24, 25, 26, 27], R' z = rv z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (rw [hkeep _ {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1])
  refine {TRUN}_run3b (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · rw [hkeep 9 {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved Mt3 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt3]; ix_saved hsv2 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE⟩, Hms⟩
  -- {HELPERC}
  ihave Hvi := {HNAME} $$ %sret %(R' 10)
  unfold {HSPEC}
  iapply ms_callHelper (wpW _) (i := 0x{J3})
    (jalx_{J3} live (fun p hp => hlive _ (interp_code_{J3} p hp)))
    interp_code_{J3} (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  have hsum : (R' 10).toInt = {RESI} := by {SUMPF}
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
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [keep_helper hkeep3 (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hR'2
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
  · ipureintro; exact EvalE.binary st d env {OP} l r st1 st2 (.int a) (.int b) _ hEl hEr {EVPF}
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals first
    | (ix_reg; done)
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
       rw [keep_helper hkeep3 (by decide) (by decide)]
       simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
       exact hR'k _ (by decide))

