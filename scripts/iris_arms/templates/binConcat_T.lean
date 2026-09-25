
#ix_piece {ARM}T_p3 from {ARM}T_p2 by
  -- run 3: operator dispatch, the string test, the left operand's copy, to `stringify`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary .add l r) d - 1088) (slot24 sret.toNat)
      (world N vsaLayoutP vsaRoomB inp (.counted (k + concatCost st2.store lv rv')) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N vsaLayoutP vsaRoomB inp (.counted k) st2 d (.binary .add l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ) ∗
      □ valOf N lv w0 w1 w2 ∗ □ valOf N rv' u0 u1 u2 ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv1 Hv2]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe Hv1 Hbin Hat; iexact Hv2
  intro F'
  refine {ARM}T_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) (kR := BitVec.ofNat 64 (u0.toNat % 2 ^ 32))
    hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ ?_ hn.op ?_ ?_ ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd
  · ix_fwd
  intros
  refine concat_route hlive ?_ fun _ => ?_
  · rcases hcat with h | h
    · right; ix_reg; rw [ofNat_lo32 (htl.trans h)]; decide
    · left; ix_reg; rw [ofNat_lo32 (htr.trans h)]; decide
  refine {ARM}T_run3b (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_reg; ix_keep [hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hcs3 : CatSaved Mt3 s ret rv :=
    ⟨by rw [hMt3]; ix_saved hsv2 using hoff, by rw [hMt3]; e2_fwd hoff; ix_keep [hkeep2, hkeep1]⟩
  have ha0 : ldv .ld Mt3 (s + 18446744073709550528#64 + 64#64).toNat = w0 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  have ha8 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 8) = w1 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  have ha16 : ldv .ld Mt3 ((s + 18446744073709550528#64 + 64#64).toNat + 16) = w2 := by
    rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #Hv1, #Hv2, #Hbin, #Hat⟩, Hms⟩
  -- the world, open for the tail; both operands' display resources
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hsto, Hcon, Hio, Hctx, %hB, #Hbw⟩
  ihave ⟨Hsto, #Hd1⟩ := dispRes_of_valOf hd st2.store B lv w0 w1 w2 $$ [Hsto Hv1]
  · iframe Hsto Hv1
  ihave ⟨Hsto, #Hd2⟩ := dispRes_of_valOf hd st2.store B rv' u0 u1 u2 $$ [Hsto Hv2]
  · iframe Hsto Hv2
  have hS64 : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  ihave ⟨Hms, HA⟩ := ms_carveWords N hS64 ha0 ha8 ha16 $$ [Hms Hv1]
  · iframe Hms Hv1
  -- `stringify(&l)`
  have hne := evalNeed_binary_rtErr .add l r d
  unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at hne
  have gS := evalCallGeom (nc := stringifyNeed) (o := 64) hsg
    (by unfold stringifyNeed Newlib.snprintfNeed; omega) (by decide) (by decide)
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (s := s + 18446744073709550528#64)
    (n := evalNeed (.binary .add l r) d - 1088) (m := stringifyNeed) (by rw [hsf]; omega)
    (by unfold stringifyNeed Newlib.snprintfNeed; omega) $$ Hst
  rw [show k + concatCost st2.store lv rv' = k + stringifyCost st2.store rv' +
      catBufCost st2.store lv rv' + stringifyCost st2.store lv by unfold concatCost catBufCost; omega]
  ihave Hs1 := hsgy $$ %(s + 18446744073709550528#64 + 64#64) %(s + 18446744073709550528#64) %lv
    %st2.store %(k + stringifyCost st2.store rv' + catBufCost st2.store lv rv') %H
    %(stringifyCost st2.store lv) %st2.out
  unfold stringifySpecT
  iapply ms_callHelper (twpW _) (i := 0x80003a40)
    (jalx_80003a40 live (fun p hp => hlive _ (interp_code_80003a40 p hp)))
    interp_code_80003a40 (by decide)
  iframe Hs1 Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg; ix_keep [hkeep2, hkeep1]⟩
  isplitl [HA Hh Hio Hcon Hst]
  · unfold stringifyPre stackAt; simp only [Regime.plus_counted]
    iframe HA Hd1 Hbin Hh Hio Hcon Hst
    ipureintro; exact ⟨⟨gS.slotGeom, stringifyChg st2.store lv⟩, gS.child⟩
  iintro %R4 %hkeep4 Hpost Hms
  unfold stringifyPost stackAt
  icases Hpost with ⟨HA, Hx, %hf1, Hh, Hio, Hcon, Hst, -⟩
  ihave ⟨%M4, Hms, %hM4⟩ := ms_uncarveVal N hS64 $$ [Hms HA]
  · iframe Hms HA
  have hcs4 : CatSaved M4 s ret rv := hcs3.agree fun k h1 h2 =>
    hM4 k (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece {ARM}T_p4 from {ARM}T_p3 by
  -- run 4: the right operand's copy, to `stringify`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted (k + stringifyCost st2.store rv' +
          catBufCost st2.store lv rv')) (((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H) ∗
        storeRepr N st2.store B ∗ consoleOwn st2.out ∗ Stdio.stdioOwn ∗
        interpCtxE inp d (errAny inp) ∗ strOwn (R4 10).toNat (strRender st2.store lv) ∗
        blockOwn ((s + 18446744073709550528#64).toNat - (evalNeed (.binary .add l r) d - 1088))
          (evalNeed (.binary .add l r) d - 1088 - stringifyNeed))
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N vsaLayoutP vsaRoomB inp (.counted k) st2 d (.binary .add l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ) ∗
      □ valOf N rv' u0 u1 u2 ∗ □ dispRes st2.store rv' ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv2 Hd2]
    · iframe Hcode Hro Hfb Hst Hslot Hh Hsto Hcon Hio Hctx Hx Hslack; iexact Hk
    · iframe Hv2 Hbin Hat; iexact Hd2
  intro F'
  refine {ARM}T_run4 (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt5 hMt5
  have hcs5 : CatSaved Mt5 s ret rv :=
    ⟨by rw [hMt5]; ix_saved hcs4.saved using hoff, by rw [hMt5]; e2_fwd hoff; exact hcs4.s5⟩
  have hb0 : ldv .ld Mt5 (s + 18446744073709550528#64 + 64#64).toNat = u0 := by
    rw [hMt5]; e2_fwd hoff; {RWREAD}
  have hb8 : ldv .ld Mt5 ((s + 18446744073709550528#64 + 64#64).toNat + 8) = u1 := by
    rw [hMt5]; e2_fwd hoff; {RWREAD}
  have hb16 : ldv .ld Mt5 ((s + 18446744073709550528#64 + 64#64).toNat + 16) = u2 := by
    rw [hMt5]; e2_fwd hoff; {RWREAD}
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hsto, Hcon, Hio, Hctx, Hx, Hslack⟩, Hk⟩, #Hv2,
    #Hd2, #Hbin, #Hat⟩, Hms⟩
  have hS64 : ∀ k, InExt ((s + 18446744073709550528#64 + 64#64).toNat, 24) k →
      InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  ihave ⟨Hms, HA⟩ := ms_carveWords N hS64 hb0 hb8 hb16 $$ [Hms Hv2]
  · iframe Hms Hv2
  -- `stringify(&r)`
  have gS := evalCallGeom (nc := stringifyNeed) (o := 64) hsg
    (by have := evalNeed_binary_rtErr .add l r d
        unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at this
        unfold stringifyNeed Newlib.snprintfNeed; omega) (by decide) (by decide)
  ihave Hs2 := hsgy $$ %(s + 18446744073709550528#64 + 64#64) %(s + 18446744073709550528#64) %rv'
    %st2.store %(k + catBufCost st2.store lv rv')
    %(((R4 10).toNat, (strRender st2.store lv).toList.length + 1) :: H)
    %(stringifyCost st2.store rv') %st2.out
  unfold stringifySpecT
  iapply ms_callHelper (twpW _) (i := 0x80003a68)
    (jalx_80003a68 live (fun p hp => hlive _ (interp_code_80003a68 p hp)))
    interp_code_80003a68 (by decide)
  iframe Hs2 Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg; ix_keep [hkeep4, hkeep2, hkeep1]⟩
  isplitl [HA Hh Hio Hcon Hst]
  · unfold stringifyPre stackAt; simp only [Regime.plus_counted]
    rw [show k + catBufCost st2.store lv rv' + stringifyCost st2.store rv' =
      k + stringifyCost st2.store rv' + catBufCost st2.store lv rv' by omega]
    iframe HA Hd2 Hbin Hh Hio Hcon Hst
    ipureintro; exact ⟨⟨gS.slotGeom, stringifyChg st2.store rv'⟩, gS.child⟩
  iintro %R6 %hkeep6 Hpost Hms
  unfold stringifyPost stackAt
  icases Hpost with ⟨HA, Hy, %hf2, Hh, Hio, Hcon, Hst, -⟩
  ihave ⟨%M6, Hms, %hM6⟩ := ms_uncarveVal N hS64 $$ [Hms HA]
  · iframe Hms HA
  have hcs6 : CatSaved M6 s ret rv := hcs5.agree fun k h1 h2 =>
    hM6 k (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece {ARM}T_p5 from {ARM}T_p4 by
  -- run 5: to `strlen(ls)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted (k + catBufCost st2.store lv rv')) {H2} ∗
        catRest N inp d st2 H B ∗ strOwn {Q1}.toNat {XR} ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF catRest; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hsto Hcon Hio Hctx Hx Hy Hslack Hk
    iframe Hbin Hat; ipureintro; exact hB
  intro F'
  refine {ARM}T_run5 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt7 hMt7
  have hcs7 : CatSaved Mt7 s ret rv := hcs6.eq hMt7
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave Hsl1 := hsl $$ %{Q1} %{XR} %(Regime.counted (k + catBufCost st2.store lv rv')) %{H2}
  iapply ms_callHelper (twpW _) (i := 0x80003a78) (entry := strlenPC)
    (jalx_80003a78 live (fun p hp => hlive _ (interp_code_80003a78 p hp)))
    interp_code_80003a78 (by decide)
  unfold strlenHeapSpec
  iframe Hsl1 Hcode Hms
  isplitl []
  · ipureintro; ix_reg; ix_keep [hkeep6]
  isplitl [Hx Hh]
  · iframe Hbin Hx Hh; ipureintro; exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, hf1.2⟩
  iintro %R8 %hkeep8 ⟨%hla, Hx, Hh⟩ Hms

#ix_piece {ARM}T_p6 from {ARM}T_p5 by
  -- run 6: to `strlen(rs)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted (k + catBufCost st2.store lv rv')) {H2} ∗
        catRest N inp d st2 H B ∗ strOwn {Q1}.toNat {XR} ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run6 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt9 hMt9
  have hcs9 : CatSaved Mt9 s ret rv := hcs7.eq hMt9
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave Hsl2 := hsl $$ %{Q2} %{YR} %(Regime.counted (k + catBufCost st2.store lv rv')) %{H2}
  iapply ms_callHelper (twpW _) (i := 0x80003a84) (entry := strlenPC)
    (jalx_80003a84 live (fun p hp => hlive _ (interp_code_80003a84 p hp)))
    interp_code_80003a84 (by decide)
  unfold strlenHeapSpec
  iframe Hsl2 Hcode Hms
  isplitl []
  · ipureintro; ix_reg; ix_keep [hkeep8]
  isplitl [Hy Hh]
  · iframe Hbin Hy Hh; ipureintro; exact ⟨List.mem_cons_self, hf2.2⟩
  iintro %R10 %hkeep10 ⟨%hlb, Hy, Hh⟩ Hms

#ix_piece {ARM}T_p7 from {ARM}T_p6 by
  -- run 7: `la + lb + 1`, to `malloc`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted (k + catBufCost st2.store lv rv')) {H2} ∗
        catRest N inp d st2 H B ∗ strOwn {Q1}.toNat {XR} ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run7 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt11 hMt11
  have hcs11 : CatSaved Mt11 s ret rv := hcs9.eq hMt11
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have h18 : R10 18 = BitVec.ofNat 64 {XR}.length := by
    rw [hkeep10 18 (by decide) (by decide)]; ix_reg; exact hla
  have hN : (R10 18 + R10 10 + 1#64).toNat = {XL} + {YL} + 1 := by
    rw [h18, hlb, ← String.length_toList, ← String.length_toList]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callMallocN A (twpW _) (i := 0x80003a90)
    (jalx_80003a90 live (fun p hp => hlive _ (interp_code_80003a90 p hp))) interp_code_80003a90
    (by decide) (.counted k) {H2} ({XL} + {YL} + 1) (catBufCost st2.store lv rv')
    (catBufChg st2.store lv rv')
  iframe Hat Hcode Hms Hst
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; exact hN, by ix_reg; ix_keep [hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  isplitl [Hh]
  · simp only [Regime.plus_counted]; iexact Hh
  iintro %R12 %hkeep12 Hst Hres Hms
  ihave Hst := stackScratch_widen (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst
  unfold mallocRes
  icases Hres with (⟨%⟨-, hρ⟩, -⟩ | ⟨%hf3, Hh, Hblk⟩)
  · cases hρ

#ix_piece {ARM}T_p8 from {ARM}T_p7 by
  -- run 8: spill `s4`, the NULL test, to `memcpy(s, ls, la)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k) {H3} ∗ blockOwn {Q}.toNat ({XL} + {YL} + 1) ∗
        catRest N inp d st2 H B ∗ strOwn {Q1}.toNat {XR} ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hblk Hrest Hx Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run8 (s := s) hlive hsf hs' hs2 hs3 ?_ ?_ ?_
  · ix_reg; ix_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  · ix_reg; exact fun h => hf3.1.nonzero (by rw [h]; rfl)
  intros
  apply swp_closeM
  intro Mt13 hMt13
  have hcs13 : CatSaved Mt13 s ret rv :=
    ⟨by rw [hMt13]; ix_saved hcs11.saved using hoff, by rw [hMt13]; e2_fwd hoff; exact hcs11.s5⟩
  have hs4 : ldv .ld Mt13 (s.toNat - 1088 + 1040) = rv 20 := by
    rw [hMt13]; e2_fwd hoff; ix_keep [hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hblk, Hrest, Hx, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have ha3 := fresh_arena hf3.1
  ihave ⟨Hb1, Hb2⟩ := blockOwn_split {Q}.toNat ({XL} + {YL} + 1) {XL} ({Q}.toNat + {XL}) ({YL} + 1)
    (by omega) rfl (by omega) $$ Hblk
  ihave ⟨%img1, %hc1, Hx1, Hx0⟩ := strOwn_cut {Q1}.toNat {XR} $$ Hx
  iapply ms_callMemcpyOwned (twpW _) hmc (i := 0x80003aa8)
    (jalx_80003aa8 live (fun p hp => hlive _ (interp_code_80003aa8 p hp))) interp_code_80003aa8
    (by decide) (dst := {Q}) (src := {Q1}) (n := {XL}) (img := img1)
    ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩ (by unfold htifLo; omega)
    ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩
  iframe Hcode Hbin Hms Hb1 Hx1
  isplitl []
  · ipureintro
    refine ⟨by ix_reg, by ix_reg; ix_keep [hkeep12, hkeep10, hkeep8, hkeep6], ?_⟩
    ix_reg; rw [hkeep12 18 (by decide) (by decide)]; ix_reg; rw [h18, String.length_toList]

#ix_piece {ARM}T_p9 from {ARM}T_p8 by
  -- run 9: to `strcpy(s + la, rs)`
  iintro %R14 %hkeep14 %h14 Hd Hx1 Hms
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k) {H3} ∗ blockOwn ({Q}.toNat + {XL}) ({YL} + 1) ∗
        ownImg (InExt ({Q}.toNat, {XL})) (fun a => img1 (a - {Q}.toNat + {Q1}.toNat)) ∗
        ownImg (InExt ({Q1}.toNat, {XL})) img1 ∗ ownImg (InExt ({Q1}.toNat + {XL}, 1)) img1 ∗
        catRest N inp d st2 H B ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF
    iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hb2 Hd Hx1 Hx0 Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run9 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt15 hMt15
  have hcs15 : CatSaved Mt15 s ret rv := hcs13.eq hMt15
  have hs4' : ldv .ld Mt15 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt15]; exact hs4
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hb2, Hd, Hx1, Hx0, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin,
    #Hat⟩, Hms⟩
  have ha1 := fresh_arena hf1.1
  have ha2 := fresh_arena hf2.1
  have ha3 := fresh_arena hf3.1
  have hd : ({Q} + BitVec.ofNat 64 {XL}).toNat = {Q}.toNat + {XL} := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  ihave Hsc1 := hsc $$ %({Q} + BitVec.ofNat 64 {XL}) %{Q2} %{YR} %(Regime.counted k) %{H3}
  unfold strcpyHeapSpec
  iapply ms_callHelper (twpW _) (i := 0x80003ab4) (entry := strcpyPC)
    (jalx_80003ab4 live (fun p hp => hlive _ (interp_code_80003ab4 p hp)))
    interp_code_80003ab4 (by decide)
  iframe Hsc1 Hcode Hms
  isplitl []
  · ipureintro
    refine ⟨?_, by ix_reg; ix_keep [hkeep14, hkeep12, hkeep10, hkeep8, hkeep6]⟩
    ix_reg; rw [hkeep14 8 (by decide) (by decide), hkeep14 18 (by decide) (by decide)]; ix_reg
    rw [hkeep12 18 (by decide) (by decide)]; ix_reg; rw [h18, String.length_toList]
  isplitl [Hb2 Hy Hh]
  · rw [hd]; iframe Hbin Hb2 Hy Hh
    ipureintro
    exact ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self, hf2.2⟩,
      ⟨by omega, by omega, .inr (by unfold htifLo; omega)⟩, by unfold htifLo; omega⟩
  iintro %R16 %hkeep16 ⟨⟨%img2, Hz, %hc2⟩, Hy, Hh⟩ Hms
  rw [hd] at hc2
  ihave Hs := ownImg_cat (q := {Q}.toNat) (q1 := {Q1}.toNat) img1 img2 hc1 hc2 $$ [Hd Hz]
  · rw [hd]; iframe Hd Hz

#ix_piece {ARM}T_p10 from {ARM}T_p9 by
  -- run 10: to `free(ls)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k) {H3} ∗ strOwn {Q}.toNat ({XR} ++ {YR}) ∗
        ownImg (InExt ({Q1}.toNat, {XL})) img1 ∗ ownImg (InExt ({Q1}.toNat + {XL}, 1)) img1 ∗
        catRest N inp d st2 H B ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF
    iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hx1 Hx0 Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run10 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt17 hMt17
  have hcs17 : CatSaved Mt17 s ret rv := hcs15.eq hMt17
  have hs4 : ldv .ld Mt17 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt17]; exact hs4'
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hx1, Hx0, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin,
    #Hat⟩, Hms⟩
  ihave Hq1 := blockOwn_of_cut {Q1}.toNat {XL} img1 img1 $$ [Hx1 Hx0]
  · iframe Hx1 Hx0
  ihave Hh := heapRes_congr (H := {H3})
    (H' := ({Q1}.toNat, {XL} + 1) :: ({Q}.toNat, {XL} + {YL} + 1) :: ({Q2}.toNat, {YL} + 1) :: H)
    (List.perm_middle (l₁ := [({Q}.toNat, {XL} + {YL} + 1), ({Q2}.toNat, {YL} + 1)])) $$ Hh
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callFreeN A (twpW _) (i := 0x80003abc)
    (jalx_80003abc live (fun p hp => hlive _ (interp_code_80003abc p hp))) interp_code_80003abc
    (by decide) (.counted k) (({Q}.toNat, {XL} + {YL} + 1) :: ({Q2}.toNat, {YL} + 1) :: H) {Q1} ({XL} + 1)
  iframe Hat Hcode Hms Hst Hq1 Hh
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; ix_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6],
      by ix_reg; ix_keep [hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  iintro %R17 %hkeep17 Hst Hh Hms
  ihave Hst := stackScratch_widen (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst

#ix_piece {ARM}T_p11 from {ARM}T_p10 by
  -- run 11: to `free(rs)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k)
          (({Q}.toNat, {XL} + {YL} + 1) :: ({Q2}.toNat, {YL} + 1) :: H) ∗
        strOwn {Q}.toNat ({XR} ++ {YR}) ∗ catRest N inp d st2 H B ∗ strOwn {Q2}.toNat {YR} ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hrest Hy Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run11 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt19 hMt19
  have hcs19 : CatSaved Mt19 s ret rv := hcs17.eq hMt19
  have hs4' : ldv .ld Mt19 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt19]; exact hs4
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hrest, Hy, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  ihave ⟨%img3, %-, Hy1, Hy0⟩ := strOwn_cut {Q2}.toNat {YR} $$ Hy
  ihave Hq2 := blockOwn_of_cut {Q2}.toNat {YL} img3 img3 $$ [Hy1 Hy0]
  · iframe Hy1 Hy0
  ihave Hh := heapRes_congr (H := ({Q}.toNat, {XL} + {YL} + 1) :: ({Q2}.toNat, {YL} + 1) :: H)
    (H' := ({Q2}.toNat, {YL} + 1) :: ({Q}.toNat, {XL} + {YL} + 1) :: H)
    (List.Perm.swap ({Q2}.toNat, {YL} + 1) ({Q}.toNat, {XL} + {YL} + 1) H) $$ Hh
  ihave ⟨Hslack2, Hst⟩ := stackScratch_narrow (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ Hst
  iapply ms_callFreeN A (twpW _) (i := 0x80003ac4)
    (jalx_80003ac4 live (fun p hp => hlive _ (interp_code_80003ac4 p hp))) interp_code_80003ac4
    (by decide) (.counted k) (({Q}.toNat, {XL} + {YL} + 1) :: H) {Q2} ({YL} + 1)
  iframe Hat Hcode Hms Hst Hq2 Hh
  isplitl []
  · ipureintro
    refine ⟨by ix_reg; ix_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6],
      by ix_reg; ix_keep [hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2,
        hkeep1], ?_⟩
    exact ⟨by rw [hsf]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [hsf]; omega,
      by rw [hsf]; omega⟩
  iintro %R18 %hkeep18 Hst Hh Hms
  ihave Hst := stackScratch_widen (s := {SP}) (n := stringifyNeed) (m := allocHeadroom)
    (by rw [hsf]; unfold stringifyNeed Newlib.snprintfNeed; omega)
    (by unfold stringifyNeed allocHeadroom Newlib.snprintfNeed; omega) $$ [Hslack2 Hst]
  · iframe Hslack2 Hst

#ix_piece {ARM}T_p12 from {ARM}T_p11 by
  -- run 12: to `value_str(sret, s)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE {SP} stringifyNeed (slot24 sret.toNat)
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k) (({Q}.toNat, {XL} + {YL} + 1) :: H) ∗
        strOwn {Q}.toNat ({XR} ++ {YR}) ∗ catRest N inp d st2 H B ∗ {SLACK})
      {KT} ∗ binImg ∗ textOwn allocText))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hh Hs Hrest Hslack Hk Hbin Hat
  intro F'
  refine {ARM}T_run12 (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4, hkeep2,
      hkeep1]
  intros
  apply swp_closeM
  intro Mt21 hMt21
  have hcs21 : CatSaved Mt21 s ret rv := hcs19.eq hMt21
  have hs4 : ldv .ld Mt21 (s.toNat - 1088 + 1040) = rv 20 := by rw [hMt21]; exact hs4'
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, ⟨Hh, Hs, Hrest, Hslack⟩, Hk⟩, #Hbin, #Hat⟩, Hms⟩
  have hlen : ({XR} ++ {YR}).toList.length = {XL} + {YL} := by
    rw [String.toList_append, List.length_append]
  have hf3' : FreshBlock vsaLayoutP {H2} {Q}.toNat (({XR} ++ {YR}).toList.length + 1) := by
    rw [hlen]; exact hf3.1
  iapply (twpW (vsaModel live)).fupd
  imod strAt_of_fresh hf3' $$ Hs with #Hs
  imodintro
  ihave Hvs := hvs $$ %sret %{Q} %({XR} ++ {YR})
  unfold valueStrSpec
  iapply ms_callHelper (twpW _) (i := 0x80003ad0)
    (jalx_80003ad0 live (fun p hp => hlive _ (interp_code_80003ad0 p hp)))
    interp_code_80003ad0 (by decide)
  iframe Hvs Hcode Hms
  isplitl []
  · ipureintro
    exact ⟨by ix_reg; ix_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6,
      hkeep4, hkeep2, hkeep1],
      by ix_reg; ix_keep [hkeep18, hkeep17, hkeep16, hkeep14, hkeep12]⟩
  isplitl [Hslot]
  · iframe Hslot Hs; ipureintro; exact ⟨hslg, fun h => hf3.1.nonzero h⟩
  iintro %R20 %hkeep20 Hval Hms

#ix_piece {ARM}T_p13 from {ARM}T_p12 by
  -- run 13: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE {SP} stringifyNeed
      (valAt N sret.toNat (.str ({XR} ++ {YR})))
      iprop(heapRes vsaLayoutP vsaRoomB (.counted k) (({Q}.toNat, {XL} + {YL} + 1) :: H) ∗
        catRest N inp d st2 H B ∗ {SLACK})
      {KT})
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hh Hrest Hslack Hk
  intro F'
  refine {ARM}T_run13 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) (v20 := rv 20) (v21 := rv 21) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · ix_keep [hkeep20, hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6, hkeep4,
      hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hcs21.saved.ra
  · rw [hoff _ (by decide)]; exact hcs21.saved.s0
  · rw [hoff _ (by decide)]; exact hcs21.saved.s1
  · rw [hoff _ (by decide)]; exact hcs21.saved.s2
  · rw [hoff _ (by decide)]; exact hcs21.saved.s3
  · rw [hoff _ (by decide)]; exact hs4
  · rw [hoff _ (by decide)]; exact hcs21.s5
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, ⟨Hh, Hrest, Hslack⟩, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := stackScratch_widen (s := {SP}) (n := evalNeed (.binary .add l r) d - 1088)
    (m := stringifyNeed) (by rw [hsf]; omega)
    (by have := evalNeed_binary_rtErr .add l r d
        unfold Newlib.RtErr.rtErrNeed Newlib.snprintfNeed at this
        unfold stringifyNeed Newlib.snprintfNeed; omega) $$ [Hslack Hst]
  · iframe Hslack Hst
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hw := world_of_catRest N inp d st2 (.counted k) (H' := (({Q}.toNat, {XL} + {YL} + 1) :: H))
    (fun b hb => List.mem_cons_of_mem _ hb) $$ [Hh Hrest]
  · iframe Hh Hrest
  iapply Hk $$ Hpc Hra
  unfold evalPost
  iexists _
  rw [strRender_eq, strRender_eq] at *
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep20, hkeep18, hkeep17, hkeep16, hkeep14, hkeep12, hkeep10, hkeep8, hkeep6,
    hkeep4, hkeep2, hkeep1]
