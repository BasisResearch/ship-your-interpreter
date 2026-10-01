import VsaIris.Vsa.SnpMove
import VsaIris.Interp.LoopArgs
import Vsa.Sim.PinW
import VsaIris.Vsa.Carry

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

theorem subw_ofNat {w c : Nat} (hcw : c ≤ w) (hw : w < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 w) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 c))
      = BitVec.ofNat 64 (w - c) := by
  rw [show BitVec.extractLsb 31 0 (BitVec.ofNat 64 w) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 c)
      = BitVec.extractLsb 31 0 (BitVec.ofNat 64 (w - c)) from by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat]
    omega]
  exact VsaIris.Interp.sext32_ofNat_eq (by omega)

theorem ssp_ret {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (sp fp p c w : Nat) (ra s0 s1 : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (hsp1 : s - 1024 ≤ sp) (hsp2 : sp + 64 ≤ s) (hsp8 : sp % 16 = 0) (hs : s ≤ 0x88000000)
    (hs1 : 0x8001ad10 + 1024 ≤ s)
    (hfp1 : s - 1024 ≤ fp) (hfp2 : fp + 24 ≤ s) (hfp8 : fp % 8 = 0) (hfps : fp + 24 ≤ sp ∨ sp + 64 ≤ fp)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h8 : R 8 = BitVec.ofNat 64 fp)
    (h9 : R 9 = BitVec.ofNat 64 c) (hcw : c ≤ w) (hw31 : w < 2 ^ 31) (hp : p + c < 2 ^ 64)
    (hw : ldv .lw Mt (fp + 12) = BitVec.ofNat 64 w) (hpp : ldv .ld Mt fp = BitVec.ofNat 64 p)
    (hra : ldv .ld Mt (sp + 56) = ra) (hs0 : ldv .ld Mt (sp + 48) = s0)
    (hs1' : ldv .ld Mt (sp + 40) = s1) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', R' 10 = 0#64 → R' 2 = BitVec.ofNat 64 (sp + 64) → R' 8 = s0 → R' 9 = s1 →
      (∀ z, z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 9 → z ≠ 10 → z ≠ 14 → z ≠ 15 → z ≠ 32 → R' z = R z) →
      SnpW live Dt DA (snpS s dst n) Q ra R'
        (writeLog (writeLog Mt [(fp + 12, 4, BitVec.ofNat 64 (w - c))]) [(fp, 8, BitVec.ofNat 64 (p + c))])) :
    SnpW live Dt DA (snpS s dst n) Q 0x800143c4#64 R Mt := by
  have n2 : (R 2).toNat = sp := by rw [h2]; simp only [BitVec.toNat_ofNat]; omega
  have n8 : (R 8).toNat = fp := by rw [h8]; simp only [BitVec.toNat_ofNat]; omega
  have hw' : ldv .lw Mt (BitVec.ofNat 64 (fp + 12)).toNat = BitVec.ofNat 64 w := by carry_close [hw]
  have hpp' : ldv .ld Mt (BitVec.ofNat 64 fp).toNat = BitVec.ofNat 64 p := by carry_close [hpp]
  have hra' : ldv .ld Mt (BitVec.ofNat 64 (sp + 56)).toNat = ra := by carry_close [hra]
  have hs0' : ldv .ld Mt (BitVec.ofNat 64 (sp + 48)).toNat = s0 := by carry_close [hs0]
  have hs1'' : ldv .ld Mt (BitVec.ofNat 64 (sp + 40)).toNat = s1 := by carry_close [hs1']
  snp_run hlive using [ofNat_add_ofNat, h2, h8, h9, hw', hpp', subw_ofNat hcw hw31, hra', hs0', hs1'']
  rw [toNat_ofNat_lt (x := fp + 12) (by omega), toNat_ofNat_lt (x := fp) (by omega)]
  refine hk _ ?_ ?_ ?_ ?_ ?_ <;> carry_close

theorem ldv_agree {Mt Mt' : Mem} (k : MKind) {a : Nat}
    (h : ∀ i, i < widthOfM k → imgM Mt' (a + i) = imgM Mt (a + i)) : ldv k Mt' a = ldv k Mt a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact h j (List.mem_range.mp hj)

theorem ssp_call {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (sp fp p src c w : Nat) (g : Nat → BitVec 8) (ra s0 s1 : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (hsp1 : s - 1024 ≤ sp) (hsp2 : sp + 64 ≤ s) (hsp8 : sp % 16 = 0) (hs : s ≤ 0x88000000)
    (hs1 : 0x8001ad10 + 1024 ≤ s)
    (hfp1 : s - 1024 ≤ fp) (hfp2 : fp + 24 ≤ s) (hfp8 : fp % 8 = 0) (hfps : fp + 24 ≤ sp ∨ sp + 64 ≤ fp)
    (G : MoveGeom s dst n p src c) (hpf : p + c ≤ fp ∨ fp + 24 ≤ p) (hps : p + c ≤ sp ∨ sp + 64 ≤ p)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h8 : R 8 = BitVec.ofNat 64 fp) (h9 : R 9 = BitVec.ofNat 64 c)
    (h10 : R 10 = BitVec.ofNat 64 p) (h15 : R 15 = BitVec.ofNat 64 src)
    (hcw : c ≤ w) (hw31 : w < 2 ^ 31)
    (hw : ldv .lw Mt (fp + 12) = BitVec.ofNat 64 w) (hpp : ldv .ld Mt fp = BitVec.ofNat 64 p)
    (hra : ldv .ld Mt (sp + 56) = ra) (hs0 : ldv .ld Mt (sp + 48) = s0)
    (hs1' : ldv .ld Mt (sp + 40) = s1) (hal : ra.toNat % 4 = 0)
    (hwin : ReadWin Dt DA (snpS s dst n) Mt src (src + c) g)
    (hk : ∀ R' Mt', R' 10 = 0#64 → R' 2 = BitVec.ofNat 64 (sp + 64) → R' 8 = s0 → R' 9 = s1 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) → Copied Mt' Mt p src c g →
      SnpW live Dt DA (snpS s dst n) Q ra R'
        (writeLog (writeLog Mt' [(fp + 12, 4, BitVec.ofNat 64 (w - c))]) [(fp, 8, BitVec.ofNat 64 (p + c))])) :
    SnpW live Dt DA (snpS s dst n) Q 0x800143b8#64 R Mt := by
  have G' := G
  obtain ⟨hd1, ⟨hdd1, hdd2⟩, hdn, hsl, hsh, hsh', hdisj⟩ := G'
  snp_run hlive using [h15, h9] at 0x800069c4
  refine memmove_nw hlive p src c g _ Mt G ?_ ?_ ?_ ?_ hwin (fun R' Mt' hF hcp => ?_)
  any_goals carry_close [h10]
  have hag : ∀ a w', (a + w' ≤ p ∨ p + c ≤ a) → ∀ i, i < w' → imgM Mt' (a + i) = imgM Mt (a + i) :=
    fun a w' ha i hi => hcp.rest _ (by omega)
  refine ssp_ret hlive sp fp p c w ra s0 s1 R' Mt' hsp1 hsp2 hsp8 hs hs1 hfp1 hfp2 hfp8 hfps
    ?_ ?_ ?_ hcw hw31 (by omega)
    ((ldv_agree .lw (hag (fp + 12) 4 (by omega))).trans hw)
    ((ldv_agree .ld (hag fp 8 (by omega))).trans hpp)
    ((ldv_agree .ld (hag (sp + 56) 8 (by omega))).trans hra)
    ((ldv_agree .ld (hag (sp + 48) 8 (by omega))).trans hs0)
    ((ldv_agree .ld (hag (sp + 40) 8 (by omega))).trans hs1') hal
    (fun R'' h10' h2' h8' h9' hkp => hk R'' Mt' h10' h2' h8' h9' (fun z hz1 hz2 => by carry_close [hkp, hF]) hcp)
  all_goals carry_close [hF, h2, h8, h9]

theorem ldv_lw_store4 (M : Mem) (a k : Nat) (hk : k < 2 ^ 31) :
    ldv .lw (writeLog M [(a, 4, BitVec.ofNat 64 k)]) a = BitVec.ofNat 64 k := by
  obtain ⟨h0, h1, h2, h3⟩ := pin4_of_writeLog M [] [] a (BitVec.ofNat 64 k) (by simp [OutLRange])
  simp only [List.nil_append] at h0 h1 h2 h3
  have e : ldv .lw (writeLog M [(a, 4, BitVec.ofNat 64 k)]) a =
      LeanRV64DExecutable.Functions.sign_extend (m := 64) ((((((swData (BitVec.ofNat 64 k)).extractLsb' 24 8).append
        ((swData (BitVec.ofNat 64 k)).extractLsb' 16 8)).append ((swData (BitVec.ofNat 64 k)).extractLsb' 8 8)).append
        ((swData (BitVec.ofNat 64 k)).extractLsb' 0 8)) : BitVec (8 * 4)) := by
    simp only [ldv, bytesVal, bytesAt, widthOfM, imgM, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
      List.map_append, List.cons_append]
    rw [h0, h1, h2, h3]; rfl
  rw [e, pinw4_sext_reassemble]
  exact VsaIris.Interp.sext32_ofNat_eq hk

theorem ssp_B {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (sp fp p src len w : Nat) (g : Nat → BitVec 8) (ra s0 s1 : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem)
    (hsp1 : s - 1024 ≤ sp) (hsp2 : sp + 64 ≤ s) (hsp8 : sp % 16 = 0) (hs : s ≤ 0x88000000)
    (hs1 : 0x8001ad10 + 1024 ≤ s)
    (hfp1 : s - 1024 ≤ fp) (hfp2 : fp + 24 ≤ s) (hfp8 : fp % 8 = 0) (hfps : fp + 24 ≤ sp ∨ sp + 64 ≤ fp)
    (G : MoveGeom s dst n p src (min len w)) (hpf : p + min len w ≤ fp ∨ fp + 24 ≤ p)
    (hps : p + min len w ≤ sp ∨ sp + 64 ≤ p)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h9 : R 9 = BitVec.ofNat 64 w) (h11 : R 11 = BitVec.ofNat 64 fp)
    (h12 : R 12 = BitVec.ofNat 64 src) (h13 : R 13 = BitVec.ofNat 64 len) (hlen : len < 2 ^ 31)
    (hw31 : w < 2 ^ 31) (hw : ldv .lw Mt (fp + 12) = BitVec.ofNat 64 w)
    (hpp : ldv .ld Mt fp = BitVec.ofNat 64 p) (hfl : ldv .lh Mt (fp + 16) = 0x208#64)
    (hra : ldv .ld Mt (sp + 56) = ra) (hs0 : ldv .ld Mt (sp + 48) = s0)
    (hs1' : ldv .ld Mt (sp + 40) = s1) (hal : ra.toNat % 4 = 0)
    (hwin : ReadWin Dt DA (snpS s dst n) Mt src (src + min len w) g)
    (hk : ∀ R' Mt', R' 10 = 0#64 → R' 2 = BitVec.ofNat 64 (sp + 64) → R' 8 = s0 → R' 9 = s1 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) → Copied Mt' Mt p src (min len w) g →
      SnpW live Dt DA (snpS s dst n) Q ra R'
        (writeLog (writeLog Mt' [(fp + 12, 4, BitVec.ofNat 64 (w - min len w))])
          [(fp, 8, BitVec.ofNat 64 (p + min len w))])) :
    SnpW live Dt DA (snpS s dst n) Q 0x800143a0#64 R Mt := by
  have n13 : (R 13).toNat = len := by rw [h13]; simp only [BitVec.toNat_ofNat]; omega
  have n9 : (R 9).toNat = w := by rw [h9]; simp only [BitVec.toNat_ofNat]; omega
  have hpp' : ldv .ld Mt (BitVec.ofNat 64 fp).toNat = BitVec.ofNat 64 p := by carry_close [hpp]
  have hfl' : ldv .lh Mt (BitVec.ofNat 64 (fp + 16)).toNat = 0x208#64 := by carry_close [hfl]
  snp_run hlive using [ofNat_add_ofNat, h2, h9, h11, h12, h13, hpp', hfl'] at 0x800143b8
  all_goals (
    refine ssp_call hlive sp fp p src (min len w) w g ra s0 s1 _ Mt hsp1 hsp2 hsp8 hs hs1 hfp1 hfp2
      hfp8 hfps G hpf hps ?_ ?_ ?_ ?_ ?_ (Nat.min_le_right _ _) hw31 hw hpp hra hs0 hs1' hal hwin
      (fun R' Mt' h10' h2' h8' h9' hkp hcp => hk R' Mt' h10' h2' h8' h9'
        (fun z hz1 hz2 => (hkp z hz1 hz2).trans (by carry_close)) hcp)
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    all_goals first
      | exact h2
      | (rw [h9]; congr 1; omega)
      | (rw [VsaIris.Interp.sext32_ofNat_eq (by omega)]; congr 1; omega))

structure PutsOut (Mt Mt' : Mem) (sp fp p src c w : Nat) (g : Nat → BitVec 8) : Prop where
  copied : ∀ i, i < c → imgM Mt' (p + i) = g (src + i)
  pw : ldv .ld Mt' fp = BitVec.ofNat 64 (p + c)
  ww : ldv .lw Mt' (fp + 12) = BitVec.ofNat 64 (w - c)
  rest : ∀ a, (a < p ∨ p + c ≤ a) → (a < fp ∨ fp + 16 ≤ a) → (a < sp - 64 ∨ sp ≤ a) →
    imgM Mt' a = imgM Mt a

theorem ssputs_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (sp fp p src len w : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt : Mem)
    (hsp1 : s - 1024 + 64 ≤ sp) (hsp2 : sp ≤ s) (hsp8 : sp % 16 = 0) (hs : s ≤ 0x88000000)
    (hs1 : 0x8001ad10 + 1024 ≤ s)
    (hfp1 : s - 1024 ≤ fp) (hfp2 : fp + 24 ≤ s) (hfp8 : fp % 8 = 0)
    (hfps : fp + 24 ≤ sp - 64 ∨ sp ≤ fp)
    (G : MoveGeom s dst n p src (min len w)) (hpf : p + min len w ≤ fp ∨ fp + 24 ≤ p)
    (hps : p + min len w ≤ sp - 64 ∨ sp ≤ p) (hss : src + min len w ≤ sp - 64 ∨ sp ≤ src)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h11 : R 11 = BitVec.ofNat 64 fp)
    (h12 : R 12 = BitVec.ofNat 64 src) (h13 : R 13 = BitVec.ofNat 64 len) (hlen : len < 2 ^ 31)
    (hw31 : w < 2 ^ 31) (hw : ldv .lw Mt (fp + 12) = BitVec.ofNat 64 w)
    (hpp : ldv .ld Mt fp = BitVec.ofNat 64 p) (hfl : ldv .lh Mt (fp + 16) = 0x208#64)
    (hal : (R 1).toNat % 4 = 0)
    (hwin : ReadWin Dt DA (snpS s dst n) Mt src (src + min len w) g)
    (hk : ∀ R' Mt', R' 10 = 0#64 → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) → PutsOut Mt Mt' sp fp p src (min len w) w g →
      SnpW live Dt DA (snpS s dst n) Q (R 1) R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x8001438c#64 R Mt := by
  have n2 : (R 2).toNat = sp := by rw [h2]; simp only [BitVec.toNat_ofNat]; omega
  have n11 : (R 11).toNat = fp := by rw [h11]; simp only [BitVec.toNat_ofNat]; omega
  have hw' : ldv .lw Mt (BitVec.ofNat 64 (fp + 12)).toNat = BitVec.ofNat 64 w := by carry_close [hw]
  snp_run hlive using [ofNat_add_ofNat, h2, h11, hw'] at 0x800143a0

  have e40 : (BitVec.ofNat 64 (sp + 18446744073709551552 + 40)).toNat = sp - 64 + 40 := by
    simp only [BitVec.toNat_ofNat]; omega
  have e48 : (BitVec.ofNat 64 (sp + 18446744073709551552 + 48)).toNat = sp - 64 + 48 := by
    simp only [BitVec.toNat_ofNat]; omega
  have e56 : (BitVec.ofNat 64 (sp + 18446744073709551552 + 56)).toNat = sp - 64 + 56 := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [e40, e48, e56]
  refine nw_gen (fun M => (∀ a, (a < sp - 64 ∨ sp ≤ a) → imgM M a = imgM Mt a) ∧
      ldv .ld M (sp - 64 + 56) = R 1 ∧ ldv .ld M (sp - 64 + 48) = R 8 ∧ ldv .ld M (sp - 64 + 40) = R 9)
    ⟨fun a ha => by simp (disch := sx_addr) only [imgM_store_miss],
     by simp (disch := (simp only [widthOfM]; sx_addr)) only [ldv_store_miss, ldv_ld_hit_eq],
     by simp (disch := (simp only [widthOfM]; sx_addr)) only [ldv_store_miss, ldv_ld_hit_eq],
     by simp (disch := (simp only [widthOfM]; sx_addr)) only [ldv_store_miss, ldv_ld_hit_eq]⟩ ?_
  rintro M1 ⟨hM1, hra1, hs01, hs11⟩
  have hag : ∀ a w', (a + w' ≤ sp - 64 ∨ sp ≤ a) → ∀ i, i < w' → imgM M1 (a + i) = imgM Mt (a + i) :=
    fun a w' ha i hi => hM1 _ (by omega)
  refine ssp_B hlive (sp - 64) fp p src len w g (R 1) (R 8) (R 9) _ M1 (by omega) (by omega) (by omega) hs
    hs1 hfp1 hfp2 hfp8 (by omega) G hpf (by omega) ?_ ?_ ?_ ?_ ?_ hlen hw31
    ((ldv_agree .lw (hag (fp + 12) 4 (by omega))).trans hw)
    ((ldv_agree .ld (hag fp 8 (by omega))).trans hpp)
    ((ldv_agree .lh (hag (fp + 16) 2 (by omega))).trans hfl) hra1 hs01 hs11 hal
    (hwin.transport fun a h1 h2 => hM1 a (by omega)) (fun R' Mt' h10' h2' h8' h9' hkp hcp => ?_)
  · apply BitVec.eq_of_toNat_eq; carry_close
  all_goals try carry_close [h11, h12, h13]
  refine hk R' _ h10' (h2'.trans (by rw [h2]; apply BitVec.eq_of_toNat_eq; carry_close)) h8' h9' (fun z hz1 hz2 => ?_) ⟨?_, ?_, ?_, ?_⟩
  all_goals carry_close [hkp, hcp.done, hcp.rest, hM1, ldv_lw_store4 _ _ _ (by omega : w - min len w < 2 ^ 31)]

end VsaIris.Sym
