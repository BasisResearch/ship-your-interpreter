import VsaIris.Vsa.SnpSvfLoop

/-!
# `snprintf` in its run

`snprintf(dst, n, fmt, a3…a7)` (`0x80005c44`, `sp = s`): the `va_list` spilled
at `s - 40`, the string `FILE` at `s - 264` over `dst[0, n - 1)`,
`_svfprintf_r`, the NUL at the `FILE`'s `_p`, the return. The format loop is
a hypothesis `SvfLoopRun` a format discharges iteration by iteration
(`SnpSvfLoop.lean`).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- A format's whole loop: from the loop head with nothing printed to
`_svfprintf_r`'s return with the stream `total`. -/
def SvfLoopRun (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s dst n : Nat) (R0 : Nat → BitVec 64)
    (Mt0 : Mem) (p ap : Nat) (total : List (BitVec 8)) : Prop :=
  ∀ R Mt, SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 0) [] R Mt →
    SvfRetK live Dt DA Q s dst n R0 Mt0 (BitVec.ofNat 64 total.length) total →
    NW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt

/-- What `snprintf` leaves: the stream cut at `n - 1` and a NUL in
`dst[0, n)`, everything outside its scratch and `dst` unchanged. -/
structure SnpOut (Mt Mt' : Mem) (s dst n : Nat) (total : List (BitVec 8)) : Prop where
  bytes : ∀ i, i < min total.length (n - 1) → imgM Mt' (dst + i) = total.getD i 0
  nul : imgM Mt' (dst + min total.length (n - 1)) = 0#8
  frame : ∀ a, ¬ (s - 1024 ≤ a ∧ a < s) → ¬ (dst ≤ a ∧ a < dst + n) → imgM Mt' a = imgM Mt a

/-- **`snprintf`'s epilogue** (`0x80005cbc`, back from `_svfprintf_r`): the
return count not below `-1`, the NUL at `_p`, the spills reloaded. -/
theorem snp_epi {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt Mt0 : Mem) (SG : SnpGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 (s - 272)) (h8 : R 8 = BitVec.ofNat 64 n)
    (h10 : R 10 = BitVec.ofNat 64 total.length) (hlen : total.length < 2 ^ 31)
    (hB : BufAt Mt s dst n total) (ra s0 s1 : BitVec 64)
    (hra : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 216)).toNat = ra)
    (hS0 : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 208)).toNat = s0)
    (hS1 : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 200)).toNat = s1) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' Mt', R' 2 = BitVec.ofNat 64 s → R' 8 = s0 → R' 9 = s1 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) →
      (∀ i, i < min total.length (n - 1) → imgM Mt' (dst + i) = total.getD i 0) →
      imgM Mt' (dst + min total.length (n - 1)) = 0#8 →
      (∀ a, ¬ (dst ≤ a ∧ a < dst + n) → imgM Mt' a = imgM Mt a) →
      NW live Dt DA (snpS s dst n) Q ra R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80005cbc#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have hn := SG.n_hi
  have hn0 := SG.n_pos
  have hd1 := SG.d_lo
  have hd2 := SG.d_hi
  have hdsep := SG.d_sep
  have hpw := hB.pw
  have hng : ¬ (BitVec.ofNat 64 total.length).toInt < (18446744073709551615#64).toInt := by
    rw [toInt_ofNat_small (by omega)]; simp
  have hn0' : BitVec.ofNat 64 n ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hpw' : ldv .ld Mt (BitVec.ofNat 64 (s - 272 + 8)).toNat =
      BitVec.ofNat 64 (dst + min total.length (n - 1)) := by
    rw [toNat_ofNat_lt (by omega), show s - 272 + 8 = snpFP s by simp only [snpFP]; omega]; exact hpw
  nx_runF [20] hlive using [ofNat_add_ofNat, h2, h8, h10, hng, hn0', hpw', hra, hS0, hS1]
  have hmin : min total.length (n - 1) < n := by omega
  refine hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [show s - 272 + 272 = s by omega]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro z h1 h2
    simp only [upd_apply, show z ≠ 1 by omega, show z ≠ 2 by omega, show z ≠ 8 by omega,
      show z ≠ 9 by omega, show z ≠ 15 by omega, ite_false]
  · intro i hi
    rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hB.bytes i hi
  · rw [imgM_sb_ofNat' _ _ _ (by omega) (by decide)]
  · intro a ha
    rw [imgM_miss_nat _ _ (by omega) (by omega)]

theorem snez_pos {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.ofNat 64 x))) = 1#64 := by
  have e : (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.ofNat 64 x)) = true := by
    simp only [LeanRV64DExecutable.Functions.zopz0zI_u, decide_eq_true_eq]
    simp only [Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt h]
    exact Int.ofNat_lt.mpr h0
  rw [e]; rfl

/-- The flags word's low half (`sw a6,24(sp)` of `0xffff0208`). -/
theorem lh_flags (Mt : Mem) (a : Nat) : ldv .lh (writeLog Mt [(a, 4, 18446744073709486600#64)]) a = 0x208#64 := by
  obtain ⟨h0, h1, _, _⟩ := pin4_of_writeLog Mt [] [] a (18446744073709486600#64) (by simp [OutLRange])
  simp only [List.nil_append] at h0 h1
  simp only [ldv, bytesVal, bytesAt, widthOfM, imgM, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
    List.map_append, List.cons_append]
  rw [h0, h1]; decide

/-- `snprintf`'s state at `_svfprintf_r`'s entry. -/
structure SnpAtSvf (s dst n : Nat) (R : Nat → BitVec 64) (Mt : Mem) (R' : Nat → BitVec 64) (Mt' : Mem) :
    Prop where
  r1 : R' 1 = 0x80005cbc#64
  r2 : R' 2 = BitVec.ofNat 64 (s - 272)
  r8 : R' 8 = BitVec.ofNat 64 n
  r11 : R' 11 = BitVec.ofNat 64 (s - 264)
  r12 : R' 12 = R 12
  r13 : R' 13 = BitVec.ofNat 64 (s - 40)
  keep : ∀ z, 18 ≤ z → z ≤ 27 → R' z = R z
  buf : BufAt Mt' s dst n []
  args : ∀ i, i < 5 → ldv .ld Mt' (BitVec.ofNat 64 (s - 40 + 8 * i)).toNat = R (13 + i)
  ra : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 216)).toNat = R 1
  s0 : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 208)).toNat = R 8
  s1 : ldv .ld Mt' (BitVec.ofNat 64 (s - 272 + 200)).toNat = R 9
  frame : ∀ a, (a < s - 272 ∨ s ≤ a) → imgM Mt' a = imgM Mt a

/-- **`snprintf`'s prologue** (`0x80005c44` → `_svfprintf_r`'s entry): the
spills, the `va_list`, the string `FILE` over `dst`. -/
theorem snp_pro {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 s) (h10 : R 10 = BitVec.ofNat 64 dst) (h11 : R 11 = BitVec.ofNat 64 n)
    (hk : ∀ R' Mt', SnpAtSvf s dst n R Mt R' Mt' → NW live Dt DA (snpS s dst n) Q 0x80007654#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80005c44#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have hn := SG.n_hi
  have hn0 := SG.n_pos
  have hx : (18446744071562067968#64 ^^^ 18446744073709551615#64 : BitVec 64) = 2147483647#64 := by decide
  have hbl : ¬ (2147483647#64).toNat < (BitVec.ofNat 64 n).toNat := by
    rw [toNat_ofNat_lt (by omega)]; simp; omega
  have eS : BitVec.ofNat 64 (s + 18446744073709551344) = BitVec.ofNat 64 (s - 272) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have hsz := snez_pos hn0 (by omega)
  have hsw := subw_ofNat' (w := n) (c := 1) (by omega) (by omega) (by omega)
  nx_runF hlive using [ofNat_add_ofNat, h2, h10, h11, hx, hbl, eS, hsz, hsw] at 0x80007654
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [show s - 272 + 8 = s - 264 by omega]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [show s - 272 + 232 = s - 40 by omega]
  · intro z h1 h2
    simp only [upd_apply, show z ≠ 1 by omega, show z ≠ 2 by omega, show z ≠ 6 by omega,
      show z ≠ 8 by omega, show z ≠ 9 by omega, show z ≠ 10 by omega, show z ≠ 11 by omega,
      show z ≠ 13 by omega, show z ≠ 14 by omega, show z ≠ 15 by omega, show z ≠ 16 by omega, ite_false]
  · rw [show snpFP s = (BitVec.ofNat 64 (s - 272 + 8)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    svf_mem; simp
  · rw [show snpFP s + 12 = (BitVec.ofNat 64 (s - 272 + 20)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    svf_mem; simp
  · rw [show snpFP s + 16 = (BitVec.ofNat 64 (s - 272 + 24)).toNat by rw [toNat_ofNat_lt (by omega)]; simp only [snpFP]; omega]
    svf_mem
    exact lh_flags _ _
  · intro i hi; simp at hi
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    · rw [show s - 40 + 8 * 0 = s - 272 + 232 by omega]; svf_mem
    · rw [show s - 40 + 8 * 1 = s - 272 + 240 by omega]; svf_mem
    · rw [show s - 40 + 8 * 2 = s - 272 + 248 by omega]; svf_mem
    · rw [show s - 40 + 8 * 3 = s - 272 + 256 by omega]; svf_mem
    · rw [show s - 40 + 8 * 4 = s - 272 + 264 by omega]; svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · intro a ha; svf_mem

/-- **`snprintf(dst, n, fmt, …)`** (`0x80005c44`) in its run, for a format
whose loop renders `total` (`SvfLoopRun`, discharged per format): the
caller's registers kept, `total` cut at `n - 1` and a NUL in `dst[0, n)`,
nothing else outside the stack scratch changed. -/
theorem snprintf_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 s) (h10 : R 10 = BitVec.ofNat 64 dst) (h11 : R 11 = BitVec.ofNat 64 n)
    (hal : (R 1).toNat % 4 = 0) (hdp : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdot : DotAt Dt DA)
    (total : List (BitVec 8)) (hlen : total.length < 2 ^ 31)
    (hloop : ∀ R0' Mt0', SnpAtSvf s dst n R Mt R0' Mt0' →
      SvfLoopRun live Dt DA Q s dst n R0' Mt0' (R0' 12).toNat (R0' 13).toNat total)
    (hk : ∀ R' Mt', R' 2 = R 2 → (∀ z, (z = 8 ∨ z = 9 ∨ (18 ≤ z ∧ z ≤ 27)) → R' z = R z) →
      SnpOut Mt Mt' s dst n total → NW live Dt DA (snpS s dst n) Q (R 1) R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80005c44#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  refine snp_pro hlive R Mt SG h2 h10 h11 fun R1 Mt1 SA => ?_
  have hdp1 : ldv .ld Mt1 0x8001b898 = 0x80019770#64 :=
    (ldv_agree .ld fun i hi => SA.frame _ (by simp only [widthOfM] at hi; omega)).trans hdp
  refine svf_entry hlive R1 Mt1 SG SA.r2 SA.r11 hdp1 hdot SA.buf fun R2 Mt2 A => ?_
  refine hloop R1 Mt1 SA R2 Mt2 A ?_
  intro R3 Mt3 h2' hkeep h10' hB hfr
  have hag : ∀ a, (s - 272 ≤ a ∧ a < s) → ¬ (snpFP s ≤ a ∧ a < snpFP s + 16) →
      imgM Mt3 a = imgM Mt1 a := fun a h1 h2 => hfr a (by
    have := SG.d_sep; simp only [SvfW, snpFP] at h2 ⊢; omega)
  have ld3 : ∀ off, 200 ≤ off → off + 8 ≤ 272 →
      ldv .ld Mt3 (BitVec.ofNat 64 (s - 272 + off)).toNat = ldv .ld Mt1 (BitVec.ofNat 64 (s - 272 + off)).toNat :=
    fun off h1 h2 => by
      rw [toNat_ofNat_lt (by omega)]
      exact ldv_agree .ld fun i hi => hag _ (by simp only [widthOfM] at hi; omega)
        (by simp only [snpFP, widthOfM] at hi ⊢; omega)
  rw [SA.r1]
  refine snp_epi hlive total R3 Mt3 Mt SG h2' ((hkeep 8 (.inl rfl)).trans SA.r8) h10' hlen hB (R 1) (R 8) (R 9)
    ((ld3 216 (by omega) (by omega)).trans SA.ra) ((ld3 208 (by omega) (by omega)).trans SA.s0)
    ((ld3 200 (by omega) (by omega)).trans SA.s1) hal fun R4 Mt4 h24 h84 h94 hk4 hb hnul hfr4 => ?_
  refine hk R4 Mt4 (h24.trans h2.symm) ?_ ⟨hb, hnul, fun a ha1 ha2 => ?_⟩
  · intro z hz
    rcases hz with rfl | rfl | ⟨h1, h2⟩
    · exact h84
    · exact h94
    · exact (hk4 z h1 h2).trans ((hkeep z (.inr (.inr ⟨h1, h2⟩))).trans (SA.keep z h1 h2))
  · rw [hfr4 a ha2, hfr a (by have := SG.d_sep; simp only [SvfW, snpFP]; omega), SA.frame a (by omega)]

end VsaIris.Sym