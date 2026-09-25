import VsaIris.Vsa.Fprintf.Top

/-!
# `fprintf(stdout, fmt, arg)` down to the inner `_vfprintf_r` (lane N5)

`fprintf_sb` composes `fprintf_wrap`, `vfp_outer` and `sbprintf_run`: from
`fprintf`'s entry (stack pointer `s`) to its return, with the inner
`_vfprintf_r` on the stack `FILE` a hook (`vfpInnerLld`, `vfpInnerS`). The
frames: `fprintf` at `s - 80`, the outer `_vfprintf_r` at `s - 672`,
`__sbprintf` at `s - 1936` (its `FILE` at `s - 1912`), the inner run at
`s - 2528`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem fprintf_sb (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hneed : 4000 ≤ need) (hs2 : need ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hal : s.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0) (hN : N < 2 ^ 31) (hbl : bytes.length < 2 ^ 31)
    (h2 : R 2 = s) (hstd : R 10 = 0x8001bb20#64)
    (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64) (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    (hSo : StdoutSb Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64)
    (hV : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = s - 1936#64 → R0 10 = 0x8001b538#64 →
      R0 11 = s - 1936#64 + 24#64 → R0 12 = R 11 → R0 13 = s - 80#64 + 32#64 → R0 1 = 0x8000de30#64 →
      SbFile Mt0 (s - 1936#64 + 24#64) [] →
      Frame Mt0 Mt (fun a => s.toNat - 1936 ≤ a ∧ a < s.toNat) →
      ldv .ld Mt0 (s - 80#64 + 32#64).toNat = R 12 →
      (∀ R' M' out pend', bytes = out ++ pend' → R' 2 = s - 1936#64 → R' 1 = 0x8000de30#64 →
        R' 10 = BitVec.ofNat 64 N → (∀ x ∈ vfpSaved, R' x = R0 x) → SbFile M' (s - 1936#64 + 24#64) pend' →
        Frame M' Mt0 (InnerReg (s - 1936#64 + 24#64).toNat ((s - 1936#64).toNat - 592)) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000de30#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 N) → Frame M' Mt (FpReg (s.toNat - 80)) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  have e80 : (s - 80#64).toNat = s.toNat - 80 := toNat_sub_lit (by decide) (by omega)
  have e672 : (s - 80#64 - 592#64).toNat = s.toNat - 672 := by
    rw [toNat_sub_lit (by decide) (by rw [e80]; omega), e80]; omega
  have e1936 : (s - 1936#64).toNat = s.toNat - 1936 := toNat_sub_lit (by decide) (by omega)
  have hsf : s - 80#64 + 80#64 = s := by rw [BitVec.sub_add_cancel]
  have hso : s - 80#64 - 592#64 + 592#64 = s - 80#64 := by rw [BitVec.sub_add_cancel]
  have hsb : s - 80#64 - 592#64 - 1264#64 = s - 1936#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_lit (by decide) (by rw [e672]; omega), e672, e1936]; omega
  have hsb' : s - 1936#64 + 1264#64 = s - 80#64 - 592#64 := by rw [← hsb, BitVec.sub_add_cancel]
  have hsoC : 0x8001ad10 ≤ (s - 80#64).toNat := by rw [e80]; omega
  refine fprintf_wrap (sf := s - 80#64) hlive (by rw [e80]; omega) (by rw [e80]; omega) hs3 hs4
    (by rw [e80]; omega) hra (by rw [hsf]; exact h2) himp hDA
    (fun R0 Mt0 h2' h10' h11' h12' h13' h1' hfr0 harg hk0 => ?_) (fun R' M' hr hf => hk R' M' hr (by rw [e80] at hf; exact hf))
  have hl0 : ∀ (kd : MKind) (a : Nat), a + 8 ≤ s.toNat - 80 → widthOfM kd ≤ 8 → ldv kd Mt0 a = ldv kd Mt a :=
    fun kd a ha hw => hfr0.ldv kd fun j hj h => by rw [e80] at h; omega
  have hSo0 : StdoutSb Mt0 := ⟨(hl0 _ _ (by omega) (by decide)).trans hSo.flagsU,
    (hl0 _ _ (by omega) (by decide)).trans hSo.flags, (hl0 _ _ (by omega) (by decide)).trans hSo.fdU,
    (hl0 _ _ (by omega) (by decide)).trans hSo.fd, (hl0 _ _ (by omega) (by decide)).trans hSo.flags2,
    (hl0 _ _ (by omega) (by decide)).trans hSo.cookie, (hl0 _ _ (by omega) (by decide)).trans hSo.writer,
    (hl0 _ _ (by omega) (by decide)).trans hSo.sinit⟩
  refine vfp_outer (sp := s - 80#64 - 592#64) (N := N) (bytes := bytes) hlive (by rw [e672]; omega)
    (by rw [e672]; omega) hs3 hs4 (by rw [e672]; omega) (by rw [h1']; decide) (by rw [h2', hso])
    h10' (h11'.trans hstd) h12' h13' ((hl0 _ _ (by omega) (by decide)).trans hdec) hdA hdv hSo0
    (by rw [hl0 _ _ (by omega) (by decide)]; exact hbase)
    (fun R1 Mt1 h2'' h10'' h11'' h12'' h13'' h1'' hfr1 hk1 => ?_) fun R' M' e10 e2 e1 ek hfr => ?_
  rotate_left
  · rw [h1']; exact hk0 R' M' e10 (e2.trans h2') (e1.trans h1') (fun x hx => (ek x hx))
      (by rw [e672] at hfr; rw [e80, Nat.sub_sub]; exact hfr)
  have e48 : (s - 80#64 + 32#64).toNat = s.toNat - 48 := by rw [toNat_add_lit (by rw [e80]; omega), e80]; omega
  have hl1 : ∀ (kd : MKind) (a : Nat), a + 8 ≤ s.toNat - 672 ∨ s.toNat - 80 ≤ a → widthOfM kd ≤ 8 →
      ldv kd Mt1 a = ldv kd Mt0 a :=
    fun kd a ha hw => hfr1.ldv kd fun j hj h => by rw [e672] at h; omega
  have hSo1 : StdoutSb Mt1 := ⟨(hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.flagsU,
    (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.flags, (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.fdU,
    (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.fd, (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.flags2,
    (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.cookie, (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.writer,
    (hl1 _ _ (.inl (by omega)) (by decide)).trans hSo0.sinit⟩
  refine sbprintf_run (sp := s - 1936#64) (N := N) (bytes := bytes) hlive hlive' hsub (by rw [e1936]; omega)
    (by rw [e1936]; omega) hs3 hs4 (by rw [e1936]; omega) (by rw [h1'']; decide) hN hbl (h2''.trans hsb'.symm)
    h10'' h11'' rfl rfl hSo1 (fun R2 Mt2 a2 a10 a11 a12 a13 a1 hsbf hfr2 hk2 => ?_)
    fun R' M' e10 e2 e1 ek hfr => ?_
  · have hfrA : Frame Mt2 Mt (fun a => s.toNat - 1936 ≤ a ∧ a < s.toNat) := by
      refine ((hfr0.mono fun a h => ?_).trans (hfr1.mono fun a h => ?_)).trans (hfr2.mono fun a h => ?_)
      · rw [e80] at h
        exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
      · rw [e672] at h
        exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
      · rw [e1936] at h
        exact ⟨h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
    have hA : ldv .ld Mt2 (s - 80#64 + 32#64).toNat = R 12 := by
      rw [hfr2.ldv .ld fun j hj h => by simp only [widthOfM] at hj; rw [e1936, e48] at h; omega,
        hl1 _ _ (.inr (by rw [e48]; omega)) (by decide)]
      exact harg
    exact hV R2 Mt2 a2 a10 a11 (by rw [a12, h12'']; try rw [h12']) (by rw [a13, h13'']; try rw [h13'])
      a1 hsbf hfrA hA hk2
  · rw [h1'']; refine hk1 R' M' e10 (e2.trans h2'') (e1.trans h1'') (fun x hx => ek x hx) ?_
    rw [e1936] at hfr; rw [e672, Nat.sub_sub]; exact hfr

end VsaIris.Sym.Fp
