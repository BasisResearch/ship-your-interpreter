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
    {o : Bool} (hSo : StdoutSbAt (consoleFlagsV o) Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64)
    (hV : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = s - 1936#64 → R0 10 = 0x8001b538#64 →
      R0 11 = s - 1936#64 + 24#64 → R0 12 = R 11 → R0 13 = s - 80#64 + 32#64 → R0 1 = 0x8000de30#64 →
      SbFile Mt0 (s - 1936#64 + 24#64) [] →
      Frame Mt0 Mt (fun a => (s.toNat - 1936 ≤ a ∧ a < s.toNat) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32)) →
      ldv .ld Mt0 (s - 80#64 + 32#64).toNat = R 12 →
      (∀ R' M' out pend', bytes = out ++ pend' → R' 2 = s - 1936#64 → R' 1 = 0x8000de30#64 →
        R' 10 = BitVec.ofNat 64 N → (∀ x ∈ vfpSaved, R' x = R0 x) → SbFile M' (s - 1936#64 + 24#64) pend' →
        Frame M' Mt0 (InnerReg (s - 1936#64 + 24#64).toNat ((s - 1936#64).toNat - 592)) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000de30#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 N) → Frame M' Mt (FpReg (s.toNat - 80)) →
      ldv .lh M' 0x8001bb30 = 0x200a#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
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
    (fun R0 Mt0 h2' h10' h11' h12' h13' h1' hfr0 harg hk0 => ?_) (fun R' M' hr hf hl => hk R' M' hr (by rw [e80] at hf; exact hf) hl)
  have hl0 : ∀ (kd : MKind) (a : Nat), a + 8 ≤ s.toNat - 80 → widthOfM kd ≤ 8 → ldv kd Mt0 a = ldv kd Mt a :=
    fun kd a ha hw => hfr0.ldv kd fun j hj h => by rw [e80] at h; omega
  have hSo0 := hSo.frame hfr0 fun a h1 h2 h => by rw [e80] at h; omega
  refine vfp_outer (sp := s - 80#64 - 592#64) (N := N) (bytes := bytes) hlive (by rw [e672]; omega)
    (by rw [e672]; omega) hs3 hs4 (by rw [e672]; omega) (by rw [h1']; decide) (by rw [h2', hso])
    h10' (h11'.trans hstd) h12' h13' ((hl0 _ _ (by omega) (by decide)).trans hdec) hdA hdv hSo0
    (by rw [hl0 _ _ (by omega) (by decide)]; exact hbase)
    (fun R1 Mt1 h2'' h10'' h11'' h12'' h13'' h1'' hSo1 hfr1 hk1 => ?_) fun R' M' e10 e2 e1 ek hfr hl => ?_
  rotate_left
  · rw [h1']; exact hk0 R' M' e10 (e2.trans h2') (e1.trans h1') (fun x hx => (ek x hx))
      (by rw [e672] at hfr; rw [e80, Nat.sub_sub]; exact hfr) hl
  have e48 : (s - 80#64 + 32#64).toNat = s.toNat - 48 := by rw [toNat_add_lit (by rw [e80]; omega), e80]; omega
  have hl1 : ∀ (kd : MKind) (a : Nat), s.toNat - 80 ≤ a → widthOfM kd ≤ 8 → ldv kd Mt1 a = ldv kd Mt0 a :=
    fun kd a ha hw => hfr1.ldv kd fun j hj h => by rw [e672] at h; rcases h with h | ⟨h, h'⟩ <;> omega
  refine sbprintf_run (sp := s - 1936#64) (N := N) (bytes := bytes) hlive hlive' hsub (by rw [e1936]; omega)
    (by rw [e1936]; omega) hs3 hs4 (by rw [e1936]; omega) (by rw [h1'']; decide) hN hbl (h2''.trans hsb'.symm)
    h10'' h11'' rfl rfl hSo1 (fun R2 Mt2 a2 a10 a11 a12 a13 a1 hsbf hfr2 hk2 => ?_)
    fun R' M' e10 e2 e1 ek hfr hl => ?_
  · have hfrA : Frame Mt2 Mt (fun a => (s.toNat - 1936 ≤ a ∧ a < s.toNat) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32)) := by
      refine ((hfr0.mono fun a h => ?_).trans (hfr1.mono fun a h => ?_)).trans (hfr2.mono fun a h => ?_)
      · rw [e80] at h
        exact .inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
      · rw [e672] at h
        rcases h with h | h
        · exact .inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
        · exact .inr h
      · rw [e1936] at h
        exact .inl ⟨h.1, Nat.lt_of_lt_of_le h.2 (by omega)⟩
    have hA : ldv .ld Mt2 (s - 80#64 + 32#64).toNat = R 12 := by
      rw [hfr2.ldv .ld fun j hj h => by simp only [widthOfM] at hj; rw [e1936, e48] at h; omega,
        hl1 _ _ (by rw [e48]; omega) (by decide)]
      exact harg
    exact hV R2 Mt2 a2 a10 a11 (by rw [a12, h12'']; try rw [h12']) (by rw [a13, h13'']; try rw [h13'])
      a1 hsbf hfrA hA hk2
  · rw [h1'']; refine hk1 R' M' e10 (e2.trans h2'') (e1.trans h1'') (fun x hx => ek x hx) ?_ hl
    rw [e1936] at hfr; rw [e672, Nat.sub_sub]; exact hfr

/-- The inner `_vfprintf_r`'s geometry under `fprintf` (`sp = s - 2528`, the
stack `FILE` at `f`, the argument slot at `ap`): the bounds `vfpInnerLld` and
`vfpInnerS` take. -/
structure InnerAt (s : BitVec 64) (need : Nat) (sp f ap : BitVec 64) : Prop where
  hs1 : s.toNat - need + 1024 ≤ sp.toNat
  hs2 : sp.toNat + 592 ≤ s.toNat
  hal : sp.toNat % 16 = 0
  hf1 : sp.toNat + 592 ≤ f.toNat
  hf2 : f.toNat + 1208 ≤ s.toNat
  hfa : f.toNat % 8 = 0
  hap1 : sp.toNat + 592 ≤ ap.toNat
  hap2 : ap.toNat + 8 ≤ s.toNat
  hapa : ap.toNat % 8 = 0

/-- **`fprintf(stdout, fmt, arg)`** with the inner `_vfprintf_r` a hook in the
shape `vfpInnerLld`/`vfpInnerS` take: its geometry (`InnerAt`), the stack
`FILE` empty, the locale and the argument word read through the frames. -/
theorem fprintf_via (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hneed : 4000 ≤ need) (hs2 : need ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hal : s.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0) (hN : N < 2 ^ 31) (hbl : bytes.length < 2 ^ 31)
    (h2 : R 2 = s) (hstd : R 10 = 0x8001bb20#64)
    (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64) (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    {o : Bool} (hSo : StdoutSbAt (consoleFlagsV o) Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64) (hloc : LocMb Mt)
    (hI : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem),
      InnerAt s need (s - 2528#64) (s - 1936#64 + 24#64) (s - 80#64 + 32#64) →
      R0 2 = s - 2528#64 + 592#64 → R0 10 = 0x8001b538#64 → R0 11 = s - 1936#64 + 24#64 → R0 12 = R 11 →
      R0 13 = s - 80#64 + 32#64 → (R0 1).toNat % 4 = 0 →
      ldv .ld Mt0 0x8001b898 = 0x80019770#64 → SbFile Mt0 (s - 1936#64 + 24#64) [] → LocMb Mt0 →
      ldv .ld Mt0 (s - 80#64 + 32#64).toNat = R 12 →
      (∀ R' M' out pend', [] ++ bytes = out ++ pend' → R' 2 = R0 2 → R' 1 = R0 1 →
        R' 10 = BitVec.ofNat 64 N → (∀ x ∈ vfpSaved, R' x = R0 x) → SbFile M' (s - 1936#64 + 24#64) pend' →
        LocMb M' → Frame M' Mt0 (InnerReg (s - 1936#64 + 24#64).toNat (s - 2528#64).toNat) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (R0 1) R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 N) → Frame M' Mt (FpReg (s.toNat - 80)) →
      ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  have e1936 : (s - 1936#64).toNat = s.toNat - 1936 := toNat_sub_lit (by decide) (by omega)
  have e2528 : (s - 2528#64).toNat = s.toNat - 2528 := toNat_sub_lit (by decide) (by omega)
  have e80 : (s - 80#64).toNat = s.toNat - 80 := toNat_sub_lit (by decide) (by omega)
  have ef : (s - 1936#64 + 24#64).toNat = s.toNat - 1912 := by
    rw [toNat_add_lit (by rw [e1936]; omega), e1936]; omega
  have eap : (s - 80#64 + 32#64).toNat = s.toNat - 48 := by rw [toNat_add_lit (by rw [e80]; omega), e80]; omega
  have esp : s - 2528#64 + 592#64 = s - 1936#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_lit (by rw [e2528]; omega), e2528, e1936]; omega
  have G : InnerAt s need (s - 2528#64) (s - 1936#64 + 24#64) (s - 80#64 + 32#64) := by
    constructor <;> (try rw [e2528]) <;> (try rw [ef]) <;> (try rw [eap]) <;> omega
  refine fprintf_sb hlive hlive' hsub (N := N) (bytes := bytes) hneed hs2 hs3 hs4 hal hra hN hbl h2 hstd himp
    hDA hdec hdA hdv hSo hbase (fun R0 Mt0 a2 a10 a11 a12 a13 a1 hsb hfr harg hk0 => ?_) hk
  have hl : ∀ (kd : MKind) (a : Nat), a + 8 ≤ 0x8001bb30 → widthOfM kd ≤ 8 → ldv kd Mt0 a = ldv kd Mt a :=
    fun kd a ha hw => hfr.ldv kd fun j hj h => by omega
  have hloc0 : LocMb Mt0 := hloc.frame hfr (fun a h1 h2 h => by omega) (fun h => by omega)
  refine hI R0 Mt0 G (a2.trans esp.symm) a10 a11 a12 a13 (by rw [a1]; decide)
    ((hl _ _ (by omega) (by decide)).trans hdec) hsb hloc0 harg fun R' M' out pend' hb e2 e1 e10 ek hS _ hF => ?_
  rw [a1]; refine hk0 R' M' out pend' (by simpa using hb) (e2.trans a2) (e1.trans a1) e10 ek hS ?_
  rw [e2528] at hF; rw [e1936, Nat.sub_sub]; exact hF

end VsaIris.Sym.Fp
