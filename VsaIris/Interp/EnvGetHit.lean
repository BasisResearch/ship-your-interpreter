import VsaIris.Interp.EnvGetSpans

/-!
# `env_get`'s hit arm, first-order

`0x80002c70`: copy `vals[i]` into `out`, `a0 := 1`, then the epilogue.
-/

namespace VsaIris.Interp

open VsaIris.Sym VsaIris.MallocFast Vsa.MemRepr Vsa.Sim

/-- The hit copy `0x80002c70`: `out := vals[i]`, `a0 := 1`. -/
theorem get_copy {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hlay : FrameLayout (imgM Mt) G n) (hi : i < n)
    (h8 : R 8 = BitVec.ofNat 64 i) (he : (R 20).toNat = G.e) (hout : (R 21).toNat = out)
    (hwo : 0x80000000 ≤ out ∧ out + 24 ≤ 0x100000000 ∧ htifLo + 16 ≤ out ∧ out % 8 = 0)
    (hdv : out + 24 ≤ G.pv ∨ G.vblk.1 + G.vblk.2 ≤ out) :
    Span live (getS s out G) 0x80002c70#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002ca0#64 ∧ CopyOut out (G.pv + 24 * i) Mt Mt' ∧
        R' 10 = 1#64 ∧ ∀ k, k ≠ 10 → k ≠ 14 → k ≠ 15 → R' k = R k) := by
  intro Q hk
  obtain ⟨hcap, -, -, hv1, hv2, -, hvw⟩ := hlay.slot hi
  have := hvw.lo; have := hvw.hi; have := hvw.htif
  have hw := hlay.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := hlay.sblk
  have := hw.lo; have := hw.hi; have := hw.htif
  have hpv : ldv .ld Mt (R 20 + 16#64).toNat = BitVec.ofNat 64 G.pv := by
    rw [show (R 20 + 16#64).toNat = G.e + 16 by rw [BitVec.toNat_add, he]; simp; omega,
      ldv_ld_img]
    unfold imgW; rw [hlay.vals]
  sx_run hl at 0x80002c84
  rw [hpv, h8, slot24_index i, ← BitVec.ofNat_add]
  generalize hA : BitVec.ofNat 64 (G.pv + 24 * i) = A
  have hAn : A.toNat = G.pv + 24 * i := by
    rw [← hA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  clear hA
  sx_run hl at 0x80002ca0
  have hout8 : (R 21 + 8#64).toNat = out + 8 := by rw [BitVec.toNat_add, hout]; simp; omega
  have hout16 : (R 21 + 16#64).toNat = out + 16 := by rw [BitVec.toNat_add, hout]; simp; omega
  have hA8 : (A + 8#64).toNat = G.pv + 24 * i + 8 := by rw [BitVec.toNat_add, hAn]; simp; omega
  have hA16 : (A + 16#64).toNat = G.pv + 24 * i + 16 := by
    rw [BitVec.toNat_add, hAn]; simp; omega
  refine hk _ _ _ ⟨rfl, ?_, by simp [upd_apply], fun k h10 h14 h15 => by
    simp [upd_apply, h10, h14, h15]⟩
  rw [hout8, hout16, hout, hA8, hA16, hAn]
  refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_hit_eq _ _ rfl]
  · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]

/-- The hit: the copy, then the epilogue, returning 1. -/
theorem get_hit {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s out n i : Nat}
    {r : BitVec 64} {sv : Nat → BitVec 64} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem}
    (hs : htifLo + 16 + 64 ≤ s) (hs' : s ≤ 0x100000000) (hra : r.toNat % 4 = 0)
    (hstk : GetStack s r sv R Mt) (hlay : FrameLayout (imgM Mt) G n) (hi : i < n)
    (h8 : R 8 = BitVec.ofNat 64 i) (he : (R 20).toNat = G.e) (hout : (R 21).toNat = out)
    (hwo : 0x80000000 ≤ out ∧ out + 24 ≤ 0x100000000 ∧ htifLo + 16 ≤ out ∧ out % 8 = 0)
    (hdv : out + 24 ≤ G.pv ∨ G.vblk.1 + G.vblk.2 ≤ out)
    (hsep : out + 24 ≤ s - 64 ∨ s ≤ out) :
    Span live (getS s out G) 0x80002c70#64 R Mt
      (fun pc' R' Mt' => pc' = r ∧ GetRet s r sv 1#64 R' ∧ CopyOut out (G.pv + 24 * i) Mt Mt') :=
  (get_copy hl hlay hi h8 he hout hwo hdv).trans fun pc' R' Mt' ⟨hpc, hco, h10, hk⟩ => by
    subst hpc
    have hstk' : GetStack s r sv R' Mt' :=
      hstk.congr (hk 2 (by decide) (by decide) (by decide))
        (hk 22 (by decide) (by decide) (by decide))
        (fun a h1 h2 => hco.frame a (by omega)) (by unfold htifLo at hs; omega)
    exact (get_epi hl hs hs' hra hstk').mono fun pc'' R'' Mt'' ⟨h1, h2, h3⟩ =>
      ⟨h1, by rw [h10] at h3; exact h3, by subst h2; exact hco⟩

end VsaIris.Interp
