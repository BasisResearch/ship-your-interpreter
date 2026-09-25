import VsaIris.Vsa.SnpPuts

/-!
# `snprintf`'s output buffer and `__ssprint_r`

Every frame of a `snprintf` run sits at a fixed offset below the caller's
`sp = s`: `snprintf` 272 bytes (its string `FILE` at `s - 264`),
`_svfprintf_r` 592 (the `uio` at `s - 640`, the iovec array at `s - 512`),
`__ssprint_r` 64, `__ssputs_r` 64.

`BufAt Mt s dst n total`: the run has printed the byte stream `total` so far;
the buffer holds `total.take (n - 1)` (C99's truncation), the `FILE`'s `_p`
and `_w` point past it. Every piece `__ssputs_r` copies appends to `total`
(`ssputs_buf`), whatever is cut.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- `snprintf`'s string `FILE`. -/
abbrev snpFP (s : Nat) : Nat := s - 264

/-- The bytes of a piece `[b, b + l)` of an image. -/
def pieceBytes (g : Nat → BitVec 8) (b l : Nat) : List (BitVec 8) :=
  (List.range l).map fun i => g (b + i)

@[simp] theorem pieceBytes_length (g : Nat → BitVec 8) (b l : Nat) : (pieceBytes g b l).length = l := by
  simp [pieceBytes]

/-- The run's output so far: `total`, cut to `n - 1` bytes in `[dst, dst + n)`,
with the `FILE`'s cursor after it. -/
structure BufAt (Mt : Mem) (s dst n : Nat) (total : List (BitVec 8)) : Prop where
  pw : ldv .ld Mt (snpFP s) = BitVec.ofNat 64 (dst + min total.length (n - 1))
  ww : ldv .lw Mt (snpFP s + 12) = BitVec.ofNat 64 (n - 1 - min total.length (n - 1))
  fl : ldv .lh Mt (snpFP s + 16) = 0x208#64
  bytes : ∀ i, i < min total.length (n - 1) → imgM Mt (dst + i) = total.getD i 0

/-- The geometry of a `snprintf(dst, n, …)` call at `sp = s`: the stack
scratch `[s - 1024, s)` in RAM above the HTIF words, the destination window
above them too and apart from the stack. -/
structure SnpGeom (s dst n : Nat) : Prop where
  s_lo : 0x8001ad10 + 1024 ≤ s
  s_hi : s ≤ 0x88000000
  s_al : s % 16 = 0
  n_pos : 0 < n
  n_hi : n < 2 ^ 31
  d_lo : 0x8001ad10 ≤ dst
  d_hi : dst + n ≤ 0x100000000
  d_sep : dst + n ≤ s - 1024 ∨ s ≤ dst

/-- A piece `[b, b + l)` `__ssputs_r` may copy: RAM off the HTIF words, apart
from the destination, the `FILE` and the two callee frames below
`_svfprintf_r`'s. -/
structure PieceGeom (s dst n b l : Nat) : Prop where
  lo : 0x80000000 ≤ b
  hi : b + l ≤ 0x100000000
  htif : b + l ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ b
  dst : b + l ≤ dst ∨ dst + n ≤ b
  fp : b + l ≤ snpFP s ∨ snpFP s + 24 ≤ b
  frames : b + l ≤ s - 992 ∨ s - 864 ≤ b

theorem ReadWin.shrink {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} {lo hi hi' : Nat}
    {g : Nat → BitVec 8} (h : ReadWin Dt DA S Mt lo hi g) (hh : hi' ≤ hi) : ReadWin Dt DA S Mt lo hi' g :=
  fun a h1 h2 => h a h1 (by omega)

theorem getD_append_left {l1 l2 : List (BitVec 8)} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l1 l2 : List (BitVec 8)} {j : Nat} :
    (l1 ++ l2).getD (l1.length + j) 0 = l2.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem pieceBytes_getD {g : Nat → BitVec 8} {b l j : Nat} (h : j < l) :
    (pieceBytes g b l).getD j 0 = g (b + j) := by
  simp [pieceBytes, List.getD_eq_getElem?_getD, h]

/-- **`__ssputs_r` on the output buffer** (called from `__ssprint_r`, `sp = s -
928`): the piece `[b, b + l)` appends to the printed stream. -/
theorem ssputs_buf {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (b l : Nat) (g : Nat → BitVec 8) (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem)
    (SG : SnpGeom s dst n) (PG : PieceGeom s dst n b l) (hl : l < 2 ^ 31)
    (hB : BufAt Mt s dst n total)
    (h2 : R 2 = BitVec.ofNat 64 (s - 928)) (h11 : R 11 = BitVec.ofNat 64 (snpFP s))
    (h12 : R 12 = BitVec.ofNat 64 b) (h13 : R 13 = BitVec.ofNat 64 l) (hal : (R 1).toNat % 4 = 0)
    (hwin : ReadWin Dt DA (snpS s dst n) Mt b (b + l) g)
    (hk : ∀ R' Mt', R' 10 = 0#64 → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 →
      (∀ z, 18 ≤ z → z ≤ 27 → R' z = R z) → BufAt Mt' s dst n (total ++ pieceBytes g b l) →
      (∀ a, (a < dst ∨ dst + n ≤ a) → (a < snpFP s ∨ snpFP s + 16 ≤ a) →
        (a < s - 992 ∨ s - 928 ≤ a) → imgM Mt' a = imgM Mt a) →
      NW live Dt DA (snpS s dst n) Q (R 1) R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x8001438c#64 R Mt := by
  obtain ⟨hs1, hs2, hsa, hn0, hn31, hd1, hd2, hdsep⟩ := SG
  obtain ⟨hb1, hb2, hb3, hbd, hbf, hbfr⟩ := PG
  obtain ⟨hpw, hww, hfl, hbytes⟩ := hB
  simp only [snpFP] at *
  have hm : min total.length (n - 1) ≤ n - 1 := Nat.min_le_right _ _
  refine ssputs_nw hlive (s - 928) (s - 264) (dst + min total.length (n - 1)) b l
    (n - 1 - min total.length (n - 1)) g R Mt (by omega) (by omega) (by omega) hs2 hs1 (by omega)
    (by omega) (by omega) (by omega) ⟨by omega, ⟨by omega, by omega⟩, hd2, hb1, by omega, by omega,
      by omega⟩ (by omega) (by omega) (by omega) h2 h11 h12 h13 hl (by omega) hww hpw hfl hal
    (hwin.shrink (by omega)) (fun R' Mt' h10' h2' h8' h9' hkp PO => hk R' Mt' h10' h2' h8' h9' hkp ?_ ?_)
  · obtain ⟨hcp, hpw', hww', hrest⟩ := PO
    have hlen : min (total ++ pieceBytes g b l).length (n - 1) =
        min total.length (n - 1) + min l (n - 1 - min total.length (n - 1)) := by
      simp only [List.length_append, pieceBytes_length]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [snpFP]; rw [hlen, hpw', Nat.add_assoc]
    · simp only [snpFP]; rw [hlen, hww']; congr 1; omega
    · simp only [snpFP]
      rw [ldv_agree .lh (fun i hi => hrest _ (by simp only [widthOfM] at hi; omega) (by omega) (by omega))]
      exact hfl
    · intro i hi
      rw [hlen] at hi
      by_cases him : i < min total.length (n - 1)
      · rw [hrest _ (by omega) (by omega) (by omega), hbytes i him,
          getD_append_left (by omega)]
      · have hj := hcp (i - min total.length (n - 1)) (by omega)
        have hm' : min total.length (n - 1) = total.length := by omega
        rw [show dst + min total.length (n - 1) + (i - min total.length (n - 1)) = dst + i by omega] at hj
        have e : i = total.length + (i - total.length) := by omega
        rw [hj, e, getD_append_right, pieceBytes_getD (by omega)]
        congr 1; omega
  · intro a h1 h2 h3
    have hm2 : min l (n - 1 - min total.length (n - 1)) ≤ n - 1 - min total.length (n - 1) :=
      Nat.min_le_right _ _
    obtain ⟨_, _, _, hrest⟩ := PO
    have e1 : a < dst + min total.length (n - 1) ∨
        dst + min total.length (n - 1) + min l (n - 1 - min total.length (n - 1)) ≤ a := by omega
    have e2 : a < s - 264 ∨ s - 264 + 16 ≤ a := h2
    have e3 : a < s - 928 - 64 ∨ s - 928 ≤ a := by
      rw [show s - 928 - 64 = s - 992 by omega]; exact h3
    exact hrest a e1 e2 e3

end VsaIris.Sym
