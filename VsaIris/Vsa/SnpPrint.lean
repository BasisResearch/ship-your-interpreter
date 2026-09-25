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
  uio : b + l ≤ s - 640 ∨ s - 616 ≤ b

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
  obtain ⟨hb1, hb2, hb3, hbd, hbf, hbfr, -⟩ := PG
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

/-! ## `__ssprint_r`: the iovec loop -/

/-- `_svfprintf_r`'s `uio` (`iov` pointer, count, `resid`). -/
abbrev snpU (s : Nat) : Nat := s - 640
/-- `_svfprintf_r`'s iovec array. -/
abbrev snpIov (s : Nat) : Nat := s - 512

/-- The iovec array holds the pieces `L` (`(base, len)`). -/
def IovAt (Mt : Mem) (s : Nat) (L : List (Nat × Nat)) : Prop :=
  ∀ j (h : j < L.length), ldv .ld Mt (snpIov s + 16 * j) = BitVec.ofNat 64 L[j].1 ∧
    ldv .ld Mt (snpIov s + 16 * j + 8) = BitVec.ofNat 64 L[j].2

/-- Every piece may be copied and reads `g`. -/
def PiecesOK (Dt : Mem) (DA : List Nat) (Mt : Mem) (s dst n : Nat) (g : Nat → BitVec 8)
    (L : List (Nat × Nat)) : Prop :=
  ∀ j (h : j < L.length), PieceGeom s dst n L[j].1 L[j].2 ∧ L[j].2 < 2 ^ 31 ∧
    ReadWin Dt DA (snpS s dst n) Mt L[j].1 (L[j].1 + L[j].2) g

/-- The bytes of the pieces, in order. -/
def catPieces (g : Nat → BitVec 8) (L : List (Nat × Nat)) : List (BitVec 8) :=
  L.flatMap fun p => pieceBytes g p.1 p.2

/-- The pieces' total length (`uio_resid`). -/
def sumLen (L : List (Nat × Nat)) : Nat := (L.map Prod.snd).sum

theorem catPieces_cons (g : Nat → BitVec 8) (p : Nat × Nat) (L : List (Nat × Nat)) :
    catPieces g (p :: L) = pieceBytes g p.1 p.2 ++ catPieces g L := by
  simp [catPieces]

theorem catPieces_append (g : Nat → BitVec 8) (L1 L2 : List (Nat × Nat)) :
    catPieces g (L1 ++ L2) = catPieces g L1 ++ catPieces g L2 := by
  simp [catPieces]

theorem catPieces_take_succ (g : Nat → BitVec 8) (L : List (Nat × Nat)) {i : Nat} (h : i < L.length) :
    catPieces g (L.take (i + 1)) = catPieces g (L.take i) ++ pieceBytes g L[i].1 L[i].2 := by
  rw [List.take_succ, List.getElem?_eq_getElem h, catPieces_append]
  simp [catPieces]

theorem sumLen_drop (L : List (Nat × Nat)) {i : Nat} (h : i < L.length) :
    sumLen (L.drop i) = L[i].2 + sumLen (L.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h]
  simp only [sumLen, List.map_cons, List.sum_cons]

theorem catPieces_of_sumLen_zero (g : Nat → BitVec 8) :
    ∀ L : List (Nat × Nat), sumLen L = 0 → catPieces g L = []
  | [], _ => rfl
  | p :: L, h => by
    simp only [sumLen, List.map_cons, List.sum_cons] at h
    have h1 : p.2 = 0 := by omega
    have h2 : sumLen L = 0 := by simp only [sumLen]; omega
    rw [catPieces_cons, catPieces_of_sumLen_zero g L h2, h1]
    rfl

theorem catPieces_take_drop (g : Nat → BitVec 8) (L : List (Nat × Nat)) (i : Nat) :
    catPieces g L = catPieces g (L.take i) ++ catPieces g (L.drop i) := by
  rw [← catPieces_append, List.take_append_drop]

/-- What `__ssprint_r` writes: the destination, the `FILE`'s cursor words,
the `uio`'s count and `resid`, the frames below `_svfprintf_r`'s. -/
def PrintW (s dst n a : Nat) : Prop :=
  (dst ≤ a ∧ a < dst + n) ∨ (snpFP s ≤ a ∧ a < snpFP s + 16) ∨
    (snpU s + 8 ≤ a ∧ a < snpU s + 24) ∨ (s - 992 ≤ a ∧ a < s - 864)

/-- **`__ssprint_r`'s loop invariant** at the loop head (`0x8000e950`), piece
`i` next: the buffer holds what the pieces before `i` printed, the count and
`resid` are the rest's, the registers are the loop's. -/
structure PrintSt (Dt : Mem) (DA : List Nat) (s dst n : Nat) (g : Nat → BitVec 8)
    (total0 : List (BitVec 8)) (L : List (Nat × Nat)) (R0 R : Nat → BitVec 64) (Mt0 Mt : Mem)
    (i : Nat) : Prop where
  lt : i < L.length
  iov : IovAt Mt s L
  pieces : PiecesOK Dt DA Mt s dst n g L
  buf : BufAt Mt s dst n (total0 ++ catPieces g (L.take i))
  cnt : ldv .lw Mt (snpU s + 8) = BitVec.ofNat 64 (L.length - i)
  res : ldv .ld Mt (snpU s + 16) = BitVec.ofNat 64 (sumLen (L.drop i))
  pos : 0 < sumLen (L.drop i)
  r2 : R 2 = BitVec.ofNat 64 (s - 928)
  r8 : R 8 = BitVec.ofNat 64 (snpIov s + 16 * i)
  r9 : R 9 = BitVec.ofNat 64 (snpU s)
  r14 : R 14 = BitVec.ofNat 64 (sumLen (L.drop i))
  r20 : R 20 = BitVec.ofNat 64 (snpFP s)
  r21 : R 21 = 18446744073709551615#64
  keep : ∀ z, (z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 19 ∨ (22 ≤ z ∧ z ≤ 27)) → R z = R0 z
  frame : ∀ a, ¬ PrintW s dst n a → imgM Mt a = imgM Mt0 a

/-- `__ssprint_r`'s loop exit (`0x8000e99c`): every piece printed. -/
structure PrintEnd (s dst n : Nat) (g : Nat → BitVec 8) (total0 : List (BitVec 8))
    (L : List (Nat × Nat)) (R0 R : Nat → BitVec 64) (Mt0 Mt : Mem) : Prop where
  buf : BufAt Mt s dst n (total0 ++ catPieces g L)
  r2 : R 2 = BitVec.ofNat 64 (s - 928)
  r9 : R 9 = BitVec.ofNat 64 (snpU s)
  keep : ∀ z, (z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 19 ∨ (22 ≤ z ∧ z ≤ 27)) → R z = R0 z
  frame : ∀ a, ¬ PrintW s dst n a → imgM Mt a = imgM Mt0 a

theorem BufAt.transport {Mt Mt' : Mem} {s dst n : Nat} {total : List (BitVec 8)}
    (h : BufAt Mt s dst n total)
    (hM : ∀ a, ((snpFP s ≤ a ∧ a < snpFP s + 18) ∨ (dst ≤ a ∧ a < dst + n)) → imgM Mt' a = imgM Mt a)
    (hn : 0 < n) : BufAt Mt' s dst n total where
  pw := (ldv_agree .ld fun i hi => hM _ (.inl (by simp only [widthOfM] at hi; omega))).trans h.pw
  ww := (ldv_agree .lw fun i hi => hM _ (.inl (by simp only [widthOfM] at hi; omega))).trans h.ww
  fl := (ldv_agree .lh fun i hi => hM _ (.inl (by simp only [widthOfM] at hi; omega))).trans h.fl
  bytes i hi := (hM _ (.inr (by omega))).trans (h.bytes i hi)

theorem IovAt.transport {Mt Mt' : Mem} {s : Nat} {L : List (Nat × Nat)} (h : IovAt Mt s L)
    (hL : L.length ≤ 8)
    (hM : ∀ a, snpIov s ≤ a → a < snpIov s + 128 → imgM Mt' a = imgM Mt a) : IovAt Mt' s L :=
  fun j hj => ⟨(ldv_agree .ld fun i hi => hM _ (by omega) (by simp only [widthOfM] at hi; omega)).trans (h j hj).1,
    (ldv_agree .ld fun i hi => hM _ (by omega) (by simp only [widthOfM] at hi; omega)).trans (h j hj).2⟩

theorem PiecesOK.transport {Dt : Mem} {DA : List Nat} {Mt Mt' : Mem} {s dst n : Nat}
    {g : Nat → BitVec 8} {L : List (Nat × Nat)} (h : PiecesOK Dt DA Mt s dst n g L)
    (hM' : ∀ a, ¬ PrintW s dst n a → imgM Mt' a = imgM Mt a) : PiecesOK Dt DA Mt' s dst n g L := by
  intro j hj
  obtain ⟨PG, hl, hw⟩ := h j hj
  refine ⟨PG, hl, hw.transport fun a h1 h2 => hM' a ?_⟩
  obtain ⟨_, _, _, hd, hf, hfr, hu⟩ := PG
  unfold PrintW; simp only [snpFP, snpU] at *; omega

/-- The loop's continuations, as definitions (the side-condition tactics
rewrite every hypothesis; a definition's arguments are small). -/
def PrintKL (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s dst n : Nat) (g : Nat → BitVec 8)
    (total0 : List (BitVec 8)) (L : List (Nat × Nat)) (R0 : Nat → BitVec 64) (Mt0 : Mem) (i : Nat) : Prop :=
  ∀ R' Mt', PrintSt Dt DA s dst n g total0 L R0 R' Mt0 Mt' i →
    NW live Dt DA (snpS s dst n) Q 0x8000e950#64 R' Mt'

def PrintKX (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s dst n : Nat) (g : Nat → BitVec 8)
    (total0 : List (BitVec 8)) (L : List (Nat × Nat)) (R0 : Nat → BitVec 64) (Mt0 : Mem) : Prop :=
  ∀ R' Mt', PrintEnd s dst n g total0 L R0 R' Mt0 Mt' →
    NW live Dt DA (snpS s dst n) Q 0x8000e99c#64 R' Mt'

/-- The memory after `__ssprint_r` stores the new `resid`. -/
theorem print_resid_mem {Dt : Mem} {DA : List Nat} {s dst n : Nat} {g : Nat → BitVec 8}
    {total : List (BitVec 8)} {L : List (Nat × Nat)} {Mt Mt0 : Mem} (v : BitVec 64)
    (SG : SnpGeom s dst n) (hL8 : L.length ≤ 8)
    (hiov : IovAt Mt s L) (hP : PiecesOK Dt DA Mt s dst n g L) (hB : BufAt Mt s dst n total)
    (hfr : ∀ a, ¬ PrintW s dst n a → imgM Mt a = imgM Mt0 a) :
    IovAt (writeLog Mt [(s - 624, 8, v)]) s L ∧
      PiecesOK Dt DA (writeLog Mt [(s - 624, 8, v)]) s dst n g L ∧
      BufAt (writeLog Mt [(s - 624, 8, v)]) s dst n total ∧
      (∀ a, ¬ PrintW s dst n a → imgM (writeLog Mt [(s - 624, 8, v)]) a = imgM Mt0 a) := by
  obtain ⟨hs1, hs2, hsa, hn0, hn31, hd1, hd2, hdsep⟩ := SG
  have hag : ∀ a, (a < s - 624 ∨ s - 616 ≤ a) → imgM (writeLog Mt [(s - 624, 8, v)]) a = imgM Mt a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  exact ⟨hiov.transport hL8 (fun a h1 h2 => hag a (by simp only [snpIov] at h1 h2; omega)),
    hP.transport fun a ha => hag a (by unfold PrintW snpU at ha; omega),
    hB.transport (fun a ha => hag a (by simp only [snpFP] at ha; omega)) hn0,
    fun a ha => (hag a (by unfold PrintW snpU at ha; omega)).trans (hfr a ha)⟩

/-- The next piece: the loop invariant at `i + 1`. -/
theorem print_next {Dt : Mem} {DA : List Nat} {s dst n : Nat} {g : Nat → BitVec 8}
    {total0 : List (BitVec 8)} {L : List (Nat × Nat)} {R0 R' : Nat → BitVec 64} {Mt Mt0 : Mem}
    {i : Nat} (SG : SnpGeom s dst n) (hL8 : L.length ≤ 8) (hi : i < L.length)
    (hiov : IovAt Mt s L) (hP : PiecesOK Dt DA Mt s dst n g L)
    (hB : BufAt Mt s dst n (total0 ++ catPieces g (L.take (i + 1))))
    (hcnt : ldv .lw Mt (snpU s + 8) = BitVec.ofNat 64 (L.length - (i + 1)))
    (hfr : ∀ a, ¬ PrintW s dst n a → imgM Mt a = imgM Mt0 a)
    (hpos : 0 < sumLen (L.drop (i + 1)))
    (h2 : R' 2 = BitVec.ofNat 64 (s - 928)) (h8 : R' 8 = BitVec.ofNat 64 (snpIov s + 16 * (i + 1)))
    (h9 : R' 9 = BitVec.ofNat 64 (snpU s)) (h14 : R' 14 = BitVec.ofNat 64 (sumLen (L.drop (i + 1))))
    (h20 : R' 20 = BitVec.ofNat 64 (snpFP s)) (h21 : R' 21 = 18446744073709551615#64)
    (hkp : ∀ z, (z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 19 ∨ (22 ≤ z ∧ z ≤ 27)) → R' z = R0 z) :
    PrintSt Dt DA s dst n g total0 L R0 R' Mt0
      (writeLog Mt [(s - 624, 8, BitVec.ofNat 64 (sumLen (L.drop (i + 1))))]) (i + 1) := by
  have SG' := SG
  obtain ⟨hs1, hs2, hsa, hn0, hn31, hd1, hd2, hdsep⟩ := SG'
  obtain ⟨hiov', hP', hB', hfr'⟩ := print_resid_mem (BitVec.ofNat 64 (sumLen (L.drop (i + 1)))) SG hL8
    hiov hP hB hfr
  have hi1 : i + 1 < L.length := by
    apply Classical.byContradiction; intro hge
    rw [List.drop_of_length_le (by omega)] at hpos; simp [sumLen] at hpos
  refine ⟨hi1, hiov', hP', hB', ?_, ?_, hpos, h2, h8, h9, h14, h20, h21, hkp, hfr'⟩
  · simp only [snpU] at hcnt ⊢
    rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), hcnt]
  · simp only [snpU]; rw [show s - 640 + 16 = s - 624 by omega]; exact ldv_store_hit _ _ _

/-- **After a piece** (`0x8000e980`, `__ssputs_r` returned `0`): `resid -= len`,
next piece or exit. -/
theorem ssprint_iterB {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (g : Nat → BitVec 8) (total0 : List (BitVec 8)) (L : List (Nat × Nat)) (R0 R : Nat → BitVec 64)
    (Mt0 Mt : Mem) (i : Nat) (SG : SnpGeom s dst n) (hL8 : L.length ≤ 8) (hi : i < L.length)
    (hiov : IovAt Mt s L) (hP : PiecesOK Dt DA Mt s dst n g L)
    (hB : BufAt Mt s dst n (total0 ++ catPieces g (L.take (i + 1))))
    (hcnt : ldv .lw Mt (snpU s + 8) = BitVec.ofNat 64 (L.length - (i + 1)))
    (hres : ldv .ld Mt (snpU s + 16) = BitVec.ofNat 64 (sumLen (L.drop i)))
    (hsum : sumLen (L.drop i) < 2 ^ 32)
    (h2 : R 2 = BitVec.ofNat 64 (s - 928)) (h8 : R 8 = BitVec.ofNat 64 (snpIov s + 16 * i))
    (h9 : R 9 = BitVec.ofNat 64 (snpU s)) (h10 : R 10 = 0#64) (h18 : R 18 = BitVec.ofNat 64 L[i].2)
    (h20 : R 20 = BitVec.ofNat 64 (snpFP s)) (h21 : R 21 = 18446744073709551615#64)
    (hkp : ∀ z, (z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 19 ∨ (22 ≤ z ∧ z ≤ 27)) → R z = R0 z)
    (hfr : ∀ a, ¬ PrintW s dst n a → imgM Mt a = imgM Mt0 a)
    (hkL : PrintKL live Dt DA Q s dst n g total0 L R0 Mt0 (i + 1))
    (hkX : PrintKX live Dt DA Q s dst n g total0 L R0 Mt0) :
    NW live Dt DA (snpS s dst n) Q 0x8000e980#64 R Mt := by
  have SG' := SG
  obtain ⟨hs1, hs2, hsa, hn0, hn31, hd1, hd2, hdsep⟩ := SG'
  simp only [snpU, snpIov] at h8 h9 hres ⊢
  have hsd := sumLen_drop L hi
  have hres' : ldv .ld Mt (BitVec.ofNat 64 (s - 640 + 16)).toNat = BitVec.ofNat 64 (sumLen (L.drop i)) := by
    rw [toNat_ofNat_lt (by omega)]; exact hres
  have hrem : BitVec.ofNat 64 (sumLen (L.drop i)) - BitVec.ofNat 64 L[i].2 =
      BitVec.ofNat 64 (sumLen (L.drop (i + 1))) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have eU : (BitVec.ofNat 64 (s - 640 + 16)).toNat = s - 624 := by rw [toNat_ofNat_lt (by omega)]; omega
  have hres2 : ldv .ld Mt (s - 624) = BitVec.ofNat 64 (sumLen (L.drop i)) := by
    rw [show s - 624 = s - 640 + 16 by omega]; exact hres
  nx_run hlive using [ofNat_add_ofNat, h2, h8, h9, h10, h18, h21, hres', hres2, hrem, eU] at 0x8000e950 0x8000e99c
  all_goals rename_i hb
  -- `__ssputs_r` never fails on a string `FILE`
  case hT.hk.hk.hk.hk.hk.hk.hk.hk.hk.hal | hT.hk.hk.hk.hk.hk.hk.hk.hk.hk.hk =>
    exfalso; rw [h10, h21] at hb; exact absurd hb (by decide)
  all_goals (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hb)
  · -- next piece
    have hpos : 0 < sumLen (L.drop (i + 1)) := by
      rcases Nat.eq_zero_or_pos (sumLen (L.drop (i + 1))) with h0 | h0
      · exact absurd (by rw [h0]) hb
      · exact h0
    refine hkL _ _ (print_next SG hL8 hi hiov hP hB hcnt hfr hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h2
    · simp only [snpIov]; rw [show s - 512 + 16 * i + 16 = s - 512 + 16 * (i + 1) by omega]
    · exact h9
    · exact h20
    · exact h21
    · intro z hz
      simp only [show z ≠ 14 by omega, show z ≠ 8 by omega, show z ≠ 13 by omega, ite_false]
      exact hkp z hz
  · -- the last piece
    have h0 : sumLen (L.drop (i + 1)) = 0 := by
      apply Classical.byContradiction; intro hne
      exact hb (ofNat_ne_of_lt (by omega) (by decide) hne)
    have hcat : catPieces g L = catPieces g (L.take (i + 1)) := by
      rw [catPieces_take_drop g L (i + 1), catPieces_of_sumLen_zero g _ h0, List.append_nil]
    obtain ⟨-, -, hB', hfr'⟩ := print_resid_mem (BitVec.ofNat 64 (sumLen (L.drop (i + 1)))) SG hL8
      hiov hP hB hfr
    refine hkX _ _ ⟨by rw [hcat]; exact hB', ?_, ?_, ?_, hfr'⟩
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h2
    · exact h9
    · intro z hz
      simp only [show z ≠ 14 by omega, show z ≠ 8 by omega, show z ≠ 13 by omega, ite_false]
      exact hkp z hz

end VsaIris.Sym
