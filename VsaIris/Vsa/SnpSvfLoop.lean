import VsaIris.Vsa.SnpSvfConv

/-!
# `_svfprintf_r`'s format loop

One iteration of the loop (`0x80007720` back to `0x80007720`): the literal run,
one conversion (`%s`, `%d`, `%lld`), `PRINT`, the flush. The data view's bytes
lie in RAM off the HTIF words, off the stack scratch and off the destination
(`DataOff`), so every literal run and `%s` string is a `PieceSrc`.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- The loop head's first instruction (`0x80007720`, `ld s6,0(sp)`): the
cursor into `s6`. -/
theorem svf_head {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (A : SvfAt s dst n R0 Mt0 p ap rt total R Mt)
    (hk : ∀ R', SvfAt s dst n R0 Mt0 p ap rt total R' Mt → R' 22 = BitVec.ofNat 64 p →
      NW live Dt DA (snpS s dst n) Q 0x80007724#64 R' Mt) :
    NW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 := A.core.r2
  have hf := A.core.fmt
  nx_runF hlive using [h2, hf, sext_zero, BitVec.add_zero] at 0x80007724
  refine hk _ (A.scratch SG ?_ ?_ fun _ _ => rfl) ?_
  · intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-- The data view off everything the run owns, in RAM off the HTIF words. -/
structure DataOff (DA : List Nat) (s dst n : Nat) : Prop where
  ram : ∀ a ∈ DA, 0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000
  htif : ∀ a ∈ DA, a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a
  stack : ∀ a ∈ DA, a < s - 1024 ∨ s ≤ a
  dst : ∀ a ∈ DA, a < dst ∨ dst + n ≤ a

/-- A run of data bytes is a piece `_svfprintf_r` may print. -/
theorem pieceSrc_of_data {DA : List Nat} {s dst n b l : Nat} (DO : DataOff DA s dst n)
    (SG : SnpGeom s dst n) (hl31 : l < 2 ^ 31) (hd' : InDA DA b (b + l + 1)) :
    PieceSrc DA s dst n b l := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hd : InDA DA b (b + l + 1) := hd'
  have hb := hd b (by omega) (by omega)
  have he := hd (b + l) (by omega) (by omega)
  have r1 := DO.ram b hb
  have r2 := DO.ram _ he
  -- an interval of data bytes misses each owned interval
  have iv : ∀ lo hi, lo < hi → (∀ a, b ≤ a → a < b + l + 1 → a < lo ∨ hi ≤ a) → b + l ≤ lo ∨ hi ≤ b := by
    intro lo hi hlh h
    by_cases h1 : b + l ≤ lo
    · exact .inl h1
    by_cases h2 : hi ≤ b
    · exact .inr h2
    exfalso
    have := h (max b lo) (Nat.le_max_left _ _) (by omega)
    omega
  have hstk0 : b + l ≤ s - 1024 ∨ s ≤ b := iv _ _ (by omega) fun a h1 h2 => DO.stack a (hd a h1 h2)
  -- one truncated subtraction per `omega` call (two send it into deep recursion)
  have hstk : b + l + 1024 ≤ s ∨ s ≤ b := by
    rcases hstk0 with h | h
    · left; omega
    · right; exact h
  have g3 : b + l ≤ snpFP s ∨ snpFP s + 24 ≤ b := by
    simp only [snpFP]; rcases hstk with h | h
    · left; omega
    · right; omega
  have g4 : b + l ≤ s - 992 ∨ s - 864 ≤ b := by
    rcases hstk with h | h
    · left; omega
    · right; omega
  have g5 : b + l ≤ s - 640 ∨ s - 616 ≤ b := by
    rcases hstk with h | h
    · left; omega
    · right; omega
  have hn := SG.n_pos
  have hdst : b + l ≤ dst ∨ dst + n ≤ b := iv _ _ (by omega) fun a h1 h2 => DO.dst a (hd a h1 h2)
  have hht : b + l ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ b := by
    have := iv 0x8001ad00 0x8001ad10 (by decide) fun a h1 h2 => by
      have h3 := DO.htif a (hd a h1 h2); omega
    omega
  have g1 : 0x80000000 ≤ b := r1.1
  have g2 : b + l ≤ 0x100000000 := by have := r2.2; omega
  exact ⟨⟨g1, g2, hht, hdst, g3, g4, g5⟩, hl31, .inl fun a h1 h2 =>
    ⟨hd a h1 (by omega), DO.stack a (hd a h1 (by omega))⟩⟩

theorem pieceBytes_congr {g g' : Nat → BitVec 8} {b l : Nat} (h : ∀ i, i < l → g (b + i) = g' (b + i)) :
    pieceBytes g b l = pieceBytes g' b l := by
  unfold pieceBytes
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The literal run's pieces: none when the run is empty. -/
theorem catPieces_lit (g : Nat → BitVec 8) {L : List (Nat × Nat)} {p q : Nat}
    (hL : L = [] ∧ p = q ∨ L = [(p, q - p)] ∧ p < q) : catPieces g L = pieceBytes g p (q - p) := by
  rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
  · simp [catPieces, pieceBytes]
  · simp [catPieces]

/-- The `va_list` slot `ap` of `snprintf`'s frame: outside what
`_svfprintf_r` writes. -/
theorem ld_ap {s dst n ap : Nat} {Mt Mt0 : Mem} (SG : SnpGeom s dst n)
    (hfr : ∀ a, ¬ SvfW s dst n a → imgM Mt a = imgM Mt0 a) (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) :
    ldv .ld Mt (BitVec.ofNat 64 ap).toNat = ldv .ld Mt0 (BitVec.ofNat 64 ap).toNat := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hdsep := SG.d_sep
  rw [toNat_ofNat_lt (by omega)]
  exact ldv_agree .ld fun i hi => hfr _ (by simp only [SvfW, snpFP, widthOfM] at hi ⊢; omega)

/-- **A `%s` iteration** (`0x80007720` → `0x80007720`): the literal run `[p, p + k)`,
the `'%s'` at `p + k`, the string at the `va_list`'s `ap`. -/
theorem svf_iterS {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 total.length) total R Mt)
    (k : Nat) (FG : FmtGeom DA p (k + 1))
    (hb : ∀ i, i < k → imgM Dt (p + i) ≠ 0#8 ∧ imgM Dt (p + i) ≠ 37#8)
    (hpc : imgM Dt (p + k) = 37#8) (hsc : imgM Dt (p + k + 1) = 0x73#8)
    (a len : Nat) (hap : ldv .ld Mt0 (BitVec.ofNat 64 ap).toNat = BitVec.ofNat 64 a)
    (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) (hstr : DStr Dt DA a len)
    (hc : total.length + k + len + 1 < 2 ^ 31)
    (hk : ∀ R' Mt', SvfAt s dst n R0 Mt0 (p + k + 2) (ap + 8)
      (BitVec.ofNat 64 (total.length + k + len))
      (total ++ pieceBytes (imgM Dt) p k ++ pieceBytes (imgM Dt) a len) R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hFlo := FG.lo
  have hFhi := FG.hi
  have hFht := FG.htif
  refine svf_head hlive R Mt SG A fun R1 A1 h22 => ?_
  refine svf_scan hlive SG hmb hmx k p R1 Mt A1 h22 ⟨fun b h1 h2 => FG.dom b h1 (by omega), hFlo,
    by omega, by omega⟩ hb (fun h => absurd (h.symm.trans hpc) (by decide)) (fun _ R2 Mt2 A2 h22' h10 => ?_) (.inr hpc)
  refine svf_lit hlive 0x8000775c#64 0x8000776c#64 (.inl ⟨rfl, rfl⟩) R2 Mt2 SG A2 h22'
    (by simpa using h10) (by omega) (by omega) (by omega) (fun _ => pieceSrc_of_data DO SG (by omega)
      (fun b h1 h2 => FG.dom b h1 (by omega))) ?_
  intro R3 Mt3 L hL St3 h22''
  have hLl : L.length ≤ 1 := by rcases hL with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have hLs : sumLen L = k := by rcases hL with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [sumLen] <;> omega
  refine svf_convStart hlive (p + k) R3 Mt3 SG St3 h22'' (fun b h1 h2 => FG.dom b (by omega) (by omega))
    (by omega) (by omega) (by omega) fun R4 Mt4 CA => ?_
  rw [hsc] at CA
  have hap' := (ld_ap SG CA.st.core.frame hap1 hap2).trans hap
  refine svf_convS hlive (p + k) a len R4 Mt4 SG CA hLl hap' hap1 hap2 (by omega) hstr
    (by have := hstr.lo; omega) (pieceSrc_of_data DO SG (by omega) hstr.dom) (by omega) (by omega)
    fun R5 Mt5 PI => ?_
  refine svf_print hlive R5 Mt5 SG PI fun R6 Mt6 g hg1 hg2 A6 => hk R6 Mt6 ?_
  have e1 : total.length + (p + k - p) + (len + sgN 0) = total.length + k + len := by simp [sgN]
  have e2 : catPieces g (L ++ sgL s 0 ++ [(a, len)]) = pieceBytes (imgM Dt) p k ++ pieceBytes (imgM Dt) a len := by
    rw [catPieces_append, catPieces_append, catPieces_lit g hL]
    simp only [sgL, ite_true, catPieces, List.flatMap_nil, List.append_nil, List.flatMap_cons]
    rw [show p + k - p = k by omega]
    congr 1
    · exact pieceBytes_congr fun i hi => hg2 _ (DO.stack _ (FG.dom _ (by omega) (by omega)))
    · exact pieceBytes_congr fun i hi => hg2 _ (DO.stack _ (hstr.dom _ (by omega) (by omega)))
  rw [e1, e2, ← List.append_assoc] at A6
  exact A6

end VsaIris.Sym
