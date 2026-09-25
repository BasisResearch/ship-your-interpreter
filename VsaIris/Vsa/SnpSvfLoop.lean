import VsaIris.Vsa.SnpSvfConv
import Vsa.Sim.SnprintfSpec39
import VsaIris.Vsa.BvLits

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
      SnpW live Dt DA (snpS s dst n) Q 0x80007724#64 R' Mt) :
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 := A.core.r2
  have hf := A.core.fmt
  snp_runF hlive using [h2, hf, sext_zero, BitVec.add_zero] at 0x80007724
  refine hk _ (A.scratch SG ?_ ?_ fun _ _ => rfl) ?_
  · intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-- The data view off everything the run owns, in RAM off the HTIF words. -/
structure DataOff (Dt : Mem) (DA : List Nat) (s dst n : Nat) : Prop where
  ram : ∀ a ∈ DA, 0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000
  htif : ∀ a ∈ DA, a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a
  stack : ∀ a ∈ DA, a < s - 1024 ∨ s ≤ a
  dst : ∀ a ∈ DA, a < dst ∨ dst + n ≤ a
  tab : TabAt Dt DA

/-- A run of data bytes is a piece `_svfprintf_r` may print. -/
theorem pieceSrc_of_data {Dt : Mem} {DA : List Nat} {s dst n b l : Nat} (DO : DataOff Dt DA s dst n)
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
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
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
      SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
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
    (by have := hstr.lo; omega) (pieceSrc_of_data DO SG (by omega) hstr.dom) (by omega) (by omega) DO.tab
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

/-! ## Renderings -/

theorem vSg_eq (v : BitVec 64) : vSg v = if 2 ^ 63 ≤ v.toNat then 45 else 0 := by
  unfold vSg
  have := BitVec.toInt_eq_toNat_cond v
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, if_pos (by rw [this]; split <;> omega)]
  · rw [if_neg h, if_neg (by rw [this]; split <;> omega)]

theorem vMag_eq (v : BitVec 64) : vMag v = if 2 ^ 63 ≤ v.toNat then (-v).toNat else v.toNat := by
  unfold vMag
  have := BitVec.toInt_eq_toNat_cond v
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, if_pos (by rw [this]; split <;> omega)]
  · rw [if_neg h, if_neg (by rw [this]; split <;> omega)]

/-- **An integer's pieces are its decimal rendering**: the sign piece (`'-'`
at `sp + 167` when set) and the `K` digits at `sp + 348 - K`, read through a
`g` that agrees with the memory `Mt` holding them. -/
theorem intPieces {s K : Nat} {v : BitVec 64} {g : Nat → BitVec 8} {Mt : Mem} (hs : 1024 ≤ s)
    (DG : DigitsAt Mt s (vMag v) K) (hg : ∀ a, PZone s a → g a = imgM Mt a)
    (hsg : imgM Mt (s - 864 + 167) = BitVec.ofNat 8 (vSg v)) :
    catPieces g (sgL s (vSg v) ++ [(s - 864 + 348 - K, K)]) = strBytes (Vsa.While.intToString v.toInt) := by
  have hK := DG.le
  have hK1 := DG.pos
  have hdig : pieceBytes g (s - 864 + 348 - K) K = (Vsa.While.natToString (vMag v)).toList.map
      (fun c => BitVec.ofNat 8 c.toNat) := by
    rw [← Vsa.Sim.digits_eq_natToString (vMag v) K (fun k => digB (vMag v) (K - 1 - k)) hK1
      (fun k _ => rfl) DG.hub DG.hlb]
    unfold pieceBytes
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [hg _ (by unfold PZone; omega), show s - 864 + 348 - K + i = s - 864 + 348 - 1 - (K - 1 - i) by omega]
    exact DG.bytes _ (by omega)
  rw [Vsa.Sim.intToString_of_bv v]
  unfold strBytes
  by_cases h : 2 ^ 63 ≤ v.toNat
  · have e : vSg v = 45 := by rw [vSg_eq, if_pos h]
    rw [if_pos h, e]
    simp only [sgL, show (45 : Nat) ≠ 0 by decide, ite_false, List.singleton_append, catPieces_cons,
      catPieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [String.toList_append, List.map_append]
    congr 1
    · simp only [pieceBytes, List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
      rw [hg _ (by unfold PZone; omega), hsg, e]; rfl
    · rw [hdig, vMag_eq, if_pos h]
  · have e : vSg v = 0 := by rw [vSg_eq, if_neg h]
    rw [if_neg h, e]
    simp only [sgL, ite_true, List.nil_append, catPieces, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [hdig, vMag_eq, if_neg h]

theorem lbu_imgM {Mt : Mem} {a b : Nat} (hb : b < 256) (h : ldv .lbu Mt a = BitVec.ofNat 64 b) :
    imgM Mt a = BitVec.ofNat 8 b := by
  simp only [ldv, bytesVal, bytesAt, widthOfM, List.range_one, List.map_cons, List.map_nil,
    List.getD_cons_zero, Nat.add_zero] at h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at this ⊢
  have := (imgM Mt a).isLt
  omega

/-- The integer conversion from the table through `PRINT` and the flush: the
value `v` rendered after the pending literal pieces. -/
def IntK (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s dst n : Nat) (R0 : Nat → BitVec 64)
    (Mt0 : Mem) (p ap c : Nat) (total : List (BitVec 8)) (L : List (Nat × Nat)) (v : BitVec 64) : Prop :=
  ∀ R' Mt' (g : Nat → BitVec 8), (∀ a, (a < s - 1024 ∨ s ≤ a) → g a = imgM Dt a) →
    SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 (c + (strBytes (Vsa.While.intToString v.toInt)).length))
      (total ++ catPieces g L ++ strBytes (Vsa.While.intToString v.toInt)) R' Mt' →
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt'

/-- From the integer's `IntAt` (`0x80008100`) to the loop head. -/
theorem svf_intTail {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (v : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (IA : IntAt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L (vMag v) (vSg v) R Mt)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntK live Dt DA Q s dst n R0 Mt0 p ap c total L v) :
    SnpW live Dt DA (snpS s dst n) Q 0x80008100#64 R Mt := by
  have hs1 := SG.s_lo
  refine svf_digits hlive R Mt SG IA hL hc hsum fun R1 Mt1 K PI DG => ?_
  refine svf_print hlive R1 Mt1 SG PI fun R2 Mt2 g hg1 hg2 A2 => ?_
  have hsg := lbu_imgM (by rcases vSg01 v with h | h <;> rw [h] <;> decide) PI.sign
  rw [toNat_ofNat_lt (by have := SG.s_hi; omega)] at hsg
  have hip := intPieces (by omega) DG hg1 hsg
  rw [List.append_assoc L, catPieces_append, hip] at A2
  have hlen : (strBytes (Vsa.While.intToString v.toInt)).length = K + sgN (vSg v) := by
    rw [← hip, catPieces_append]; simp [sgL, sgN, catPieces]; split <;> simp <;> omega
  rw [← List.append_assoc] at A2
  refine hk R2 Mt2 g hg2 ?_
  rw [hlen]; exact A2

/-- **A `%lld` iteration** (`0x80007720` → `0x80007720`): the literal run
`[p, p + k)`, `"%lld"` at `p + k`, the 64-bit value at `ap`. -/
theorem svf_iterLLD {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 total.length) total R Mt)
    (k : Nat) (FG : FmtGeom DA p (k + 3))
    (hb : ∀ i, i < k → imgM Dt (p + i) ≠ 0#8 ∧ imgM Dt (p + i) ≠ 37#8)
    (hpc : imgM Dt (p + k) = 37#8) (hl1 : imgM Dt (p + k + 1) = 0x6c#8)
    (hl2 : imgM Dt (p + k + 2) = 0x6c#8) (hd : imgM Dt (p + k + 3) = 0x64#8)
    (v : BitVec 64) (hv : ldv .ld Mt0 (BitVec.ofNat 64 ap).toNat = v)
    (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) (hc : total.length + k + 21 < 2 ^ 31)
    (hk : ∀ R' Mt', SvfAt s dst n R0 Mt0 (p + k + 4) (ap + 8)
      (BitVec.ofNat 64 (total.length + k + (strBytes (Vsa.While.intToString v.toInt)).length))
      (total ++ pieceBytes (imgM Dt) p k ++ strBytes (Vsa.While.intToString v.toInt)) R' Mt' →
      SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
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
  rw [hl1] at CA
  refine svf_disp hlive (p + k + 1) 0x6c _ (.inr (.inr ⟨rfl, rfl⟩)) R4 Mt4 (by omega) CA.r25 CA.r24
    CA.r26 CA.r22 DO.tab fun R5 h25 h24 hkp5 => ?_
  have h6 : R5 6 = 0#64 := (hkp5 6 (by decide) (by decide) (by decide) (by decide)).trans CA.r6
  refine svf_convLL hlive (p + k + 2) R5 Mt4 (fun b h1 h2 => FG.dom b (by omega) (by omega))
    (by omega) (by omega) (by omega) hl2 h25 h6 fun R6 h25' h24' h6' hkp6 => ?_
  rw [hd] at h24'
  have k26 : R6 26 = 90#64 := (hkp6 26 (by decide) (by decide) (by decide) (by decide)).trans
    ((hkp5 26 (by decide) (by decide) (by decide) (by decide)).trans CA.r26)
  have k22 : R6 22 = 0x8001a0fc#64 := (hkp6 22 (by decide) (by decide) (by decide) (by decide)).trans
    ((hkp5 22 (by decide) (by decide) (by decide) (by decide)).trans CA.r22)
  refine svf_disp hlive (p + k + 2 + 1) 0x64 _ (.inr (.inl ⟨rfl, rfl⟩)) R6 Mt4 (by omega) h25' h24'
    k26 k22 DO.tab fun R7 h25'' _ hkp7 => ?_
  have kk : ∀ z, z ≠ 6 → z ≠ 14 → z ≠ 15 → z ≠ 24 → z ≠ 25 → R7 z = R4 z := fun z a b c d e =>
    (hkp7 z b c d e).trans ((hkp6 z a c d e).trans (hkp5 z b c d e))
  have St7 := CA.st.update SG (R' := R7) (fun z hz => kk z (by omega) (by omega) (by omega) (by omega) (by omega))
    (kk 23 (by decide) (by decide) (by decide) (by decide) (by decide)) (fun _ _ => rfl) CA.st.core.fmt
    CA.st.core.ret CA.st.core.ap
  have hv' := (ld_ap SG CA.st.core.frame hap1 hap2).trans hv
  refine svf_intQ hlive (p + k + 2 + 1 + 1) v R7 Mt4 SG St7 CA.sign h25''
    ((hkp7 6 (by decide) (by decide) (by decide) (by decide)).trans h6')
    ((kk 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans CA.r20)
    ((kk 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans CA.r27) hv' hap1 hap2
    fun R8 Mt8 IA => ?_
  refine svf_intTail hlive v R8 Mt8 SG IA hLl (by omega) (by omega) fun R9 Mt9 g hg A9 => hk R9 Mt9 ?_
  rw [catPieces_lit g hL, show p + k - p = k by omega,
    pieceBytes_congr (g' := imgM Dt) fun i hi => hg _ (DO.stack _ (FG.dom _ (by omega) (by omega)))] at A9
  rw [show p + k + 2 + 1 + 1 = p + k + 4 by omega] at A9
  exact A9

theorem lw_ap {s dst n ap : Nat} {Mt Mt0 : Mem} (SG : SnpGeom s dst n)
    (hfr : ∀ a, ¬ SvfW s dst n a → imgM Mt a = imgM Mt0 a) (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) :
    ldv .lw Mt (BitVec.ofNat 64 ap).toNat = ldv .lw Mt0 (BitVec.ofNat 64 ap).toNat := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hdsep := SG.d_sep
  rw [toNat_ofNat_lt (by omega)]
  exact ldv_agree .lw fun i hi => hfr _ (by simp only [SvfW, snpFP, widthOfM] at hi ⊢; omega)

/-- **A `%d` iteration** (`0x80007720` → `0x80007720`): the literal run
`[p, p + k)`, `"%d"` at `p + k`, the 32-bit value at `ap` (sign-extended). -/
theorem svf_iterD {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 total.length) total R Mt)
    (k : Nat) (FG : FmtGeom DA p (k + 1))
    (hb : ∀ i, i < k → imgM Dt (p + i) ≠ 0#8 ∧ imgM Dt (p + i) ≠ 37#8)
    (hpc : imgM Dt (p + k) = 37#8) (hd : imgM Dt (p + k + 1) = 0x64#8)
    (v : BitVec 64) (hv : ldv .lw Mt0 (BitVec.ofNat 64 ap).toNat = v)
    (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s) (hc : total.length + k + 21 < 2 ^ 31)
    (hk : ∀ R' Mt', SvfAt s dst n R0 Mt0 (p + k + 2) (ap + 8)
      (BitVec.ofNat 64 (total.length + k + (strBytes (Vsa.While.intToString v.toInt)).length))
      (total ++ pieceBytes (imgM Dt) p k ++ strBytes (Vsa.While.intToString v.toInt)) R' Mt' →
      SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
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
  rw [hd] at CA
  refine svf_disp hlive (p + k + 1) 0x64 _ (.inr (.inl ⟨rfl, rfl⟩)) R4 Mt4 (by omega) CA.r25 CA.r24
    CA.r26 CA.r22 DO.tab fun R7 h25'' _ hkp7 => ?_
  have St7 := CA.st.update SG (R' := R7) (fun z hz => hkp7 z (by omega) (by omega) (by omega) (by omega))
    (hkp7 23 (by decide) (by decide) (by decide) (by decide)) (fun _ _ => rfl) CA.st.core.fmt
    CA.st.core.ret CA.st.core.ap
  have hv' := (lw_ap SG CA.st.core.frame hap1 hap2).trans hv
  refine svf_intD hlive (p + k + 1 + 1) v R7 Mt4 SG St7 CA.sign h25''
    ((hkp7 6 (by decide) (by decide) (by decide) (by decide)).trans CA.r6)
    ((hkp7 20 (by decide) (by decide) (by decide) (by decide)).trans CA.r20)
    ((hkp7 27 (by decide) (by decide) (by decide) (by decide)).trans CA.r27) hv' hap1 hap2
    fun R8 Mt8 IA => ?_
  refine svf_intTail hlive v R8 Mt8 SG IA hLl (by omega) (by omega) fun R9 Mt9 g hg A9 => hk R9 Mt9 ?_
  rw [catPieces_lit g hL, show p + k - p = k by omega,
    pieceBytes_congr (g' := imgM Dt) fun i hi => hg _ (DO.stack _ (FG.dom _ (by omega) (by omega)))] at A9
  rw [show p + k + 1 + 1 = p + k + 2 by omega] at A9
  exact A9

/-- **The last iteration** (`0x80007720` → `_svfprintf_r`'s return): the literal
run `[p, p + k)`, then the NUL. -/
theorem svf_iterEnd {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (DO : DataOff Dt DA s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 total.length) total R Mt)
    (k : Nat) (FG : FmtGeom DA p k)
    (hb : ∀ i, i < k → imgM Dt (p + i) ≠ 0#8 ∧ imgM Dt (p + i) ≠ 37#8)
    (hz : imgM Dt (p + k) = 0#8) (hc : total.length + k + 1 < 2 ^ 31) (hal : (R0 1).toNat % 4 = 0)
    (hk : SvfRetK live Dt DA Q s dst n R0 Mt0 (BitVec.ofNat 64 (total.length + k))
      (total ++ pieceBytes (imgM Dt) p k)) :
    SnpW live Dt DA (snpS s dst n) Q 0x80007720#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hFlo := FG.lo
  have hFhi := FG.hi
  refine svf_head hlive R Mt SG A fun R1 A1 h22 => ?_
  refine svf_scan hlive SG hmb hmx k p R1 Mt A1 h22 FG hb (fun _ R2 Mt2 A2 h22' h10 => ?_)
    (fun h => absurd (h.symm.trans hz) (by decide)) (.inl hz)
  refine svf_lit hlive 0x80007960#64 0x800079b0#64 (.inr ⟨rfl, rfl⟩) R2 Mt2 SG A2 h22'
    (by simpa using h10) (by omega) (by omega) (by omega) (fun _ => pieceSrc_of_data DO SG (by omega)
      (fun b h1 h2 => FG.dom b h1 (by omega))) ?_
  intro R3 Mt3 L hL St3 _
  refine svf_end hlive R3 Mt3 SG St3 hal ?_
  rw [catPieces_lit _ hL, show p + k - p = k by omega]
  rw [pieceBytes_congr (g' := imgM Dt) fun i hi => by
      unfold gOf; rw [if_neg (by have := DO.stack _ (FG.dom (p + i) (by omega) (by omega)); omega)]]
  exact hk

end VsaIris.Sym
