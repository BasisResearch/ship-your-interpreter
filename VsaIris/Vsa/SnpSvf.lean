import VsaIris.Vsa.SnpPrint
import VsaIris.Vsa.SnpStrlen

/-!
# `_svfprintf_r` on `snprintf`'s string `FILE`

`_svfprintf_r(ptr, fp, fmt, ap)` at `sp = s - 272` (its frame `[s - 864,
s - 272)`). The prologue asks the locale for the decimal point (`strlen(".")`)
and clears the multibyte state; the format loop scans literal runs with the
locale's `mbtowc` (`__ascii_mbtowc`), prints each run and each conversion as
iovec pieces, and flushes them through `__ssprint_r` (`ssprint_nw`).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-- The locale's decimal point `"."` (`0x80019770`), a data string. -/
structure DotAt (Dt : Mem) (DA : List Nat) : Prop where
  dom : InDA DA 0x80019770 0x80019772
  b0 : imgM Dt 0x80019770 = 0x2e#8
  b1 : imgM Dt 0x80019771 = 0#8

theorem DotAt.str {Dt : Mem} {DA : List Nat} {S : Nat → Prop} {Mt : Mem} (h : DotAt Dt DA) :
    StrRead Dt DA S Mt 0x80019770 1 (imgM Dt) where
  win a h1 h2 := .inl ⟨h.dom a h1 h2, rfl⟩
  nz i hi := by
    rw [show i = 0 by omega, Nat.add_zero, h.b0]; decide
  nul := h.b1
  lo := by decide
  hi := by decide
  htif := by decide

/-- An indirect jump's target with bit 0 cleared (`memset`'s `jr 12(a3)`),
as a mask the literal simprocs evaluate. -/
theorem update0_and (x : BitVec 64) : Sail.BitVec.update x 0 0#1 = x &&& 0xFFFFFFFFFFFFFFFE#64 := by
  show Sail.BitVec.updateSubrange' x 0 1 (0#1) = _
  have hmask : (~~~(((BitVec.allOnes 1).zeroExtend 64) <<< 0) : BitVec 64) = 0xFFFFFFFFFFFFFFFE#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hy : (((0#1 : BitVec 1).zeroExtend 64) <<< 0 : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [Sail.BitVec.updateSubrange', hmask, hy, BitVec.or_zero, BitVec.and_comm]

/-- The string `FILE`'s flags, unsigned. -/
theorem lhu_of_lh {Mt : Mem} {a : Nat} (h : ldv .lh Mt a = 0x208#64) : ldv .lhu Mt a = 0x208#64 := by
  simp only [ldv, bytesVal, widthOfM] at h ⊢
  generalize ((bytesAt (imgM Mt) a 2).getD 1 0#8).append ((bytesAt (imgM Mt) a 2).getD 0 0#8) = v at h ⊢
  have h2 := congrArg (fun x : BitVec 64 => x.setWidth 16) h
  simp only [LeanRV64DExecutable.Functions.sign_extend, LeanRV64DExecutable.zero_extend,
    Sail.BitVec.signExtend, Sail.BitVec.zeroExtend] at h2 ⊢
  have e : BitVec.setWidth 16 (BitVec.signExtend 64 v) = v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
    simp only [hi, decide_true, Bool.true_and]
    split
    · simp only [show i < 64 by omega, decide_true, Bool.true_and]
    · rename_i hc; exact absurd trivial hc
  have hv : v = 0x208#16 := by rw [← e, h2]; decide
  subst hv; decide

/-- A load past a store, both at `ofNat` addresses. -/
theorem ldv_miss_nat (k : MKind) (Mt : Mem) {x y w : Nat} (v : BitVec 64) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (h : x + widthOfM k ≤ y ∨ y + w ≤ x) :
    ldv k (writeLog Mt [((BitVec.ofNat 64 y).toNat, w, v)]) (BitVec.ofNat 64 x).toNat =
      ldv k Mt (BitVec.ofNat 64 x).toNat := by
  rw [toNat_ofNat_lt hx, toNat_ofNat_lt hy]; exact ldv_store_miss k Mt v h

theorem imgM_miss_nat (Mt : Mem) {a y w : Nat} (v : BitVec 64) (hy : y < 2 ^ 64) (h : a < y ∨ y + w ≤ a) :
    imgM (writeLog Mt [((BitVec.ofNat 64 y).toNat, w, v)]) a = imgM Mt a := by
  rw [toNat_ofNat_lt hy]; exact imgM_store_miss Mt v h

/-- Loads and bytes through a run's stores at `ofNat` addresses. -/
macro "svf_mem" : tactic =>
  `(tactic| (simp (disch := (first | omega | (simp only [widthOfM]; omega))) only [ldv_miss_nat, imgM_miss_nat, ldv_store_hit, ldv_lw_zero_eq]))

/-- `_svfprintf_r` after `memset` (`0x800076a4`), from the entry registers `R0`
and memory `Mt0`: the frame at `s - 864`, the first spills, the `FILE`'s
flags, and every byte outside the frame unchanged. -/
structure SvfPro (s : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (R : Nat → BitVec 64) (Mt : Mem) :
    Prop where
  r2 : R 2 = BitVec.ofNat 64 (s - 864)
  r8 : R 8 = R0 10
  r9 : R 9 = BitVec.ofNat 64 (s - 264)
  r22 : R 22 = R0 12
  keep : ∀ z, 18 ≤ z → z ≤ 27 → z ≠ 22 → R z = R0 z
  ra : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 584)).toNat = R0 1
  s0 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 576)).toNat = R0 8
  s1 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 568)).toNat = R0 9
  s6 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 528)).toNat = R0 22
  fp : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 8)).toNat = BitVec.ofNat 64 (s - 264)
  ap : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 24)).toNat = R0 13
  fl : ldv .lhu Mt (BitVec.ofNat 64 (s - 264 + 16)).toNat = 0x208#64
  frame : ∀ a, (a < s - 864 ∨ s - 272 ≤ a) → imgM Mt a = imgM Mt0 a

#ix_piece svfPro_p1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (hs1 : 0x8001c168 + 1024 ≤ s) (hs2 : s ≤ 0x88000000)
    (hsa : s % 16 = 0)
    (h2 : R 2 = BitVec.ofNat 64 (s - 272)) (h11 : R 11 = BitVec.ofNat 64 (s - 264))
    (hdp : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdot : DotAt Dt DA)
    (hfl : ldv .lhu Mt (BitVec.ofNat 64 (s - 264 + 16)).toNat = 0x208#64)
    (eS : BitVec.ofNat 64 (s - 272 + 18446744073709551024) = BitVec.ofNat 64 (s - 864))
    (hK : ∀ R' Mt', SvfPro s R Mt R' Mt' → NW live Dt DA (snpS s dst n) Q 0x800076a4#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007654#64 R Mt by
  nx_run [17] hlive using [ofNat_add_ofNat, h2, h11, hdp, eS]

#ix_piece svfPro_p2 from svfPro_p1 by
  refine strlen_nw hlive hdot.str _ ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide
  intro R' h10' hkp

/-- `strlen`'s kept registers, at the literal values the prologue set. -/
macro "svf_keep " h:ident " [" zs:num,* "]" : tactic => do
  let mut t ← `(tactic| skip)
  for z in zs.getElems do
    let nm := Lean.mkIdent (Lean.Name.mkSimple s!"k{z.getNat}")
    t ← `(tactic| ($t; have $nm := SLKeep.get $h $z (by decide); simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at $nm:ident))
  return t

#ix_piece svfPro_p3 from svfPro_p2 by
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  svf_keep hkp [2, 8, 9, 22, 18, 19, 20, 21, 23, 24, 25, 26, 27]
  nx_run hlive using [ofNat_add_ofNat, k2, k8, k9, k22] at 0x80006b38

#ix_piece svfPro_p4 from svfPro_p3 by
  have h13 : ((15#64 - 8#64) <<< 2 + 2147511088#64 : BitVec 64) = 0x80006b4c#64 := by decide
  have hjr : Sail.BitVec.update (0x80006b4c#64 + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x00c#12)) 0 0#1 =
      0x80006b58#64 := by decide
  refine nt_80006b38 hlive ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h13, hjr]; decide
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h13, hjr]
  nx_run [9] hlive using [ofNat_add_ofNat, k2, k8, k9, k22]

#ix_piece svfPro_p5 from svfPro_p4 by
  refine hK _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k8
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k9
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k22
  · intro z h1 h2 h3
    have := SLKeep.get hkp z (by omega)
    simp only [upd_apply] at this ⊢
    repeat rw [if_neg (by omega)] at this
    repeat rw [if_neg (by omega)]
    exact this
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem; exact hfl
  · intro a ha
    svf_mem

-- `_svfprintf_r`'s prologue to `memset`'s return (`0x80007654` → `0x800076a4`).
#ix_chain svfPro := [svfPro_p1, svfPro_p2, svfPro_p3, svfPro_p4, svfPro_p5]


/-- The spill slots of `_svfprintf_r`'s frame hold the caller's `ra` and
callee-saved registers. -/
structure SvfSaved (Mt : Mem) (s : Nat) (R0 : Nat → BitVec 64) : Prop where
  ra : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 584)).toNat = R0 1
  s0 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 576)).toNat = R0 8
  s1 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 568)).toNat = R0 9
  s2 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 560)).toNat = R0 18
  s3 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 552)).toNat = R0 19
  s4 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 544)).toNat = R0 20
  s5 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 536)).toNat = R0 21
  s6 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 528)).toNat = R0 22
  s7 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 520)).toNat = R0 23
  s8 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 512)).toNat = R0 24
  s9 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 504)).toNat = R0 25
  s10 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 496)).toNat = R0 26
  s11 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 488)).toNat = R0 27

/-- What `_svfprintf_r` (with `__ssprint_r` and `__ssputs_r` below it) may
write: its frames `[s - 992, s - 272)`, the destination and the `FILE`. -/
def SvfW (s dst n a : Nat) : Prop :=
  (s - 992 ≤ a ∧ a < s - 272) ∨ (dst ≤ a ∧ a < dst + n) ∨ (snpFP s ≤ a ∧ a < snpFP s + 16)

/-- **The format loop's head** (`0x80007720`): the format cursor `p`, the
argument cursor `ap`, the return count `rt`, the stream printed so far
`total` (in the buffer, cut at `n - 1`), an empty `uio`, the loop's fixed
registers, the caller's spills, and everything outside `SvfW` as at the
entry. -/
structure SvfAt (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat) (rt : BitVec 64)
    (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (s - 864)
  r8 : R 8 = R0 10
  r9 : R 9 = 0x8001b798#64
  r18 : R 18 = 16#64
  r19 : R 19 = 37#64
  r21 : R 21 = BitVec.ofNat 64 (s - 864 + 352)
  r23 : R 23 = BitVec.ofNat 64 (s - 864 + 352)
  fmt : ldv .ld Mt (BitVec.ofNat 64 (s - 864)).toNat = BitVec.ofNat 64 p
  fp : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 8)).toNat = BitVec.ofNat 64 (s - 264)
  ret : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 16)).toNat = rt
  ap : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 24)).toNat = BitVec.ofNat 64 ap
  uio : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 224)).toNat = BitVec.ofNat 64 (s - 864 + 352)
  cnt : ldv .lw Mt (BitVec.ofNat 64 (s - 864 + 232)).toNat = 0#64
  res : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 240)).toNat = 0#64
  saved : SvfSaved Mt s R0
  buf : BufAt Mt s dst n total
  frame : ∀ a, ¬ SvfW s dst n a → imgM Mt a = imgM Mt0 a

#ix_piece svfPro2_p1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (SP : SvfPro s R0 Mt0 R Mt) (hB : BufAt Mt0 s dst n [])
    (hK : ∀ R' Mt', SvfAt s dst n R0 Mt0 (R0 12).toNat (R0 13).toNat 0#64 [] R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x800076a4#64 R Mt by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := SP.r2
  have h9 := SP.r9
  have hfl := SP.fl
  nx_run [16] hlive using [ofNat_add_ofNat, h2, h9, hfl]

#ix_piece svfPro2_p2 from svfPro2_p1 by
  nx_run hlive using [ofNat_add_ofNat, h2, h9, hfl] at 0x80007720

#ix_piece svfPro2_p3 from svfPro2_p2 by
  have hs3 := SG.n_pos
  refine hK _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done))
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact SP.r8
  · svf_mem; rw [SP.r22]; simp
  · svf_mem; exact SP.fp
  · svf_mem
  · svf_mem; rw [SP.ap]; simp
  · svf_mem
  · svf_mem
  · svf_mem
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals svf_mem
    · exact SP.ra
    · exact SP.s0
    · exact SP.s1
    · exact SP.keep 18 (by omega) (by omega) (by omega)
    · exact SP.keep 19 (by omega) (by omega) (by omega)
    · exact SP.keep 20 (by omega) (by omega) (by omega)
    · exact SP.keep 21 (by omega) (by omega) (by omega)
    · exact SP.s6
    · exact SP.keep 23 (by omega) (by omega) (by omega)
    · exact SP.keep 24 (by omega) (by omega) (by omega)
    · exact SP.keep 25 (by omega) (by omega) (by omega)
    · exact SP.keep 26 (by omega) (by omega) (by omega)
    · exact SP.keep 27 (by omega) (by omega) (by omega)
  · have hdsep := SG.d_sep
    refine hB.transport (fun a ha => ?_) hs3
    simp only [snpFP] at ha
    svf_mem
    exact SP.frame a (by omega)
  · intro a ha
    simp only [SvfW, snpFP] at ha
    svf_mem
    exact SP.frame a (by omega)

-- `memset`'s return to the loop head (`0x800076a4` → `0x80007720`).
#ix_chain svfPro2 := [svfPro2_p1, svfPro2_p2, svfPro2_p3]

/-- **`_svfprintf_r`'s prologue** (`0x80007654`, `sp = s - 272`, `fp = s - 264`):
the loop head's state `SvfAt` with the format and argument cursors from `a2`,
`a3`, nothing printed. -/
theorem svf_entry {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (h2 : R 2 = BitVec.ofNat 64 (s - 272)) (h11 : R 11 = BitVec.ofNat 64 (s - 264))
    (hdp : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdot : DotAt Dt DA) (hB : BufAt Mt s dst n [])
    (hK : ∀ R' Mt', SvfAt s dst n R Mt (R 12).toNat (R 13).toNat 0#64 [] R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80007720#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007654#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hfl : ldv .lhu Mt (BitVec.ofNat 64 (s - 264 + 16)).toNat = 0x208#64 := by
    rw [toNat_ofNat_lt (by omega)]
    exact lhu_of_lh hB.fl
  refine svfPro hlive R Mt (by omega) hs2 SG.s_al h2 h11 hdp hdot hfl ?_ fun R' Mt' SP =>
    svfPro2 hlive R Mt R' Mt' SG SP hB hK
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

end VsaIris.Sym
