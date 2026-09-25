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
  `(tactic| (simp (disch := (first | omega | (simp only [widthOfM]; omega))) only [ldv_miss_nat, imgM_miss_nat, ldv_store_hit, ldv_lw_zero_eq, ldv_lw_store4]))

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

/-- What the format loop keeps throughout: the format cursor `p` (at `sp`),
the argument cursor `ap`, the return count `rt`, the stream printed so far
`total` (in the buffer, cut at `n - 1`), the loop's fixed registers, the
caller's spills, and everything outside `SvfW` as at the entry. -/
structure SvfCore (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat) (rt : BitVec 64)
    (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (s - 864)
  r8 : R 8 = R0 10
  r9 : R 9 = 0x8001b798#64
  r18 : R 18 = 16#64
  r19 : R 19 = 37#64
  r21 : R 21 = BitVec.ofNat 64 (s - 864 + 352)
  fmt : ldv .ld Mt (BitVec.ofNat 64 (s - 864)).toNat = BitVec.ofNat 64 p
  fp : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 8)).toNat = BitVec.ofNat 64 (s - 264)
  ret : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 16)).toNat = rt
  ap : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 24)).toNat = BitVec.ofNat 64 ap
  uio : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 224)).toNat = BitVec.ofNat 64 (s - 864 + 352)
  saved : SvfSaved Mt s R0
  buf : BufAt Mt s dst n total
  frame : ∀ a, ¬ SvfW s dst n a → imgM Mt a = imgM Mt0 a

/-- **The format loop's head** (`0x80007720`): `SvfCore` and an empty `uio`. -/
structure SvfAt (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat) (rt : BitVec 64)
    (total : List (BitVec 8)) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  core : SvfCore s dst n R0 Mt0 p ap rt total R Mt
  r23 : R 23 = BitVec.ofNat 64 (s - 864 + 352)
  cnt : ldv .lw Mt (BitVec.ofNat 64 (s - 864 + 232)).toNat = 0#64
  res : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 240)).toNat = 0#64

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
  refine hK _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done))
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact SP.r8
  · svf_mem; rw [SP.r22]; simp
  · svf_mem; exact SP.fp
  · svf_mem
  · svf_mem; rw [SP.ap]; simp
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
  · svf_mem
  · svf_mem

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

/-! ## The format scan -/

/-- The loop's fixed registers. -/
def SvfRegs (R' R : Nat → BitVec 64) : Prop :=
  ∀ z, z = 2 ∨ z = 8 ∨ z = 9 ∨ z = 18 ∨ z = 19 ∨ z = 21 → R' z = R z

/-- The bytes `SvfCore` reads besides the format, return and argument slots:
the `FILE` and `uio` pointers, the spills, and everything outside the frames. -/
def SvfKeep (s a : Nat) : Prop :=
  (s - 864 + 8 ≤ a ∧ a < s - 864 + 16) ∨ (s - 864 + 224 ≤ a ∧ a < s - 864 + 232) ∨
    (s - 864 + 488 ≤ a ∧ a < s - 272) ∨ a < s - 992 ∨ s - 272 ≤ a

/-- **`SvfCore` across a stretch of the loop**: the kept bytes unchanged, the
fixed registers kept, new format, return and argument slots. -/
theorem SvfCore.update {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap p' ap' : Nat}
    {rt rt' : BitVec 64} {total : List (BitVec 8)} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (A : SvfCore s dst n R0 Mt0 p ap rt total R Mt) (SG : SnpGeom s dst n) (hR : SvfRegs R' R)
    (hM : ∀ a, SvfKeep s a → imgM Mt' a = imgM Mt a)
    (hf : ldv .ld Mt' (BitVec.ofNat 64 (s - 864)).toNat = BitVec.ofNat 64 p')
    (hr : ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + 16)).toNat = rt')
    (ha : ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + 24)).toNat = BitVec.ofNat 64 ap') :
    SvfCore s dst n R0 Mt0 p' ap' rt' total R' Mt' := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hdsep := SG.d_sep
  have ag : ∀ (k : MKind) (off : Nat), ((8 ≤ off ∧ off + widthOfM k ≤ 16) ∨
      (224 ≤ off ∧ off + widthOfM k ≤ 232) ∨ 488 ≤ off) → off + widthOfM k ≤ 592 →
      ldv k Mt' (BitVec.ofNat 64 (s - 864 + off)).toNat = ldv k Mt (BitVec.ofNat 64 (s - 864 + off)).toNat :=
    fun k off h1 h2 => by
      rw [toNat_ofNat_lt (by omega)]
      exact ldv_agree k fun i hi => hM _ (by unfold SvfKeep; omega)
  have sv := A.saved
  refine ⟨(hR 2 (by omega)).trans A.r2, (hR 8 (by omega)).trans A.r8, (hR 9 (by omega)).trans A.r9,
    (hR 18 (by omega)).trans A.r18, (hR 19 (by omega)).trans A.r19, (hR 21 (by omega)).trans A.r21,
    hf, (ag .ld 8 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans A.fp, hr, ha,
    (ag .ld 224 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans A.uio,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    A.buf.transport (fun a ha => hM a (by simp only [snpFP] at ha; unfold SvfKeep; omega)) SG.n_pos,
    fun a ha => (hM a (by simp only [SvfW, snpFP] at ha; unfold SvfKeep; omega)).trans (A.frame a ha)⟩
  · exact (ag .ld 584 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.ra
  · exact (ag .ld 576 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s0
  · exact (ag .ld 568 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s1
  · exact (ag .ld 560 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s2
  · exact (ag .ld 552 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s3
  · exact (ag .ld 544 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s4
  · exact (ag .ld 536 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s5
  · exact (ag .ld 528 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s6
  · exact (ag .ld 520 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s7
  · exact (ag .ld 512 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s8
  · exact (ag .ld 504 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s9
  · exact (ag .ld 496 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s10
  · exact (ag .ld 488 (by simp only [widthOfM]; omega) (by simp only [widthOfM]; omega)).trans sv.s11

/-- `SvfCore` survives a scratch write inside `[s - 864 + 168, s - 864 + 224)`
(`mbtowc`'s character, the sign and digit buffers) and new values in the
registers the loop does not fix. -/
theorem SvfCore.scratch {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat}
    {rt : BitVec 64} {total : List (BitVec 8)} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (A : SvfCore s dst n R0 Mt0 p ap rt total R Mt) (SG : SnpGeom s dst n) (hR : SvfRegs R' R)
    (hM : ∀ a, (a < s - 864 + 168 ∨ s - 864 + 224 ≤ a) → imgM Mt' a = imgM Mt a) :
    SvfCore s dst n R0 Mt0 p ap rt total R' Mt' := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have ag : ∀ (off : Nat), off + 8 ≤ 168 →
      ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + off)).toNat = ldv .ld Mt (BitVec.ofNat 64 (s - 864 + off)).toNat :=
    fun off h1 => by
      rw [toNat_ofNat_lt (by omega)]
      exact ldv_agree .ld fun i hi => hM _ (by simp only [widthOfM] at hi; omega)
  refine A.update SG hR (fun a ha => hM a (by unfold SvfKeep at ha; omega)) ?_
    ((ag 16 (by omega)).trans A.ret) ((ag 24 (by omega)).trans A.ap)
  have := ag 0 (by omega)
  simp only [Nat.add_zero] at this
  exact this.trans A.fmt

/-- Its layer over an empty `uio`. -/
theorem SvfAt.scratch {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat}
    {rt : BitVec 64} {total : List (BitVec 8)} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (A : SvfAt s dst n R0 Mt0 p ap rt total R Mt) (SG : SnpGeom s dst n) (hR : SvfRegs R' R)
    (h23 : R' 23 = R 23) (hM : ∀ a, (a < s - 864 + 168 ∨ s - 864 + 224 ≤ a) → imgM Mt' a = imgM Mt a) :
    SvfAt s dst n R0 Mt0 p ap rt total R' Mt' := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  refine ⟨A.core.scratch SG hR hM, h23.trans A.r23, ?_, ?_⟩
  · rw [toNat_ofNat_lt (by omega)]
    exact (ldv_agree .lw fun i hi => hM _ (by simp only [widthOfM] at hi; omega)).trans
      (by have := A.cnt; rwa [toNat_ofNat_lt (by omega)] at this)
  · rw [toNat_ofNat_lt (by omega)]
    exact (ldv_agree .ld fun i hi => hM _ (by simp only [widthOfM] at hi; omega)).trans
      (by have := A.res; rwa [toNat_ofNat_lt (by omega)] at this)

theorem SvfAt.ld0 {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat}
    {rt : BitVec 64} {total : List (BitVec 8)} {R : Nat → BitVec 64} {Mt : Mem}
    (A : SvfAt s dst n R0 Mt0 p ap rt total R Mt) (k : MKind) {a : Nat}
    (h : ∀ i, i < widthOfM k → ¬ SvfW s dst n (a + i)) : ldv k Mt a = ldv k Mt0 a :=
  ldv_agree k fun i hi => A.core.frame _ (h i hi)

theorem lbu_img_ofNat (Dt : Mem) (q : Nat) (hq : q < 2 ^ 64) :
    ldv .lbu Dt (BitVec.ofNat 64 q).toNat = BitVec.ofNat 64 (imgM Dt q).toNat := by
  rw [toNat_ofNat_lt hq]
  simp only [ldv, bytesVal, bytesAt, widthOfM, List.range_one, List.map_cons, List.map_nil,
    List.getD_cons_zero, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]

theorem snez_ofNat (b : BitVec 8) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u (0#64) (BitVec.ofNat 64 b.toNat))) =
      if b = 0#8 then 0#64 else 1#64 := by
  have e : BitVec.ofNat 64 b.toNat = BitVec.zeroExtend 64 b := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [e]
  split
  · rename_i h; exact snez_zero h
  · rename_i h; exact snez_one h

/-- The scan after `mbtowc` returned on the byte at `q` (`0x80007744`). -/
structure ScanAt (Dt : Mem) (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat)
    (rt : BitVec 64) (total : List (BitVec 8)) (q : Nat) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  svf : SvfAt s dst n R0 Mt0 p ap rt total R Mt
  r22 : R 22 = BitVec.ofNat 64 q
  r10 : R 10 = if imgM Dt q = 0#8 then 0#64 else 1#64
  wc : ldv .lw Mt (BitVec.ofNat 64 (s - 864 + 180)).toNat = BitVec.ofNat 64 (imgM Dt q).toNat

/-- **One `mbtowc` call of the scan** (`0x80007724` → `0x80007744`): the
locale's `__ascii_mbtowc` on the format byte at `q`. -/
theorem svf_mbtowc {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    (q : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (A : SvfAt s dst n R0 Mt0 p ap rt total R Mt) (h22 : R 22 = BitVec.ofNat 64 q)
    (hq : InDA DA q (q + 1)) (hq1 : 0x80000000 ≤ q) (hq2 : q + 1 ≤ 0x100000000)
    (hq3 : q + 1 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ q)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64)
    (hk : ∀ R' Mt', ScanAt Dt s dst n R0 Mt0 p ap rt total q R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80007744#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007724#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have hd1 := SG.d_lo
  have h2 := A.core.r2
  have h8 := A.core.r8
  have h9 := A.core.r9
  have hmb' : ldv .ld Mt 0x8001b880 = 0x80012268#64 :=
    (A.ld0 .ld fun i hi => by simp only [SvfW, snpFP, widthOfM] at hi ⊢; omega).trans hmb
  have hmx' : ldv .lbu Mt 0x8001b8f8 = 1#64 :=
    (A.ld0 .lbu fun i hi => by simp only [SvfW, snpFP, widthOfM] at hi ⊢; omega).trans hmx
  have hbq := lbu_img_ofNat Dt q (by omega)
  nx_run hlive using [ofNat_add_ofNat, h2, h8, h9, h22, hmb', hmx', hbq] at 0x80007744
  refine hk _ _ ⟨A.scratch SG ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro a ha
    svf_mem
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h22
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact snez_ofNat _
  · exact ldv_lw_store4 Mt _ _ (by have := (imgM Dt q).isLt; omega)

/-- The scan's branch on `mbtowc`'s result (`0x80007744`): the end of the
format (`hZ`), a conversion (`hP`), or the next byte (`hN`). -/
theorem svf_scan_br {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    (q : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n) (hq : q + 1 < 2 ^ 64)
    (S : ScanAt Dt s dst n R0 Mt0 p ap rt total q R Mt)
    (hZ : imgM Dt q = 0#8 → ∀ R', SvfRegs R' R → R' 23 = R 23 → R' 22 = BitVec.ofNat 64 q → R' 10 = 0#64 →
      NW live Dt DA (snpS s dst n) Q 0x80007960#64 R' Mt)
    (hP : imgM Dt q = 37#8 → ∀ R', SvfRegs R' R → R' 23 = R 23 → R' 22 = BitVec.ofNat 64 q → R' 10 = 1#64 →
      NW live Dt DA (snpS s dst n) Q 0x8000775c#64 R' Mt)
    (hN : imgM Dt q ≠ 0#8 → imgM Dt q ≠ 37#8 → ∀ R', SvfRegs R' R → R' 23 = R 23 →
      R' 22 = BitVec.ofNat 64 (q + 1) → NW live Dt DA (snpS s dst n) Q 0x80007724#64 R' Mt) :
    NW live Dt DA (snpS s dst n) Q 0x80007744#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 := S.svf.core.r2
  have h19 := S.svf.core.r19
  have h22 := S.r22
  have h10 := S.r10
  have hwc := S.wc
  by_cases hz : imgM Dt q = 0#8
  · rw [if_pos hz] at h10
    nx_runF hlive using [ofNat_add_ofNat, h2, h10, h19, h22, hwc] at 0x80007960
    exact hZ hz _ (fun _ _ => rfl) rfl h22 h10
  rw [if_neg hz] at h10
  by_cases hp : imgM Dt q = 37#8
  · have hp' : BitVec.ofNat 64 (imgM Dt q).toNat = 37#64 := by rw [hp]; rfl
    nx_runF hlive using [ofNat_add_ofNat, h2, h10, h19, h22, hwc, hp'] at 0x8000775c
    refine hP hp _ ?_ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h22
    · exact h10
  · have hp' : BitVec.ofNat 64 (imgM Dt q).toNat ≠ 37#64 := fun h => hp (by
      apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this; have := (imgM Dt q).isLt; simp; omega)
    nx_runF hlive using [ofNat_add_ofNat, h2, h10, h19, h22, hwc, hp'] at 0x80007724
    refine hN hz hp _ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-- A format read by the scan: bytes `[q, q + k]` in the data view, in RAM off
the HTIF words. -/
structure FmtGeom (DA : List Nat) (q k : Nat) : Prop where
  dom : InDA DA q (q + k + 1)
  lo : 0x80000000 ≤ q
  hi : q + k + 1 ≤ 0x100000000
  htif : q + k + 1 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ q

/-- **The literal scan** (`0x80007724`): `k` ordinary bytes from `q`, then the
NUL (`hZ`, at `0x80007960`) or a `'%'` (`hP`, at `0x8000775c`). -/
theorem svf_scan {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    (SG : SnpGeom s dst n)
    (hmb : ldv .ld Mt0 0x8001b880 = 0x80012268#64) (hmx : ldv .lbu Mt0 0x8001b8f8 = 1#64) :
    ∀ k q (R : Nat → BitVec 64) (Mt : Mem), SvfAt s dst n R0 Mt0 p ap rt total R Mt →
      R 22 = BitVec.ofNat 64 q → FmtGeom DA q k →
      (∀ i, i < k → imgM Dt (q + i) ≠ 0#8 ∧ imgM Dt (q + i) ≠ 37#8) →
      (imgM Dt (q + k) = 0#8 → ∀ R' Mt', SvfAt s dst n R0 Mt0 p ap rt total R' Mt' →
        R' 22 = BitVec.ofNat 64 (q + k) → R' 10 = 0#64 →
        NW live Dt DA (snpS s dst n) Q 0x80007960#64 R' Mt') →
      (imgM Dt (q + k) = 37#8 → ∀ R' Mt', SvfAt s dst n R0 Mt0 p ap rt total R' Mt' →
        R' 22 = BitVec.ofNat 64 (q + k) → R' 10 = 1#64 →
        NW live Dt DA (snpS s dst n) Q 0x8000775c#64 R' Mt') →
      (imgM Dt (q + k) = 0#8 ∨ imgM Dt (q + k) = 37#8) →
      NW live Dt DA (snpS s dst n) Q 0x80007724#64 R Mt := by
  intro k
  induction k with
  | zero =>
    intro q R Mt A h22 G _ hZ hP hend
    refine svf_mbtowc hlive q R Mt SG A h22 (fun b h1 h2 => G.dom b h1 (by omega)) G.lo
      (by have := G.hi; omega) (by have := G.htif; omega) hmb hmx fun R' Mt' S => ?_
    refine svf_scan_br hlive q R' Mt' SG (by have := G.hi; omega) S
      (fun hz R'' hR h23 h22' h10 => hZ hz R'' Mt' (S.svf.scratch SG hR h23 fun _ _ => rfl) h22' h10)
      (fun hp R'' hR h23 h22' h10 => hP hp R'' Mt' (S.svf.scratch SG hR h23 fun _ _ => rfl) h22' h10)
      (fun hz hp => ?_)
    rcases hend with h | h
    · exact absurd h hz
    · exact absurd h hp
  | succ k ih =>
    intro q R Mt A h22 G hb hZ hP hend
    have hb0 := hb 0 (by omega)
    simp only [Nat.add_zero] at hb0
    refine svf_mbtowc hlive q R Mt SG A h22 (fun b h1 h2 => G.dom b h1 (by omega)) G.lo
      (by have := G.hi; omega) (by have := G.htif; omega) hmb hmx fun R' Mt' S => ?_
    refine svf_scan_br hlive q R' Mt' SG (by have := G.hi; omega) S
      (fun hz => absurd hz hb0.1) (fun hp => absurd hp hb0.2)
      (fun _ _ R'' hR h23 h22' => ?_)
    have e : q + (k + 1) = q + 1 + k := by omega
    rw [e] at hZ hP hend
    refine ih (q + 1) R'' Mt' (S.svf.scratch SG hR h23 fun _ _ => rfl) h22'
      ⟨fun b h1 h2 => G.dom b (by omega) (by omega), by have := G.lo; omega,
        by have := G.hi; omega, by have := G.htif; omega⟩
      (fun i hi => by rw [show q + 1 + i = q + (i + 1) by omega]; exact hb (i + 1) (by omega))
      hZ hP hend

/-! ## Pending pieces -/

/-- Where a piece's bytes come from: the data view outside the stack scratch
(the format, a `%s` string) or the scratch itself (the sign, the digits). -/
structure PieceSrc (DA : List Nat) (s dst n b l : Nat) : Prop where
  geom : PieceGeom s dst n b l
  small : l < 2 ^ 31
  src : (∀ a, b ≤ a → a < b + l → a ∈ DA ∧ (a < s - 1024 ∨ s ≤ a)) ∨ (s - 1024 ≤ b ∧ b + l ≤ s)

/-- The bytes the flush prints: the scratch's at the flush, the data view's
elsewhere. -/
def gOf (s : Nat) (Dt Mt : Mem) (a : Nat) : BitVec 8 :=
  if s - 1024 ≤ a ∧ a < s then imgM Mt a else imgM Dt a

theorem piecesOK_of_src {Dt : Mem} {DA : List Nat} {Mt : Mem} {s dst n : Nat}
    {L : List (Nat × Nat)} (h : ∀ j (hj : j < L.length), PieceSrc DA s dst n L[j].1 L[j].2) :
    PiecesOK Dt DA Mt s dst n (gOf s Dt Mt) L := fun j hj => by
  obtain ⟨hg, hs, hsrc⟩ := h j hj
  refine ⟨hg, hs, fun a h1 h2 => ?_⟩
  rcases hsrc with hd | ⟨hb1, hb2⟩
  · obtain ⟨hda, hout⟩ := hd a h1 h2
    exact .inl ⟨hda, by unfold gOf; rw [if_neg (by omega)]⟩
  · refine .inr ⟨.inr (.inl ⟨by simp only [snpNeed]; omega, by omega⟩), ?_⟩
    unfold gOf; rw [if_pos (by omega)]

/-- **A conversion in progress**: `SvfCore` and the pending pieces `L` in the
`uio` (at most three: a literal run, a sign, a body). -/
structure SvfSt (DA : List Nat) (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat)
    (rt : BitVec 64) (total : List (BitVec 8)) (L : List (Nat × Nat)) (R : Nat → BitVec 64)
    (Mt : Mem) : Prop where
  core : SvfCore s dst n R0 Mt0 p ap rt total R Mt
  r23 : R 23 = BitVec.ofNat 64 (s - 864 + 352 + 16 * L.length)
  cnt : ldv .lw Mt (BitVec.ofNat 64 (s - 864 + 232)).toNat = BitVec.ofNat 64 L.length
  res : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 240)).toNat = BitVec.ofNat 64 (sumLen L)
  iov : IovAt Mt s L
  src : ∀ j (hj : j < L.length), PieceSrc DA s dst n L[j].1 L[j].2
  len : L.length ≤ 3
  sum : sumLen L < 2 ^ 31

/-- `subw` of two addresses a short distance apart. -/
theorem subw_ofNat' {w c : Nat} (hcw : c ≤ w) (hw : w < 2 ^ 64) (hd : w - c < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 w) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 c))
      = BitVec.ofNat 64 (w - c) := by
  rw [show BitVec.extractLsb 31 0 (BitVec.ofNat 64 w) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 c)
      = BitVec.extractLsb 31 0 (BitVec.ofNat 64 (w - c)) from by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat]
    omega]
  exact VsaIris.Interp.sext32_ofNat_eq (by omega)

/-- `addw` of two small counts. -/
theorem addw_ofNat {a b : Nat} (h : a + b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (a + b) := by
  rw [show BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)
      = BitVec.extractLsb 31 0 (BitVec.ofNat 64 (a + b)) from by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.extractLsb_toNat, BitVec.toNat_ofNat]
    omega]
  exact VsaIris.Interp.sext32_ofNat_eq h

/-- The literal piece's stores make an `SvfSt` of one piece. -/
theorem SvfSt.ofLit {DA : List Nat} {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem}
    {p ap c len : Nat} {total : List (BitVec 8)} {R R' : Nat → BitVec 64} {Mt : Mem}
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total R Mt) (SG : SnpGeom s dst n)
    (hc : c + len < 2 ^ 31) (hsrc : PieceSrc DA s dst n p len) (hR : SvfRegs R' R)
    (h23 : R' 23 = BitVec.ofNat 64 (s - 864 + 352 + 16)) :
    SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 (c + len)) total [(p, len)] R'
      (writeLog (writeLog (writeLog (writeLog (writeLog Mt
        [((BitVec.ofNat 64 (s - 864 + 352 + 8)).toNat, 8, BitVec.ofNat 64 len)])
        [((BitVec.ofNat 64 (s - 864 + 352)).toNat, 8, BitVec.ofNat 64 p)])
        [((BitVec.ofNat 64 (s - 864 + 240)).toNat, 8, BitVec.ofNat 64 len)])
        [((BitVec.ofNat 64 (s - 864 + 232)).toNat, 4, 1#64)])
        [((BitVec.ofNat 64 (s - 864 + 16)).toNat, 8, BitVec.ofNat 64 (c + len))]) := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hl := hsrc.small
  refine ⟨A.core.update SG hR (fun a ha => ?_) ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
  · unfold SvfKeep at ha
    svf_mem
  · svf_mem; exact A.core.fmt
  · svf_mem
  · svf_mem; exact A.core.ap
  · simpa using h23
  · svf_mem; rfl
  · svf_mem; simp [sumLen]
  · intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [snpIov, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
    refine ⟨?_, ?_⟩
    · rw [show s - 512 = (BitVec.ofNat 64 (s - 864 + 352)).toNat by rw [toNat_ofNat_lt (by omega)]; omega]
      svf_mem
    · rw [show s - 512 + 8 = (BitVec.ofNat 64 (s - 864 + 352 + 8)).toNat by rw [toNat_ofNat_lt (by omega)]; omega]
      svf_mem
  · intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    exact hsrc
  · simp [sumLen]; omega

/-- **The literal run's piece** (`0x80007970`): `(p, len)` appended to the
`uio`, the return count advanced; then the conversion (`s4 ≠ 0`, `hP`) or the
end (`hE`). -/
theorem svf_litBody {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c len : Nat} {total : List (BitVec 8)}
    (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (A : SvfAt s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total R Mt) (h24 : R 24 = BitVec.ofNat 64 len)
    (hc : c + len < 2 ^ 31) (hsrc : PieceSrc DA s dst n p len)
    (hP : R 20 ≠ 0#64 → ∀ R' Mt', SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 (c + len)) total
      [(p, len)] R' Mt' → R' 22 = R 22 → NW live Dt DA (snpS s dst n) Q 0x8000776c#64 R' Mt')
    (hE : R 20 = 0#64 → ∀ R' Mt', SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 (c + len)) total
      [(p, len)] R' Mt' → R' 22 = R 22 → NW live Dt DA (snpS s dst n) Q 0x800079b0#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007970#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := A.core.r2
  have h23 := A.r23
  have hf := A.core.fmt
  have hr := A.core.ret
  have hcn := A.cnt
  have hres := A.res
  have hl := hsrc.small
  have haw := addw_ofNat hc
  nx_runF hlive using [ofNat_add_ofNat, Nat.zero_add, h2, h23, h24, hf, hr, hcn, hres, haw] at 0x8000776c 0x800079b0
  all_goals rename_i hcnd
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hcnd
  · refine hP hcnd _ _ (SvfSt.ofLit A SG hc hsrc ?_ ?_) ?_
    · intro z hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · refine hE (Classical.not_not.mp hcnd) _ _ (SvfSt.ofLit A SG hc hsrc ?_ ?_) ?_
    · intro z hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

end VsaIris.Sym
