import VsaIris.Vsa.SnpSvf

/-!
# `_svfprintf_r`'s conversions: `%s`, `%d`, `%lld`

From the conversion start (`0x8000776c`) through the jump table to `PRINT`'s
entry state `PrintIn` (`SnpSvf.lean`): `%s` through `strlen_nw`, the integer
conversions through the sign, the digit loop over `umod_nw`/`udiv_nw` and the
digits' bounds (`DigitsAt`, the form M3's `digits_eq_natToString` takes).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

/-! ## The conversion dispatch -/

/-- A jump-table load at a literal address: the bytes are the table's. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (apply snpRO_mem_img; (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]); decide))

/-- `_svfprintf_r`'s conversion table (`0x8001a0fc`, 91 words, `.rodata`) in
the run's data view: read like the format, not fetched, so it needs no
liveness. -/
structure TabAt (Dt : Mem) (DA : List Nat) : Prop where
  dom : InDA DA 0x8001a0fc 0x8001a268
  img : ∀ a, 0x8001a0fc ≤ a → a < 0x8001a268 → imgM Dt a = snpROImg a

theorem TabAt.lw {Dt : Mem} {DA : List Nat} (h : TabAt Dt DA) {a : Nat} (h1 : 0x8001a0fc ≤ a)
    (h2 : a + 4 ≤ 0x8001a268) : ldv .lw Dt a = ldvf .lw snpROImg a := by
  unfold ldv ldvf bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  simp only [widthOfM] at this
  exact h.img _ (by omega) (by omega)

/-- **The conversion table** (`0x80007798`): the character `c` in `s8` at
the cursor `x` (`s9`) dispatches through `0x8001a0fc` to `%s`, `%d` or the
`l` modifier. -/
theorem svf_disp {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {S : Nat → Prop} (x c : Nat) (tgt : BitVec 64)
    (hc : c = 0x73 ∧ tgt = 0x80007f4c#64 ∨ c = 0x64 ∧ tgt = 0x80008008#64 ∨ c = 0x6c ∧ tgt = 0x80008534#64)
    (R : Nat → BitVec 64) (Mt : Mem) (hx : x + 1 < 2 ^ 64)
    (h25 : R 25 = BitVec.ofNat 64 x) (h24 : R 24 = BitVec.ofNat 64 c) (h26 : R 26 = 90#64)
    (h22 : R 22 = 0x8001a0fc#64) (hT : TabAt Dt DA)
    (hk : ∀ R', R' 25 = BitVec.ofNat 64 (x + 1) → R' 24 = BitVec.ofNat 64 c →
      (∀ z, z ≠ 14 → z ≠ 15 → z ≠ 24 → z ≠ 25 → R' z = R z) → NW live Dt DA S Q tgt R' Mt) :
    NW live Dt DA S Q 0x80007798#64 R Mt := by
  have hTd := hT.dom
  have ts := (hT.lw (a := 0x8001a248) (by decide) (by decide)).trans snpRO_lw_8001a248
  have td := (hT.lw (a := 0x8001a20c) (by decide) (by decide)).trans snpRO_lw_8001a20c
  have tl := (hT.lw (a := 0x8001a22c) (by decide) (by decide)).trans snpRO_lw_8001a22c
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals nx_runF hlive using [ofNat_add_ofNat, h22, h24, h25, h26, sext_zero, BitVec.add_zero,
    BitVec.reduceToNat, ts, td, tl] at 0x80007f4c 0x80008008 0x80008534 0x800077f8
  all_goals refine hk _ ?_ ?_ ?_
  all_goals (try intro z h14 h15 h24' h25')
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h14, h15, h24', h25'])
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  all_goals first | rfl | (rw [h24]; decide) | skip

/-- The bytes `SvfSt` reads besides the format, return and argument slots:
`SvfKeep`, the `uio` and the iovec array. -/
def StKeep (s a : Nat) : Prop :=
  SvfKeep s a ∨ (s - 864 + 224 ≤ a ∧ a < s - 864 + 248) ∨ (s - 864 + 352 ≤ a ∧ a < s - 864 + 480)

/-- **`SvfSt` across a stretch of a conversion**: the kept bytes and fixed
registers unchanged, new format, return and argument slots. -/
theorem SvfSt.update {DA : List Nat} {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem}
    {p ap p' ap' : Nat} {rt rt' : BitVec 64} {total : List (BitVec 8)} {L : List (Nat × Nat)}
    {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt) (SG : SnpGeom s dst n)
    (hR : SvfRegs R' R) (h23 : R' 23 = R 23) (hM : ∀ a, StKeep s a → imgM Mt' a = imgM Mt a)
    (hf : ldv .ld Mt' (BitVec.ofNat 64 (s - 864)).toNat = BitVec.ofNat 64 p')
    (hr : ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + 16)).toNat = rt')
    (ha : ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + 24)).toNat = BitVec.ofNat 64 ap') :
    SvfSt DA s dst n R0 Mt0 p' ap' rt' total L R' Mt' := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hL := St.len
  have ag : ∀ (k : MKind) (off : Nat), 224 ≤ off → off + widthOfM k ≤ 248 →
      ldv k Mt' (BitVec.ofNat 64 (s - 864 + off)).toNat = ldv k Mt (BitVec.ofNat 64 (s - 864 + off)).toNat :=
    fun k off h1 h2 => by
      rw [toNat_ofNat_lt (by omega)]
      exact ldv_agree k fun i hi => hM _ (.inr (.inl ⟨by omega, by omega⟩))
  refine ⟨St.core.update SG hR (fun a ha => hM a (.inl ha)) hf hr ha, h23.trans St.r23,
    (ag .lw 232 (by omega) (by simp only [widthOfM]; omega)).trans St.cnt,
    (ag .ld 240 (by omega) (by simp only [widthOfM]; omega)).trans St.res,
    St.iov.transport (by omega) (fun a h1 h2 => ?_), St.src, St.len, St.sum⟩
  simp only [snpIov] at h1 h2
  exact hM a (.inr (.inr ⟨by omega, by omega⟩))

/-- `SvfSt` in a memory agreeing on everything it reads. -/
theorem SvfSt.agree {DA : List Nat} {s dst n : Nat} {R0 : Nat → BitVec 64} {Mt0 : Mem}
    {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)} {L : List (Nat × Nat)}
    {R : Nat → BitVec 64} {Mt Mt' : Mem}
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt) (SG : SnpGeom s dst n)
    (hM : ∀ a, (StKeep s a ∨ (s - 864 ≤ a ∧ a < s - 864 + 8) ∨ (s - 864 + 16 ≤ a ∧ a < s - 864 + 32)) →
      imgM Mt' a = imgM Mt a) :
    SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt' := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have ag : ∀ off, (off + 8 ≤ 8 ∨ (16 ≤ off ∧ off + 8 ≤ 32)) →
      ldv .ld Mt' (BitVec.ofNat 64 (s - 864 + off)).toNat = ldv .ld Mt (BitVec.ofNat 64 (s - 864 + off)).toNat :=
    fun off h => by
      rw [toNat_ofNat_lt (by omega)]
      exact ldv_agree .ld fun i hi => hM _ (.inr (by simp only [widthOfM] at hi; omega))
  refine St.update SG (fun _ _ => rfl) rfl (fun a ha => hM a (.inl ha)) ?_
    ((ag 16 (by omega)).trans St.core.ret) ((ag 24 (by omega)).trans St.core.ap)
  have := ag 0 (by omega)
  simp only [Nat.add_zero] at this
  exact this.trans St.core.fmt

/-- The conversion's state at the table (`0x80007798`): the cursor past the
`'%'`, no sign, no flags, precision `-1`, width `0`. -/
structure ConvAt (DA : List Nat) (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat)
    (rt : BitVec 64) (total : List (BitVec 8)) (L : List (Nat × Nat)) (x c : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  st : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt
  sign : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = 0#64
  r25 : R 25 = BitVec.ofNat 64 x
  r24 : R 24 = BitVec.ofNat 64 c
  r6 : R 6 = 0#64
  r20 : R 20 = 18446744073709551615#64
  r27 : R 27 = 0#64
  r26 : R 26 = 90#64
  r22 : R 22 = 0x8001a0fc#64

/-- **A conversion starts** (`0x8000776c`, the `'%'` at `q`): the cursor
advanced past it, the sign cleared, the specification's defaults, the
character after the `'%'` loaded. -/
theorem svf_convStart {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (q : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt) (h22 : R 22 = BitVec.ofNat 64 q)
    (hq : InDA DA (q + 1) (q + 2)) (hq1 : 0x80000000 ≤ q) (hq2 : q + 2 ≤ 0x100000000)
    (hq3 : q + 2 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ q)
    (hk : ∀ R' Mt', ConvAt DA s dst n R0 Mt0 (q + 1) ap rt total L (q + 1) (imgM Dt (q + 1)).toNat R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80007798#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x8000776c#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := St.core.r2
  have hbq := lbu_img_ofNat Dt (q + 1) (by omega)
  nx_runF hlive using [ofNat_add_ofNat, h2, h22, hbq] at 0x80007798
  refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro a ha; unfold StKeep SvfKeep at ha; svf_mem
  · svf_mem
  · svf_mem; exact St.core.ret
  · svf_mem; exact St.core.ap
  · svf_mem
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-! ## `%s` -/

/-- **`%s` after `strlen`** (`0x80009e88`): the spilled flags and argument
cursor reloaded, `size = len`, no sign, precision `0`, `PRINT`. -/
theorem svf_convS_ret {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (q a len : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 (q + 2) 0 (BitVec.ofNat 64 c) total L R Mt) (hL : L.length ≤ 1)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = 0#64)
    (h56 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 56)).toNat = 0#64)
    (h48 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 48)).toNat = 0#64)
    (h32 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 32)).toNat = BitVec.ofNat 64 (ap + 8))
    (h10 : R 10 = BitVec.ofNat 64 len) (h26 : R 26 = BitVec.ofNat 64 a)
    (hsrc : PieceSrc DA s dst n a len) (hc : c + len + 1 < 2 ^ 31) (hsum : sumLen L + len + 1 < 2 ^ 31)
    (hk : ∀ R' Mt', PrintIn DA s dst n R0 Mt0 (q + 2) (ap + 8) c total L a len 0 R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x8000782c#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80009e88#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := St.core.r2
  have h24 := St.core.ap
  have hlen : len < 2 ^ 31 := by omega
  have hsx := VsaIris.Interp.sext32_ofNat_eq hlen
  have hng : ¬ (BitVec.ofNat 64 len).toInt < (0#64).toInt := by
    rw [toInt_ofNat_small (by omega)]; simp
  nx_runF hlive using [ofNat_add_ofNat, h2, h10, h167, h56, h48, h32, h24, hsx, hng] at 0x8000782c
  refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, hL, ?_, ?_, ?_, ?_, .inl rfl, ?_, ?_, ?_, .inl ?_, ?_,
    ?_, hsrc, hc, hsum⟩
  · intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · intro a ha; unfold StKeep SvfKeep at ha; svf_mem
  · svf_mem; exact St.core.fmt
  · svf_mem; exact St.core.ret
  · svf_mem
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, sgN, ite_true, Nat.add_zero])
  · decide
  · decide
  · decide
  · exact h26
  · svf_mem; exact h167
  · svf_mem

/-- A `%s` argument: a NUL-terminated string in the data view, in RAM off the
HTIF words with the word loop's eight bytes of slack. -/
structure DStr (Dt : Mem) (DA : List Nat) (a len : Nat) : Prop where
  dom : InDA DA a (a + len + 1)
  nz : ∀ i, i < len → imgM Dt (a + i) ≠ 0
  nul : imgM Dt (a + len) = 0
  lo : 0x80000000 ≤ a
  hi : a + len + 8 ≤ 0x100000000
  htif : a + len + 8 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ a

theorem DStr.read {Dt : Mem} {DA : List Nat} {a len : Nat} (h : DStr Dt DA a len) (S : Nat → Prop)
    (Mt : Mem) : StrRead Dt DA S Mt a len (imgM Dt) where
  win b h1 h2 := .inl ⟨h.dom b h1 h2, rfl⟩
  nz := h.nz
  nul := h.nul
  lo := h.lo
  hi := h.hi
  htif := h.htif

/-- **`%s`** (from the table, `0x80007798`): the argument pointer loaded
from the `va_list`, `strlen` of the string, `PRINT` with the string as the
body. -/
theorem svf_convS {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (q a len : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (CA : ConvAt DA s dst n R0 Mt0 (q + 1) ap (BitVec.ofNat 64 c) total L (q + 1) 0x73 R Mt)
    (hL : L.length ≤ 1)
    (hap : ldv .ld Mt (BitVec.ofNat 64 ap).toNat = BitVec.ofNat 64 a) (hap1 : s - 40 ≤ ap)
    (hap2 : ap + 8 ≤ s) (hq : q + 3 < 2 ^ 64) (hstr : DStr Dt DA a len) (ha0 : a ≠ 0)
    (hsrc : PieceSrc DA s dst n a len) (hc : c + len + 1 < 2 ^ 31) (hsum : sumLen L + len + 1 < 2 ^ 31)
    (hT : TabAt Dt DA)
    (hk : ∀ R' Mt', PrintIn DA s dst n R0 Mt0 (q + 2) (ap + 8) c total L a len 0 R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x8000782c#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80007798#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  refine svf_disp hlive (q + 1) 0x73 _ (.inl ⟨rfl, rfl⟩) R Mt (by omega) CA.r25 CA.r24 CA.r26 CA.r22 hT
    fun R1 h25 h24 hkp => ?_
  have hsa := SG.s_al
  have St := CA.st
  have hk1 : ∀ z, z = 2 ∨ z = 6 ∨ z = 8 ∨ z = 9 ∨ z = 18 ∨ z = 19 ∨ z = 20 ∨ z = 21 ∨ z = 23 ∨ z = 27 →
      R1 z = R z := fun z hz => hkp z (by omega) (by omega) (by omega) (by omega)
  have h2 : R1 2 = BitVec.ofNat 64 (s - 864) := (hk1 2 (by omega)).trans St.core.r2
  have h6 : R1 6 = 0#64 := (hk1 6 (by omega)).trans CA.r6
  have h20 : R1 20 = 18446744073709551615#64 := (hk1 20 (by omega)).trans CA.r20
  have h27 : R1 27 = 0#64 := (hk1 27 (by omega)).trans CA.r27
  have hapf := St.core.ap
  have hahi := hstr.hi
  have ha0' : BitVec.ofNat 64 a ≠ 0#64 := fun h => ha0 (by
    have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega)
  have hz16 : (0#64 &&& 16#64 : BitVec 64) = 0#64 := by decide
  nx_runF hlive using [ofNat_add_ofNat, h2, h6, h20, h24, h25, h27, hapf, hap, ha0', hz16] at 0x80006cf0
  refine strlen_nw hlive (hstr.read _ _) _ ?_ ?_ fun R2 h10 hkp2 => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hR : SvfRegs R2 R := by
    intro z hz
    rw [hkp2 z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> exact hk1 _ (by omega)
  refine svf_convS_ret hlive q a len R2 _ SG (St.update SG hR ?_ ?_ ?_ ?_ ?_) hL ?_ ?_ ?_ ?_ h10 ?_ hsrc
    hc hsum hk
  · rw [hkp2 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hk1 23 (by omega)
  · intro a ha; unfold StKeep SvfKeep at ha; svf_mem
  · svf_mem
  · svf_mem; exact St.core.ret
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · svf_mem
  · rw [hkp2 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-! ## `%d` and `%lld` -/

/-- **`ll`** (`0x80008534`, the first `l` at `x - 1`): the second `l` at `x`,
the `d` at `x + 1`, the quad flag, back to the table. -/
theorem svf_convLL {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat} (x : Nat)
    (R : Nat → BitVec 64) (Mt : Mem)
    (hx : InDA DA x (x + 2)) (hx1 : 0x80000000 ≤ x) (hx2 : x + 2 ≤ 0x100000000)
    (hx3 : x + 2 ≤ 0x8001ad00 ∨ 0x8001ad08 ≤ x)
    (hl : imgM Dt x = 0x6c#8) (h25 : R 25 = BitVec.ofNat 64 x) (h6 : R 6 = 0#64)
    (hk : ∀ R', R' 25 = BitVec.ofNat 64 (x + 1) → R' 24 = BitVec.ofNat 64 (imgM Dt (x + 1)).toNat →
      R' 6 = 32#64 → (∀ z, z ≠ 6 → z ≠ 15 → z ≠ 24 → z ≠ 25 → R' z = R z) →
      NW live Dt DA (snpS s dst n) Q 0x80007798#64 R' Mt) :
    NW live Dt DA (snpS s dst n) Q 0x80008534#64 R Mt := by
  have hb0 := lbu_img_ofNat Dt x (by omega)
  have hb1 := lbu_img_ofNat Dt (x + 1) (by omega)
  rw [hl] at hb0
  nx_runF hlive using [ofNat_add_ofNat, h25, h6, hb0, hb1] at 0x80007798
  refine hk _ ?_ ?_ ?_ fun z h6' h15 h24 h25' => ?_
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · decide
  · simp only [h6', h15, h24, h25', ite_false]

/-- The sign byte and magnitude `_svfprintf_r` prints a signed value with. -/
def vSg (v : BitVec 64) : Nat := if v.toInt < 0 then 45 else 0

def vMag (v : BitVec 64) : Nat := if v.toInt < 0 then (-v).toNat else v.toNat

/-- The integer conversion after its argument (`0x80008100`): the sign byte
at `sp + 167`, the magnitude `m` in `a4`, precision `-1`, width `0`. -/
structure IntAt (DA : List Nat) (s dst n : Nat) (R0 : Nat → BitVec 64) (Mt0 : Mem) (p ap : Nat)
    (rt : BitVec 64) (total : List (BitVec 8)) (L : List (Nat × Nat)) (m sg : Nat)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  st : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt
  sign : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = BitVec.ofNat 64 sg
  sg01 : sg = 0 ∨ sg = 45
  r14 : R 14 = BitVec.ofNat 64 m
  mlt : m < 2 ^ 64
  r6 : R 6 = 0#64 ∨ R 6 = 32#64
  r20 : R 20 = 18446744073709551615#64
  r28 : R 28 = 0#64

theorem ldv_lbu_sb45 (Mt : Mem) (a : Nat) : ldv .lbu (writeLog Mt [(a, 1, 45#64)]) a = 45#64 := by
  have := ldv_lbu_sb Mt a 45#8
  rwa [show BitVec.zeroExtend 64 (45#8) = 45#64 by decide] at this

theorem vSg_pos {v : BitVec 64} (h : (0#64).toInt ≤ v.toInt) : vSg v = 0 := by
  unfold vSg; rw [if_neg (by simp at h; omega)]

theorem vMag_pos {v : BitVec 64} (h : (0#64).toInt ≤ v.toInt) : vMag v = v.toNat := by
  unfold vMag; rw [if_neg (by simp at h; omega)]

theorem vSg_neg {v : BitVec 64} (h : ¬ (0#64).toInt ≤ v.toInt) : vSg v = 45 := by
  unfold vSg; rw [if_pos (by simp at h; omega)]

theorem vMag_neg {v : BitVec 64} (h : ¬ (0#64).toInt ≤ v.toInt) : vMag v = (-v).toNat := by
  unfold vMag; rw [if_pos (by simp at h; omega)]

theorem vSg_pos' {v : BitVec 64} (h : ¬ v.toInt < (0#64).toInt) : vSg v = 0 := by
  unfold vSg; rw [if_neg (by simp at h; omega)]

theorem vMag_pos' {v : BitVec 64} (h : ¬ v.toInt < (0#64).toInt) : vMag v = v.toNat := by
  unfold vMag; rw [if_neg (by simp at h; omega)]

theorem vSg_neg' {v : BitVec 64} (h : v.toInt < (0#64).toInt) : vSg v = 45 := by
  unfold vSg; rw [if_pos (by simp at h; omega)]

theorem vMag_neg' {v : BitVec 64} (h : v.toInt < (0#64).toInt) : vMag v = (-v).toNat := by
  unfold vMag; rw [if_pos (by simp at h; omega)]

theorem vSg01 (v : BitVec 64) : vSg v = 0 ∨ vSg v = 45 := by unfold vSg; split <;> simp

theorem vMag_lt (v : BitVec 64) : vMag v < 2 ^ 64 := by unfold vMag; split <;> exact BitVec.isLt _

/-- **`%lld`'s argument** (`0x80008008` with the quad flag): the 64-bit value
`v` loaded from the `va_list`, the cursors stored, the sign byte and
magnitude. -/
theorem svf_intQ {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (x : Nat) (v : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = 0#64)
    (h25 : R 25 = BitVec.ofNat 64 x) (h6 : R 6 = 32#64) (h20 : R 20 = 18446744073709551615#64)
    (h27 : R 27 = 0#64)
    (hv : ldv .ld Mt (BitVec.ofNat 64 ap).toNat = v) (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s)
    (hk : ∀ R' Mt', IntAt DA s dst n R0 Mt0 x (ap + 8) rt total L (vMag v) (vSg v) R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80008100#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80008008#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := St.core.r2
  have hapf := St.core.ap
  nx_runF hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80008100
  all_goals rename_i hc _
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc)
  all_goals refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  all_goals (try (svf_mem; done))
  all_goals (try (svf_mem; exact St.core.ret))
  · svf_mem; rw [vSg_pos hc]; exact h167
  · exact vSg01 v
  · rw [vMag_pos hc]; simp
  · exact vMag_lt v
  · exact .inr h6
  · exact h20
  · rw [ldv_lbu_sb45, vSg_neg hc]
  · exact vSg01 v
  · rw [vMag_neg hc]; apply BitVec.eq_of_toNat_eq; simp
  · exact vMag_lt v
  · exact .inr h6
  · exact h20

/-- **`%d`'s argument** (`0x80008008`, no size flag): the 32-bit value
sign-extended to `v`, the cursors stored, the sign byte and magnitude. -/
theorem svf_intD {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap : Nat} {rt : BitVec 64} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} (x : Nat) (v : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap rt total L R Mt)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = 0#64)
    (h25 : R 25 = BitVec.ofNat 64 x) (h6 : R 6 = 0#64) (h20 : R 20 = 18446744073709551615#64)
    (h27 : R 27 = 0#64)
    (hv : ldv .lw Mt (BitVec.ofNat 64 ap).toNat = v) (hap1 : s - 40 ≤ ap) (hap2 : ap + 8 ≤ s)
    (hk : ∀ R' Mt', IntAt DA s dst n R0 Mt0 x (ap + 8) rt total L (vMag v) (vSg v) R' Mt' →
      NW live Dt DA (snpS s dst n) Q 0x80008100#64 R' Mt') :
    NW live Dt DA (snpS s dst n) Q 0x80008008#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := St.core.r2
  have hapf := St.core.ap
  nx_runF hlive using [ofNat_add_ofNat, h2, h6, h20, h25, h27, hapf, hv] at 0x80008100
  all_goals rename_i hc _
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc)
  all_goals refine hk _ _ ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  all_goals (try (svf_mem; done))
  all_goals (try (svf_mem; exact St.core.ret))
  all_goals first
    | exact vMag_lt v
    | exact vSg01 v
    | exact .inl h6
    | exact h20
    | (svf_mem; rw [vSg_pos' hc]; exact h167)
    | (rw [ldv_lbu_sb45, vSg_neg' hc]; done)
    | (rw [vMag_pos' hc]; simp; done)
    | (rw [vMag_neg' hc]; apply BitVec.eq_of_toNat_eq; simp; done)

/-! ## The digits -/

/-- The digit byte `k` places up. -/
def digB (m k : Nat) : BitVec 8 := BitVec.ofNat 8 (48 + m / 10 ^ k % 10)

/-- The registers one digit iteration keeps. -/
def DigKeep (R' R : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 1 → z ≠ 5 → z ≠ 8 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 15 → z ≠ 22 → z ≠ 23 →
    z ≠ 25 → z ≠ 26 → R' z = R z

/-- The memory after digit `j`'s store. -/
abbrev digMem (Mt : Mem) (s mag j : Nat) : Mem :=
  writeLog Mt [((BitVec.ofNat 64 (s - 864 + 348 - j - 1)).toNat, 1, BitVec.ofNat 64 (mag / 10 ^ j % 10 + 48))]

/-- **One digit** (`0x8000831c`): `mag / 10^j % 10` stored below the digits so
far, the quotient by `10`, the loop test on the old value. -/
theorem svf_digStep {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (mag j : Nat) (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (h8 : R 8 = BitVec.ofNat 64 (mag / 10 ^ j)) (h25 : R 25 = BitVec.ofNat 64 (s - 864 + 348 - j))
    (h23 : R 23 = BitVec.ofNat 64 j) (h27 : R 27 = 0#64) (hj : j < 20) (hm : mag < 2 ^ 64)
    (hL : 9 < mag / 10 ^ j → ∀ R', R' 8 = BitVec.ofNat 64 (mag / 10 ^ (j + 1)) →
      R' 25 = BitVec.ofNat 64 (s - 864 + 348 - (j + 1)) → R' 23 = BitVec.ofNat 64 (j + 1) →
      R' 27 = 0#64 → DigKeep R' R → NW live Dt DA (snpS s dst n) Q 0x8000831c#64 R' (digMem Mt s mag j))
    (hX : mag / 10 ^ j ≤ 9 → ∀ R', R' 26 = BitVec.ofNat 64 (s - 864 + 348 - (j + 1)) →
      R' 23 = BitVec.ofNat 64 (j + 1) → DigKeep R' R →
      NW live Dt DA (snpS s dst n) Q 0x80008358#64 R' (digMem Mt s mag j)) :
    NW live Dt DA (snpS s dst n) Q 0x8000831c#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  nx_runF hlive using [h8, h25, h23, h27] at 0x800046f4
  refine VsaIris.Interp.umod_nw hlive (BitVec.ofNat 64 (mag / 10 ^ j)) 10#64 0x80008328#64 _ Mt
    (by decide) ?_ ?_ ?_ (by decide) fun R1 hm1 hk1 => ?_
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done))
  have hq1 : mag / 10 ^ j < 2 ^ 64 := by have := Nat.div_le_self mag (10 ^ j); omega
  have hd : R1 10 = BitVec.ofNat 64 (mag / 10 ^ j % 10) := by
    have e10 : (10#64).toNat = 10 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [hm1, e10, toNat_ofNat_lt hq1, toNat_ofNat_lt (by omega)]
  have kk : ∀ z, (z = 8 ∨ z = 23 ∨ z = 25 ∨ z = 27) → R1 z = R z := fun z hz => by
    rw [hk1 z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hz with rfl | rfl | rfl | rfl <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have k8 := (kk 8 (by omega)).trans h8
  have k23 := (kk 23 (by omega)).trans h23
  have k25 := (kk 25 (by omega)).trans h25
  have k27 := (kk 27 (by omega)).trans h27
  have kR1 : ∀ z, z ≠ 1 → z ≠ 5 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R1 z = R z := fun z a b c d e f => by
    rw [hk1 z a b c d e f]; simp only [upd_apply, a, c, d, ite_false]
  clear hk1 kk
  have ea : BitVec.ofNat 64 (s - 864 + 348 - j) + 18446744073709551615#64 =
      BitVec.ofNat 64 (s - 864 + 348 - j - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_m1 (by omega) (by omega), toNat_ofNat_lt (by omega)]
  have ed : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (mag / 10 ^ j % 10) + 48#64)) =
      BitVec.ofNat 64 (mag / 10 ^ j % 10 + 48) := by
    rw [ofNat_add_ofNat]; exact VsaIris.Interp.sext32_ofNat_eq (by omega)
  have ej : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 j + 1#64)) = BitVec.ofNat 64 (j + 1) := by
    rw [ofNat_add_ofNat]; exact VsaIris.Interp.sext32_ofNat_eq (by omega)
  nx_runF hlive using [hd, k8, k23, k25, k27, ea, ed, ej] at 0x800046ac
  refine VsaIris.Interp.udiv_nw hlive (BitVec.ofNat 64 (mag / 10 ^ j)) 10#64 0x80008308#64 _ _
    (by decide) ?_ ?_ ?_ (by decide) fun R2 hq2 _ hk2 => ?_
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; done))
  have hq : R2 10 = BitVec.ofNat 64 (mag / 10 ^ (j + 1)) := by
    have e10 : (10#64).toNat = 10 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [hq2, e10, toNat_ofNat_lt hq1, toNat_ofNat_lt (by
      have := Nat.div_le_self (mag / 10 ^ j) 10; rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega),
      Nat.pow_succ, Nat.div_div_eq_div_mul]
  have j8 : R2 8 = BitVec.ofNat 64 (mag / 10 ^ j) := by
    rw [hk2 8 (by decide) (by decide) (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k8
  have j26 : R2 26 = BitVec.ofNat 64 (s - 864 + 348 - j - 1) := by
    rw [hk2 26 (by decide) (by decide) (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have j23 : R2 23 = BitVec.ofNat 64 (j + 1) := by
    rw [hk2 23 (by decide) (by decide) (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have j27 : R2 27 = 0#64 := by
    rw [hk2 27 (by decide) (by decide) (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact k27
  have kR2 : ∀ z, z ≠ 1 → z ≠ 5 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → z ≠ 23 → z ≠ 26 → R2 z = R z :=
    fun z a b c d e f g h => by
      rw [hk2 z c d e f]; simp only [upd_apply, a, c, d, g, h, ite_false]; exact kR1 z a b c d e f
  clear hk2
  nx_runF hlive using [hq, j8, j26, j23] at 0x8000831c 0x80008358
  all_goals rename_i hc
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  all_goals rw [toNat_ofNat_lt hq1] at hc
  · refine hX (by simpa using hc) _ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [j26]
      rw [show s - 864 + 348 - j - 1 = s - 864 + 348 - (j + 1) by omega]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact j23
    · intro z a b c d e f g h i k l m
      simp only [upd_apply, c, h, i, l, ite_false]; exact kR2 z a b d e f g k m
  · refine hL (by simp at hc; omega) _ ?_ ?_ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [show s - 864 + 348 - j - 1 = s - 864 + 348 - (j + 1) by omega]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact j23
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact j27
    · intro z a b c d e f g h i k l m
      simp only [upd_apply, c, h, i, l, ite_false]; exact kR2 z a b d e f g k m

theorem imgM_sb_ofNat (Mt : Mem) (a k : Nat) (hk : k < 256) :
    imgM (writeLog Mt [(a, 1, BitVec.ofNat 64 k)]) a = BitVec.ofNat 8 k := by
  have e : BitVec.ofNat 64 k = BitVec.zeroExtend 64 (BitVec.ofNat 8 k) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega
  rw [e, imgM_sb_zext]

theorem imgM_sb_ofNat' (Mt : Mem) (a k : Nat) (ha : a < 2 ^ 64) (hk : k < 256) :
    imgM (writeLog Mt [((BitVec.ofNat 64 a).toNat, 1, BitVec.ofNat 64 k)]) a = BitVec.ofNat 8 k := by
  have := imgM_sb_ofNat Mt a k hk
  rwa [toNat_ofNat_lt ha]

theorem DigKeep.trans {R R' R'' : Nat → BitVec 64} (h1 : DigKeep R' R) (h2 : DigKeep R'' R') :
    DigKeep R'' R := fun z a b c d e f g h i j k l => (h2 z a b c d e f g h i j k l).trans (h1 z a b c d e f g h i j k l)

theorem ten_pow_20 : 2 ^ 64 < 10 ^ 20 := by decide

/-- **The digit loop** (`0x8000831c`): the digits of `mag` stored downwards from
`sp + 348`, `K` of them, low digit first; the exit (`0x80008358`) with the
digit-count bounds `digits_eq_natToString` takes. -/
theorem svf_digLoop {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (mag : Nat) (hm : mag < 2 ^ 64) (Rs : Nat → BitVec 64) (Mts : Mem) (SG : SnpGeom s dst n)
    (hX : ∀ K R' Mt', 1 ≤ K → mag / 10 ^ (K - 1) ≤ 9 → (K = 1 ∨ 9 < mag / 10 ^ (K - 2)) → K ≤ 20 →
      R' 26 = BitVec.ofNat 64 (s - 864 + 348 - K) → R' 23 = BitVec.ofNat 64 K → DigKeep R' Rs →
      (∀ i, i < K → imgM Mt' (s - 864 + 348 - 1 - i) = digB mag i) →
      (∀ a, (a < s - 864 + 348 - K ∨ s - 864 + 348 ≤ a) → imgM Mt' a = imgM Mts a) →
      NW live Dt DA (snpS s dst n) Q 0x80008358#64 R' Mt') :
    ∀ f j (R : Nat → BitVec 64) (Mt : Mem), j + f = 20 → R 8 = BitVec.ofNat 64 (mag / 10 ^ j) →
      R 25 = BitVec.ofNat 64 (s - 864 + 348 - j) → R 23 = BitVec.ofNat 64 j → R 27 = 0#64 →
      DigKeep R Rs → (j = 0 ∧ 9 < mag ∨ 9 < mag / 10 ^ (j - 1)) →
      (∀ i, i < j → imgM Mt (s - 864 + 348 - 1 - i) = digB mag i) →
      (∀ a, (a < s - 864 + 348 - j ∨ s - 864 + 348 ≤ a) → imgM Mt a = imgM Mts a) →
      NW live Dt DA (snpS s dst n) Q 0x8000831c#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  intro f
  induction f with
  | zero =>
    intro j R Mt hjf _ _ _ _ _ hc _ _
    exfalso
    rcases hc with ⟨h0, _⟩ | hc
    · omega
    · have h1 : 10 ^ (j - 1) * 10 ≤ mag := by
        have := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 10) (n := j - 1))).mp (by omega : 10 ≤ mag / 10 ^ (j - 1))
        rw [Nat.mul_comm]; exact this
      have h2 : 10 ^ (j - 1) * 10 = 10 ^ 20 := by rw [← Nat.pow_succ]; congr 1; omega
      have := ten_pow_20; omega
  | succ f ih =>
    intro j R Mt hjf h8 h25 h23 h27 hkp hc hdig hM
    have hj : j < 20 := by omega
    refine svf_digStep hlive mag j R Mt SG h8 h25 h23 h27 hj hm ?_ ?_
    · intro hlt R' h8' h25' h23' h27' hkp'
      refine ih (j + 1) R' _ (by omega) h8' h25' h23' h27' (hkp.trans hkp') (.inr (by simpa using hlt))
        (fun i hi => ?_) (fun a ha => ?_)
      · rcases Nat.lt_or_ge i j with h | h
        · rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hdig i h
        · have hij : i = j := by omega
          subst hij
          rw [show s - 864 + 348 - 1 - i = (BitVec.ofNat 64 (s - 864 + 348 - i - 1)).toNat by
            rw [toNat_ofNat_lt (by omega)]; omega]
          rw [imgM_sb_ofNat _ _ _ (by omega)]
          unfold digB; congr 1; omega
      · rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hM a (by omega)
    · intro hle R' h26' h23' hkp'
      refine hX (j + 1) R' _ (by omega) (by simpa using hle) ?_ (by omega) h26' h23' (hkp.trans hkp')
        (fun i hi => ?_) (fun a ha => ?_)
      · rcases hc with ⟨h0, _⟩ | hc
        · left; omega
        · right; simpa using hc
      · rcases Nat.lt_or_ge i j with h | h
        · rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hdig i h
        · have hij : i = j := by omega
          subst hij
          rw [show s - 864 + 348 - 1 - i = (BitVec.ofNat 64 (s - 864 + 348 - i - 1)).toNat by
            rw [toNat_ofNat_lt (by omega)]; omega]
          rw [imgM_sb_ofNat _ _ _ (by omega)]
          unfold digB; congr 1; omega
      · rw [imgM_miss_nat _ _ (by omega) (by omega)]; exact hM a (by omega)

/-- What an integer conversion's digits are: `K` bytes at `sp + 348 - K`, the
decimal digits of `mag` most significant first, with the bounds that make
`K` the digit count. -/
structure DigitsAt (Mt : Mem) (s mag K : Nat) : Prop where
  pos : 1 ≤ K
  le : K ≤ 20
  hub : mag / 10 ^ (K - 1) ≤ 9
  hlb : K = 1 ∨ 9 < mag / 10 ^ (K - 2)
  bytes : ∀ i, i < K → imgM Mt (s - 864 + 348 - 1 - i) = digB mag i

/-- The digits' piece. -/
theorem digSrc {DA : List Nat} {s dst n K : Nat} (SG : SnpGeom s dst n) (hK : K ≤ 20) :
    PieceSrc DA s dst n (s - 864 + 348 - K) K := by
  have := SG.s_lo; have := SG.s_hi; have := SG.d_sep; have := SG.d_lo
  exact ⟨⟨by omega, by omega, by omega, by omega, by simp only [snpFP]; omega, by omega, by omega⟩,
    by omega, .inr ⟨by omega, by omega⟩⟩

/-- The integer conversion's continuation into `PRINT`. -/
def IntPrintK (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s dst n : Nat) (R0 : Nat → BitVec 64)
    (Mt0 : Mem) (p ap c : Nat) (total : List (BitVec 8)) (L : List (Nat × Nat)) (m sg : Nat) : Prop :=
  ∀ R' Mt' K, PrintIn DA s dst n R0 Mt0 p ap c total L (s - 864 + 348 - K) K sg R' Mt' →
    DigitsAt Mt' s m K → NW live Dt DA (snpS s dst n) Q 0x8000782c#64 R' Mt'

/-- **One digit** (`0x80008100`, `m ≤ 9`): `'0' + m` at `sp + 347`, `PRINT`. -/
theorem svf_dig1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m sg : Nat} (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (IA : IntAt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L m sg R Mt) (hm9 : m ≤ 9)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m sg) :
    NW live Dt DA (snpS s dst n) Q 0x80008100#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 := IA.st.core.r2
  have h14 := IA.r14
  have h20 := IA.r20
  have h167 := IA.sign
  have hsa := SG.s_al
  have hn9 : ¬ (9#64).toNat < (BitVec.ofNat 64 m).toNat := by rw [toNat_ofNat_lt (by omega)]; simp; omega
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (m + 48))) = BitVec.ofNat 64 (m + 48) :=
    VsaIris.Interp.sext32_ofNat_eq (by omega)
  have h167' : ldv .lbu (writeLog Mt [((BitVec.ofNat 64 (s - 864 + 347)).toNat, 1, BitVec.ofNat 64 (m + 48))])
      (BitVec.ofNat 64 (s - 864 + 167)).toNat = BitVec.ofNat 64 sg := by
    rw [ldv_miss_nat _ _ _ (by omega) (by omega) (by simp only [widthOfM]; omega)]; exact h167
  nx_runF hlive using [ofNat_add_ofNat, h2, h14, h20, h167, hn9, hsx, h167'] at 0x8000782c
  all_goals rename_i hsg _
  all_goals refine hk _ _ 1 ⟨IA.st.update SG ?_ ?_ ?_ ?_ ?_ ?_, hL, ?_, ?_, ?_, ?_, IA.sg01, ?_, ?_, ?_,
    .inr ?_, ?_, ?_, ?_, by omega, by omega⟩ ⟨Nat.le_refl _, by omega, by simpa using hm9, .inl rfl, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  · svf_mem; exact IA.st.core.fmt
  · svf_mem; exact IA.st.core.ret
  · svf_mem; exact IA.st.core.ap
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · exact IA.r28
  · rcases IA.sg01 with h | h <;> subst h <;> first | rfl | (simp at hsg) | decide
  · rw [show s - 864 + 348 - 1 = s - 864 + 347 by omega]
  · exact IA.r20
  · svf_mem; exact h167
  · svf_mem
  · exact digSrc SG (by omega)
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [show s - 864 + 348 - 1 - 0 = s - 864 + 347 by omega]
    svf_mem
    rw [imgM_sb_ofNat' _ _ _ (by omega) (by omega)]
    unfold digB; congr 1; simp; omega
  · svf_mem; exact IA.st.core.fmt
  · svf_mem; exact IA.st.core.ret
  · svf_mem; exact IA.st.core.ap
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · rcases IA.r6 with h | h <;> rw [h] <;> decide
  · exact IA.r28
  · rcases IA.sg01 with h | h <;> subst h <;> first | rfl | (simp at hsg) | decide
  · rw [show s - 864 + 348 - 1 = s - 864 + 347 by omega]
  · exact IA.r20
  · svf_mem; exact h167
  · svf_mem
  · exact digSrc SG (by omega)
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [show s - 864 + 348 - 1 - 0 = s - 864 + 347 by omega]
    svf_mem
    rw [imgM_sb_ofNat' _ _ _ (by omega) (by omega)]
    unfold digB; congr 1; simp; omega
/-- The digit loop's spills (`0x800082c8`): `s7`, `s4`, `s0`, `t3`, `t1` and
the buffer end. -/
structure DigSpill (s : Nat) (Rs : Nat → BitVec 64) (t1 : BitVec 64) (Mt : Mem) : Prop where
  s7 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 48)).toNat = Rs 23
  s4 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 56)).toNat = 18446744073709551615#64
  s0 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 120)).toNat = Rs 8
  t3 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 32)).toNat = 0#64
  t1 : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 40)).toNat = t1
  e : ldv .ld Mt (BitVec.ofNat 64 (s - 864 + 112)).toNat = BitVec.ofNat 64 (s - 864 + 348)

theorem svf_digExit0 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m K : Nat} (Rs R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L Rs Mt) (t1 : BitVec 64)
    (ht1 : t1 = 0#64 ∨ t1 = 32#64) (DS : DigSpill s Rs t1 Mt) (hR : ∀ z, z = 2 ∨ z = 9 ∨ z = 18 ∨ z = 19 ∨ z = 21 → R z = Rs z)
    (h26 : R 26 = BitVec.ofNat 64 (s - 864 + 348 - K)) (DG : DigitsAt Mt s m K)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = BitVec.ofNat 64 0)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m 0) :
    NW live Dt DA (snpS s dst n) Q 0x80008358#64 R Mt := by
  have hK1 := DG.pos
  have hK := DG.le
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 : R 2 = BitVec.ofNat 64 (s - 864) := (hR 2 (by omega)).trans St.core.r2
  have hsub : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (s - 864 + 348)) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (s - 864 + 348 - K))) = BitVec.ofNat 64 K := by
    rw [subw_ofNat' (by omega) (by omega) (by omega)]; congr 1; omega
  have hsa := SG.s_al
  have hsx := VsaIris.Interp.sext32_ofNat_eq (a := K) (by omega)
  have h167' : ldv .lbu (writeLog (writeLog Mt [((BitVec.ofNat 64 (s - 864 + 104)).toNat, 8, R 20)])
      [((BitVec.ofNat 64 (s - 864 + 40)).toNat, 8, R 23)]) (BitVec.ofNat 64 (s - 864 + 167)).toNat =
      BitVec.ofNat 64 0 := by svf_mem; exact h167
  have hsx1 := VsaIris.Interp.sext32_ofNat_eq (a := K + 1) (by omega)
  nx_runF hlive using [ofNat_add_ofNat, h2, h26, DS.s7, DS.s4, DS.s0, DS.t3, DS.t1, DS.e, h167', hsub, hsx, hsx1] at 0x8000782c
  all_goals refine hk _ _ K ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, hL, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_,
    .inr ?_, ?_, ?_, digSrc SG DG.le, by omega, by omega⟩ ⟨DG.pos, DG.le, DG.hub, DG.hlb, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> exact hR _ (by omega)))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  · svf_mem; exact St.core.fmt
  · svf_mem; exact St.core.ret
  · svf_mem; exact St.core.ap
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · simp [sgN]
  · exact h26
  · svf_mem; exact h167
  · svf_mem
  · intro i hi
    have := DG.bytes i hi
    svf_mem; exact this

theorem svf_digExit45 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m K : Nat} (Rs R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L Rs Mt) (t1 : BitVec 64)
    (ht1 : t1 = 0#64 ∨ t1 = 32#64) (DS : DigSpill s Rs t1 Mt) (hR : ∀ z, z = 2 ∨ z = 9 ∨ z = 18 ∨ z = 19 ∨ z = 21 → R z = Rs z)
    (h26 : R 26 = BitVec.ofNat 64 (s - 864 + 348 - K)) (DG : DigitsAt Mt s m K)
    (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = BitVec.ofNat 64 45)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m 45) :
    NW live Dt DA (snpS s dst n) Q 0x80008358#64 R Mt := by
  have hK1 := DG.pos
  have hK := DG.le
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have h2 : R 2 = BitVec.ofNat 64 (s - 864) := (hR 2 (by omega)).trans St.core.r2
  have hsub : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (s - 864 + 348)) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (s - 864 + 348 - K))) = BitVec.ofNat 64 K := by
    rw [subw_ofNat' (by omega) (by omega) (by omega)]; congr 1; omega
  have hsa := SG.s_al
  have hsx := VsaIris.Interp.sext32_ofNat_eq (a := K) (by omega)
  have h167' : ldv .lbu (writeLog (writeLog Mt [((BitVec.ofNat 64 (s - 864 + 104)).toNat, 8, R 20)])
      [((BitVec.ofNat 64 (s - 864 + 40)).toNat, 8, R 23)]) (BitVec.ofNat 64 (s - 864 + 167)).toNat =
      BitVec.ofNat 64 45 := by svf_mem; exact h167
  have hsx1 := VsaIris.Interp.sext32_ofNat_eq (a := K + 1) (by omega)
  nx_runF hlive using [ofNat_add_ofNat, h2, h26, DS.s7, DS.s4, DS.s0, DS.t3, DS.t1, DS.e, h167', hsub, hsx, hsx1] at 0x8000782c
  all_goals refine hk _ _ K ⟨St.update SG ?_ ?_ ?_ ?_ ?_ ?_, hL, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_,
    .inr ?_, ?_, ?_, digSrc SG DG.le, by omega, by omega⟩ ⟨DG.pos, DG.le, DG.hub, DG.hlb, ?_⟩
  all_goals (try (intro z hz; rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> exact hR _ (by omega)))
  all_goals (try (intro a ha; unfold StKeep SvfKeep at ha; svf_mem))
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
  · svf_mem; exact St.core.fmt
  · svf_mem; exact St.core.ret
  · svf_mem; exact St.core.ap
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · rcases ht1 with h | h <;> rw [h] <;> decide
  · simp [sgN]
  · exact h26
  · svf_mem; exact h167
  · svf_mem
  · intro i hi
    have := DG.bytes i hi
    svf_mem; exact this

/-- **The digit loop's exit** (`0x80008358`): the spills reloaded, `size = K`,
`realsz` with the sign, `PRINT`. -/
theorem svf_digExit {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m sg K : Nat} (Rs R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (St : SvfSt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L Rs Mt) (t1 : BitVec 64)
    (ht1 : t1 = 0#64 ∨ t1 = 32#64) (DS : DigSpill s Rs t1 Mt) (hR : ∀ z, z = 2 ∨ z = 9 ∨ z = 18 ∨ z = 19 ∨ z = 21 → R z = Rs z)
    (h26 : R 26 = BitVec.ofNat 64 (s - 864 + 348 - K)) (DG : DigitsAt Mt s m K)
    (hsg : sg = 0 ∨ sg = 45) (h167 : ldv .lbu Mt (BitVec.ofNat 64 (s - 864 + 167)).toNat = BitVec.ofNat 64 sg)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m sg) :
    NW live Dt DA (snpS s dst n) Q 0x80008358#64 R Mt := by
  rcases hsg with rfl | rfl
  · exact svf_digExit0 hlive Rs R Mt SG St t1 ht1 DS hR h26 DG h167 hL hc hsum hk
  · exact svf_digExit45 hlive Rs R Mt SG St t1 ht1 DS hR h26 DG h167 hL hc hsum hk

/-- **Several digits** (`0x80008100`, `m > 9`): the spills, the digit loop, its
exit, `PRINT`. -/
theorem svf_digMulti {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m sg : Nat} (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (IA : IntAt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L m sg R Mt) (hm9 : 9 < m)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m sg) :
    NW live Dt DA (snpS s dst n) Q 0x80008100#64 R Mt := by
  have hs1 := SG.s_lo
  have hs2 := SG.s_hi
  have hsa := SG.s_al
  have h2 := IA.st.core.r2
  have h14 := IA.r14
  have h9 : (9#64).toNat < (BitVec.ofNat 64 m).toNat := by rw [toNat_ofNat_lt IA.mlt]; simp; omega
  have h1024 : R 6 &&& 1024#64 = 0#64 := by rcases IA.r6 with h | h <;> rw [h] <;> decide
  nx_runF hlive using [ofNat_add_ofNat, h2, h14, h9, h1024] at 0x8000831c
  refine svf_digLoop hlive m IA.mlt _ _ SG (fun K R' Mt' hK1 hub hlb hK h26 h23 hkp hdig hM => ?_) 20 0 _ _
    rfl (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) (.inl ⟨rfl, hm9⟩)
    (fun i hi => absurd hi (by omega)) (fun _ _ => rfl)
  have hMM : ∀ a, (a < s - 864 + 328 ∨ s - 864 + 348 ≤ a) →
      imgM Mt' a = imgM (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
        [((BitVec.ofNat 64 (s - 864 + 48)).toNat, 8, R 23)])
        [((BitVec.ofNat 64 (s - 864 + 56)).toNat, 8, R 20)])
        [((BitVec.ofNat 64 (s - 864 + 120)).toNat, 8, R 8)])
        [((BitVec.ofNat 64 (s - 864 + 32)).toNat, 8, R 28)])
        [((BitVec.ofNat 64 (s - 864 + 40)).toNat, 8, R 6)])
        [((BitVec.ofNat 64 (s - 864 + 112)).toNat, 8, BitVec.ofNat 64 (s - 864 + 348))]) a :=
    fun a ha => hM a (by omega)
  have agree : ∀ (k : MKind) (off : Nat), (off + widthOfM k ≤ 328) →
      ldv k Mt' (BitVec.ofNat 64 (s - 864 + off)).toNat = ldv k (writeLog (writeLog (writeLog (writeLog
        (writeLog (writeLog Mt
        [((BitVec.ofNat 64 (s - 864 + 48)).toNat, 8, R 23)])
        [((BitVec.ofNat 64 (s - 864 + 56)).toNat, 8, R 20)])
        [((BitVec.ofNat 64 (s - 864 + 120)).toNat, 8, R 8)])
        [((BitVec.ofNat 64 (s - 864 + 32)).toNat, 8, R 28)])
        [((BitVec.ofNat 64 (s - 864 + 40)).toNat, 8, R 6)])
        [((BitVec.ofNat 64 (s - 864 + 112)).toNat, 8, BitVec.ofNat 64 (s - 864 + 348))])
        (BitVec.ofNat 64 (s - 864 + off)).toNat :=
    fun k off h => by rw [toNat_ofNat_lt (by omega)]; exact ldv_agree k fun i hi => hMM _ (by omega)
  refine svf_digExit hlive R R' Mt' SG (IA.st.agree SG fun a ha => ?_) (R 6) IA.r6 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    (fun z hz => ?_) h26 ⟨hK1, hK, hub, hlb, hdig⟩ IA.sg01 ?_ hL hc hsum hk
  · rw [hMM a (by unfold StKeep SvfKeep at ha; omega)]; unfold StKeep SvfKeep at ha; svf_mem
  · rw [agree .ld 48 (by simp only [widthOfM]; omega)]; svf_mem
  · rw [agree .ld 56 (by simp only [widthOfM]; omega)]; svf_mem; exact IA.r20
  · rw [agree .ld 120 (by simp only [widthOfM]; omega)]; svf_mem
  · rw [agree .ld 32 (by simp only [widthOfM]; omega)]; svf_mem; exact IA.r28
  · rw [agree .ld 40 (by simp only [widthOfM]; omega)]; svf_mem
  · rw [agree .ld 112 (by simp only [widthOfM]; omega)]; svf_mem
  · rw [hkp z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [agree .lbu 167 (by simp only [widthOfM]; omega)]; svf_mem; exact IA.sign

/-- **An integer's digits** (`0x80008100`): one digit or the loop, then `PRINT`. -/
theorem svf_digits {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    {R0 : Nat → BitVec 64} {Mt0 : Mem} {p ap c : Nat} {total : List (BitVec 8)}
    {L : List (Nat × Nat)} {m sg : Nat} (R : Nat → BitVec 64) (Mt : Mem) (SG : SnpGeom s dst n)
    (IA : IntAt DA s dst n R0 Mt0 p ap (BitVec.ofNat 64 c) total L m sg R Mt)
    (hL : L.length ≤ 1) (hc : c + 20 + 1 < 2 ^ 31) (hsum : sumLen L + 20 + 1 < 2 ^ 31)
    (hk : IntPrintK live Dt DA Q s dst n R0 Mt0 p ap c total L m sg) :
    NW live Dt DA (snpS s dst n) Q 0x80008100#64 R Mt := by
  rcases Nat.lt_or_ge 9 m with h | h
  · exact svf_digMulti hlive R Mt SG IA h hL hc hsum hk
  · exact svf_dig1 hlive R Mt SG IA h hL hc hsum hk


end VsaIris.Sym
