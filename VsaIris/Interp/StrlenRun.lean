import VsaIris.Interp.StrSteps

/-!
# `strlen` as a symbolic run over a persistent string

The whole of newlib's `strlen` (`0x80006cf0`) as one `SW` run
(`StrCode.lean`, `StrRun.lean`) whose data view is the string's bytes
`[P, P + len]` (`Strlen.strText`, persistent, read by total reads) and which
owns no byte. The word loop's `ld` reads the word containing the NUL whole:
its up to seven bytes past the NUL are nobody's (`sr_havoc`), and the run
holds for every value they may hold. The zero-byte test only depends on the
string's bytes (`StrlenMagic.detect_all_ones`, byte by byte), and every byte
the tail tests lies at or before the NUL.

H3's arithmetic (`Strlen.lean`: `tailAddr`, `armVal`, `snez_finalG`, …) is
reused through `LCtx.old`, the H3 context at the trivial liveness: those
lemmas read only the geometry and the string.
-/

namespace VsaIris.Interp.StrLeaf

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen
open Vsa.Sim Vsa.MemRepr
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `strlen`'s end: back at `r` with the length in `a0`. -/
def LenEnd (r : BitVec 64) (len : Nat) (rv : Nat → BitVec 64) (_ : Nat → BitVec 8) : Prop :=
  rv 32 = r ∧ rv 1 = r ∧ rv 10 = BitVec.ofNat 64 len

/-- **The side conditions of a `strlen` run**: the read window's geometry
(`[P, P + len + 8)`, RAM, off the HTIF words), the string's bytes, the
return alignment, and the live code. -/
structure LCtx (live : Nat → Prop) (P r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8) :
    Prop where
  regions : ReadRegions P len
  str : StrBytes P.toNat len bv
  retAlign : r.toNat % 4 = 0
  code : ∀ p ∈ strCode, live p.1

/-- `strlen`'s run over the string `[P, P + len]` at `bv`, owning `S`. -/
abbrev LW (live : Nat → Prop) (P r : BitVec 64) (len : Nat) (bv : Nat → BitVec 8)
    (S : Nat → Prop) : BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SW live (strText P.toNat len bv) S (LenEnd r len)

variable {live : Nat → Prop} {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8}
  {S : Nat → Prop} {R : Nat → BitVec 64}

/-- H3's context at the trivial liveness (its arithmetic reads only the
geometry and the string). -/
def LCtx.old (c : LCtx live P r len bv) : Ctx (fun _ => True) P r len bv :=
  ⟨c.regions, c.str, c.retAlign, fun _ _ => trivial⟩

/-! ## Values -/

/-- A byte function agreeing with the data view reads the string. -/
theorem agree_at {p n : Nat} {f : Nat → BitVec 8} (hf : ∀ q ∈ strText p n bv, f q.1 = q.2)
    {k : Nat} (hk : k ≤ n) : f (p + k) = bv (p + k) :=
  hf _ (mem_strText p n k bv hk)

theorem ldvf_lbu (f : Nat → BitVec 8) (a : Nat) :
    ldvf .lbu f a = zero_extend (m := 64) (f a) := rfl

theorem zext_eq_zero (b : BitVec 8) : zero_extend (m := 64) b = 0#64 ↔ b = 0#8 := by
  have := zext_beqz b
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq] at this
  exact this

/-- The byte at offset `k ≤ len` is NUL exactly at the terminator. -/
theorem byte_zero_iff (c : LCtx live P r len bv) {k : Nat} (hk : k ≤ len) :
    bv (P.toNat + k) = 0#8 ↔ k = len := by
  have hb := byteBeq c.old k hk
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq] at hb
  exact hb

/-- Byte `k` of a doubleword load. -/
theorem ldvf_ld_byte (f : Nat → BitVec 8) (a k : Nat) (hk : k < 8) :
    (ldvf .ld f a).extractLsb' (8 * k) 8 = f (a + k) := by
  have e : ldvf .ld f a = sign_extend (m := 64) (f (a + 7) ++ f (a + 6) ++ f (a + 5) ++
      f (a + 4) ++ f (a + 3) ++ f (a + 2) ++ f (a + 1) ++ f (a + 0)) := rfl
  rw [e, sext64_self]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.reduceMul, Nat.add_zero]
    rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

/-- **The zero-byte test of a word**, from the string's bytes alone: the
word at `P + t` (`t ≤ len`) has no zero byte exactly when it lies before the
NUL, whatever its bytes past the NUL hold. -/
theorem word_test (c : LCtx live P r len bv) {f : Nat → BitVec 8}
    (hf : ∀ q ∈ strText P.toNat len bv, f q.1 = q.2) {t : Nat} (ht : t ≤ len) :
    strlenWordVal (ldvf .ld f (P.toNat + t)) = BitVec.allOnes 64 ↔ t + 8 ≤ len := by
  rw [detect_all_ones]
  constructor
  · intro h
    refine Classical.byContradiction fun hlt => ?_
    have hk : len - t < 8 := by omega
    apply h (len - t) hk
    rw [ldvf_ld_byte f _ _ hk, show P.toNat + t + (len - t) = P.toNat + len by omega,
      agree_at hf (Nat.le_refl len)]
    exact (byte_zero_iff c (Nat.le_refl len)).2 rfl
  · intro h k hk
    rw [ldvf_ld_byte f _ _ hk, show P.toNat + t + k = P.toNat + (t + k) by omega,
      agree_at hf (by omega)]
    intro h0
    have := (byte_zero_iff c (show t + k ≤ len by omega)).1 h0
    omega

/-! ## The end -/

theorem lenEnd (hR1 : R 1 = r) (h10 : R 10 = BitVec.ofNat 64 len) {Mt : Mem} :
    LW live P r len bv S r R Mt :=
  sr_done fun _ _ hm => ⟨hm.pc, by rw [hm.regs 1 (by decide) (by decide), hR1],
    by rw [hm.regs 10 (by decide) (by decide), h10]⟩


/-- A load inside the read window is `LdOK`. -/
theorem ldok (c : LCtx live P r len bv) {k w : Nat} (h : k + w ≤ len + 8) :
    LdOK (P.toNat + k) w := by
  have := c.regions.lo; have := c.regions.hi; have h3 := c.regions.htif
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h3 | h3
  · left; omega
  · right; omega

/-! ## The seven return arms (`addi a0,a3,-(8-k); ret`) -/

theorem armAlign (c : LCtx live P r len bv) {R : Nat → BitVec 64} (hra : R 1 = r) (v : BitVec 64) :
    (upd R 10 v 1).toNat % 4 = 0 := by
  rw [upd_other _ _ (by decide), hra]; exact c.retAlign

theorem armEnd {R : Nat → BitVec 64} {Mt : Mem} {t k : Nat} (imm : BitVec 12)
    (hra : R 1 = r) (h13 : R 13 = BitVec.ofNat 64 (t + 8)) (hk : k ≤ 8) (hlen : t + k = len)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    LW live P r len bv S (upd R 10 (R 13 + sign_extend (m := 64) imm) 1)
      (upd R 10 (R 13 + sign_extend (m := 64) imm)) Mt := by
  have e : upd R 10 (R 13 + sign_extend (m := 64) imm) 1 = r := by
    rw [upd_other _ _ (by decide)]; exact hra
  rw [e]
  exact lenEnd (by rw [upd_other _ _ (by decide)]; exact hra)
    (by rw [upd_same, h13]; exact armVal t len k imm hk hlen himm)

/-! ## The byte tail `0x80006d2c … 0x80006d70` -/

/-- In the byte tail, `k` bytes of the last word tested: `a3 = t + 8`,
`a4 = P + (t + 8)`, and the NUL lies in `[t + k, t + 8)`. -/
structure TK (P r : BitVec 64) (len t k : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = r
  a3 : R 13 = BitVec.ofNat 64 (t + 8)
  a4 : R 14 = P + BitVec.ofNat 64 (t + 8)
  lo : t + k ≤ len
  hi : len < t + 8

theorem TK.upd15 {t k : Nat} {R : Nat → BitVec 64} (h : TK P r len t k R) (v : BitVec 64)
    (hk : t + (k + 1) ≤ len) : TK P r len t (k + 1) (upd R 15 v) :=
  ⟨by rw [upd_other _ _ (by decide)]; exact h.ra, by rw [upd_other _ _ (by decide)]; exact h.a3,
   by rw [upd_other _ _ (by decide)]; exact h.a4, hk, h.hi⟩

/-- A tail test's address. -/
theorem tailAddrOf (c : LCtx live P r len bv) {t k : Nat} {R : Nat → BitVec 64}
    (ha4 : R 14 = P + BitVec.ofNat 64 (t + 8)) (hlo : t + k ≤ len) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) (hk : k ≤ 8) :
    ((R 14) + sign_extend (m := 64) imm).toNat = P.toNat + (t + k) := by
  rw [ha4]; exact tailAddr c.old t k hk (by omega) imm himm

theorem tailOK (c : LCtx live P r len bv) {t k : Nat} {R : Nat → BitVec 64}
    (ha4 : R 14 = P + BitVec.ofNat 64 (t + 8)) (hlo : t + k ≤ len) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) (hk : k ≤ 8) :
    LdOK ((R 14) + sign_extend (m := 64) imm).toNat 1 := by
  rw [tailAddrOf c ha4 hlo imm himm hk]; exact ldok c (by omega)

/-- The tested byte, read through any image agreeing with the string. -/
theorem tailZero (c : LCtx live P r len bv) {t k : Nat} {R : Nat → BitVec 64}
    (ha4 : R 14 = P + BitVec.ofNat 64 (t + 8)) (hlo : t + k ≤ len)
    {f : Nat → BitVec 8} (hf : ∀ q ∈ strText P.toNat len bv, f q.1 = q.2)
    (imm : BitVec 12) (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k)))
    (hk : k ≤ 8) :
    f ((R 14) + sign_extend (m := 64) imm).toNat = 0#8 ↔ t + k = len := by
  rw [tailAddrOf c ha4 hlo imm himm hk, agree_at hf hlo]
  exact byte_zero_iff c hlo

theorem sext_ffe : (sign_extend (m := 64) (0xffe#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 6)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem tail6 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 6 R) : LW live P r len bv S 0x80006d60#64 R Mt := by
  refine slH_80006d60 c.code (tailOK c h.a4 h.lo _ sext_ffe (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ffe (by omega)
  refine slO_80006d64 c.code (sl_80006d68 c.code (sl_80006d6c c.code (sl_80006d70 c.code ?_ ?_)))
  · simp only [upd_other _ _ (show (1 : Nat) ≠ 10 by decide), upd_other _ _ (show (1 : Nat) ≠ 15 by decide), h.ra]
    exact c.retAlign
  · have e1 : ∀ v1 v2 v3 v4, upd (upd (upd (upd R 15 v1) 10 v2) 10 v3) 10 v4 1 = r := by
      intro v1 v2 v3 v4; simp only [upd_other _ _ (show (1 : Nat) ≠ 10 by decide),
        upd_other _ _ (show (1 : Nat) ≠ 15 by decide), h.ra]
    rw [e1]
    refine lenEnd (by rw [e1]) ?_
    simp only [upd_same, upd_other _ _ (show (13 : Nat) ≠ 10 by decide),
      upd_other _ _ (show (13 : Nat) ≠ 15 by decide), h.a3]
    rw [ldvf_lbu]
    have hlo := h.lo; have hhi := h.hi; have hnw := c.regions.hi
    have := snez_finalG t 0 len (f ((R 14) + sign_extend (m := 64) (0xffe#12)).toNat)
      (by omega) (by omega) (by omega) (hb.trans ⟨fun e => by omega, fun e => by omega⟩)
    rw [show t + 8 * (0 + 1) = t + 8 by omega] at this
    exact this

theorem sext_ff8 : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 0)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_ff9 : (sign_extend (m := 64) (0xff9#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 1)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_ffa : (sign_extend (m := 64) (0xffa#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 2)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_ffb : (sign_extend (m := 64) (0xffb#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 3)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_ffc : (sign_extend (m := 64) (0xffc#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 4)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_ffd : (sign_extend (m := 64) (0xffd#12) : BitVec 64) = -(BitVec.ofNat 64 (8 - 5)) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem tail5 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 5 R) : LW live P r len bv S 0x80006d58#64 R Mt := by
  refine slH_80006d58 c.code (tailOK c h.a4 h.lo _ sext_ffd (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ffd (by omega)
  refine sl_80006d5c c.code (fun hz => ?_) (fun hnz => ?_)
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    exact sl_80006dbc c.code (sl_80006dc0 c.code (armAlign c (by rw [upd_other _ _ (by decide)]; exact h.ra) _)
      (armEnd _ (by rw [upd_other _ _ (by decide)]; exact h.ra) (by rw [upd_other _ _ (by decide)]; exact h.a3)
        (by omega) he sext_ffd))
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hlo := h.lo; have hhi := h.hi
    have hne : t + 5 ≠ len := fun e => hnz (hb.2 e)
    exact tail6 c (h.upd15 _ (by omega))

theorem tail4 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 4 R) : LW live P r len bv S 0x80006d50#64 R Mt := by
  refine slH_80006d50 c.code (tailOK c h.a4 h.lo _ sext_ffc (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ffc (by omega)
  refine sl_80006d54 c.code (fun hz => ?_) (fun hnz => ?_)
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    exact sl_80006db4 c.code (sl_80006db8 c.code (armAlign c (by rw [upd_other _ _ (by decide)]; exact h.ra) _)
      (armEnd _ (by rw [upd_other _ _ (by decide)]; exact h.ra) (by rw [upd_other _ _ (by decide)]; exact h.a3)
        (by omega) he sext_ffc))
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hlo := h.lo; have hhi := h.hi
    have hne : t + 4 ≠ len := fun e => hnz (hb.2 e)
    exact tail5 c (h.upd15 _ (by omega))

theorem tail3 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 3 R) : LW live P r len bv S 0x80006d48#64 R Mt := by
  refine slH_80006d48 c.code (tailOK c h.a4 h.lo _ sext_ffb (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ffb (by omega)
  refine sl_80006d4c c.code (fun hz => ?_) (fun hnz => ?_)
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    exact sl_80006da4 c.code (sl_80006da8 c.code (armAlign c (by rw [upd_other _ _ (by decide)]; exact h.ra) _)
      (armEnd _ (by rw [upd_other _ _ (by decide)]; exact h.ra) (by rw [upd_other _ _ (by decide)]; exact h.a3)
        (by omega) he sext_ffb))
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hlo := h.lo; have hhi := h.hi
    have hne : t + 3 ≠ len := fun e => hnz (hb.2 e)
    exact tail4 c (h.upd15 _ (by omega))

theorem tail2 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 2 R) : LW live P r len bv S 0x80006d40#64 R Mt := by
  refine slH_80006d40 c.code (tailOK c h.a4 h.lo _ sext_ffa (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ffa (by omega)
  refine sl_80006d44 c.code (fun hz => ?_) (fun hnz => ?_)
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    exact sl_80006dac c.code (sl_80006db0 c.code (armAlign c (by rw [upd_other _ _ (by decide)]; exact h.ra) _)
      (armEnd _ (by rw [upd_other _ _ (by decide)]; exact h.ra) (by rw [upd_other _ _ (by decide)]; exact h.a3)
        (by omega) he sext_ffa))
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hlo := h.lo; have hhi := h.hi
    have hne : t + 2 ≠ len := fun e => hnz (hb.2 e)
    exact tail3 c (h.upd15 _ (by omega))

theorem tail1 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : TK P r len t 1 R) : LW live P r len bv S 0x80006d38#64 R Mt := by
  refine slH_80006d38 c.code (tailOK c h.a4 h.lo _ sext_ff9 (by omega)) fun f hf => ?_
  have hb := tailZero c h.a4 h.lo hf _ sext_ff9 (by omega)
  refine sl_80006d3c c.code (fun hz => ?_) (fun hnz => ?_)
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    exact sl_80006d94 c.code (sl_80006d98 c.code (armAlign c (by rw [upd_other _ _ (by decide)]; exact h.ra) _)
      (armEnd _ (by rw [upd_other _ _ (by decide)]; exact h.ra) (by rw [upd_other _ _ (by decide)]; exact h.a3)
        (by omega) he sext_ff9))
  · rw [upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hlo := h.lo; have hhi := h.hi
    have hne : t + 1 ≠ len := fun e => hnz (hb.2 e)
    exact tail2 c (h.upd15 _ (by omega))

/-- At the tail entry `0x80006d2c`: `a0 = P`, `a4 = P + (t + 8)`, the NUL in
`[t, t + 8)`. -/
structure TailAt (P r : BitVec 64) (len t : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = r
  a0 : R 10 = P
  a4 : R 14 = P + BitVec.ofNat 64 (t + 8)
  lo : t ≤ len
  hi : len < t + 8

theorem tail0 (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h0 : TailAt P r len t R) : LW live P r len bv S 0x80006d2c#64 R Mt := by
  have hlo := h0.lo; have hhi := h0.hi
  refine slH_80006d2c c.code (tailOK c (k := 0) h0.a4 (by omega) _ sext_ff8 (by omega)) fun f hf => ?_
  have hb := tailZero c (k := 0) h0.a4 (by omega) hf _ sext_ff8 (by omega)
  have h3 : ∀ v : BitVec 64, (upd R 15 v 14 - upd R 15 v 10) = BitVec.ofNat 64 (t + 8) := by
    intro v
    rw [upd_other _ _ (by decide), upd_other _ _ (by decide), h0.a4, h0.a0]
    exact sub_a4_a0_val P (t + 8)
  have hT : ∀ v : BitVec 64, TK P r len t 0 (upd (upd R 15 v) 13 (upd R 15 v 14 - upd R 15 v 10)) :=
    fun v => ⟨by simp only [upd_other _ _ (show (1 : Nat) ≠ 13 by decide),
        upd_other _ _ (show (1 : Nat) ≠ 15 by decide)]; exact h0.ra,
      by rw [upd_same]; exact h3 v,
      by simp only [upd_other _ _ (show (14 : Nat) ≠ 13 by decide),
        upd_other _ _ (show (14 : Nat) ≠ 15 by decide)]; exact h0.a4, by omega, h0.hi⟩
  refine sl_80006d30 c.code (sl_80006d34 c.code (fun hz => ?_) (fun hnz => ?_))
  · rw [upd_other _ _ (by decide), upd_same, ldvf_lbu, zext_eq_zero] at hz
    have he := hb.1 hz
    have h := hT (ldvf .lbu f ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat)
    exact sl_80006d9c c.code (sl_80006da0 c.code (armAlign c h.ra _)
      (armEnd _ h.ra h.a3 (by omega) he sext_ff8))
  · rw [upd_other _ _ (by decide), upd_same, ldvf_lbu, zext_eq_zero] at hnz
    have hne : t + 0 ≠ len := fun e => hnz (hb.2 e)
    have h := hT (ldvf .lbu f ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat)
    exact tail1 c ⟨h.ra, h.a3, h.a4, by omega, h.hi⟩

/-! ## The word scan `0x80006d10 … 0x80006d28` -/

/-- At the word-loop head `0x80006d10`, `t` bytes scanned. -/
structure WordAt (P r : BitVec 64) (len t : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = r
  a0 : R 10 = P
  a1 : R 11 = BitVec.allOnes 64
  a3 : R 13 = magic7f
  a4 : R 14 = P + BitVec.ofNat 64 t
  tle : t ≤ len

theorem a4_plus8 (x : BitVec 64) (t : Nat) :
    (x + BitVec.ofNat 64 t) + sign_extend (m := 64) (0x008#12) = x + BitVec.ofNat 64 (t + 8) := by
  have := a4_incrG x t 0
  simpa using this

/-- **The word scan.** `n` bounds the words left before the NUL. -/
theorem wordRun (c : LCtx live P r len bv) :
    ∀ (n t : Nat) (R : Nat → BitVec 64) (Mt : Mem), len < t + 8 * n + 8 → WordAt P r len t R →
      LW live P r len bv S 0x80006d10#64 R Mt := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro t R Mt hn h
    have htle := h.tle
    have hnw := c.regions.nowrap
    have ha : ((R 14) + sign_extend (m := 64) (0x000#12)).toNat = P.toNat + t := by
      rw [sext0_add, h.a4]; exact ptrN P t (by omega)
    refine slH_80006d10 c.code (by rw [ha]; exact ldok c (by omega)) fun f hf => ?_
    have htest := word_test c hf htle
    refine sl_80006d14 c.code (sl_80006d18 c.code (sl_80006d1c c.code (sl_80006d20 c.code
      (sl_80006d24 c.code (sl_80006d28 c.code (fun heq => ?_) (fun hne => ?_))))))
    all_goals first
      | (simp (disch := decide) only [upd_same, upd_other] at heq
         rw [h.a3, h.a1, strlenWordVal_eq, ha] at heq)
      | (simp (disch := decide) only [upd_same, upd_other] at hne
         rw [h.a3, h.a1, strlenWordVal_eq, ha] at hne)
  · exact absurd (htest.1 heq) (by omega)
  · refine tail0 c ⟨?_, ?_, ?_, htle, by omega⟩
    · simp (disch := decide) only [upd_same, upd_other]; exact h.ra
    · simp (disch := decide) only [upd_same, upd_other]; exact h.a0
    · simp (disch := decide) only [upd_same, upd_other]; rw [h.a4]; exact a4_plus8 P t
  · have hle := htest.1 heq
    refine ih (t + 8) _ Mt (by omega) ⟨?_, ?_, ?_, ?_, ?_, hle⟩
    all_goals simp (disch := decide) only [upd_same, upd_other]
    · exact h.ra
    · exact h.a0
    · exact h.a1
    · exact h.a3
    · rw [h.a4]; exact a4_plus8 P t
  · refine tail0 c ⟨?_, ?_, ?_, htle, ?_⟩
    · simp (disch := decide) only [upd_same, upd_other]; exact h.ra
    · simp (disch := decide) only [upd_same, upd_other]; exact h.a0
    · simp (disch := decide) only [upd_same, upd_other]; rw [h.a4]; exact a4_plus8 P t
    · exact Classical.byContradiction fun hc => hne (htest.2 (by omega))

/-! ## The magic setup, the byte peel, and the entry -/

/-- At the magic setup `0x80006cfc`, `t` bytes scanned. -/
structure AlignAt (P r : BitVec 64) (len t : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = r
  a0 : R 10 = P
  a4 : R 14 = P + BitVec.ofNat 64 t
  tle : t ≤ len

theorem alignRun (c : LCtx live P r len bv) {t : Nat} {R : Nat → BitVec 64} {Mt : Mem}
    (h : AlignAt P r len t R) : LW live P r len bv S 0x80006cfc#64 R Mt := by
  refine sl_80006cfc c.code (sl_80006d00 c.code (sl_80006d04 c.code (sl_80006d08 c.code
    (sl_80006d0c c.code (wordRun c len t _ Mt (by omega) ⟨?_, ?_, ?_, ?_, ?_, h.tle⟩)))))
  all_goals simp (disch := decide) only [upd_same, upd_other]
  · exact h.ra
  · exact h.a0
  · exact allOnes_build
  · exact magic_build
  · exact h.a4

/-- At the byte-peel head `0x80006d78`, `m` bytes peeled. -/
structure PeelAt (P r : BitVec 64) (len m : Nat) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = r
  a0 : R 10 = P
  a4 : R 14 = P + BitVec.ofNat 64 m
  mle : m ≤ len

theorem peelRun (c : LCtx live P r len bv) :
    ∀ (n m : Nat) (R : Nat → BitVec 64) (Mt : Mem), len = m + n → PeelAt P r len m R →
      LW live P r len bv S 0x80006d78#64 R Mt := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro m R Mt hn h
    have hmle := h.mle
    have hnw := c.regions.nowrap
    have ha : ((R 14) + sign_extend (m := 64) (0x000#12)).toNat = P.toNat + m := by
      rw [sext0_add, h.a4]; exact ptrN P m (by omega)
    have hptr1 : (P + BitVec.ofNat 64 (m + 1)).toNat = P.toNat + (m + 1) := ptrN P (m + 1) (by omega)
    refine slH_80006d78 c.code (by rw [ha]; exact ldok c (by omega)) fun f hf => ?_
    have hz : f (P.toNat + m) = 0#8 ↔ m = len := by
      rw [agree_at hf hmle]; exact byte_zero_iff c hmle
    have h14 : R 14 + sign_extend (m := 64) (0x001#12) = P + BitVec.ofNat 64 (m + 1) := by
      rw [h.a4]; exact Strlen.a4_incr1 P m
    refine sl_80006d7c c.code (sl_80006d80 c.code (sl_80006d84 c.code (fun hnz => ?_) (fun hz0 => ?_)))
    all_goals first
      | (simp (disch := decide) only [upd_same, upd_other] at hnz
         rw [ldvf_lbu, ha, Ne, zext_eq_zero, hz] at hnz)
      | (simp (disch := decide) only [upd_same, upd_other] at hz0
         rw [ldvf_lbu, ha, Ne, zext_eq_zero, hz, Classical.not_not] at hz0)
  · exact absurd (by omega : m = len) hnz
  · -- the NUL: `sub a4,a4,a0; addi a0,a4,-1; ret`
    refine sl_80006d88 c.code (sl_80006d8c c.code (sl_80006d90 c.code ?_ ?_))
    · simp (disch := decide) only [upd_same, upd_other]; rw [h.ra]; exact c.retAlign
    · have e1 : ∀ v1 v2 v3 v4 v5, upd (upd (upd (upd (upd R 15 v1) 14 v2) 13 v3) 14 v4) 10 v5 1 = r := by
        intro v1 v2 v3 v4 v5; simp (disch := decide) only [upd_other]; exact h.ra
      rw [e1]
      refine lenEnd (by rw [e1]) ?_
      simp (disch := decide) only [upd_same, upd_other]
      rw [h14, h.a0, sub_a4_a0_val P (m + 1),
        show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(BitVec.ofNat 64 1) from by
          apply BitVec.eq_of_toNat_eq; decide,
        BitVec.add_neg_eq_sub, ofNat_sub (m + 1) 1 (by omega), hz0]
      rfl
  · -- a character: the alignment test
    have hml : m + 1 ≤ len := by omega
    refine sl_80006d74 c.code (fun hal => ?_) (fun hnal => ?_)
    · refine alignRun c ⟨?_, ?_, ?_, hml⟩
      all_goals simp (disch := decide) only [upd_same, upd_other]
      · exact h.ra
      · exact h.a0
      · exact h14
    · simp (disch := decide) only [upd_same, upd_other] at hnal
      rw [h14] at hnal
      refine ih (m + 1) _ Mt (by omega) ⟨?_, ?_, ?_, hml⟩
      all_goals simp (disch := decide) only [upd_same, upd_other]
      · exact h.ra
      · exact h.a0
      · exact h14
  · -- the NUL
    refine sl_80006d88 c.code (sl_80006d8c c.code (sl_80006d90 c.code ?_ ?_))
    · simp (disch := decide) only [upd_same, upd_other]; rw [h.ra]; exact c.retAlign
    · have e1 : ∀ v1 v2 v3 v4 v5, upd (upd (upd (upd (upd R 15 v1) 14 v2) 13 v3) 14 v4) 10 v5 1 = r := by
        intro v1 v2 v3 v4 v5; simp (disch := decide) only [upd_other]; exact h.ra
      rw [e1]
      refine lenEnd (by rw [e1]) ?_
      simp (disch := decide) only [upd_same, upd_other]
      rw [h14, h.a0, sub_a4_a0_val P (m + 1),
        show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(BitVec.ofNat 64 1) from by
          apply BitVec.eq_of_toNat_eq; decide,
        BitVec.add_neg_eq_sub, ofNat_sub (m + 1) 1 (by omega), hz0]
      rfl

/-- **`strlen` from its entry**, over a persistent string. -/
theorem strlenRunL (c : LCtx live P r len bv) {R : Nat → BitVec 64} {Mt : Mem}
    (h1 : R 1 = r) (h10 : R 10 = P) : LW live P r len bv S 0x80006cf0#64 R Mt := by
  refine sl_80006cf0 c.code (sl_80006cf4 c.code (sl_80006cf8 c.code (fun hnz => ?_) (fun hz => ?_)))
  · simp (disch := decide) only [upd_same, upd_other] at hnz
    rw [h10] at hnz
    refine peelRun c len 0 _ Mt (by omega) ⟨?_, ?_, ?_, Nat.zero_le _⟩
    all_goals simp (disch := decide) only [upd_same, upd_other]
    · exact h1
    · exact h10
    · rw [h10, sext0_add]; exact (BitVec.add_zero P).symm
  · refine alignRun c ⟨?_, ?_, ?_, Nat.zero_le _⟩
    all_goals simp (disch := decide) only [upd_same, upd_other]
    · exact h1
    · exact h10
    · rw [h10, sext0_add]; exact (BitVec.add_zero P).symm

end VsaIris.Interp.StrLeaf
