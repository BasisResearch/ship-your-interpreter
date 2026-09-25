import VsaIris.Vsa.Fprintf.Sfv

/-!
# `_vfprintf_r`'s format scan (lane N5)

`_vfprintf_r`'s main loop (`0x8000a9b8`) reads the format one character at a
time through the locale's `mbtowc` (`__ascii_mbtowc` in the C locale, one
byte per call, `__locale_mb_cur_max` = 1). The character goes to the stack
word `sp + 180`; the loop advances `s9` past every character other than `%`
and NUL.

`vfp_mb` is one round trip (`0x8000a9b8` → `0x8000a9d8`) for any format byte;
`vfp_scan` runs the loop over a run of literal bytes. The format bytes are
data-view bytes (`FmtAt`); the locale's function pointer and `mb_cur_max`
are owned bytes of newlib's data (`LocMb`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- `snez` of a nonzero word. -/
theorem snez_one {x : BitVec 64} (h : x ≠ 0#64) :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u 0#64 x)) = 1#64 := by
  have hx : 0 < x.toNat := Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (by simp [e]))
  rw [(ult_iff _ _).2 (by simpa using hx)]; decide

/-- `snez` of zero. -/
theorem snez_zero :
    LeanRV64DExecutable.zero_extend (m := 64) (LeanRV64DExecutable.Functions.bool_to_bit
      (LeanRV64DExecutable.Functions.zopz0zI_u 0#64 0#64)) = 0#64 := by
  rw [(ult_false_iff _ _).2 (by simp)]; decide

/-- A byte stored as a word and loaded back with `lw`. -/
theorem lw_zext8 (b : BitVec 8) :
    BitVec.signExtend 64 (BitVec.ofNat 32 ((BitVec.zeroExtend 64 b).toNat % 4294967296)) =
      BitVec.zeroExtend 64 b := by
  have hb := b.isLt
  have hm : (BitVec.ofNat 32 ((BitVec.zeroExtend 64 b).toNat % 4294967296)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem zext8_ne {b c : BitVec 8} (h : b ≠ c) : BitVec.zeroExtend 64 b ≠ BitVec.zeroExtend 64 c :=
  fun e => h (by
    have e' := congrArg BitVec.toNat e
    have := b.isLt; have := c.isLt
    simp only [BitVec.toNat_setWidth, Nat.reducePow] at e' this
    exact BitVec.eq_of_toNat_eq (by omega))

/-- The format's bytes `bs` at `P`: data-view bytes, below `tohost`. -/
structure FmtAt (Dt : Mem) (DA : List Nat) (P : Nat) (bs : List (BitVec 8)) : Prop where
  lo : 0x80000000 ≤ P
  hi : P + bs.length < 0x8001ad00
  mem : ∀ i, i < bs.length → P + i ∈ DA
  byte : ∀ i (h : i < bs.length), ldv .lbu Dt (P + i) = BitVec.zeroExtend 64 bs[i]

theorem FmtAt.tail {P : Nat} {b : BitVec 8} {bs : List (BitVec 8)} (h : FmtAt Dt DA P (b :: bs)) :
    FmtAt Dt DA (P + 1) bs where
  lo := by have := h.lo; omega
  hi := by have := h.hi; simp only [List.length_cons] at this; omega
  mem i hi := by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact h.mem (i + 1) (by simp; omega)
  byte i hi := by
    rw [Nat.add_assoc, Nat.add_comm 1 i]
    exact h.byte (i + 1) (by simp; omega)

/-- The C locale's `mbtowc` and `mb_cur_max` in newlib's data. -/
structure LocMb (M : Mem) : Prop where
  mbtowc : ldv .ld M 0x8001b880 = 0x80012268#64
  curMax : ldv .lbu M 0x8001b8f8 = 1#64

/-- The stack word `mbtowc` writes. -/
def MbReg (sp : Nat) (a : Nat) : Prop := sp + 180 ≤ a ∧ a < sp + 184

theorem LocMb.frame {M M' : Mem} {Reg : Nat → Prop} (h : LocMb M) (hF : Frame M' M Reg)
    (hR : ∀ a, 0x8001b880 ≤ a → a < 0x8001b888 → ¬ Reg a) (hR' : ¬ Reg 0x8001b8f8) : LocMb M' where
  mbtowc := by rw [hF.ldv .ld (fun j hj => hR _ (by omega) (by simp only [widthOfM] at hj; omega))]; exact h.mbtowc
  curMax := by rw [hF.ldv .lbu (fun j hj => by simp only [widthOfM] at hj; rw [show j = 0 by omega]; exact hR')]
               exact h.curMax

/-- The registers one `mbtowc` round trip keeps. -/
abbrev mbKeep : List Nat := [2, 3, 4, 5, 6, 7, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- **One `mbtowc` round trip** (`0x8000a9b8` → `0x8000a9d8`) on the format
byte `b` at `s9 = P`: `a0` is `b ≠ 0`, the byte is at `sp + 180`. -/
theorem vfp_mb (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp P : BitVec 64} {need : Nat} {b : BitVec 8}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h9 : R 9 = 0x8001b798#64) (h25 : R 25 = P)
    (hP1 : 0x80000000 ≤ P.toNat) (hP2 : P.toNat < 0x8001ad00) (hPD : P.toNat ∈ DA)
    (hfb : ldv .lbu Dt P.toNat = BitVec.zeroExtend 64 b) (hL : LocMb Mt)
    (hk : ∀ R' : Nat → BitVec 64, (b = 0#8 → R' 10 = 0#64) → (b ≠ 0#8 → R' 10 = 1#64) →
      (∀ x ∈ mbKeep, R' x = R x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9d8#64 R'
        (writeLog Mt [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 b)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b8#64 R Mt := by
  have hmx := hL.curMax; have hmb := hL.mbtowc
  have e0 : P + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = P := by
    simp [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  have hea : LdOK P.toNat 1 := by unfold LdOK tohostAddr; omega
  have hDA : ∀ a ∈ accAddrs P.toNat 1, a ∈ DA := by
    intro a ha; rw [mem_accAddrs_iff] at ha; rw [show a = P.toNat by omega]; exact hPD
  have hkeep : ∀ x ∈ mbKeep, R x = R x := fun _ _ => rfl
  nx_run hlive using [h2, h9, h25, hmx, hmb, BitVec.add_assoc] at 2147558004
  refine itD_80012274 hlive ?_ ?_ ?_
  all_goals simp (config := {failIfUnchanged := false}) only [upd_apply, Nat.reduceEqDiff, ite_true,
    ite_false, e0, hfb]
  any_goals exact hea
  any_goals exact hDA
  nx_run hlive using [h2, h9, h25, hmx, hmb, BitVec.add_assoc] at 2147558012
  refine itD_8001227c hlive ?_ ?_ ?_
  all_goals simp (config := {failIfUnchanged := false}) only [upd_apply, Nat.reduceEqDiff, ite_true,
    ite_false, e0, hfb]
  any_goals exact hea
  any_goals exact hDA
  nx_run hlive using [h2, h9, h25, hmx, hmb, BitVec.add_assoc] at 2147527128
  refine hk _ (fun e => ?_) (fun e => ?_) (by keep_chain hkeep)
  · subst e; rsimp; rw [show BitVec.zeroExtend 64 (0#8) = 0#64 by decide]; exact snez_zero
  · rsimp; exact snez_one fun h => zext8_ne e (h.trans (by decide))

/-- `mbtowc`'s store stays in `MbReg`. -/
theorem mb_frame (Mt : Mem) (sp : BitVec 64) (v : BitVec 64) (hsp : sp.toNat + 184 < 2 ^ 64) :
    Frame (writeLog Mt [((sp + 180#64).toNat, 4, v)]) Mt (MbReg sp.toNat) :=
  Frame.store Mt v fun b h1 h2 => by
    have e : (sp + 180#64).toNat = sp.toNat + 180 := by rw [BitVec.toNat_add]; simp; omega
    rw [e] at h1 h2; unfold MbReg; omega

theorem LocMb.mb {M : Mem} (h : LocMb M) {sp : BitVec 64} (v : BitVec 64) (hsp : 0x80100000 ≤ sp.toNat)
    (hsp2 : sp.toNat + 184 < 2 ^ 64) : LocMb (writeLog M [((sp + 180#64).toNat, 4, v)]) :=
  h.frame (mb_frame M sp v hsp2) (fun a h1 h2 hr => by unfold MbReg at hr; omega)
    (fun hr => by unfold MbReg at hr; omega)

/-- The registers the format scan keeps. -/
abbrev scanKeep : List Nat := [2, 3, 4, 5, 6, 7, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31]

/-- **One literal format byte** (neither NUL nor `%`): back at the loop head
with `s9` one byte on. -/
theorem vfp_lit (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp P : BitVec 64} {need : Nat} {b : BitVec 8}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h9 : R 9 = 0x8001b798#64) (h19 : R 19 = 37#64) (h25 : R 25 = P)
    (hP1 : 0x80000000 ≤ P.toNat) (hP2 : P.toNat < 0x8001ad00) (hPD : P.toNat ∈ DA)
    (hfb : ldv .lbu Dt P.toNat = BitVec.zeroExtend 64 b) (hb0 : b ≠ 0#8) (hb37 : b ≠ 37#8) (hL : LocMb Mt)
    (hk : ∀ R' : Nat → BitVec 64, R' 25 = P + 1#64 → (∀ x ∈ scanKeep, R' x = R x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b8#64 R'
        (writeLog Mt [((sp + 180#64).toNat, 4, BitVec.zeroExtend 64 b)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b8#64 R Mt := by
  refine vfp_mb hlive hs1 hs2 hs3 hs4 hal h2 h9 h25 hP1 hP2 hPD hfb hL fun R1 _ h10 hk1 => ?_
  have e10 := h10 hb0
  have k2 : R1 2 = sp := (hk1 2 (by decide)).trans h2
  have k19 : R1 19 = 37#64 := (hk1 19 (by decide)).trans h19
  have k25 : R1 25 = P := (hk1 25 (by decide)).trans h25
  have hz37 : BitVec.zeroExtend 64 b ≠ 37#64 := fun h => zext8_ne hb37 (h.trans (by decide))
  have hkeep : ∀ x ∈ scanKeep, R1 x = R x := fun x hx => hk1 x (by simp only [scanKeep, mbKeep, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
  nx_run hlive using [k2, k19, k25, e10, lw_zext8, hz37, BitVec.add_assoc] at 2147527096
  refine hk _ ?_ ?_
  · rsimp
  · keep_chain hkeep

/-- **A run of literal format bytes** `bs` (no NUL, no `%`) from the loop
head: back at the head with `s9` past them, the scan's registers kept, only
`mbtowc`'s stack word changed. -/
theorem vfp_scan (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {s sp : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) :
    ∀ (bs : List (BitVec 8)) (P : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem),
      FmtAt Dt DA P.toNat bs → (∀ b ∈ bs, b ≠ 0#8 ∧ b ≠ 37#8) →
      R 2 = sp → R 9 = 0x8001b798#64 → R 19 = 37#64 → R 25 = P → LocMb Mt →
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), R' 25 = P + BitVec.ofNat 64 bs.length →
        (∀ x ∈ scanKeep, R' x = R x) → LocMb Mt' → Frame Mt' Mt (MbReg sp.toNat) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b8#64 R' Mt') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b8#64 R Mt
  | [], P, R, Mt, _, _, _, _, _, h25, hL, hk =>
    hk R Mt (by rw [h25]; simp) (fun _ _ => rfl) hL (Frame.refl _ _)
  | b :: bs, P, R, Mt, hF, hbs, h2, h9, h19, h25, hL, hk => by
    have hP1 := hF.lo; have hP2 := hF.hi
    simp only [List.length_cons] at hP2
    have hb := hbs b (List.mem_cons_self ..)
    have hfb := hF.byte 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at hfb
    have hPD := hF.mem 0 (by simp); rw [Nat.add_zero] at hPD
    have eP : (P + 1#64).toNat = P.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    refine vfp_lit hlive hs1 hs2 hs3 hs4 hal h2 h9 h19 h25 (by omega) (by omega) hPD hfb hb.1 hb.2 hL
      fun R1 h25' hk1 => ?_
    have hsp : 0x80100000 ≤ sp.toNat := by omega
    refine vfp_scan hlive hs1 hs2 hs3 hs4 hal bs (P + 1#64) R1 _ (by rw [eP]; exact hF.tail)
      (fun c hc => hbs c (List.mem_cons_of_mem _ hc)) ((hk1 2 (by decide)).trans h2)
      ((hk1 9 (by decide)).trans h9) ((hk1 19 (by decide)).trans h19) h25'
      (hL.mb _ hsp (by omega)) fun R' Mt' e25 hk' hL' hfr => ?_
    refine hk R' Mt' ?_ (fun x hx => (hk' x hx).trans (hk1 x hx)) hL'
      ((mb_frame Mt sp _ (by omega)).trans hfr)
    rw [e25, BitVec.add_assoc, List.length_cons]
    congr 1
    apply BitVec.eq_of_toNat_eq; simp; omega

end VsaIris.Sym.Fp
