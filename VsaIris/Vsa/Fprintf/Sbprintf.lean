import VsaIris.Vsa.Fprintf.InnerS

/-!
# `__sbprintf(reent, stdout, fmt, ap)` (lane N5)

`__sbprintf` (`0x8000dda8`) builds a fully buffered `FILE` at `sp + 24`
(flags `stdout`'s minus `__SNBF`: `0x2008`, a 1024-byte buffer at
`sp + 208`, `stdout`'s descriptor, cookie and `_write`), runs `_vfprintf_r` on
it (the hook `hV`: `vfpInnerLld` or `vfpInnerS`), flushes it (`_fflush_r`:
`fflushF_run`, or `fflushF_run0` with nothing left), and returns the count.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

/-- `stdout`'s fields `__sbprintf` copies, and the boundary data the flush
reads, with `_flags = fl`: `0x000a` at `interp_run`'s entry, `0x200a` once
the `ORIENT` block has run (`consoleFlagsV`). -/
structure StdoutSbAt (fl : BitVec 64) (M : Mem) : Prop where
  flagsU : ldv .lhu M 0x8001bb30 = fl
  flags : ldv .lh M 0x8001bb30 = fl
  fdU : ldv .lhu M 0x8001bb32 = 1#64
  fd : ldv .lh M 0x8001bb32 = 1#64
  flags2 : ldv .lw M 0x8001bbd0 = 0#64
  cookie : ldv .ld M 0x8001bb50 = 0x8001bb20#64
  writer : ldv .ld M 0x8001bb60 = 0x8000efd4#64
  sinit : ldv .ld M 0x8001b580 = 0x80005d2c#64

/-- `stdout` oriented (`_flags = 0x200a`): what `__sbprintf` reads. -/
abbrev StdoutSb (M : Mem) : Prop := StdoutSbAt 0x200a#64 M

/-- The fields survive a change off `0x8001b580..0x8001bbd4`. -/
theorem StdoutSbAt.frame {fl : BitVec 64} {M M' : Mem} {Reg : Nat → Prop} (h : StdoutSbAt fl M)
    (hF : Frame M' M Reg) (hR : ∀ a, 0x8001b580 ≤ a → a < 0x8001bbd4 → ¬ Reg a) : StdoutSbAt fl M' := by
  have l : ∀ (kd : MKind) (a : Nat), 0x8001b580 ≤ a → a + widthOfM kd ≤ 0x8001bbd4 →
      ldv kd M' a = ldv kd M a := fun kd a h1 h2 => hF.ldv kd fun j hj => hR _ (by omega) (by omega)
  exact ⟨(l _ _ (by decide) (by decide)).trans h.flagsU, (l _ _ (by decide) (by decide)).trans h.flags,
    (l _ _ (by decide) (by decide)).trans h.fdU, (l _ _ (by decide) (by decide)).trans h.fd,
    (l _ _ (by decide) (by decide)).trans h.flags2, (l _ _ (by decide) (by decide)).trans h.cookie,
    (l _ _ (by decide) (by decide)).trans h.writer, (l _ _ (by decide) (by decide)).trans h.sinit⟩

/-- The bytes `__sbprintf` changes: its frame and the callee frames below,
`stdout`'s flags, `errno`. -/
def SbpReg (sp : Nat) (a : Nat) : Prop :=
  (sp - 1024 ≤ a ∧ a < sp + 1264) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

theorem fflushF0Mt_frame (M : Mem) {sp f B ra s0 s1 s2 s3 : BitVec 64} (hsp : 0x80100000 ≤ sp.toNat)
    (hsp2 : sp.toNat + 2048 < 2 ^ 64) (hf : sp.toNat ≤ f.toNat) (hf2 : f.toNat + 1208 < 2 ^ 64) :
    Frame (fflushF0Mt M sp f B ra s0 s1 s2 s3) M (SfvReg f.toNat sp.toNat) := by
  unfold fflushF0Mt sflushF0Mt
  frame_chain

theorem sbSfv_reg {sp : BitVec 64} (hsp : sp.toNat + 2048 < 2 ^ 64) :
    ∀ a, SfvReg (sp + 24#64).toNat sp.toNat a → (sp.toNat - 256 ≤ a ∧ a < sp.toNat + 1232) ∨
      (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) := fun a h => by
  unfold SfvReg at h; rw [sp_lit (by omega)] at h
  rcases h with h | h | h | h | h | h
  all_goals first | exact .inl (by omega) | exact .inr (.inl h) | exact .inr (.inr h)

theorem sbInner_reg {sp : BitVec 64} (hsp : sp.toNat + 2048 < 2 ^ 64) :
    ∀ a, InnerReg (sp + 24#64).toNat (sp.toNat - 592) a → (sp.toNat - 976 ≤ a ∧ a < sp.toNat + 1232) ∨
      (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) := fun a h => by
  unfold InnerReg at h; rw [sp_lit (by omega)] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h
  · left; rw [Nat.sub_sub] at h1; exact ⟨h1, by omega⟩
  · left; constructor <;> omega
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- **`__sbprintf` after the flush** (`0x8000de80`): no `__SERR` on the stack
`FILE`, the (stub) lock closed, the frame restored, the count returned. -/
theorem sbprintf_tail {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {M : Mem} {R C : Nat → BitVec 64}
    {s sp : BitVec 64} {need N : Nat}
    (hs1 : s.toNat - need + 2048 ≤ sp.toNat) (hs2 : sp.toNat + 1264 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : (C 1).toNat % 4 = 0)
    (h2 : R 2 = sp) (h10 : R 10 = 0#64) (h9 : R 9 = BitVec.ofNat 64 N)
    (hfl : ldv .lhu M (sp + 40#64).toNat = 0x2008#64)
    (hs_ra : ldv .ld M (sp + 1256#64).toNat = C 1) (hs_s0 : ldv .ld M (sp + 1248#64).toNat = C 8)
    (hs_s1 : ldv .ld M (sp + 1240#64).toNat = C 9) (hs_s2 : ldv .ld M (sp + 1232#64).toNat = C 18)
    (hk : ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 N → R' 2 = sp + 1264#64 → R' 1 = C 1 →
      R' 8 = C 8 → R' 9 = C 9 → R' 18 = C 18 → (∀ x ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27], R' x = R x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (C 1) R' M) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000de80#64 R M := by
  nx_run hlive using [h2, h10, h9, hfl, hs_ra, hs_s0, hs_s1, hs_s2, BitVec.add_assoc]
  refine hk _ (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp

set_option hygiene false in
/-- The end of `__sbprintf` after the flush (both flushes): the tail and the post. -/
local macro "sb_finish" : tactic => `(tactic| (
      have hSf := sbSfv_reg (sp := sp) (by omega)
      have hIR := sbInner_reg (sp := sp) (by omega)
      have hsp : ∀ k, 1232 ≤ k → k + 8 ≤ 1264 → ∀ M0 : Mem, Frame M0 M1 (SfvReg (sp + 24#64).toNat sp.toNat) →
          ldv .ld M0 (sp + BitVec.ofNat 64 k).toNat = ldv .ld M1 (sp + BitVec.ofNat 64 k).toNat := fun k h1 h2 M0 hF =>
        hF.ldv .ld fun j hj h => by simp only [widthOfM] at hj; rw [eo k (by omega)] at h; have := hSf _ h; omega
      have hsp1 : ∀ k, 1232 ≤ k → k + 8 ≤ 1264 → ldv .ld M1 (sp + BitVec.ofNat 64 k).toNat = _ := fun k h1 h2 =>
        hfr1.ldv .ld fun j hj h => by simp only [widthOfM] at hj; rw [eo k (by omega)] at h; have := hIR _ h; omega
      have kR : ∀ x, x ∈ iRegs → x ≠ 32 → x ≠ 10 → x ∉ callClob → R2 x = _ := fun x a b c d => hret.keep x a b c d
      refine sbprintf_tail hlive hs1 hs2 hs3 hs4 hal hra (C := R) (N := N) ?_ hret.a0 ?_ ?_ ?_ ?_ ?_ ?_
        fun R3 e10' e2' e1' e8 e9 e18 ek => ?_
      · rw [kR 2 (by decide) (by decide) (by decide) (by decide)]; rsimp; exact e2
      · rw [kR 9 (by decide) (by decide) (by decide) (by decide)]; rsimp
      · have hnr : ∀ j, j < widthOfM .lhu → ¬ SfvReg (sp + 24#64).toNat sp.toNat ((sp + 40#64).toNat + j) := by
          intro j hj h
          simp only [widthOfM] at hj
          rw [eo 40 (by omega)] at h
          unfold SfvReg at h
          rw [ef24] at h
          omega
        rw [hFr.ldv .lhu hnr]
        have := hSb1.flagsU; simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; exact this
      all_goals try (rw [hsp _ (by omega) (by omega) _ hFr, hsp1 _ (by omega) (by omega)]; nx_mem)
      refine hk R3 _ e10' (e2'.trans h2.symm) e1' (fun x hx => ?_) ?_ ?hsfl
      · simp only [vfpSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact e8
        · exact e9
        · exact e18
        all_goals (rw [ek _ (by decide), kR _ (by decide) (by decide) (by decide) (by decide)]; rsimp
                   rw [ekeep _ (by decide)]; rsimp; assumption)
      · refine ((Frame.trans ?_ (hfr1.mono fun a h => ?_)).trans (hFr.mono fun a h => ?_))
        · repeat (refine Frame.snoc ?_ ?_)
          all_goals first | exact Frame.refl _ _ |
            (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
             unfold SbpReg; omega)
        · unfold SbpReg
          rcases hIR a h with ⟨h1, h2⟩ | h | h
          · exact .inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h1, by omega⟩
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · unfold SbpReg
          rcases hSf a h with ⟨h1, h2⟩ | h | h
          · exact .inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h1, by omega⟩
          · exact .inr (.inl h)
          · exact .inr (.inr h)))

#ix_piece sbprintf_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp P ap : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hs1 : s.toNat - need + 2048 ≤ sp.toNat) (hs2 : sp.toNat + 1264 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (hN : N < 2 ^ 31) (hbl : bytes.length < 2 ^ 31)
    (h2 : R 2 = sp + 1264#64) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = P)
    (h13 : R 13 = ap) (hSo : StdoutSb Mt)
    (hV : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = sp → R0 10 = 0x8001b538#64 → R0 11 = sp + 24#64 →
      R0 12 = P → R0 13 = ap → R0 1 = 0x8000de30#64 → SbFile Mt0 (sp + 24#64) [] →
      Frame Mt0 Mt (fun a => sp.toNat ≤ a ∧ a < sp.toNat + 1264) →
      (∀ R' M' out pend', bytes = out ++ pend' → R' 2 = sp → R' 1 = 0x8000de30#64 → R' 10 = BitVec.ofNat 64 N →
        (∀ x ∈ vfpSaved, R' x = R0 x) → SbFile M' (sp + 24#64) pend' →
        Frame M' Mt0 (InnerReg (sp + 24#64).toNat (sp.toNat - 592)) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000de30#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R0 Mt0)
    (hk : ∀ R' M', R' 10 = BitVec.ofNat 64 N → R' 2 = R 2 → R' 1 = R 1 → (∀ x ∈ vfpSaved, R' x = R x) →
      Frame M' Mt (SbpReg sp.toNat) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000dda8#64 R Mt by
  have e : sp + 1264#64 + 18446744073709550352#64 = sp := by rw [BitVec.add_assoc]; simp
  have hfl := hSo.flagsU; have hf2 := hSo.flags2; have hfd := hSo.fdU; have hck := hSo.cookie
  have hwr := hSo.writer
  nf_go 3 [14] hlive using [h2, h10, h11, h12, h13, hfl, hf2, hfd, hck, hwr, e, BitVec.add_assoc] at 2147526788

#ix_piece sbprintf_2 from sbprintf_1 by
  have eo : ∀ k : Nat, k ≤ 1300 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have ef : ∀ k : Nat, k ≤ 1300 → sp + 24#64 + BitVec.ofNat 64 k = sp + BitVec.ofNat 64 (24 + k) := fun k hk => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]
  refine hV _ _ (by rsimp; exact f2) (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp)
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, ?_, ?_, fun i h => absurd h (by simp)⟩ ?_
    fun R1 M1 out pend' hb e2 e1 e10 ekeep hSb1 hfr1 => ?_
  · simp only [ef 16 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 16 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 24 (by omega), ef 184 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 32 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 48 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 64 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [ef 176 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · nx_mem; exact hSo.flags
  · nx_mem; exact hSo.fd
  · nx_mem; exact hSo.sinit
  · simp only [List.length_nil, Nat.add_zero, ef 184 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · simp only [List.length_nil, Nat.sub_zero, ef 12 (by omega), BitVec.reduceAdd]; nx_mem; try decide
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ |
      (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
       omega)

#ix_piece sbprintf_3 from sbprintf_2 by
  have k18 : R1 18 = 0x8001b538#64 := by rw [ekeep 18 (by decide)]; rsimp; exact f18
  have hNt : ((0#64).toInt ≤ (BitVec.ofNat 64 N).toInt) = True :=
    eq_true (by rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)]; omega)
  nx_run hlive using [e2, e1, e10, k18, hNt, BitVec.add_assoc] at 2147544524
  have ef24 : (sp + 24#64).toNat = sp.toNat + 24 := eo 24 (by omega)
  have hB0 : sp + 24#64 + 184#64 ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h; rw [toNat_add_lit (by rw [ef24]; omega), ef24] at this; simp at this
  have C : FfCtx s sp (sp + 24#64) (sp + 24#64 + 184#64) 0x8000de80#64 need
      (upd (upd (upd (upd R1 9 (BitVec.ofNat 64 N)) 11 (sp + 24#64)) 10 2147595576#64) 1 2147540608#64) M1 :=
    ⟨by omega, by omega, hs3, hs4, hal, by decide, by rw [ef24]; omega, by rw [ef24]; omega, by rw [ef24]; omega,
      by rsimp, by rsimp, by rsimp, by rsimp; exact e2, hSb1.sinit, hSb1.flags, hSb1.flagsU, hSb1.flags2,
      hSb1.base, hB0, hSb1.size, hSb1.writer, hSb1.cookie, hSb1.sfl, hSb1.sfd⟩
  by_cases hpe : pend' = []

#ix_piece sbprintf_4a from sbprintf_3 at 1 by
  subst hpe
  have hP : ldv .ld M1 (sp + 24#64).toNat = sp + 24#64 + 184#64 := by have := hSb1.p; simpa using this
  refine fflushF_run0 hlive C hP fun R2 hret => ?_
  rsimp
  have hFr := fflushF0Mt_frame M1 (sp := sp) (f := sp + 24#64) (B := sp + 24#64 + 184#64) (ra := 0x8000de80#64)
    (by omega) (by omega) (by rw [ef24]; omega) (by rw [ef24]; omega)
    (s0 := R1 8) (s1 := BitVec.ofNat 64 N) (s2 := R1 18) (s3 := R1 19)
  rw [List.append_nil] at hb
  subst hb
  sb_finish
  case hsfl => nx_mem; exact hSb1.sfl

#ix_piece sbprintf_4b from sbprintf_3 at 2 by
  have hlen := hSb1.len
  have hn : 0 < pend'.length := List.length_pos_iff.2 hpe
  have eB : (sp + 24#64 + 184#64).toNat = sp.toNat + 208 := by
    rw [toNat_add_lit (by rw [ef24]; omega), ef24]
  have hP : ldv .ld M1 (sp + 24#64).toNat = sp + 24#64 + 184#64 + BitVec.ofNat 64 pend'.length := by
    rw [hSb1.p, ← ofNat_add_ofNat, ← BitVec.add_assoc]
  refine fflushF_run hlive C hn (by omega) (by rw [eB]; omega) (by rw [eB]; omega) hP (.inr (by rw [eB]; unfold tohostAddr; omega))
    (fun i hi => by rw [eB, ef24]; omega) (fun i hi => .inl ⟨by rw [eB]; unfold outS; omega, by
      have := hSb1.buf i hi; rw [eB]; rw [show (sp + 24#64 + 184#64).toNat = sp.toNat + 208 from eB] at this
      exact this⟩) fun R2 hret => ?_
  rsimp
  have hFl := SbFile.flushed (fp := sp) (ra := 0x8000de80#64) (s0 := R1 8) (s1 := BitVec.ofNat 64 N)
    (s2 := R1 18) (s3 := R1 19) hSb1.toSbFixed (Frame.refl M1 _) (by rw [ef24]; omega) (by rw [ef24]; omega)
    (by rw [ef24]; omega) (by omega)
  have hFr := hFl.2
  rw [String.append_assoc, ← putcs_append, ← hb]
  sb_finish
  case hsfl => exact hFl.1.sfl

/-! **`sbprintf_run`**: `__sbprintf(reent, stdout, fmt, ap)` with the inner run a hook. -/
#ix_tree sbprintf_run := sbprintf_1 [sbprintf_2 [sbprintf_3 [sbprintf_4a, sbprintf_4b]]]

end VsaIris.Sym.Fp
