import VsaIris.Vsa.Stderr.FprintfHead
import VsaIris.Vsa.Stderr.SprintHook
import VsaIris.Vsa.Stderr.SEmpty
import VsaIris.Vsa.Fprintf.SConv
import VsaIris.Vsa.Fprintf.ScanTo
import VsaIris.Vsa.Fprintf.Strlen

/-!
# `fprintf(stderr, "%s\n", p)` from `_vfprintf_r`'s loop head (lane N3)

From `FprLoop`, `_vfprintf_r` scans to the `%` (`vfp_toTerm`) and stages the
string (`s_stage`, `strlen` through `strlen_sw`), then flushes it
(`vfp_printH` with `sprintErr_hook`). An empty string skips the flush
(`s_empty`). It then scans the `"\n"` to the NUL (`vfp_toTerm`), flushes it
at the end (`vfp_end` with `sprintErr_hook`) and returns into `fprintf`,
whose epilogue returns to the caller. Between the stages, `FprMid` carries
`stderr`'s fields, `_vfprintf_r`'s spills, `fprintf`'s saved `ra` and the
frame. The stages only write `LoopReg` (the loop's stack slots) and the
flushes (`SprintPost`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout
open VsaIris.Interp.StrLeaf VsaIris.Inst.Strlen

/-- The loop's stack slots the scans and the staging write. -/
def LoopReg (sp : Nat) (a : Nat) : Prop :=
  (sp ≤ a ∧ a < sp + 248) ∨ (sp + 352 ≤ a ∧ a < sp + 368)

/-- `stderr`'s fields and the locale as `_vfprintf_r`'s loop reads them. -/
structure ErrSt (M : Mem) : Prop where
  loc : Fp.LocMb M
  flagsU : ldv .lhu M 0x8001bbe8 = 0x201a#64
  flagsS : ldv .lh M 0x8001bbe8 = 0x201a#64
  fd : ldv .lh M 0x8001bbea = 2#64
  cursor : ldv .ld M 0x8001bbd8 = 0x8001bc4f#64
  base : ldv .ld M 0x8001bbf0 = 0x8001bc4f#64
  cookie : ldv .ld M 0x8001bc08 = 0x8001bbd8#64
  writer : ldv .ld M 0x8001bc18 = 0x8000efd4#64
  flags2 : ldv .lw M 0x8001bc88 = 0#64

/-- The state between the stages: `stderr`, `_vfprintf_r`'s spills of the
caller's registers `C`, `fprintf`'s saved `ra` (at `sp + 616`), the memory
changed only in `FprReg s`. -/
structure FprMid (M Mt : Mem) (s sp ra : BitVec 64) (C : Nat → BitVec 64) : Prop where
  err : ErrSt M
  spills : Fp.VfpSpills M sp C
  fra : ldv .ld M (sp.toNat + 616) = ra
  frame : Fp.Frame M Mt (FprReg s)

/-- The stack geometry of the body: `sp = s - 672`, in RAM, aligned. -/
structure FprSp (s sp : BitVec 64) : Prop where
  eq : sp.toNat + 672 = s.toNat
  lo : 0x80100000 ≤ s.toNat - 4096
  hi : s.toNat ≤ 0x88000000
  al : sp.toNat % 16 = 0

theorem ErrSt.frame {M M' : Mem} {Reg : Nat → Prop} (h : ErrSt M) (hF : Fp.Frame M' M Reg)
    (hR : ∀ a, Reg a → 0x8001bc90 ≤ a) : ErrSt M' := by
  have T : ∀ (k : MKind) (a : Nat), a + 8 ≤ 0x8001bc90 → ldv k M' a = ldv k M a := fun k a ha =>
    hF.ldv k fun j hj hr => by
      have := hR _ hr; have : widthOfM k ≤ 8 := by cases k <;> decide
      omega
  exact ⟨h.loc.frame hF (fun a h1 h2 hr => by have := hR a hr; omega) (fun hr => by have := hR _ hr; omega),
    (T _ _ (by omega)).trans h.flagsU, (T _ _ (by omega)).trans h.flagsS, (T _ _ (by omega)).trans h.fd,
    (T _ _ (by omega)).trans h.cursor, (T _ _ (by omega)).trans h.base, (T _ _ (by omega)).trans h.cookie,
    (T _ _ (by omega)).trans h.writer, (T _ _ (by omega)).trans h.flags2⟩

theorem VfpSpills.frame {M M' : Mem} {sp : BitVec 64} {C : Nat → BitVec 64} {Reg : Nat → Prop}
    (h : Fp.VfpSpills M sp C) (hF : Fp.Frame M' M Reg) (hsp : sp.toNat + 600 < 2 ^ 64)
    (hR : ∀ a, Reg a → ¬ (sp.toNat + 488 ≤ a ∧ a < sp.toNat + 592)) : Fp.VfpSpills M' sp C := by
  have T : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp.toNat + k) = ldv .ld M (sp.toNat + k) :=
    fun k h1 h2 => hF.ldv _ fun j hj hr => hR _ hr (by simp only [widthOfM] at hj; omega)
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    Fp.sp_lit (by omega)
  have T' : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp + BitVec.ofNat 64 k).toNat =
      ldv .ld M (sp + BitVec.ofNat 64 k).toNat := fun k h1 h2 => by rw [eo k (by omega)]; exact T k h1 h2
  exact ⟨(T 584 (by omega) (by omega)).trans h.ra, (T 576 (by omega) (by omega)).trans h.s0,
    (T' 568 (by omega) (by omega)).trans h.s1, (T' 560 (by omega) (by omega)).trans h.s2,
    (T' 552 (by omega) (by omega)).trans h.s3, (T 544 (by omega) (by omega)).trans h.s4,
    (T' 536 (by omega) (by omega)).trans h.s5, (T 528 (by omega) (by omega)).trans h.s6,
    (T' 520 (by omega) (by omega)).trans h.s7, (T' 512 (by omega) (by omega)).trans h.s8,
    (T' 504 (by omega) (by omega)).trans h.s9, (T' 496 (by omega) (by omega)).trans h.s10,
    (T' 488 (by omega) (by omega)).trans h.s11⟩

/-- **The invariant through a stage** writing only `LoopReg`. -/
theorem FprMid.step {M M' Mt : Mem} {s sp ra : BitVec 64} {C : Nat → BitVec 64} (h : FprMid M Mt s sp ra C)
    (hS : FprSp s sp) (hF : Fp.Frame M' M (LoopReg sp.toNat)) : FprMid M' Mt s sp ra C := by
  have e := hS.eq; have l := hS.lo; have hi := hS.hi
  refine ⟨h.err.frame hF fun a ha => by unfold LoopReg at ha; omega,
    VfpSpills.frame h.spills hF (by omega) fun a ha => by unfold LoopReg at ha; omega, ?_,
    Fp.Frame.trans h.frame (hF.mono fun a ha => .inl (by unfold LoopReg at ha; omega))⟩
  rw [hF.ldv _ fun j hj hr => by unfold LoopReg at hr; simp only [widthOfM] at hj; omega]
  exact h.fra

/-- **The invariant through a flush**: `SprintPost` rewrites `stderr`'s flags
with the same value. -/
theorem FprMid.sprint {M M' Mt : Mem} {s sp ra : BitVec 64} {C : Nat → BitVec 64} (h : FprMid M Mt s sp ra C)
    (hS : FprSp s sp) (hP : SprintPost M M' sp) : FprMid M' Mt s sp ra C := by
  have e := hS.eq; have l := hS.lo; have hi := hS.hi
  let Reg : Nat → Prop := fun a => (sp.toNat - 256 ≤ a ∧ a < sp.toNat) ∨
    (sp.toNat + 232 ≤ a ∧ a < sp.toNat + 248) ∨ (0x8001bbe8 ≤ a ∧ a < 0x8001bbea) ∨ Stdio.errnoFoot a
  have hF : Fp.Frame M' M Reg := fun a ha => hP.frame a (fun h' => ha (.inl h'))
    (fun h' => ha (.inr (.inl h'))) (fun h' => ha (.inr (.inr (.inl h')))) (fun h' => ha (.inr (.inr (.inr h'))))
  have hE : ∀ a, Reg a → (a < 0x8001b880 ∨ 0x8001b900 ≤ a) ∧ (a < 0x8001bbd8 ∨ 0x8001bc90 ≤ a ∨
      (0x8001bbe8 ≤ a ∧ a < 0x8001bbea)) := fun a ha => by
    simp only [Reg, Stdio.errnoFoot, Stdio.InRange] at ha; omega
  have T : ∀ (k : MKind) (a : Nat), 0x8001bbd8 ≤ a → a + 8 ≤ 0x8001bc90 →
      (a + widthOfM k ≤ 0x8001bbe8 ∨ 0x8001bbea ≤ a) →
      widthOfM k ≤ 8 → ldv k M' a = ldv k M a := fun k a h0 ha hb hw =>
    hF.ldv k fun j hj hr => by have := hE _ hr; omega
  have hR : ∀ a, Reg a → FprReg s a := fun a ha => by
    simp only [Reg] at ha
    unfold FprReg
    rcases ha with ha | ha | ha | ha
    · exact .inl ⟨by omega, by omega⟩
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inl (.inl ⟨by omega, by omega⟩))
    · exact .inr (.inr ha)
  have er := h.err
  refine ⟨⟨er.loc.frame hF (fun a h1 h2 hr => by have := hE a hr; omega)
      (fun hr => by have := hE _ hr; omega), hP.flagsU, hP.flagsS,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.fd,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.cursor,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.base,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.cookie,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.writer,
    (T _ _ (by omega) (by omega) (by simp only [widthOfM]; omega) (by decide)).trans er.flags2⟩,
    VfpSpills.frame h.spills hF (by omega) fun a ha => by
      simp only [Reg, Stdio.errnoFoot, Stdio.InRange] at ha; omega, ?_,
    Fp.Frame.trans h.frame (hF.mono hR)⟩
  rw [hF.ldv _ fun j hj hr => by
    simp only [Reg, Stdio.errnoFoot, Stdio.InRange, widthOfM] at hr hj; omega]
  exact h.fra

/-- What the body leaves: the memory changed only in `FprReg s`, `stderr`
set up. -/
structure FprPost (Mt Mf : Mem) (s : BitVec 64) : Prop where
  frame : Fp.Frame Mf Mt (FprReg s)
  err : ErrSt Mf

/-- The data view: `_impure_ptr`, then the format and the string. -/
abbrev fprDA (DA : List Nat) : List Nat := accAddrs 0x8001b970 8 ++ DA

/-- `stderr`'s 184 bytes are in the footprint. -/
theorem stderr_cover (s : BitVec 64) (need : Nat) :
    Fp.Cover (outS s need) (0x8001bbd8#64).toNat ((0x8001bbd8#64).toNat + 184) := by
  intro b h1 h2
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1 h2
  exact .inl ⟨.inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))), by unfold impureW; omega⟩

/-- **The end**: the `"\n"` pending at `0x8000aca8`, flushed (`vfp_end` with
`sprintErr_hook`), `_vfprintf_r`'s return, `fprintf`'s epilogue. -/
theorem fpr_end {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt M : Mem} {R R0 : Nat → BitVec 64}
    {s sp ra : BitVec 64} {cnt : Nat} (hS : FprSp s sp)
    (hP : Fp.VfpPend R M sp 0x8001b538#64 0x8001bbd8#64 cnt [(0x800195e2, [10#8])])
    (hI : FprMid M Mt s sp ra (fprC R0))
    (hnlA : 0x800195e2 ∈ DA) (hnl : imgM Dt 0x800195e2 = 10#8)
    (h1 : R0 1 = ra) (h2 : R0 2 = s) (hra : ra.toNat % 4 = 0)
    (hk : ∀ R' Mf, RetOK R0 R' (BitVec.ofNat 64 cnt) → FprPost Mt Mf s →
      SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q (t ++ putcs [10#8]) ra R' Mf) :
    SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q t 0x8000aca8#64 R M := by
  have e := hS.eq; have l := hS.lo; have hi := hS.hi; have hal := hS.al
  have eo : ∀ k : Nat, k ≤ 700 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    Fp.sp_lit (by omega)
  have er := hI.err
  have a0 := hP.arr 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, List.length_singleton] at a0
  rw [show (BitVec.ofNat 64 (sp.toNat + 352)).toNat = (sp + 352#64).toNat by
      rw [eo 352 (by omega)]; simp; omega,
    show (BitVec.ofNat 64 (sp.toNat + 352 + 8)).toNat = (sp + 360#64).toNat by
      rw [eo 360 (by omega)]; simp; omega] at a0
  refine Fp.vfp_end hlive (Post := fun out M' => out = [10#8] ∧ SprintPost M M' sp) (C := fprC R0)
    (fl := 0x201a#64) (need := 4096) (hs1 := by omega) (hs2 := by omega) (hs3 := hi) (hs4 := l)
    (hal := hal) (hf1 := by decide) (hf2 := by decide) (hfa := by decide) (hfC := stderr_cover s 4096)
    (hfsp := .inl (by simp only [BitVec.toNat_ofNat]; omega)) (hP := hP)
    (hE := ⟨by rw [show (0x8001bbd8#64 + 16#64).toNat = 0x8001bbe8 from rfl]; exact er.flagsS,
      by rw [show (0x8001bbd8#64 + 176#64).toNat = 0x8001bc88 from rfl]; exact er.flags2,
      by decide, by decide⟩)
    (hS := hI.spills) (hra := by rw [fprC, ite_eq_left rfl]; decide) (hpl := by simp [Fp.piecesLen])
    (hSh := fun R0' r2 r10 r11 r12 r1 k => ?_)
    (hPR := fun out M' h => h.2.endRet er.flagsS (by omega) (by omega))
    (hk0 := fun h => by simp [Fp.piecesLen] at h) (hk1 := fun out M' hpost R' q10 q2 q1 qs => ?_)
  · refine sprintErr_hook hlive (ra := 0x8000cfac#64) (p := 0x800195e2#64) (bs := [10#8])
      (by omega) (by omega) hi l hal (by decide) (by decide) r1 r2 r10 r11 r12
      (by rw [hP.resid]; rfl) hP.base a0.1 a0.2 (by decide) (by decide) (by unfold tohostAddr; decide)
      (fun i hi' => ?_) (fun i hi' => ?_) er.flagsU er.flagsS er.fd er.base er.writer er.cookie k
    · obtain rfl : i = 0 := by simp at hi'; omega
      refine ⟨.inl (by simp only [BitVec.toNat_ofNat]; omega), ?_, by decide⟩
      simp only [BitVec.toNat_ofNat, stdioFoot, InRange]; omega
    · obtain rfl : i = 0 := by simp at hi'; omega
      exact ⟨hnlA, hnl⟩
  · obtain ⟨rfl, hSP⟩ := hpost
    have hI2 := (hI.sprint hS hSP).step hS (Fp.Frame.store (a := (sp + 232#64).toNat) (w := 4) M' (0#64) fun b h1 h2 => by
      rw [eo 232 (by omega)] at h1 h2; unfold LoopReg; omega)
    have hfra : ldv .ld (writeLog M' [((sp + 232#64).toNat, 4, 0#64)]) (sp + 592#64 + 24#64).toNat = ra := by
      rw [BitVec.add_assoc, show (592#64 + 24#64 : BitVec 64) = BitVec.ofNat 64 616 from rfl, eo 616 (by omega)]
      exact hI2.fra
    have hfraM : ldv .ld M' (sp + 616#64).toNat = ra := by
      rw [eo 616 (by omega)]; exact (hI.sprint hS hSP).fra
    have hsp' : sp + 672#64 = s := by
      apply BitVec.eq_of_toNat_eq; rw [eo 672 (by omega)]; omega
    rw [show fprC R0 1 = 0x80006204#64 from ite_eq_left rfl]
    nx_run hlive using [q2, hfra, hfraM, hsp', BitVec.add_assoc]
    refine hk _ _ (retOK_of ?_ ?_) ⟨hI2.frame, hI2.err⟩
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, q10]
    · intro x hx h32 h10 hc
      simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;>
        first | exact h1.symm | exact h2.symm | exact absurd rfl h32 | exact absurd rfl h10 |
          (simp at hc; done) | exact (qs _ (by decide)).trans (by simp [fprC])

theorem scanReg_loopReg {sp a : Nat} (h : Fp.ScanReg sp a) : LoopReg sp a := by
  unfold Fp.ScanReg Fp.MbReg at h; unfold LoopReg; omega

/-- **The `"\n"`**: from the loop head at `fmt + 2`, the scan to the NUL
(`vfp_toTerm`), then `fpr_end`. -/
theorem fpr_nl {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt M : Mem} {R R0 : Nat → BitVec 64}
    {s sp ra : BitVec 64} {cnt : Nat} (hS : FprSp s sp)
    (hL : Fp.VfpLoop R M sp 0x8001b538#64 0x8001bbd8#64 0x800195e2#64 cnt)
    (hI : FprMid M Mt s sp ra (fprC R0))
    (hF : Fp.FmtAt Dt (fprDA DA) 0x800195e2 [10#8, 0#8])
    (hnlA : 0x800195e2 ∈ DA) (hnl : imgM Dt 0x800195e2 = 10#8) (hcnt : cnt + 1 < 2 ^ 31)
    (h1 : R0 1 = ra) (h2 : R0 2 = s) (hra : ra.toNat % 4 = 0)
    (hk : ∀ R' Mf, RetOK R0 R' (BitVec.ofNat 64 (cnt + 1)) → FprPost Mt Mf s →
      SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q (t ++ putcs [10#8]) ra R' Mf) :
    SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q t 0x8000a9b0#64 R M := by
  have e := hS.eq; have l := hS.lo; have hi := hS.hi; have hal := hS.al
  refine Fp.vfp_toTerm hlive (need := 4096) (c := 0#8) (bs := [10#8]) (.inl rfl) (by omega) (by omega) hi l hal
    hL hI.err.loc hF (by decide) hcnt fun R' M' hSP _ => ?_
  have hp := hSP.pend
  simp only [Fp.litIov, List.length_singleton] at hp
  rw [if_neg (by decide)] at hp
  exact fpr_end hlive hS hp (hI.step hS (hSP.frame.mono fun a h => scanReg_loopReg h)) hnlA hnl h1 h2 hra hk

theorem FprSp.off {s sp : BitVec 64} {a : Nat} (hS : FprSp s sp)
    (h : a < s.toNat - 4096 ∨ s.toNat ≤ a) : a < sp.toNat - 256 ∨ sp.toNat ≤ a := by
  have := hS.eq
  rcases h with h | h
  · have := Nat.add_lt_of_lt_sub h
    exact .inl (Nat.lt_sub_of_add_lt (by omega))
  · exact .inr (by omega)

theorem sReg_loopReg {sp a : Nat} (h : Fp.SReg sp 0 a) : LoopReg sp a := by
  unfold Fp.SReg at h; unfold LoopReg; omega

/-- The string's bytes, read from the data view. -/
def strBs (Dt : Mem) (p n : Nat) : List (BitVec 8) := (List.range n).map fun i => imgM Dt (p + i)

theorem strBs_length (Dt : Mem) (p n : Nat) : (strBs Dt p n).length = n := by simp [strBs]

/-- The string `p` as `fprintf`'s run reads it: `n` bytes and a NUL in the
data view (`DA`), in RAM, off `tohost`, the call's stack, newlib's data and
`errno`. -/
structure FprStr (live : Nat → Prop) (Dt : Mem) (DA : List Nat) (s p : BitVec 64) (n : Nat) : Prop where
  ctx : LCtx live p 0x8000cfcc#64 n (imgM Dt)
  mem : ∀ i, i ≤ n → p.toNat + i ∈ DA
  len : n < 2 ^ 30
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + n ≤ 0x100000000
  tohost : p.toNat + n ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat
  off : ∀ i, i < n → (p.toNat + i < s.toNat - 4096 ∨ s.toNat ≤ p.toNat + i) ∧
    ¬ stdioFoot (p.toNat + i) ∧ (p.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ p.toNat + i)

/-- `strlen`'s code and the string are in the run's view. -/
theorem FprStr.sub {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {s p : BitVec 64} {n : Nat}
    (h : FprStr live Dt DA s p n) :
    ∀ q ∈ strCode ++ strText p.toNat n (imgM Dt), q ∈ stdioText ++ dataOf Dt (fprDA DA) := by
  intro q hq
  rcases List.mem_append.1 hq with h' | h'
  · exact List.mem_append_left _ (strCode_stdio q h')
  · refine List.mem_append_right _ ?_
    unfold strText at h'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h'
    exact List.mem_map_of_mem (f := fun a => (a, imgM Dt a))
      (List.mem_append_right _ (h.mem k (by have := List.mem_range.1 hk; omega)))

/-- **`%s`**: from the loop head at `fmt`, the scan to the `%`
(`vfp_toTerm`), the string staged (`s_stage`) and flushed (`vfp_printH`
with `sprintErr_hook`), or nothing for an empty string (`s_empty`), then
`fpr_nl`. -/
theorem fpr_s {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt M : Mem} {R R0 : Nat → BitVec 64}
    {s sp ra p : BitVec 64} {n : Nat} (hS : FprSp s sp)
    (hL : Fp.VfpLoop R M sp 0x8001b538#64 0x8001bbd8#64 0x800195e0#64 0)
    (hI : FprMid M Mt s sp ra (fprC R0))
    (hap : ldv .ld M (sp + 24#64).toNat = sp + 624#64) (harg : ldv .ld M (sp.toNat + 624) = p)
    (hstr : FprStr live Dt DA s p n)
    (hF0 : Fp.FmtAt Dt (fprDA DA) 0x800195e0 [37#8]) (hSF : Fp.SFmt Dt (fprDA DA) 0x800195e0)
    (hF : Fp.FmtAt Dt (fprDA DA) 0x800195e2 [10#8, 0#8])
    (hnlA : 0x800195e2 ∈ DA) (hnl : imgM Dt 0x800195e2 = 10#8)
    (h1 : R0 1 = ra) (h2 : R0 2 = s) (hra : ra.toNat % 4 = 0)
    (hk : ∀ R' Mf, RetOK R0 R' (BitVec.ofNat 64 (n + 1)) → FprPost Mt Mf s →
      SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q
        (t ++ putcs (strBs Dt p.toNat n) ++ putcs [10#8]) ra R' Mf) :
    SWPO live (stdioText ++ dataOf Dt (fprDA DA)) iRegs (outS s 4096) Q t 0x8000a9b0#64 R M := by
  have e := hS.eq; have l := hS.lo; have hi := hS.hi; have hal := hS.al
  have eo : ∀ k : Nat, k ≤ 700 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    Fp.sp_lit (by omega)
  have hp0 : p ≠ 0#64 := fun h => by have := hstr.lo; rw [h] at this; simp at this
  refine Fp.vfp_toTerm hlive (need := 4096) (c := 37#8) (bs := []) (.inr rfl) (by omega) (by omega) hi l hal
    hL hI.err.loc hF0 (by simp) (by simp) fun R1 M1 hSP _ => ?_
  have hP1 := hSP.pend
  simp only [Fp.litIov, List.length_nil, Nat.add_zero, if_pos] at hP1
  have h25 : R1 25 = 0x800195e0#64 := by rw [hSP.s9]; rfl
  have hI1 := hI.step hS (hSP.frame.mono fun a h => scanReg_loopReg h)
  have T1 : ∀ k, k ≤ 700 → (k + 8 ≤ 16 ∨ 24 ≤ k) → k + 8 ≤ 180 ∨ 184 ≤ k → k + 8 ≤ 232 ∨ 248 ≤ k →
      k + 8 ≤ 352 ∨ 368 ≤ k → ldv .ld M1 (sp.toNat + k) = ldv .ld M (sp.toNat + k) := fun k hk h16 hm hu hi =>
    hSP.frame.ldv _ fun j hj hr => by
      unfold Fp.ScanReg Fp.MbReg at hr; simp only [widthOfM] at hj; omega
  have hap1 : ldv .ld M1 (sp + 24#64).toNat = sp + 624#64 := by
    rw [eo 24 (by omega), T1 24 (by omega) (by omega) (by omega) (by omega) (by omega), ← eo 24 (by omega)]
    exact hap
  have harg1 : ldv .ld M1 (sp + 624#64).toNat = p := by
    rw [eo 624 (by omega), T1 624 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact harg
  have hsp624 : (sp + 624#64).toNat = sp.toNat + 624 := eo 624 (by omega)
  rw [show Fp.termPC 37#8 = 0x8000a9fc#64 from rfl]
  have e2 : (0x800195e0#64 + 2#64 : BitVec 64) = 0x800195e2#64 := rfl
  by_cases hn0 : n = 0
  · subst hn0
    refine Fp.s_empty hlive (need := 4096) (X := 0x800195e0#64) (ap := sp + 624#64) (str := p)
      (by omega) (by omega) hi l hal (by decide) (by decide) (by rw [hsp624]; omega) (by rw [hsp624]; omega)
      (by rw [hsp624]; omega) (by decide) hP1 h25 hSF hap1 harg1 hp0
      (fun R0' Mt0 r1 r10 k => Fp.strlen_sw hstr.ctx hstr.sub r1 r10 k) fun R2 M2 hL2 _ _ hF2 => ?_
    rw [e2] at hL2
    refine fpr_nl hlive hS hL2 (hI1.step hS (hF2.mono fun a h => sReg_loopReg h)) hF hnlA hnl (by omega)
      h1 h2 hra fun R' Mf r q => ?_
    have := hk R' Mf r q
    simp only [strBs, List.range_zero, List.map_nil] at this
    rwa [show putcs [] = "" from rfl, String.append_empty] at this
  have hbl := strBs_length Dt p.toNat n
  have hn := hstr.len
  refine Fp.s_stage hlive (need := 4096) (X := 0x800195e0#64) (ap := sp + 624#64) (str := p) (iovs := [])
    (bs := strBs Dt p.toNat n) (cnt := 0)
    (by omega) (by omega) hi l hal (by decide) (by decide) (by rw [hsp624]; omega) (by rw [hsp624]; omega)
    (by rw [hsp624]; omega) (by simp) (by simp [Fp.piecesLen]; omega) (by simp [Fp.piecesLen]; omega)
    (by omega) hP1 h25 hSF hap1 harg1 hp0
    (fun R0' Mt0 r1 r10 k => Fp.strlen_sw hstr.ctx hstr.sub r1 r10 (by rw [hbl] at k; exact k))
    fun R2 M2 hP2 h24 hz32 _ hF2 => ?_
  have hI2 := hI1.step hS (hF2.mono fun a h => sReg_loopReg h)
  have er := hI2.err
  have a0 := hP2.arr 0 (by simp)
  simp only [List.nil_append, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at a0
  rw [show (BitVec.ofNat 64 (sp.toNat + 352)).toNat = (sp + 352#64).toNat by
      rw [eo 352 (by omega)]; simp; omega,
    show (BitVec.ofNat 64 (sp.toNat + 352 + 8)).toNat = (sp + 360#64).toNat by
      rw [eo 360 (by omega)]; simp; omega, BitVec.ofNat_toNat, BitVec.setWidth_eq] at a0
  refine Fp.vfp_printH hlive (Post := fun out M' => out = strBs Dt p.toNat n ∧ SprintPost M2 M' sp)
    (need := 4096) (by omega) (by omega) hi l hal hP2 h24 hz32
    (fun R0' r2 r10 r11 r12 r1 k => ?_) (fun out M' h => h.2.printRet (by omega) (by omega))
    fun R3 M3 out hpost hL3 => ?_
  · refine sprintErr_hook hlive (ra := 0x8000b8d4#64) (p := p) (bs := strBs Dt p.toNat n)
      (by omega) (by omega) hi l hal (by omega) (by decide) r1 r2 r10 r11 r12
      (by rw [hP2.resid]; simp [Fp.piecesLen]) hP2.base a0.1 a0.2 hstr.lo (by rw [hbl]; exact hstr.hi)
      (by rw [hbl]; exact hstr.tohost) (fun i hi' => ?_) (fun i hi' => ?_)
      er.flagsU er.flagsS er.fd er.base er.writer er.cookie k
    · rw [hbl] at hi'
      obtain ⟨q1, q2, q3⟩ := hstr.off i hi'
      exact ⟨FprSp.off hS q1, q2, q3⟩
    · rw [hbl] at hi'
      exact ⟨hstr.mem i (by omega), by simp [strBs]⟩
  · obtain ⟨rfl, hSP3⟩ := hpost
    have hI3 := (hI2.sprint hS hSP3).step hS (Fp.Frame.store (a := (sp + 232#64).toNat) (w := 4) M3 (0#64)
      fun b h1 h2 => by rw [eo 232 (by omega)] at h1 h2; unfold LoopReg; omega)
    rw [e2, Nat.zero_add, hbl] at hL3
    exact fpr_nl hlive hS hL3 hI3 hF hnlA hnl (by omega) h1 h2 hra hk

end VsaIris.Sym
