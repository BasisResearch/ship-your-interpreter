import VsaIris.Vsa.Fprintf.LldEmit

/-!
# `%lld` from `%` to the loop head (lane N5)

`vfp_lld` composes the parse (`lld_head`), the digits (`lld_mag`), the
staging (`lld_stage`) and the print (`vfp_print`): from the `%` of `"%lld"`
to the loop head past the `d`, the argument's decimal rendering (`lldBytes`:
`'-'` for a negative argument, then the digits of its magnitude) handed to
the stack `FILE`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- What `%lld` prints for `v`. -/
def lldBytes (v : BitVec 64) : List (BitVec 8) :=
  (if isNeg v then [45#8] else []) ++ digBytes (lldMag v).toNat

theorem lldSign_eq_zero {v : BitVec 64} : lldSign v = 0#8 ↔ ¬ isNeg v := by
  unfold lldSign; split <;> simp_all

theorem piecesBytes_lldIovs (sp : Nat) (v : BitVec 64) :
    piecesBytes (lldIovs sp (lldSign v) (digBytes (lldMag v).toNat)) = lldBytes v := by
  unfold lldIovs lldBytes piecesBytes
  by_cases h : isNeg v
  · have : lldSign v ≠ 0#8 := fun e => (lldSign_eq_zero.1 e) h
    simp [this, h, lldSign]
  · have : lldSign v = 0#8 := lldSign_eq_zero.2 h
    simp [this, h]

/-- **`VfpPend` across a register and memory frame** that spares the loop
registers, reent/`FILE`/count, the `uio` and the pending iovs. -/
theorem VfpPend.transport {R R' : Nat → BitVec 64} {Mt Mt' : Mem} {sp reent f : BitVec 64} {cnt : Nat}
    {iovs : List (Nat × List (BitVec 8))} {Reg : Nat → Prop} (h : VfpPend R Mt sp reent f cnt iovs)
    (hsp : sp.toNat + 600 < 2 ^ 64) (hn : iovs.length ≤ 8) (hR : ∀ x ∈ [2, 9, 18, 19, 21, 23], R' x = R x) (hM : Frame Mt' Mt Reg)
    (hReg : ∀ a, Reg a → (a < sp.toNat ∨ sp.toNat + 24 ≤ a) ∧ (a < sp.toNat + 224 ∨ sp.toNat + 248 ≤ a) ∧
      (a < sp.toNat + 352 ∨ sp.toNat + 352 + 16 * iovs.length ≤ a)) :
    VfpPend R' Mt' sp reent f cnt iovs := by
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  have ld : ∀ (kd : MKind) (a : Nat), ((a + 8 ≤ sp.toNat + 24 ∧ sp.toNat ≤ a) ∨
      (sp.toNat + 224 ≤ a ∧ a + 8 ≤ sp.toNat + 248) ∨ (sp.toNat + 352 ≤ a ∧ a + 8 ≤ sp.toNat + 352 + 16 * iovs.length)) →
      widthOfM kd ≤ 8 → ldv kd Mt' a = ldv kd Mt a := fun kd a ha hw =>
    hM.ldv kd fun j hj hr => by have := hReg _ hr; omega
  refine ⟨(hR 2 (by decide)).trans h.spR, (hR 9 (by decide)).trans h.s1, (hR 18 (by decide)).trans h.s2,
    (hR 19 (by decide)).trans h.s3, (hR 21 (by decide)).trans h.s5, (hR 23 (by decide)).trans h.s7, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [ld .ld _ (.inl (by omega)) (by decide)]; exact h.reent
  · rw [ld .ld _ (.inl (by rw [eo 8 (by omega)]; omega)) (by decide)]; exact h.file
  · rw [ld .ld _ (.inl (by rw [eo 16 (by omega)]; omega)) (by decide)]; exact h.count
  · rw [ld .ld _ (.inr (.inl (by rw [eo 224 (by omega)]; omega))) (by decide)]; exact h.base
  · rw [ld .lw _ (.inr (.inl (by rw [eo 232 (by omega)]; omega))) (by decide)]; exact h.iovcnt
  · rw [ld .ld _ (.inr (.inl (by rw [eo 240 (by omega)]; omega))) (by decide)]; exact h.resid
  · intro j hj
    have hj' : j + 1 ≤ iovs.length := hj
    have e1 : (BitVec.ofNat 64 (sp.toNat + 352 + 16 * j)).toNat = sp.toNat + 352 + 16 * j := by
      rw [BitVec.toNat_ofNat]; omega
    have e2 : (BitVec.ofNat 64 (sp.toNat + 352 + 16 * j + 8)).toNat = sp.toNat + 352 + 16 * j + 8 := by
      rw [BitVec.toNat_ofNat]; omega
    obtain ⟨a1, a2⟩ := h.arr j hj
    refine ⟨?_, ?_⟩
    · rw [e1, ld .ld _ (.inr (.inr (by omega))) (by decide), ← e1]; exact a1
    · rw [e2, ld .ld _ (.inr (.inr (by omega))) (by decide), ← e2]; exact a2

/-- The bytes `vfp_lld` changes. -/
def LldReg (f sp : Nat) (a : Nat) : Prop :=
  (sp + 24 ≤ a ∧ a < sp + 32) ∨ a = sp + 167 ∨ MagReg sp a ∨ StageReg sp a ∨ PrintReg f sp a

theorem lldMt_frame (Mt : Mem) {sp : BitVec 64} (ap v : BitVec 64) (hsp : sp.toNat + 200 < 2 ^ 64) :
    Frame (lldMt Mt sp ap v) Mt (fun a => (sp.toNat + 24 ≤ a ∧ a < sp.toNat + 32) ∨ a = sp.toNat + 167) := by
  have e24 : (sp + 24#64).toNat = sp.toNat + 24 := sp_lit (by omega)
  have e167 : (sp + 167#64).toNat = sp.toNat + 167 := sp_lit (by omega)
  unfold lldMt
  split
  · refine (((Frame.refl _ _).snoc ?_).snoc ?_).snoc ?_ <;> intro b h1 h2 <;>
      simp only [e24, e167] at h1 h2 <;> omega
  · refine ((Frame.refl _ _).snoc ?_).snoc ?_ <;> intro b h1 h2 <;> simp only [e24, e167] at h1 h2 <;> omega

theorem lldMt_sign (Mt : Mem) {sp : BitVec 64} (ap v : BitVec 64) (hsp : sp.toNat + 200 < 2 ^ 64) :
    ldv .lbu (lldMt Mt sp ap v) (sp + 167#64).toNat = BitVec.zeroExtend 64 (lldSign v) := by
  have e24 : (sp + 24#64).toNat = sp.toNat + 24 := sp_lit (by omega)
  have e167 : (sp + 167#64).toNat = sp.toNat + 167 := sp_lit (by omega)
  unfold lldMt lldSign
  split
  · rw [ldv_lbu_hit] <;> first | decide | rfl
  · rw [ldv_lbu_miss _ _ (by rw [e24, e167]; omega), ldv_lbu_hit] <;> first | decide | rfl

theorem lldMt_signImg (Mt : Mem) {sp : BitVec 64} (ap v : BitVec 64) (hsp : sp.toNat + 200 < 2 ^ 64) :
    imgM (lldMt Mt sp ap v) (sp.toNat + 167) = lldSign v := by
  have e24 : (sp + 24#64).toNat = sp.toNat + 24 := sp_lit (by omega)
  have e167 : (sp + 167#64).toNat = sp.toNat + 167 := sp_lit (by omega)
  unfold lldMt lldSign
  split
  · rw [← e167, show (45#64 : BitVec 64) = BitVec.zeroExtend 64 (45#8) by decide, imgM_sb_zext]
  · rw [imgM_store_miss _ _ (by rw [e24]; omega), ← e167,
      show (0#64 : BitVec 64) = BitVec.zeroExtend 64 (0#8) by decide, imgM_sb_zext]

theorem vfp_lld (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f ap v : BitVec 64} {need cnt : Nat} {pend0 : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (hcnt : cnt + 21 < 2 ^ 31)
    (hP : VfpPend R Mt sp 0x8001b538#64 f cnt []) (h25 : R 25 = 0x800192c0#64) (hFm : LldFmt Dt DA)
    (hap : ldv .ld Mt (sp + 24#64).toNat = ap) (hv : ldv .ld Mt ap.toNat = v) (hF : SbFile Mt f pend0)
    (hk : ∀ R' M' out pend', pend0 ++ lldBytes v = out ++ pend' →
      VfpLoop R' M' sp 0x8001b538#64 f 0x800192c4#64 (cnt + lldCnt (lldSign v) (digBytes (lldMag v).toNat)) →
      SbFile M' f pend' → Frame M' Mt (LldReg f.toNat sp.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000a9b0#64 R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9fc#64 R Mt := by
  refine lld_head hlive hs1 hs2 hs3 hs4 hal hap1 hap2 hapa hP.spR h25 hFm hap hv fun R1 Mt1 H1 => ?_
  have k12 : R1 2 = sp := (H1.keep 2 (by decide)).trans hP.spR
  refine lld_mag hlive hlive' hsub hs1 hs2 hs3 hs4 hal k12 H1.mag H1.prec H1.t3 H1.t4 fun R2 Mt2 H2 => ?_
  have hm1 := H1.mem; subst hm1
  have hsp : sp.toNat + 600 < 2 ^ 64 := by omega
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  have hMF : Frame Mt2 Mt (fun a => ((sp.toNat + 24 ≤ a ∧ a < sp.toNat + 32) ∨ a = sp.toNat + 167) ∨
      MagReg sp.toNat a) :=
    ((lldMt_frame Mt ap v (by omega)).mono fun a h => .inl h).trans (H2.frame.mono fun a h => .inr h)
  have kR2 : ∀ x ∈ [2, 9, 18, 19, 21, 23], R2 x = R x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (H2.keep _ (by decide)).trans (H1.keep _ (by decide))
  have P2 : VfpPend R2 Mt2 sp 0x8001b538#64 f cnt [] := hP.transport hsp (by simp) kR2 hMF
    (fun a h => by unfold MagReg at h; simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; omega)
  have hsg2 : ldv .lbu Mt2 (sp + 167#64).toNat = BitVec.zeroExtend 64 (lldSign v) := by
    rw [H2.frame.ldv .lbu (fun j hj h => by
      simp only [widthOfM] at hj; rw [eo 167 (by omega)] at h; unfold MagReg at h; omega)]
    exact lldMt_sign Mt ap v (by omega)
  have hL1 := digBytes_pos (lldMag v).toNat
  have hL2 := digBytes_len (lldMag v).toNat (lldMag v).isLt
  refine lld_stage (ds := digBytes (lldMag v).toNat) (sg := lldSign v) hlive hs1 hs2 hs3 hs4 hal hL1 hL2 hcnt P2
    H2.ptr H2.a3 H2.a4 (H2.t5.trans (lldMt_sign Mt ap v (by omega))) H2.t1
    ((H2.keep 22 (by decide)).trans H1.prec) ((H2.keep 28 (by decide)).trans H1.t3)
    ((H2.keep 29 (by decide)).trans H1.t4) hsg2 fun R3 Mt3 P3 k3 hF3 => ?_
  have hlen : piecesLen (lldIovs sp.toNat (lldSign v) (digBytes (lldMag v).toNat)) = (lldBytes v).length := by
    rw [piecesLen_eq, piecesBytes_lldIovs]
  have hbl : (digBytes (lldMag v).toNat).length ≤ (lldBytes v).length ∧ (lldBytes v).length ≤ 21 := by
    unfold lldBytes; split <;> simp <;> omega
  have hMF3 : Frame Mt3 Mt (fun a => (((sp.toNat + 24 ≤ a ∧ a < sp.toNat + 32) ∨ a = sp.toNat + 167) ∨
      MagReg sp.toNat a) ∨ StageReg sp.toNat a) :=
    (hMF.mono fun a h => .inl h).trans (hF3.mono fun a h => .inr h)
  have hSb3 : SbFile Mt3 f pend0 := hF.frame_out hMF3 (by omega) fun b hb => by
    unfold MagReg StageReg at hb; omega
  have hz32 : ldv .ld Mt3 (sp + 32#64).toNat = 0#64 := by
    rw [hF3.ldv .ld (fun j hj h => by
      simp only [widthOfM] at hj; rw [eo 32 (by omega)] at h; unfold StageReg at h; omega)]
    exact H2.zero32
  have hsrcs : ∀ p ∈ lldIovs sp.toNat (lldSign v) (digBytes (lldMag v).toNat), PieceOK Dt DA s need Mt3 f sp p := by
    intro p hp
    have hnS : ∀ a, sp.toNat ≤ a → a < sp.toNat + 348 → (a < sp.toNat + 232 ∨ sp.toNat + 248 ≤ a) →
        ¬ SprintReg f.toNat sp.toNat (sp.toNat + 224) a := fun a h1 h2 h3 hr => by
      unfold SprintReg SfvCallReg LoopReg SfvReg at hr; omega
    unfold lldIovs at hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp; subst hp
        refine ⟨fun i hi => ?_, by omega, by simp; omega, by simp; omega, fun i hi => hnS _ (by omega) (by simp at hi; omega)
          (by simp at hi; omega)⟩
        simp only [List.length_singleton] at hi
        obtain rfl : i = 0 := by omega
        refine .inr ⟨by unfold outS; omega, ?_⟩
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hF3 _ (fun h => by unfold StageReg at h; omega), H2.frame _ (fun h => by unfold MagReg at h; omega)]
        exact lldMt_signImg Mt ap v (by omega)
    · unfold PieceOK; dsimp only
      refine ⟨fun i hi => ?_, by omega, by omega, by omega, fun i hi => hnS _ (by omega) (by omega) (by omega)⟩
      refine .inr ⟨by unfold outS; omega, ?_⟩
      rw [hF3 _ (fun h => by unfold StageReg at h; omega)]
      exact H2.digits i hi
  refine vfp_print hlive hlive' hsub hs1 hs2 hs3 hs4 hal hf1 hf2 hfa P3
    ((k3 24 (by decide)).trans ((H2.keep 24 (by decide)).trans H1.fmt))
    (by unfold lldIovs; split <;> simp) (by omega) (by omega) hsrcs hz32 hSb3
    fun R4 M4 out pend' hrel HL hSb' hfr4 => ?_
  rw [piecesBytes_lldIovs] at hrel
  refine hk R4 M4 out pend' hrel HL hSb' ((hMF3.mono fun a h => ?_).trans (hfr4.mono fun a h => .inr (.inr (.inr (.inr h)))))
  unfold LldReg
  rcases h with ((h | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

end VsaIris.Sym.Fp
