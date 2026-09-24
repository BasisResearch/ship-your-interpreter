import VsaIris.Interp.CallCloBind
import VsaIris.Interp.ExecBlock

/-!
# The closure call: the body's entry (lane E4)

From `jal value_null(sp+144)` (`0x80003328`, the parameters bound) to G's
closure loop head (`0x80003354`) or, for an empty body, the normal end
(`0x80003954`), for either WP (`cloBodyEntry`): `value_null` fills the result
slot, the slot is lent out (`slot24`, as `closureSeq{T,P}_body` take it), and
`CloB_runB` reads the body node and its count.

`CloAt`: what every exit of the path needs of the registers and the frame
(the caller's `sret`, `in`, the callee-saved registers the path never
writes, the spills).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The registers and frame words every exit of the closure path needs. -/
structure CloAt (R : Nat → BitVec 64) (Mt : Mem) (s inp sret ret : BitVec 64) (rv : Nat → BitVec 64) :
    Prop where
  sp : R 2 = s + 18446744073709550528#64
  s1 : R 9 = sret
  s2 : R 18 = inp
  keep : ∀ x ∈ [20, 22, 24, 25, 26, 27], R x = rv x
  spills : CloSpills Mt s ret rv

/-- `CloAt` through a write to a register it does not speak of. -/
theorem CloAt.upd {R : Nat → BitVec 64} {Mt : Mem} {s inp sret ret : BitVec 64} {rv : Nat → BitVec 64}
    (h : CloAt R Mt s inp sret ret rv) {x : Nat} (hx : x ∉ [2, 9, 18, 20, 22, 24, 25, 26, 27])
    (w : BitVec 64) : CloAt (upd R x w) Mt s inp sret ret rv := by
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hx
  obtain ⟨h2, h9, h18, h20, h22, h24, h25, h26, h27⟩ := hx
  refine ⟨?_, ?_, ?_, fun y hy => ?_, h.spills⟩
  · simp only [upd_apply, Ne.symm h2, ite_false]; exact h.sp
  · simp only [upd_apply, Ne.symm h9, ite_false]; exact h.s1
  · simp only [upd_apply, Ne.symm h18, ite_false]; exact h.s2
  · have : y ≠ x := by
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy; omega
    simp only [upd_apply, this, ite_false]; exact h.keep y hy

/-- The result slot `sp+144` of `eval_expr`'s frame. -/
theorem cloSlotGeom {s : BitVec 64} (hfg : EvalFrameG s) :
    SlotGeom (s + 18446744073709550528#64 + 144#64) := by
  have h := evalSP_off' hfg 144 (by decide)
  have := hfg.lo; have := hfg.al; have := hfg.hi
  refine ⟨?_, ?_, ?_⟩ <;> rw [h] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega

section Entry

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **The body's entry**, for either WP: `value_null(sp+144)`, the slot lent
out, the body node's count: G's loop head at index `0` (a nonempty body) or
the normal end (an empty one). -/
theorem cloBodyEntry (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N Wp p)
    {s inp sret ret fr q line bod : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {P : Nat → Prop} {m : Mem} {body : List Stmt}
    (hfg : EvalFrameG s)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hqv : ∀ a ∈ accAddrs (q.toNat + 32) 8, P a ∧ (m[a]?).isSome)
    (hbod : ldv .ld m (q + 32#64).toNat = bod)
    (hbr : StmtReprWithin m P bod.toNat (.block body)) (hpg : ∀ k, P k → ReadOK k)
    (hpd : CloPD R Mt s inp sret ret fr q line rv) (F : IProp GF) :
    codeRes ∗ roOn P m ∗ ms 0x80003328#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ F ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (arr : BitVec 64) (count : Nat),
          ⌜body ≠ [] ∧ BlockNode m P bod arr count body ∧ ClosureHead R' s bod inp fr 0 ∧
            CloAt R' Mt' s inp sret ret rv⌝ -∗ F -∗
          ms 0x80003354#64 R' (closureS s) Mt' -∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat -∗
          Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜body = [] ∧ CloAt R' Mt' s inp sret ret rv⌝ -∗ F -∗
          ms 0x80003954#64 R' (closureS s) Mt' -∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat -∗
          Wp.W Φ))
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off' hfg
  have hslg := cloSlotGeom hfg
  have h144 := hoff 144 (by decide)
  obtain ⟨arr, count, hsn, hcnt, hlen, hbn⟩ := blockNode_of hbr hpg
  iintro ⟨#Hcode, #Hro, Hms, HF, Hk⟩
  -- `value_null(sp+144)`
  ihave Hvn := hvn $$ %(s + 18446744073709550528#64 + 144#64)
  unfold valueNullSpec
  iapply ms_callHelperSlot Wp (i := 0x80003328)
    (jalx_80003328 live (fun p hp => hlive _ (interp_code_80003328 p hp)))
    interp_code_80003328 (by decide) (a := s + 18446744073709550528#64 + 144#64) (R := R) (Mt := Mt)
    (S := InExt (s.toNat - 1088, 1088)) (v := .null)
    (fun b hb => by simp only [InExt] at hb ⊢; rw [h144] at hb; omega) hslg
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; exact hpd.a0
  iintro %R1 %w0 %w1 %w2 %hk1 #-
  -- the slot lent out
  iintro Hms
  ihave Hms := ms_iff (T := fun k => closureS s k ∨ InExt ((s + 18446744073709550528#64 + 144#64).toNat, 24) k)
    (fun k => by
      simp only [closureS, InExt]; rw [h144]
      constructor
      · intro h; by_cases h' : s.toNat - 1088 + 144 ≤ k ∧ k < s.toNat - 1088 + 144 + 24
        · exact .inr h'
        · exact .inl ⟨h, h'⟩
      · rintro (⟨h, _⟩ | h) <;> omega) $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => by
    simp only [closureS, InExt] at h1 h2; rw [h144] at h2; exact h1.2 ⟨by omega, by omega⟩) $$ Hms
  ihave Hslot := ownSet_forget _ _ $$ Hslot
  -- the body node and its count
  have hk2 : ∀ y ∈ fRegs, upd R1 1 (BitVec.ofNat 64 (0x80003328 + 4)) y = R y := fun y hy => by
    have : y ≠ 1 := fun h => by subst h; simp at hy
    simp only [upd_apply, this, ite_false]; exact hk1 y hy (by simp)
  have hsw : CloSpills (slotWrite Mt (s + 18446744073709550528#64 + 144#64).toNat w0 w1 w2) s ret rv :=
    hpd.spills.agree fun k h1 h2 _ _ => imgM_slotWrite_out w0 w1 w2 (by
      simp only [InExt]; rw [h144]; omega)
  have hat : CloAt (upd R1 1 (BitVec.ofNat 64 (0x80003328 + 4)))
      (slotWrite Mt (s + 18446744073709550528#64 + 144#64).toNat w0 w1 w2) s inp sret ret rv :=
    ⟨(hk2 2 (by decide)).trans hpd.sp, (hk2 9 (by decide)).trans hpd.s1,
      (hk2 18 (by decide)).trans hpd.s2,
      fun x hx => (hk2 x ((by decide : ∀ z ∈ [20, 22, 24, 25, 26, 27], z ∈ fRegs) x hx)).trans
        (hpd.keep x hx), hsw⟩
  ihave #Hdv := roOwn_data (DA := accAddrs (q.toNat + 32) 8 ++ accAddrs (bod.toNat + 16) 4)
    (fun a ha => by
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hqv a ha
      · refine hsn.view a ?_
        simp only [stmtView, List.mem_append, mem_accAddrs_iff] at ha ⊢
        omega) $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(F ∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (arr : BitVec 64) (count : Nat),
          ⌜body ≠ [] ∧ BlockNode m P bod arr count body ∧ ClosureHead R' s bod inp fr 0 ∧
            CloAt R' Mt' s inp sret ret rv⌝ -∗ F -∗
          ms 0x80003354#64 R' (closureS s) Mt' -∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat -∗
          Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜body = [] ∧ CloAt R' Mt' s inp sret ret rv⌝ -∗ F -∗
          ms 0x80003954#64 R' (closureS s) Mt' -∗ slot24 (s + 18446744073709550528#64 + 144#64).toNat -∗
          Wp.W Φ))))
  rotate_left
  · unfold slot24 blockOwn
    iframe Hdv Hms HF Hslot; iexact Hk
  intro F'
  refine CloB_runB (count := count) hlive hq1 hq2 hq3 hsn.lo hsn.hi hsn.off
    (by rcases Nat.eq_zero_or_pos count with h | h
        · omega
        · exact (hbn h).small)
    ((hk2 21 (by decide)).trans hpd.s5) hbod hcnt ?_ ?_
  · -- a nonempty body: G's loop head
    intro hgt
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hR2 hMt2
    have hsmall : count < 2 ^ 31 := by
      rcases Nat.eq_zero_or_pos count with h | h
      · omega
      · exact (hbn h).small
    have hpos : 0 < count := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hgt
      rw [ofNat_toInt_small hsmall] at hgt; simp at hgt; omega
    have hat2 := ((hat.upd (x := 16) (by decide) bod).upd (x := 8) (by decide) 0#64).upd (x := 15)
      (by decide) (BitVec.ofNat 64 count)
    have hch : ClosureHead (upd (upd (upd (upd R1 1 (BitVec.ofNat 64 (0x80003328 + 4))) 16 bod) 8 0#64) 15
        (BitVec.ofNat 64 count)) s bod inp fr 0 :=
      ⟨hat2.sp, by ix_reg, by ix_reg <;> rfl, hat2.s2, by ix_reg; exact (hk2 19 (by decide)).trans hpd.s3⟩
    have hne : body ≠ [] := fun h => by subst h; simp at hlen; omega
    unfold F'
    iintro ⟨⟨HF, Hslot, Hk⟩, Hms⟩
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %_ %_ %(BitVec.ofNat 64 arr) %count %⟨hne, hbn hpos, hch, hat2⟩ HF Hms Hslot
  · -- an empty body: the normal end
    intro hle
    apply swp_closeRM
    intro R2 Mt2 hR2 hMt2
    subst hR2 hMt2
    have hsmall : count < 2 ^ 31 := by
      rcases Nat.eq_zero_or_pos count with h | h
      · omega
      · exact (hbn h).small
    have h0 : count = 0 := by
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hle
      rw [ofNat_toInt_small hsmall] at hle; simp at hle; omega
    have hat2 := ((hat.upd (x := 16) (by decide) bod).upd (x := 8) (by decide) 0#64).upd (x := 15)
      (by decide) (BitVec.ofNat 64 count)
    unfold F'
    iintro ⟨⟨HF, Hslot, Hk⟩, Hms⟩
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ %_ %_ %⟨List.eq_nil_of_length_eq_zero (by omega), hat2⟩ HF Hms Hslot

end Entry

end VsaIris.Interp
