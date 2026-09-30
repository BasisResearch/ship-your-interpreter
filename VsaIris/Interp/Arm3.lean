import VsaIris.Interp.ArmEval
import VsaIris.Interp.ArmLogical
import VsaIris.Interp.SymInterp

/-!
Arms whose prologue saves `ra, s0, s1, s2` (logical, unary): the frame invariant `Frame3`
kept between steps, its transport through helper and child calls, and the matching epilogue.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- The invariant of a 3-save arm between steps: saved words, the node, result slot, input
and environment registers, and the untouched callee-saved registers. -/
structure Frame3 (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret aX inp aE : BitVec 64) : Prop where
  r2 : R 2 = evalSP s
  r8 : R 8 = aX
  r9 : R 9 = sret
  r18 : R 18 = inp
  s3 : R 19 = rv 19
  hi : ∀ x ∈ hiSaved, R x = rv x
  saved : EvalSaved3 Mt s ret (rv 8) (rv 9) (rv 18)
  ae : ldv .ld Mt (s.toNat - 1088) = aE

abbrev keep3 : List Nat := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem hi_keep3 : ∀ x ∈ hiSaved, x ∈ keep3 := by decide
theorem keep3_fRegs : ∀ x ∈ keep3, x ∈ fRegs := by decide
theorem keep3_callee : ∀ x ∈ keep3, x ∈ calleeSaved := by decide
theorem keep3_ne1 : ∀ x ∈ keep3, x ≠ 1 := by decide

theorem Frame3.regs {rv R R' : Nat → BitVec 64} {Mt Mt' : Mem} {s ret sret aX inp aE : BitVec 64}
    (f : Frame3 rv R Mt s ret sret aX inp aE) (hk : ∀ x ∈ keep3, R' x = R x)
    (hsv : EvalSaved3 Mt' s ret (rv 8) (rv 9) (rv 18)) (hae : ldv .ld Mt' (s.toNat - 1088) = aE) :
    Frame3 rv R' Mt' s ret sret aX inp aE :=
  ⟨(hk 2 (by decide)).trans f.r2, (hk 8 (by decide)).trans f.r8, (hk 9 (by decide)).trans f.r9,
    (hk 18 (by decide)).trans f.r18, (hk 19 (by decide)).trans f.s3,
    fun x hx => (hk x (hi_keep3 x hx)).trans (f.hi x hx), hsv, hae⟩

/-- Transport through a call whose callee keeps every register outside `clob` and the frame
outside the 24 bytes at frame offset `o`. -/
theorem Frame3.helper {rv R R' : Nat → BitVec 64} {Mt Mt' : Mem} {s ret sret aX inp aE : BitVec 64}
    {clob : List Nat} {o : Nat} (f : Frame3 rv R Mt s ret sret aX inp aE)
    (hk : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (hcl : ∀ x ∈ keep3, x ∉ clob)
    (ho : 8 ≤ o) (ho' : o + 24 ≤ 1056)
    (hag : ∀ k, s.toNat - 1088 ≤ k → k < s.toNat - 1088 + 1088 → (k < s.toNat - 1088 + o ∨
      s.toNat - 1088 + o + 24 ≤ k) → imgM Mt' k = imgM Mt k) (v : BitVec 64) :
    Frame3 rv (upd R' 1 v) Mt' s ret sret aX inp aE :=
  f.regs (fun x hx => by
      rw [upd_other _ _ (keep3_ne1 x hx)]; exact hk x (keep3_fRegs x hx) (hcl x hx))
    (f.saved.agree fun a h1 h2 => hag a (by omega) (by omega) (by omega))
    (by rw [ldv_ld_congr fun j hj => hag _ (by omega) (by omega) (by omega)]; exact f.ae)

/-- Transport through a recursive child call writing its result slot at frame offset `o`. -/
theorem Frame3.child {rv R R' : Nat → BitVec 64} {Mt : Mem} {s ret sret aX inp aE : BitVec 64}
    {o n : Nat} (f : Frame3 rv R Mt s ret sret aX inp aE) (hk : KeepRegs calleeSaved R R')
    (g : ArmGeo s ret sret n) (ho : 8 ≤ o) (ho' : o + 24 ≤ 1056) (w0 w1 w2 v : BitVec 64) :
    Frame3 rv (upd R' 1 v)
      (slotWrite Mt (evalSP s + BitVec.ofNat 64 o).toNat w0 w1 w2) s ret sret aX inp aE := by
  have hoff := g.off o (by omega)
  have hs := g.lo
  have hsv : EvalSaved3 (slotWrite Mt (evalSP s + BitVec.ofNat 64 o).toNat w0 w1 w2) s ret
      (rv 8) (rv 9) (rv 18) :=
    ((f.saved.store w0 (by omega)).store w1 (by omega)).store w2 (by omega)
  refine f.regs (fun x hx => ?_) hsv ?_
  · rw [upd_other _ _ (keep3_ne1 x hx)]; exact hk x (keep3_callee x hx)
  · unfold slotWrite
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
    exact f.ae

/-- The part of `Frame3` the epilogue needs. -/
structure EpiFrame3 (rv R : Nat → BitVec 64) (Mt : Mem) (s ret : BitVec 64) : Prop where
  r2 : R 2 = evalSP s
  s3 : R 19 = rv 19
  hi : ∀ x ∈ hiSaved, R x = rv x
  saved : EvalSaved3 Mt s ret (rv 8) (rv 9) (rv 18)

theorem Frame3.epi {rv R : Nat → BitVec 64} {Mt : Mem} {s ret sret aX inp aE : BitVec 64}
    (f : Frame3 rv R Mt s ret sret aX inp aE) : EpiFrame3 rv R Mt s ret :=
  ⟨f.r2, f.s3, f.hi, f.saved⟩

theorem EpiFrame3.helper {rv R R' : Nat → BitVec 64} {Mt : Mem} {s ret : BitVec 64}
    {clob : List Nat} (f : EpiFrame3 rv R Mt s ret)
    (hk : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (hcl : ∀ x ∈ keep3, x ∉ clob) (v : BitVec 64) :
    EpiFrame3 rv (upd R' 1 v) Mt s ret := by
  have kk : ∀ x ∈ keep3, upd R' 1 v x = R x := fun x hx => by
    rw [upd_other _ _ (keep3_ne1 x hx)]; exact hk x (keep3_fRegs x hx) (hcl x hx)
  exact ⟨(kk 2 (by decide)).trans f.r2, (kk 19 (by decide)).trans f.s3,
    fun x hx => (kk x (hi_keep3 x hx)).trans (f.hi x hx), f.saved⟩

/-- Post of a 3-save epilogue. -/
structure EpiPost3 (R R' : Nat → BitVec 64) (s ret v8 v9 v18 : BitVec 64) : Prop where
  ra : R' 1 = ret
  sp : R' 2 = s
  s0 : R' 8 = v8
  s1 : R' 9 = v9
  s2 : R' 18 = v18
  s3 : R' 19 = R 19
  hi : ∀ x ∈ hiSaved, R' x = R x

theorem EpiPost3.keep {R R' rv : Nat → BitVec 64} {s ret : BitVec 64}
    (he : EpiPost3 R R' s ret (rv 8) (rv 9) (rv 18)) (h19 : R 19 = rv 19)
    (hk : ∀ x ∈ hiSaved, R x = rv x) (hsp : rv 2 = s) : KeepRegs calleeSaved rv R' := by
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | hx
  · exact he.sp.trans hsp.symm
  · exact he.s0
  · exact he.s1
  · exact he.s2
  · exact he.s3.trans h19
  · have hx' : x ∈ hiSaved := by simp only [hiSaved, List.mem_cons, List.not_mem_nil]; omega
    exact (he.hi x hx').trans (hk x hx')

/-- A reflected 3-save epilogue from `pc` to the return address. -/
def EpiRun3 (pc : BitVec 64) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    {v8 v9 v18 : BitVec 64},
    ArmGeo s ret sret n → R 2 = evalSP s → EvalSaved3 Mt s ret v8 v9 v18 →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) pc ret R Mt
      (fun R' _ => EpiPost3 R R' s ret v8 v9 v18)

set_option hygiene false in
macro "epi3_run" : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n v8 v9 v18 g h2 hsv Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al; have hal := g.ral
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    rw [hoff _ (by decide)]; exact hsv.ra
  have hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8 := by
    rw [hoff _ (by decide)]; exact hsv.s0
  have hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9 := by
    rw [hoff _ (by decide)]; exact hsv.s1
  have hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18 := by
    rw [hoff _ (by decide)]; exact hsv.s2
  clear g h2 hsv hoff
  sym_run hlive using [h2', hRA, hS0, hS1, hS2, hsf, hal]
  refine hk _ _ ⟨by ix_reg, by ix_reg; exact evalSP_restore s, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg, fun x hx => ?_⟩
  simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg))

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem valOf_dupK (N : NativeAddrs) {K : IProp GF} (v : Value) (w0 w1 w2 : BitVec 64) :
    iprop(K ∗ □ valOf N v w0 w1 w2) ⊢ iprop(K ∗ □ valOf N v w0 w1 w2) ∗ □ valOf N v w0 w1 w2 := by
  iintro ⟨HK, #Hv⟩
  iframe HK Hv

/-- After a helper call from a 3-save frame: the epilogue and the caller's exit. -/
theorem ArmAt.finish3 (Wp : MachWP (GF := GF) (vsaModel live)) {i : Nat}
    (hlive : ∀ p ∈ interpText, live p.1) (hepi : EpiRun3 (BitVec.ofNat 64 (i + 4)))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret : BitVec 64} {n : Nat} {rv R R' : Nat → BitVec 64} {Mt : Mem}
    {Out Wd K : IProp GF} {DA : List Nat} {v : Value} {clob : List Nat}
    (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true)
    (g : ArmGeo s ret sret n) (f : EpiFrame3 rv R Mt s ret) (hsp : rv 2 = s)
    (hk : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (hcl : ∀ x ∈ keep3, x ∉ clob)
    (hOut : Out = valAt N sret.toNat v) (hexit : ExitK Wp Φ N s ret sret rv n v Wd K) :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) Out Wd K)
      (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4)))
      (InExt (s.toNat - 1088, 1088)) Mt := by
  subst hOut
  have f' := f.helper hk hcl (BitVec.ofNat 64 (i + 4))
  refine ArmAt.run Wp hv (hepi hlive g f'.r2 f'.saved) fun R5 _ p5 => ?_
  exact ArmAt.finish Wp hexit g.sg.le g.need p5.ra (p5.keep f'.s3 (fun x hx => f'.hi x hx) hsp)

/-- `value_bool` on a known bit, then a 3-save epilogue, then the caller's exit. -/
theorem ArmAt.boolFinish3 (Wp : MachWP (GF := GF) (vsaModel live)) (J : JalAt valueBoolPC)
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b)
    (hepi : EpiRun3 (BitVec.ofNat 64 (J.i + 4))) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF} {DA : List Nat} {c : Bool}
    {b : BitVec 64} (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true)
    (g : ArmGeo s ret sret n) (f : EpiFrame3 rv R Mt s ret) (hsp : rv 2 = s)
    (h10 : R 10 = sret) (h11 : R 11 = b) (hb : (b != 0#64) = c)
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool c) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 J.i) R
      (InExt (s.toNat - 1088, 1088)) Mt :=
  ArmAt.callBool Wp J hlive hvb h10 h11 g.slg fun _ hk =>
    ArmAt.finish3 Wp hlive hepi hv g f hsp hk (by decide) (by rw [hb]) hexit

/-- `value_truthy` on the operand copy at frame offset `64`. -/
theorem ArmAt.callTruthy (Wp : MachWP (GF := GF) (vsaModel live)) (J : JalAt valueTruthyPC)
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvt : ⊢ ∀ p v, valueTruthySpec (vsaModel live) N Wp p v) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret : BitVec 64} {n : Nat}
    {R : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF} {v : Value} {w0 w1 w2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hK : K ⊢ K ∗ □ valOf N v w0 w1 w2)
    (h10 : R 10 = evalSP s + 64#64)
    (h0 : ldv .ld Mt (s.toNat - 1088 + 64) = w0) (h8 : ldv .ld Mt (s.toNat - 1088 + 72) = w1)
    (h16 : ldv .ld Mt (s.toNat - 1088 + 80) = w2)
    (hk : ∀ R' Mt', (∀ x ∈ fRegs, x ∉ [10, 14, 15] → R' x = R x) →
      R' 10 = (if v.truthy then 1#64 else 0#64) →
      (∀ k, s.toNat - 1088 ≤ k → k < s.toNat - 1088 + 1088 → (k < s.toNat - 1088 + 64 ∨
        s.toNat - 1088 + 64 + 24 ≤ k) → imgM Mt' k = imgM Mt k) →
      ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 (J.i + 4))
        (upd R' 1 (BitVec.ofNat 64 (J.i + 4))) (InExt (s.toNat - 1088, 1088)) Mt') :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 J.i) R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  have hoff := g.off
  have hsf := g.sf
  unfold ArmAt entryF evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Ho, Hw, HK⟩, Hms⟩
  ihave ⟨HK, #Hv⟩ := hK $$ HK
  ihave Hvt := hvt $$ %(evalSP s + 64#64) %v
  iapply ms_callTruthy Wp (J.exec live hlive) J.mem J.al (S := InExt (s.toNat - 1088, 1088))
    ⟨hoff 64 (by decide), rfl, rfl⟩
    (fun b hb => by rw [hoff 64 (by decide)] at hb; simp only [VsaIris.InExt] at hb ⊢; omega)
    ⟨by rw [hoff 64 (by decide)]; have := g.lo; have := g.al; omega,
      by rw [hoff 64 (by decide)]; unfold Vsa.Sim.tohostAddr; have := g.lo; omega,
      by rw [hoff 64 (by decide)]; have := g.hi; omega⟩ h0 h8 h16
  iframe Hvt Hcode Hv Hms %h10
  iintro %R' %Mt' %⟨hkeep, hbit, hag⟩ Hms
  iapply hk R' Mt' hkeep hbit (fun k h1 h2 h3 => hag k (by simp only [VsaIris.InExt]; omega)
    (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega))
  iframe Hms; unfold entryF evalArmF; iframe Hcode Hro Hfb Hst Ho Hw HK

end

end VsaIris.Interp
