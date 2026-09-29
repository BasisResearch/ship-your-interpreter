import Vsa.Compiler.SimUnary
import Vsa.Compiler.RTOps

/-!
# Binary operator code

`run_op`: the code of a binary operator, on two represented operands in
`(a0, a1)` and `(a2, a3)` whose `binOpSem` result is `v`, returns `v` and grows the
object heap by at most `64` bytes per unit of `binOpCost`, or reaches the error
exit without that room.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The result of a binary operator's code. -/
structure OpRet (H : CloMap) (m m' : Mem) (h h' c : Nat) (L L' : GRegs) (v : Value) : Prop where
  hp : Has L' hpO (BitVec.ofNat 64 h')
  grow : h ≤ h'
  within : h' ≤ h + c
  room : h' ≤ objEnd
  al : h' % 8 = 0
  frame : ∀ a, a % 8 = 0 → (a + 8 ≤ h ∨ h' ≤ a) → (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
    rdW m' a = rdW m a
  val : InA H m' h' L' v
  keep : Keep addClob L L'

theorem catNeed_le (s : Store) (l r : Value) : catNeed s l r ≤ 64 * concatCost s l r := by
  unfold catNeed concatCost stringifyCost roundUp16; omega

theorem addNeed_le (s : Store) (l r : Value) : addNeed s l r ≤ 64 * binOpCost s .add l r := by
  cases l <;> cases r <;> simp only [addNeed, binOpCost] <;> first | exact catNeed_le _ _ _ | omega

theorem keep_call {S : List Nat} {L L' : GRegs} {r : BitVec 64} (hS : ∀ x ∈ S, x ∈ addClob)
    (h : Keep S (gset L 1 r) L') : Keep addClob L L' :=
  (Keep.gset (Keep.refl _ L) (by decide)).trans (h.mono hS)

theorem Operands.gset1 {H : CloMap} {m : Mem} {h : Nat} {L : GRegs} {l r : Value} {t1 p1 t2 p2 : BitVec 64}
    (hops : Operands H m h L l r t1 p1 t2 p2) (w : BitVec 64) : Operands H m h (gset L 1 w) l r t1 p1 t2 p2 :=
  ⟨by reg_simp []; exact hops.h10, by reg_simp []; exact hops.h11, by reg_simp []; exact hops.h12,
    by reg_simp []; exact hops.h13, hops.vl, hops.vr⟩

theorem Operands.gset14 {H : CloMap} {m : Mem} {h : Nat} {L : GRegs} {l r : Value} {t1 p1 t2 p2 : BitVec 64}
    (hops : Operands H m h L l r t1 p1 t2 p2) (w : BitVec 64) : Operands H m h (gset L 14 w) l r t1 p1 t2 p2 :=
  ⟨by reg_simp []; exact hops.h10, by reg_simp []; exact hops.h11, by reg_simp []; exact hops.h12,
    by reg_simp []; exact hops.h13, hops.vl, hops.vr⟩

theorem keep_14 {L : GRegs} {w r : BitVec 64} {S : List Nat} (h14 : 14 ∈ S) :
    Keep S (gset L 1 r) (gset (gset L 14 w) 1 r) := fun x hx => by
  simp only [lookupG_set]
  by_cases h1 : x = 1
  · simp [h1]
  · have : x ≠ 14 := fun e => hx (by rw [e]; exact h14)
    simp [h1, this]

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

/-- A routine that keeps the memory and the object heap. -/
theorem opRet_same {H : CloMap} {m : Mem} {h : Nat} {L L' : GRegs} {v : Value} {c : Nat} {S : List Nat}
    {r : BitVec 64} (hS : ∀ x ∈ S, x ∈ addClob) (hno : hpO ∉ S) (h8 : Has L hpO (BitVec.ofNat 64 h))
    (hh : ObjPtr h) (hv : InA H m h L' v) (hk : Keep S (gset L 1 r) L') : OpRet H m m h h c L L' v where
  hp := hk.has hno (by reg_simp []; exact h8)
  grow := Nat.le_refl _
  within := by omega
  room := hh.hi
  al := hh.al
  frame _ _ _ _ := rfl
  val := hv
  keep := keep_call hS hk

theorem run_op {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String} {op : BinOp}
    {l r v : Value} {t1 p1 t2 p2 : BitVec 64} {q : Nat} (hops : Operands H m h L l r t1 p1 t2 p2)
    (hseg : Seg code q (opCode q op)) (hq : PosOK (q + (opCode q op).length))
    (hbin : binOpSem s op l r = some v) (h8 : Has L hpO (BitVec.ofNat 64 h)) (hh : ObjPtr h)
    (hfx : FixedOK m) (hfb : fixedAddr 7 + 40 ≤ h) (hc : CloOK H s m h) (hinj : CloInj H) :
    Reaches code ⟨pcOf q, L, m, o⟩ (fun B => B.out = o ∧
      ((B.pc = pcOf errPos ∧ objEnd < h + 64 * binOpCost s op l r) ∨
        (B.pc = pcOf (q + (opCode q op).length) ∧
          ∃ h', OpRet H m B.mem h h' (64 * binOpCost s op l r) L B.regs v))) := by
  have hq1 : PosOK (q + 1) := posOK_le hq (by cases op <;> simp [opCode])
  have hal1 := pcOf_aligned hq1
  cases op with
  | add =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_add hR (s := s) (hops.gset1 _) (by reg_simp []; exact h8) (by reg_simp []) hal1
      hh hfx hfb hc) ?_
    rintro B ⟨ho, hB⟩
    rw [hbin] at hB
    rcases hB with ⟨hpc, h', hb, ret⟩ | ⟨hpc, hov⟩
    · refine ⟨ho, .inr ⟨by simp [hpc, opCode], h', ret.hp, ret.grow,
        Nat.le_trans hb (by have := addNeed_le s l r; omega), ret.room, ret.al, ret.frame, ret.val,
        keep_call (fun _ h => h) ret.keep⟩⟩
    · exact ⟨ho, .inl ⟨hpc, by have := addNeed_le s l r; omega⟩⟩
  | sub =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_sub hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨by simp [hpc, opCode], h, opRet_same hR (S := [t0, a1]) (by decide) (by decide) h8 hh hv hk⟩⟩
  | mul =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_mul hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨by simp [hpc, opCode], h, opRet_same hR (S := [ra, t0, a0, a1, a2, a3, s10]) (by decide) (by decide) h8 hh hv hk⟩⟩
  | div =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_div hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨by simp [hpc, opCode], h, opRet_same hR (S := [ra, t0, a0, a1, a2, a3, s10]) (by decide) (by decide) h8 hh hv hk⟩⟩
  | mod =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_mod hR (s := s) (hops.gset1 _) (by reg_simp []) hal1) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨by simp [hpc, opCode], h, opRet_same hR (S := [ra, t0, a0, a1, a2, a3, s10]) (by decide) (by decide) h8 hh hv hk⟩⟩
  | eq =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_eq hR (hops.gset1 _) hinj (by reg_simp []) hal1) ?_
    rintro B ⟨hpc, ho, hm, g10, g11, hk⟩
    simp only [binOpSem] at hbin; cases hbin
    rw [hm]
    refine ⟨ho, .inr ⟨by simp [hpc, opCode], h, opRet_same hR (S := eqClob) (by decide) (by decide) h8 hh
      ⟨_, _, g10, g11, rfl, ?_⟩ hk⟩⟩
    cases l.equal r <;> rfl
  | ne =>
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine ex_bind (run_eq hR (hops.gset1 _) hinj (by reg_simp []) hal1) ?_
    rintro ⟨pc, L2, m2, o2⟩ ⟨hpc, ho, hm, g10, g11, hk⟩
    simp only at hpc ho hm g10 g11 hk; subst hpc ho hm
    have k11 := has_mem g11 (by decide); have e11 := srcVal_of_has g11
    simp only [a1] at k11 e11
    apply run_from hR.fits hseg 1 _ (by rfl) (by simp [opCode])
    wp_simp [opCode, k11, e11]
    simp only [binOpSem] at hbin; cases hbin
    refine reach_here ⟨rfl, .inr ⟨by simp [opCode], h, opRet_same hR (S := t0 :: a1 :: eqClob) (r := pcOf (q + 1)) (by decide)
      (by decide) h8 hh ⟨1, 1#64 - (if l.equal r = true then 1 else 0), by reg_simp []; exact g10,
        by reg_simp [], rfl, ?_⟩ ?_⟩⟩
    · cases l.equal r <;> rfl
    · reg_simp []; exact hk.mono (by decide)
  | lt =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .lt) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨hpc.trans rfl, h, opRet_same hR (S := a4 :: cmpClob) (by decide) (by decide) h8 hh hv
      ((keep_14 (by decide)).trans (hk.mono (by decide)))⟩⟩
  | le =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .le) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨hpc.trans rfl, h, opRet_same hR (S := a4 :: cmpClob) (by decide) (by decide) h8 hh hv
      ((keep_14 (by decide)).trans (hk.mono (by decide)))⟩⟩
  | gt =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .gt) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨hpc.trans rfl, h, opRet_same hR (S := a4 :: cmpClob) (by decide) (by decide) h8 hh hv
      ((keep_14 (by decide)).trans (hk.mono (by decide)))⟩⟩
  | ge =>
    have hq2 : PosOK (q + 1 + 1) := posOK_le hq (by simp [opCode])
    apply run_whole hR.fits hseg
    wp_simp [opCode, hq]
    refine reaches_mono (run_cmp hR (s := s) (op := .ge) (by simp [IsOrd]) (hops.gset14 _ |>.gset1 _)
      (by reg_simp []; rfl) (by reg_simp []) (pcOf_aligned hq2)) ?_
    rintro B ⟨ho, hm, hB⟩
    rw [hbin] at hB
    obtain ⟨hpc, hv, hk⟩ := hB
    rw [hm]
    exact ⟨ho, .inr ⟨hpc.trans rfl, h, opRet_same hR (S := a4 :: cmpClob) (by decide) (by decide) h8 hh hv
      ((keep_14 (by decide)).trans (hk.mono (by decide)))⟩⟩
end

end Vsa.Compiler
