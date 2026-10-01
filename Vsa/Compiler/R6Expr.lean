import Vsa.Compiler.SimBin
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem MS.keep {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {B : AM} (hm : MS code T V st d env Γ sp fs B) {S : List Nat}
    {L : GRegs} (hk : Keep S B.regs L) (hS : Scratch S := by decide) {pc : BitVec 64} :
    MS code T V st d env Γ sp fs ⟨pc, L, B.mem, B.out⟩ :=
  hm.transport hS hk (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl

theorem MS.reenv {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) {env' : Addr}
    {Γ' : List (List String)} (hc : ChainL V.F st.store env' Γ') {B : AM} (hk : Keep [envR] A.regs B.regs)
    (he : Has B.regs envR (BitVec.ofNat 64 (V.fa env'))) (hmem : B.mem = A.mem) (hout : B.out = A.out) :
    MS code T V st d env' Γ' sp fs B where
  rel := hmem ▸ hm.rel
  img := hmem ▸ hm.img
  clo := hmem ▸ hm.clo
  chn := hc
  out := hout ▸ hm.out
  ho := hk.has (by decide) hm.ho
  hf := hk.has (by decide) hm.hf
  henv := he
  hsp := hk.has (by decide) hm.hsp
  hdep := hk.has (by decide) hm.hdep
  stk := hm.stk
  hfal := hm.hfal

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem ESpec.bindTr {st : St} {d : Nat} {env : Addr} {e : Expr} {st1 : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env e st1 v n) {V : View} {Γ : List (List String)} {sp fs k pos : Nat} {A : AM}
    (hm : MS code T V st d env Γ sp fs A) (hA : A.pc = pcOf pos) (hwf : WfE T Γ e)
    (hs1 : Seg code pos (gexpr T Γ k pos e)) {rest : List Ins}
    (hs2 : Seg code (pos + (gexpr T Γ k pos e).length) (Call (pos + (gexpr T Γ k pos e).length) trPos :: rest))
    (hP : PosOK (pos + (gexpr T Γ k pos e).length +
      (Call (pos + (gexpr T Γ k pos e).length) trPos :: rest).length))
    (htmp : 16 + 16 * (k + tE e) ≤ fs) {V0 : View} {n0 N : Nat} (hW : Within V0 V n0) (hN : n0 + n ≤ N)
    {R : AM → Prop}
    (hk : ∀ V1 B L', EPost code T V st d env Γ sp fs k A n st1 v V1 B → Keep [1, t0, a0] B.regs L' →
      Has L' a0 (if v.truthy then 1 else 0) →
      Reaches code ⟨pcOf (pos + (gexpr T Γ k pos e).length + 1), L', B.mem, B.out⟩
        (fun B => (B.pc = pcOf errPos ∧ ¬ Room V0 N) ∨ R B)) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V0 N) ∨ R B) := by
  have hq : PosOK (pos + (gexpr T Γ k pos e).length + 1) := by simp only [List.length_cons] at hP; omega
  refine hE.bind hm hA hwf hs1 (by omega) htmp (fun B h1 h2 => .inl ⟨h1, Room.not_within h2 hW hN⟩)
    fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨pc1, L1, m1, o1⟩ := B
  simp only at hpc h10 h11 hv; subst hpc
  apply run_whole hR.fits ((seg_app_iff (a := [_]) (b := rest)).mp hs2).1
  wp_simp [hq]
  refine ex_bind (run_tr hR.fits hR.tr (L := gset L1 1 (pcOf (pos + (gexpr T Γ k pos e).length + 1)))
    (m := m1) (o := o1) (by reg_simp []; exact h10) (by reg_simp []; exact h11) (by reg_simp [])
    (pcOf_aligned hq)) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hm2, ho2, g10, hk2⟩
  simp only at hpc2 hm2 ho2 g10 hk2; subst hpc2 hm2 ho2
  rw [trW_repr hv] at g10
  exact hk V1 _ L2 hp ((Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide))) g10

end

end Vsa.Compiler
