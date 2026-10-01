import Vsa.Compiler.StuckDefs
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem EStuck.cond {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr}
    (ihc : EStuck code T n st d env c) {V : View} {C : GCtx} {sp fs pos tgt : Nat} {A : AM}
    (hm : MS code T V st d env C.Γ sp fs A) (hA : A.pc = pcOf pos) (hwc : WfE T C.Γ c)
    (s1 : Seg code pos (gexpr T C.Γ 0 pos c))
    (s2 : Seg code (pos + (gexpr T C.Γ 0 pos c).length) [Call (pos + (gexpr T C.Γ 0 pos c).length) trPos])
    (s3 : Seg code (pos + (gexpr T C.Γ 0 pos c).length + 1)
      (jmpIfZero (pos + (gexpr T C.Γ 0 pos c).length + 1) tgt))
    (hP : PosOK (pos + (gexpr T C.Γ 0 pos c).length + 1 + 2)) (htgt : PosOK tgt) (htmp : 16 + 16 * tE c ≤ fs)
    (hk : ∀ st1 v V1 B, EvalE st d env c st1 v → MS code T V1 st1 d env C.Γ sp fs B →
      B.pc = pcOf (bif v.truthy then pos + (gexpr T C.Γ 0 pos c).length + 3 else tgt) → Fail code n B) :
    Fail code n A := by
  by_cases hec : HasE st d env c
  · obtain ⟨st1, v, Dc⟩ := hec
    obtain ⟨nc, hE⟩ := spec_e hR (T := T) Dc
    apply Fail.of_reaches
    refine ex_bind (run_cond hR hE hm hA hwc (seg_app_iff.mpr ⟨seg_app_iff.mpr ⟨s1, s2⟩, s3.cast (by simp; omega)⟩) hP htgt htmp) ?_
    rintro B (⟨h1, -⟩ | ⟨V1, hp1⟩)
    · exact reach_here (fail_err hR h1)
    obtain ⟨hpc1, hm1⟩ := hp1.out
    refine reach_here (hk st1 v V1 B Dc hm1 ?_)
    rw [hpc1]; cases v.truthy <;> rfl
  · exact ihc V C.Γ sp fs 0 pos A hm hA hwc s1 (by unfold PosOK at *; omega) (by omega) hec

end

end Vsa.Compiler
