import Vsa.Compiler.SimBlock
import Vsa.Compiler.R6Expr

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_cond {st : St} {d : Nat} {env : Addr} {c : Expr} {st1 : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env c st1 v n) {V : View} {C : GCtx} {sp fs pos tgt : Nat} {A : AM}
    (hm : MS code T V st d env C.Γ sp fs A) (hA : A.pc = pcOf pos) (hwf : WfE T C.Γ c)
    (hseg : Seg code pos (gexpr T C.Γ 0 pos c ++ [Call (pos + (gexpr T C.Γ 0 pos c).length) trPos] ++
      jmpIfZero (pos + (gexpr T C.Γ 0 pos c).length + 1) tgt))
    (hP : PosOK (pos + (gexpr T C.Γ 0 pos c).length + 3)) (htgt : PosOK tgt) (htmp : 16 + 16 * tE c ≤ fs) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V1, SPost code T V st d env C sp fs (if v.truthy then pos + (gexpr T C.Γ 0 pos c).length + 3 else tgt)
        A n st1 .normal V1 B) := by
  rw [List.append_assoc, List.singleton_append] at hseg
  obtain ⟨s1, s23⟩ := seg_app_iff.mp hseg
  have s3 := (seg_app_iff (a := [_])).mp s23 |>.2
  refine hE.bindTr hR hm hA hwf s1 s23 (by simpa [jmpIfZero] using hP) (by omega) (Within.refl V 0) (by omega)
    fun V1 B L2 hp hk g10 => ?_
  apply run_jumps hR.fits s3
  cases hvt : v.truthy
  · wp_simp [jmpIfZero, g10.wp, htgt, hvt]
    exact reach_here (.inr ⟨V1, ⟨by simp, hp.ms.keep hk⟩, hp.grow, hp.within, hp.stack, hp.obj⟩)
  · wp_simp [jmpIfZero, g10.wp, hP, hvt]
    exact reach_here (.inr ⟨V1, ⟨by simp, hp.ms.keep hk⟩, hp.grow, hp.within, hp.stack, hp.obj⟩)


end

end Vsa.Compiler
