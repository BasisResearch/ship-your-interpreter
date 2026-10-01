import Vsa.Compiler.SimStmt1

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem StOut.fin {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env : Addr} {C : GCtx}
    {sp fs fin fin' : Nat} {B : AM} {t : Status} (h : StOut code T V' st' d env C sp fs fin B t)
    (ht : t ≠ .normal) : StOut code T V' st' d env C sp fs fin' B t := by
  cases t with
  | normal => exact absurd rfl ht
  | brk => exact h
  | cont => exact h
  | ret v => exact h

theorem SPost.seq {code : List Ins} {T : List String} {V V1 V2 : View} {st st1 st2 : St} {d : Nat} {env : Addr}
    {C : GCtx} {sp fs fin1 fin2 : Nat} {A B B' C' : AM} {n1 n2 : Nat} {t : Status}
    (h1 : SPost code T V st d env C sp fs fin1 A n1 st1 .normal V1 B)
    (h2 : SPost code T V1 st1 d env C sp fs fin2 B' n2 st2 t V2 C') (hm : B'.mem = B.mem) :
    SPost code T V st d env C sp fs fin2 A (n1 + n2) st2 t V2 C' :=
  ⟨h2.out, h1.grow.trans h2.grow, h1.within.add h2.within, h1.stack.trans (hm ▸ h2.stack),
    h1.obj.trans (hm ▸ h2.obj) h1.grow.le⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem qNil (st : St) (d : Nat) (env : Addr) : QSpec code T st d env [] st .normal 0 := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  exact reach_here (.inr ⟨V, ⟨by rw [hA]; simp [gseq], hm⟩, VGrow.refl _ _, Within.refl _ _,
    StackKeep.refl _ _ _ _, ObjAgree.refl _ _⟩)

theorem qConsNormal {st : St} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt} {st1 st2 : St} {t : Status}
    {n1 n2 : Nat} (hS : SSpec code T st d env s st1 .normal n1) (hQ : QSpec code T st1 d env ss st2 t n2) :
    QSpec code T st d env (s :: ss) st2 t (n1 + n2) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gseq] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append] at hP
  simp only [tSeq] at htmp
  refine ex_bind (hS V C sp fs pos A hm hA hwf.1 hctx s1 (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  obtain ⟨hpc1, hm1⟩ := hp1.out
  refine reaches_mono (hQ V1 C sp fs _ B hm1 hpc1 hwf.2 hctx s2 (by rw [← Nat.add_assoc] at hP; exact hP)
    (by omega)) ?_
  rintro C' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩
  · exact .inr ⟨V2, by rw [List.length_append, ← Nat.add_assoc]; exact hp1.seq hp2 rfl⟩

theorem qConsAbrupt {st : St} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt} {st1 : St} {t : Status}
    {n : Nat} (hS : SSpec code T st d env s st1 t n) (ht : t ≠ .normal) :
    QSpec code T st d env (s :: ss) st1 t n := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gseq] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append] at hP
  simp only [tSeq] at htmp
  refine reaches_mono (hS V C sp fs pos A hm hA hwf.1 hctx s1 (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨V1, ⟨hp1.out.fin ht, hp1.grow, hp1.within, hp1.stack, hp1.obj⟩⟩

end

end Vsa.Compiler
