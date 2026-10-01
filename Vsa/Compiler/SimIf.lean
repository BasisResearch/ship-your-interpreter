import Vsa.Compiler.SimCond
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem MS.setpc {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {pc : BitVec 64} {L : GRegs} {m : Mem} {o : Array String}
    (h : MS code T V st d env Γ sp fs ⟨pc, L, m, o⟩) (pc' : BitVec 64) : MS code T V st d env Γ sp fs ⟨pc', L, m, o⟩ :=
  ⟨h.rel, h.img, h.clo, h.chn, h.out, h.ho, h.hf, h.henv, h.hsp, h.hdep, h.stk, h.hfal⟩

theorem SPost.cast {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr} {C : GCtx}
    {sp fs fin fin' : Nat} {A B : AM} {n : Nat} {st' : St} {t : Status} {V' : View}
    (hp : SPost code T V st d env C sp fs fin A n st' t V' B) (h : fin = fin') :
    SPost code T V st d env C sp fs fin' A n st' t V' B := h ▸ hp

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem SPost.jump {V : View} {st : St} {d : Nat} {env : Addr} {C : GCtx} {sp fs fin fin' : Nat} {A B : AM}
    {n : Nat} {st' : St} {t : Status} {V' : View}
    (hp : SPost code T V st d env C sp fs fin A n st' t V' B) (hseg : Seg code fin [J fin fin'])
    (hfin : PosOK fin) (hfin' : PosOK fin') :
    Reaches code B (fun B' => SPost code T V st d env C sp fs fin' A n st' t V' B') := by
  by_cases ht : t = .normal
  · subst ht
    obtain ⟨hpc, hm⟩ := hp.out
    obtain ⟨pc, L, m, o⟩ := B
    simp only at hpc hm; subst hpc
    apply run_jumps hR.fits hseg
    wp_simp [hfin, hfin']
    exact reach_here ⟨⟨rfl, hm.setpc _⟩, hp.grow, hp.within, hp.stack, hp.obj⟩
  · exact reach_here ⟨hp.out.fin ht, hp.grow, hp.within, hp.stack, hp.obj⟩

private theorem run_cond_split {st : St} {d : Nat} {env : Addr} {c : Expr} {st1 : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env c st1 v n) {V : View} {C : GCtx} {sp fs pos tgt : Nat} {A : AM}
    (hm : MS code T V st d env C.Γ sp fs A) (hA : A.pc = pcOf pos) (hwf : WfE T C.Γ c)
    (s1 : Seg code pos (gexpr T C.Γ 0 pos c))
    (s2 : Seg code (pos + (gexpr T C.Γ 0 pos c).length) [Call (pos + (gexpr T C.Γ 0 pos c).length) trPos])
    (s3 : Seg code (pos + (gexpr T C.Γ 0 pos c).length + 1)
      (jmpIfZero (pos + (gexpr T C.Γ 0 pos c).length + 1) tgt))
    (hP : PosOK (pos + (gexpr T C.Γ 0 pos c).length + 3)) (htgt : PosOK tgt) (htmp : 16 + 16 * tE c ≤ fs) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V1, SPost code T V st d env C sp fs (if v.truthy then pos + (gexpr T C.Γ 0 pos c).length + 3 else tgt)
        A n st1 .normal V1 B) :=
  run_cond hR hE hm hA hwf (seg_app_iff.mpr ⟨seg_app_iff.mpr ⟨s1, s2⟩, s3.cast (by simp; omega)⟩) hP htgt htmp

theorem sIfTrue {st : St} {d : Nat} {env : Addr} {c : Expr} {t : Stmt} {e : Option Stmt} {st1 st2 : St}
    {v : Value} {status : Status} {nc nt : Nat} (hE : ESpec code T st d env c st1 v nc) (htr : v.truthy = true)
    (hS : SSpec code T st1 d env t st2 status nt) : SSpec code T st d env (.ifStmt c t e) st2 status (nc + nt) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwt, hwe⟩ := hwf
  have htl : 16 + 16 * tE c ≤ fs ∧ 16 + 16 * tS t ≤ fs := by
    cases e <;> simp only [tS] at htmp <;> omega
  cases e
  all_goals
    have h := And.intro hseg hP
    simp only [gstmt, jmpIfZero, List.append_assoc, ↓segP_app, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd] at h
    simp only [gstmt, jmpIfZero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
    obtain ⟨⟨s1, -⟩, ⟨s2, -⟩, ⟨s3, p3⟩, ⟨sct, p4⟩, ⟨sJ, pJ⟩, -, p6⟩ := h
    refine ex_bind (run_cond_split hR hE hm hA hwc s1 s2 s3 p3 pJ htl.1) ?_
    rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
    · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
    rw [htr, if_pos rfl] at hp1
    obtain ⟨hpc1, hm1⟩ := hp1.out
    refine ex_bind (hS V1 C sp fs _ B hm1 hpc1 hwt hctx sct p4 htl.2) ?_
    rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
    · exact reach_here (.inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩)
    refine reaches_mono (SPost.jump hR (hp1.seq hp2 rfl) sJ p4 p6) ?_
    intro B'' hB''
    exact .inr ⟨V2, hB''.cast (by omega)⟩

theorem sIfFalse {st : St} {d : Nat} {env : Addr} {c : Expr} {t e : Stmt} {st1 st2 : St}
    {v : Value} {status : Status} {nc ne : Nat} (hE : ESpec code T st d env c st1 v nc) (hfa : v.truthy = false)
    (hS : SSpec code T st1 d env e st2 status ne) :
    SSpec code T st d env (.ifStmt c t (some e)) st2 status (nc + ne) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwt, hwe⟩ := hwf
  simp only [tS] at htmp
  have h := And.intro hseg hP
  simp only [gstmt, jmpIfZero, List.append_assoc, ↓segP_app, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at h
  simp only [gstmt, jmpIfZero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
  obtain ⟨⟨s1, -⟩, ⟨s2, -⟩, ⟨s3, p3⟩, -, ⟨-, pJ⟩, sce, p6⟩ := h
  refine ex_bind (run_cond_split hR hE hm hA hwc s1 s2 s3 p3 pJ (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  rw [hfa] at hp1
  simp only [Bool.false_eq_true, if_false] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  refine reaches_mono (hS V1 C sp fs _ B hm1 hpc1 hwe hctx sce p6 (by omega)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩
  · exact .inr ⟨V2, (hp1.seq hp2 rfl).cast (by omega)⟩

theorem sIfNone {st : St} {d : Nat} {env : Addr} {c : Expr} {t : Stmt} {st1 : St} {v : Value} {nc : Nat}
    (hE : ESpec code T st d env c st1 v nc) (hfa : v.truthy = false) :
    SSpec code T st d env (.ifStmt c t none) st1 .normal nc := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwt, hwe⟩ := hwf
  simp only [tS] at htmp
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨h5, sce⟩ := hseg.append
  obtain ⟨h4, sJ⟩ := h5.append
  obtain ⟨hcond, sct⟩ := h4.append
  simp only [List.length_append, List.length_singleton, jmpIfZero, List.length_cons, List.length_nil] at sct sJ sce hP ⊢
  refine reaches_mono (run_cond hR hE hm hA hwc hcond (posOK_le hP (by omega)) (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact .inl ⟨h1, h2⟩
  rw [hfa] at hp1
  simp only [Bool.false_eq_true, if_false] at hp1
  exact .inr ⟨V1, hp1.cast (by omega)⟩

end

end Vsa.Compiler
