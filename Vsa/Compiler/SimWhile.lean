import Vsa.Compiler.SimIf

/-!
# Forward simulation: `while`
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem ExitAt.here {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env : Addr} {C : GCtx}
    {sp fs x : Nat} {B : AM} (h : ExitAt code T V' st' d env C sp fs (some (x, C.blk)) B) :
    B.pc = pcOf x ∧ MS code T V' st' d env C.Γ sp fs B := by
  obtain ⟨h1, h2⟩ := h
  simp only [Nat.sub_self, List.drop_zero] at h2
  exact ⟨h1, h2⟩

theorem StOut.loop_ret {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env : Addr} {C : GCtx}
    {sp fs fin fin' b c : Nat} {B : AM} {v : Value}
    (h : StOut code T V' st' d env (C.loop b c) sp fs fin B (.ret v)) :
    StOut code T V' st' d env C sp fs fin' B (.ret v) := h

theorem CtxOK.loop {C : GCtx} (h : CtxOK C) {b c : Nat} (hb : PosOK b) (hc : PosOK c) : CtxOK (C.loop b c) where
  blk := h.blk
  brk p dt e := by
    have e' : some (b, C.blk) = some (p, dt) := e
    cases e'; exact ⟨Nat.le_refl _, hb⟩
  cont p dt e := by
    have e' : some (c, C.blk) = some (p, dt) := e
    cases e'; exact ⟨Nat.le_refl _, hc⟩
  ret := h.ret

/-- The start of a `while` statement's body. -/
def wBody (T : List String) (C : GCtx) (pos : Nat) (c : Expr) : Nat := pos + (gexpr T C.Γ 0 pos c).length + 3

/-- The exit of a `while` statement. -/
def wExit (T : List String) (C : GCtx) (pos : Nat) (c : Expr) (b : Stmt) : Nat :=
  wBody T C pos c + (gstmt T (C.loop 0 0) (wBody T C pos c) b).length + 1

/-- The pieces of a `while` statement's code. -/
theorem while_segs {code : List Ins} {T : List String} {C : GCtx} {pos : Nat} {c : Expr} {b : Stmt}
    (hseg : Seg code pos (gstmt T C pos (.whileStmt c b))) :
    Seg code pos (gexpr T C.Γ 0 pos c ++ [Call (pos + (gexpr T C.Γ 0 pos c).length) trPos] ++
      jmpIfZero (pos + (gexpr T C.Γ 0 pos c).length + 1) (wExit T C pos c b)) ∧
    Seg code (wBody T C pos c) (gstmt T (C.loop (wExit T C pos c b) pos) (wBody T C pos c) b) ∧
    Seg code (wExit T C pos c b - 1) [J (wExit T C pos c b - 1) pos] ∧
    (gstmt T C pos (.whileStmt c b)).length = wExit T C pos c b - pos ∧
    (gstmt T (C.loop (wExit T C pos c b) pos) (wBody T C pos c) b).length = wExit T C pos c b - 1 - wBody T C pos c ∧
    pos + 3 ≤ wBody T C pos c ∧ wBody T C pos c < wExit T C pos c b := by
  have hl := gstmt_len T (GCtx.Sh.loop ⟨rfl, rfl, rfl, rfl, rfl⟩ (wExit T C pos c b) pos 0 0 :
      (C.loop _ pos).Sh (C.loop 0 0)) (wBody T C pos c) b
  simp only [gstmt] at hseg ⊢
  obtain ⟨h4, sJ⟩ := hseg.append
  obtain ⟨hcond, sb⟩ := h4.append
  simp only [wExit, wBody] at hl ⊢
  simp only [List.length_append, jmpIfZero, List.length_cons, List.length_nil, hl] at sb sJ
  refine ⟨hcond, sb.cast (by omega), sJ.cast (by omega), ?_, by rw [hl]; omega, by omega, by omega⟩
  simp only [List.length_append, jmpIfZero, List.length_cons, List.length_nil, hl]
  omega

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR


theorem sWhileFalse {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {st1 : St} {v : Value} {nc : Nat}
    (hE : ESpec code T st d env c st1 v nc) (hfa : v.truthy = false) :
    SSpec code T st d env (.whileStmt c b) st1 .normal nc := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwb⟩ := hwf
  simp only [tS] at htmp
  obtain ⟨hcond, sb, sJ, hlen, hlb, hw1, hw2⟩ := while_segs hseg
  rw [hlen] at hP ⊢
  refine reaches_mono (run_cond hR hE hm hA hwc hcond (posOK_le hP (by have hwb : wBody T C pos c = pos + (gexpr T C.Γ 0 pos c).length + 3 := rfl; omega))
    (posOK_le hP (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact .inl ⟨h1, h2⟩
  rw [hfa] at hp1
  simp only [Bool.false_eq_true, if_false] at hp1
  exact .inr ⟨V1, hp1.cast (by omega)⟩

theorem sWhileBreak {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {st1 st2 : St} {v : Value}
    {nc nb : Nat} (hE : ESpec code T st d env c st1 v nc) (htr : v.truthy = true)
    (hS : SSpec code T st1 d env b st2 .brk nb) :
    SSpec code T st d env (.whileStmt c b) st2 .normal (nc + nb) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwb⟩ := hwf
  simp only [tS] at htmp
  obtain ⟨hcond, sb, sJ, hlen, hlb, hw1, hw2⟩ := while_segs hseg
  rw [hlen] at hP ⊢
  have hPx : PosOK (wExit T C pos c b) := posOK_le hP (by omega)
  refine ex_bind (run_cond hR hE hm hA hwc hcond (posOK_le hP (by have hwb : wBody T C pos c = pos + (gexpr T C.Γ 0 pos c).length + 3 := rfl; omega)) hPx
    (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  rw [htr, if_pos rfl] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  refine reaches_mono (hS V1 (C.loop (wExit T C pos c b) pos) sp fs (wBody T C pos c) B hm1 hpc1 hwb
    (hctx.loop hPx (posOK_le hP (by omega))) sb (by rw [hlb]; exact posOK_le hP (by omega)) (by omega)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩
  obtain ⟨hpc2, hm2⟩ := ExitAt.here hp2.out
  have hp2' : SPost code T V1 st1 d env C sp fs (wExit T C pos c b) B nb st2 .normal V2 B' :=
    ⟨⟨hpc2, hm2⟩, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩
  exact .inr ⟨V2, (hp1.seq hp2' rfl).cast (by omega)⟩

theorem sWhileRet {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {st1 st2 : St} {v rv : Value}
    {nc nb : Nat} (hE : ESpec code T st d env c st1 v nc) (htr : v.truthy = true)
    (hS : SSpec code T st1 d env b st2 (.ret rv) nb) :
    SSpec code T st d env (.whileStmt c b) st2 (.ret rv) (nc + nb) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hwc, hwb⟩ := hwf
  simp only [tS] at htmp
  obtain ⟨hcond, sb, sJ, hlen, hlb, hw1, hw2⟩ := while_segs hseg
  rw [hlen] at hP ⊢
  have hPx : PosOK (wExit T C pos c b) := posOK_le hP (by omega)
  refine ex_bind (run_cond hR hE hm hA hwc hcond (posOK_le hP (by have hwb : wBody T C pos c = pos + (gexpr T C.Γ 0 pos c).length + 3 := rfl; omega)) hPx
    (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  rw [htr, if_pos rfl] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  refine reaches_mono (hS V1 (C.loop (wExit T C pos c b) pos) sp fs (wBody T C pos c) B hm1 hpc1 hwb
    (hctx.loop hPx (posOK_le hP (by omega))) sb (by rw [hlb]; exact posOK_le hP (by omega)) (by omega)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩
  exact .inr ⟨V2, hp1.seq ⟨hp2.out.loop_ret, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩ rfl⟩

theorem sWhileLoop {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {st1 st2 st3 : St} {v : Value}
    {status status' : Status} {nc nb nr : Nat} (hE : ESpec code T st d env c st1 v nc) (htr : v.truthy = true)
    (hS : SSpec code T st1 d env b st2 status nb) (hst : status = .normal ∨ status = .cont)
    (hW : SSpec code T st2 d env (.whileStmt c b) st3 status' nr) :
    SSpec code T st d env (.whileStmt c b) st3 status' (nc + nb + nr) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  have hwf' := hwf
  obtain ⟨hwc, hwb⟩ := hwf
  have htmp' := htmp
  simp only [tS] at htmp
  have hseg' := hseg
  have hP' := hP
  obtain ⟨hcond, sb, sJ, hlen, hlb, hw1, hw2⟩ := while_segs hseg
  rw [hlen] at hP
  have hPx : PosOK (wExit T C pos c b) := posOK_le hP (by omega)
  refine ex_bind (run_cond hR hE hm hA hwc hcond (posOK_le hP (by have hwb : wBody T C pos c = pos + (gexpr T C.Γ 0 pos c).length + 3 := rfl; omega)) hPx
    (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  rw [htr, if_pos rfl] at hp1
  obtain ⟨hpc1, hm1⟩ := hp1.out
  have hPpos : PosOK pos := posOK_le hP (by omega)
  refine ex_bind (hS V1 (C.loop (wExit T C pos c b) pos) sp fs (wBody T C pos c) B hm1 hpc1 hwb
    (hctx.loop hPx hPpos) sb (by rw [hlb]; exact posOK_le hP (by omega)) (by omega)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact reach_here (.inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩)
  -- back to the head
  have hback : Reaches code B' (fun B'' => SPost code T V1 st1 d env C sp fs pos B nb st2 .normal V2 B'') := by
    rcases hst with rfl | rfl
    · obtain ⟨hpc2, hm2⟩ := hp2.out
      rw [hlb, show wBody T C pos c + (wExit T C pos c b - 1 - wBody T C pos c) = wExit T C pos c b - 1 by omega]
        at hpc2
      obtain ⟨pc2, L2, m2, o2⟩ := B'
      simp only at hpc2 hm2; subst hpc2
      apply run_jumps hR.fits sJ
      wp_simp [posOK_le hP (by omega : wExit T C pos c b - 1 ≤ _), hPpos]
      exact reach_here ⟨⟨rfl, hm2.setpc _⟩, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩
    · obtain ⟨hpc2, hm2⟩ := ExitAt.here hp2.out
      exact reach_here ⟨⟨hpc2, hm2⟩, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩
  refine ex_bind hback fun B'' hp2' => ?_
  obtain ⟨hpc3, hm3⟩ := hp2'.out
  refine reaches_mono (hW V2 C sp fs pos B'' hm3 hpc3 hwf' hctx hseg' hP' htmp') ?_
  rintro B3 (⟨h1, h2⟩ | ⟨V3, hp3⟩)
  · exact .inl ⟨h1, Room.not_within h2 (hp1.within.add hp2'.within) (by omega)⟩
  · exact .inr ⟨V3, (hp1.seq hp2' rfl).seq hp3 rfl⟩

end

end Vsa.Compiler
