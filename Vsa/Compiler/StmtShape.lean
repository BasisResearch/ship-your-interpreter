import Vsa.Compiler.StmtCases

/-!
# Shapes of compiled compound statements

The code of `if`, `while` and blocks as explicit concatenations, and the
control fragments both simulation directions share: running a condition and
its branch, and the scope a statement list leaves.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem cstmt_block (C : Ctx) (pos : Nat) (ss : List Stmt) :
    cstmt C pos (.block ss) = ((cseq ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ pos ss).1,
      (cseq ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ pos ss).2.2) := rfl

theorem cstmt_ifNone (C : Ctx) (pos : Nat) (c : Expr) (t : Stmt) :
    cstmt C pos (.ifStmt c t none) =
      (cexpr C.Γ 0 pos c ++ [.br .ne a0 0 (bSkip 1),
        .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1)
          (pos + (cexpr C.Γ 0 pos c).length + 2 +
            (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).1.length))] ++
        (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).1,
       (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).2) := rfl

theorem cstmt_ifSome (C : Ctx) (pos : Nat) (c : Expr) (t e : Stmt) :
    cstmt C pos (.ifStmt c t (some e)) =
      let cc := cexpr C.Γ 0 pos c
      let ct := cstmt C (pos + cc.length + 2) t
      let elsePos := pos + cc.length + 2 + ct.1.length + 1
      let ce := cstmt ⟨C.Γ, ct.2, C.brk, C.cont⟩ elsePos e
      (cc ++ [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + cc.length + 1) elsePos)] ++ ct.1 ++
        [.jal 0 (jOff (elsePos - 1) (elsePos + ce.1.length))] ++ ce.1, ce.2) := rfl

theorem cstmt_while (C : Ctx) (pos : Nat) (c : Expr) (b : Stmt) :
    cstmt C pos (.whileStmt c b) =
      let cc := cexpr C.Γ 0 pos c
      let bpos := pos + cc.length + 2
      let endPos := bpos + (cstmt ⟨C.Γ, C.next, 0, 0⟩ bpos b).1.length + 1
      let cb := cstmt ⟨C.Γ, C.next, endPos, pos⟩ bpos b
      (cc ++ [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + cc.length + 1) endPos)] ++ cb.1 ++
        [.jal 0 (jOff (bpos + cb.1.length) pos)], cb.2) := rfl

theorem cseq_tail : ∀ (ss : List Stmt) (C : Ctx) (pos : Nat) (f : List (String × Nat)) (g : Scope),
    C.Γ = f :: g → ∃ f', (cseq C pos ss).2.1 = f' :: g
  | [], C, pos, f, g, h => ⟨f, by simp [cseq, h]⟩
  | s :: ss, C, pos, f, g, h => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      rw [cseq_decl]
      obtain ⟨f0, g0, hΓ, hdi⟩ := declInfo_cases C x (by rw [h]; simp)
      rw [h] at hΓ; cases hΓ
      rcases hdi with ⟨i, -, hdi⟩ | ⟨-, hdi⟩
      · exact cseq_tail ss _ _ f g (by rw [hdi]; exact h)
      · exact cseq_tail ss _ _ _ g (by rw [hdi])
    · rw [cseq_other C pos s ss (fun x e he => hd ⟨x, e, he⟩)]
      exact cseq_tail ss _ _ f g h

/-- A block's context: a new empty innermost frame. -/
theorem At.block {code : List Ins} {C : Ctx} {pos : Nat} (h : At code C pos) :
    At code ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ pos := by
  refine ⟨h.lay, by simp, ?_, ?_, ?_, h.nextle, h.posok⟩
  · simpa [slots_cons] using h.nd
  · intro i hi; exact h.lt i (by simpa [slots_cons] using hi)
  · intro fr hfr x hx
    rcases List.mem_cons.mp hfr with rfl | hfr
    · rfl
    · exact h.nat fr hfr x hx

section
variable {code : List Ins}

/-- Evaluate a condition and branch on it: fall through when truthy, else jump to `L`.
Either the condition errors (and has no evaluation), or it evaluates. -/
theorem sim_cond {C : Ctx} {pos L : Nat} {c : Expr} {st : St} {d : Nat} {env : Addr} {A : AM}
    (hAt : At code C pos) (hc : CondE C.Γ.names c)
    (hseg : Seg code pos (cexpr C.Γ 0 pos c ++ [.br .ne a0 0 (bSkip 1),
      .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1) L)]))
    (hL : PosOK L) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A) :
    ∃ B, Star code A B ∧
      ((∃ st1 v, EvalE st d env c st1 v ∧ SR C.Γ env st1 B ∧ SameParents st.store st1.store ∧
          B.pc = pcOf (if v.truthy then pos + (cexpr C.Γ 0 pos c).length + 2 else L)) ∨
        (astep code B = some (.halt 70) ∧ ∀ st1 v, ¬ EvalE st d env c st1 v)) := by
  have hs := CondE.simple hc
  obtain ⟨hs1, hs2⟩ := hseg.append
  have hend := Seg.end_ok hAt.fits hseg (by simp)
  simp only [List.length_append, List.length_cons, List.length_nil] at hend
  obtain ⟨B1, r1, hB1⟩ := sim_expr hAt.lay hAt.nd hAt.slot_bound c hs 0 pos st d env A hc
    (by have := tdepth_le C.Γ c 0 pos hs; have := hend.small; omega) hs1
    (by unfold PosOK at *; omega) hA hsr.1
  rcases hB1 with ⟨v, st1, hev, hty, hout, hBo, hBpc, hB0, hBc, -⟩ | ⟨hh, hne⟩
  · have r2 := run_cond₀ hAt.fits hs2 hBpc (by unfold PosOK at *; omega) hL hB0
    refine ⟨_, r1.trans r2, .inl ⟨st1, v, hev, ⟨hBc, ?_⟩, EvalE.sameParents c hs hev, ?_⟩⟩
    · simp only [outStr]; rw [hBo, hout]; exact hsr.2
    · have := word_truthy hc hty
      by_cases ht : v.truthy
      · rw [if_pos ht, if_neg (fun h => by rw [this.mp h] at ht; cases ht)]
      · rw [if_neg ht, if_pos (this.mpr (by simpa using ht))]
  · exact ⟨B1, r1, .inr ⟨hh, fun st1 v => hne v st1⟩⟩

end

end Vsa.Compiler
