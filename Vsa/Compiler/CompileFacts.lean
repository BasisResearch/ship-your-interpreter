import Vsa.Compiler.Compile
import Vsa.Compiler.Subset
import Vsa.Compiler.ExprSim

/-!
# Structural facts about the compiler's output

Temporary depth is bounded by the code length of an expression, and the slot
counter grows by at most one per emitted instruction; so in fitting code every
slot and temporary lies in its memory region.
-/

namespace Vsa.Compiler

open Vsa.While

theorem li_length_pos (rd : Nat) (n : BitVec 64) : 0 < (li rd n).length := by
  unfold li; split <;> simp

theorem tdepth_le (Γ : Scope) : ∀ (e : Expr) (k pos : Nat), Simple e →
    tdepth e ≤ (cexpr Γ k pos e).length
  | .int _, _, _, _ => Nat.zero_le _
  | .bool _, _, _, _ => Nat.zero_le _
  | .var _, _, _, _ => Nat.zero_le _
  | .assign _ e, k, pos, hs => by
    have := tdepth_le Γ e k pos hs
    simp only [tdepth, cexpr, List.length_append]; omega
  | .binary _ l r, k, pos, hs => by
    have h1 := tdepth_le Γ l k pos hs.1
    have h2 := tdepth_le Γ r (k + 1)
      (pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length) hs.2
    simp only [List.length_append, List.length_cons, List.length_nil] at h2
    simp only [tdepth, cexpr, List.length_append, List.length_cons, List.length_nil]
    omega
  | .unary .neg e, k, pos, hs => by
    have := tdepth_le Γ e k pos hs
    simp only [tdepth, cexpr, List.length_append]; omega
  | .unary .not e, k, pos, hs => by
    have := tdepth_le Γ e k pos hs
    simp only [tdepth, cexpr, List.length_append]; omega
  | .str _, _, _, h => h.elim
  | .null, _, _, h => h.elim
  | .logical _ _ _, _, _, h => h.elim
  | .call _ _, _, _, h => h.elim
  | .fn _ _ _, _, _, h => h.elim

theorem cexpr_pos (Γ : Scope) : ∀ (e : Expr) (k pos : Nat), Simple e →
    0 < (cexpr Γ k pos e).length
  | .int n, _, _, _ => li_length_pos _ _
  | .bool _, _, _, _ => by simp [cexpr]
  | .var _, _, _, _ => by simp [cexpr]
  | .assign _ e, k, pos, hs => by simp [cexpr]; omega
  | .binary _ l r, k, pos, hs => by
    have := cexpr_pos Γ l k pos hs.1
    simp only [cexpr, List.length_append]; omega
  | .unary .neg e, k, pos, hs => by simp [cexpr]
  | .unary .not e, k, pos, hs => by simp [cexpr]
  | .str _, _, _, h => h.elim
  | .null, _, _, h => h.elim
  | .logical _ _ _, _, _, h => h.elim
  | .call _ _, _, _, h => h.elim
  | .fn _ _ _, _, _, h => h.elim

mutual

theorem cstmt_next (C : Ctx) (pos : Nat) : ∀ (s : Stmt),
    C.next ≤ (cstmt C pos s).2 ∧ (cstmt C pos s).2 ≤ C.next + (cstmt C pos s).1.length
  | .expr e => by
    cases e with
    | call f args =>
      cases f with
      | var x => simp [cstmt]
      | _ => simp [cstmt]
    | _ => simp [cstmt]
  | .block ss => by
    have := cseq_next { C with Γ := [] :: C.Γ } pos ss
    simp only [cstmt]; exact this
  | .ifStmt c t e => by
    cases e with
    | none =>
      have := cstmt_next C (pos + (cexpr C.Γ 0 pos c).length + 2) t
      simp only [cstmt, List.length_append]; omega
    | some e =>
      have h1 := cstmt_next C (pos + (cexpr C.Γ 0 pos c).length + 2) t
      have h2 := cstmt_next { C with next := (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).2 }
        (pos + (cexpr C.Γ 0 pos c).length + 2 +
          (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).1.length + 1) e
      simp only [cstmt, List.length_append] at h2 ⊢; omega
  | .whileStmt c b => by
    have := cstmt_next ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩
      (pos + (cexpr C.Γ 0 pos c).length + 2) b
    dsimp only at this
    simp only [cstmt, List.length_append]; omega
  | .varDecl _ _ => by simp [cstmt]
  | .forStmt _ _ _ _ => by simp [cstmt]
  | .ret _ => by simp [cstmt]
  | .brk => by simp [cstmt]
  | .cont => by simp [cstmt]

theorem cseq_next (C : Ctx) (pos : Nat) : ∀ (ss : List Stmt),
    C.next ≤ (cseq C pos ss).2.2 ∧ (cseq C pos ss).2.2 ≤ C.next + (cseq C pos ss).1.length
  | [] => by simp [cseq]
  | s :: ss => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      obtain ⟨Γ0, n0, b0, c0⟩ := C
      cases Γ0 with
      | nil =>
        have ih := cseq_next ⟨[[(x, n0)]], n0 + 1, b0, c0⟩ (pos + ((cexpr [] 0 pos e) ++
          liN s2 (varAddr n0) ++ [Ins.sd a0 s2]).length) ss
        simp only [cseq]
        simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
        generalize cseq _ _ ss = R at ih ⊢
        obtain ⟨c, G, n⟩ := R
        dsimp only at ih ⊢
        omega
      | cons f g =>
        cases hl : f.lookup x with
        | some i =>
          have ih := cseq_next ⟨f :: g, n0, b0, c0⟩ (pos + ((cexpr (f :: g) 0 pos e) ++
            liN s2 (varAddr i) ++ [Ins.sd a0 s2]).length) ss
          simp only [cseq, hl]
          simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
          generalize cseq _ _ ss = R at ih ⊢
          obtain ⟨c, G, n⟩ := R
          dsimp only at ih ⊢
          omega
        | none =>
          have ih := cseq_next ⟨((x, n0) :: f) :: g, n0 + 1, b0, c0⟩ (pos + ((cexpr (f :: g) 0 pos e) ++
            liN s2 (varAddr n0) ++ [Ins.sd a0 s2]).length) ss
          simp only [cseq, hl]
          simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
          generalize cseq _ _ ss = R at ih ⊢
          obtain ⟨c, G, n⟩ := R
          dsimp only at ih ⊢
          omega
    · have hc : cseq C pos (s :: ss) = ((cstmt C pos s).1 ++ (cseq { C with next := (cstmt C pos s).2 }
          (pos + (cstmt C pos s).1.length) ss).1, (cseq { C with next := (cstmt C pos s).2 }
          (pos + (cstmt C pos s).1.length) ss).2) := by
        cases s with
        | varDecl x i =>
          cases i with
          | some e => exact absurd ⟨x, e, rfl⟩ hd
          | none => rfl
        | _ => rfl
      rw [hc]
      have h1 := cstmt_next C pos s
      have ih := cseq_next { C with next := (cstmt C pos s).2 } (pos + (cstmt C pos s).1.length) ss
      dsimp only at ih
      simp only [List.length_append]
      omega

end

mutual

/-- Code length and slot counter do not depend on the loop targets. -/
theorem cstmt_targets (C : Ctx) (b c : Nat) (pos : Nat) : ∀ (s : Stmt),
    (cstmt ⟨C.Γ, C.next, b, c⟩ pos s).1.length = (cstmt C pos s).1.length ∧
      (cstmt ⟨C.Γ, C.next, b, c⟩ pos s).2 = (cstmt C pos s).2
  | .expr e => by
    cases e with
    | call f args =>
      cases f with
      | var x => simp [cstmt]
      | _ => simp [cstmt]
    | _ => simp [cstmt]
  | .block ss => by
    have := cseq_targets ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ b c pos ss
    simp only [cstmt]; exact ⟨this.1, this.2.2⟩
  | .ifStmt cnd t e => by
    have h1 := cstmt_targets C b c (pos + (cexpr C.Γ 0 pos cnd).length + 2) t
    cases e with
    | none => simp only [cstmt, List.length_append, List.length_cons, List.length_nil]; omega
    | some e =>
      have h2 := cstmt_targets ⟨C.Γ, (cstmt C (pos + (cexpr C.Γ 0 pos cnd).length + 2) t).2, C.brk, C.cont⟩
        b c (pos + (cexpr C.Γ 0 pos cnd).length + 2 +
          (cstmt C (pos + (cexpr C.Γ 0 pos cnd).length + 2) t).1.length + 1) e
      dsimp only at h2
      simp only [cstmt, List.length_append, List.length_cons, List.length_nil, h1.1, h1.2]
      exact ⟨by rw [h2.1], h2.2⟩
  | .whileStmt cnd body => by
    have h1 := cstmt_targets ⟨C.Γ, C.next, 0, 0⟩ b c (pos + (cexpr C.Γ 0 pos cnd).length + 2) body
    have h2 := cstmt_targets C 0 0 (pos + (cexpr C.Γ 0 pos cnd).length + 2) body
    have h3 := cstmt_targets C (pos + (cexpr C.Γ 0 pos cnd).length + 2 +
      (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos cnd).length + 2) body).1.length + 1) pos
      (pos + (cexpr C.Γ 0 pos cnd).length + 2) body
    have h4 := cstmt_targets C (pos + (cexpr C.Γ 0 pos cnd).length + 2 +
      (cstmt ⟨C.Γ, C.next, b, c⟩ (pos + (cexpr C.Γ 0 pos cnd).length + 2) body).1.length + 1) pos
      (pos + (cexpr C.Γ 0 pos cnd).length + 2) body
    dsimp only at h1 h2 h3 h4
    simp only [cstmt, List.length_append, List.length_cons, List.length_nil]
    all_goals trivial
  | .varDecl _ _ => by simp [cstmt]
  | .forStmt _ _ _ _ => by simp [cstmt]
  | .ret _ => by simp [cstmt]
  | .brk => by simp [cstmt]
  | .cont => by simp [cstmt]

theorem cseq_targets (C : Ctx) (b c : Nat) (pos : Nat) : ∀ (ss : List Stmt),
    (cseq ⟨C.Γ, C.next, b, c⟩ pos ss).1.length = (cseq C pos ss).1.length ∧
      (cseq ⟨C.Γ, C.next, b, c⟩ pos ss).2.1 = (cseq C pos ss).2.1 ∧
      (cseq ⟨C.Γ, C.next, b, c⟩ pos ss).2.2 = (cseq C pos ss).2.2
  | [] => by simp [cseq]
  | s :: ss => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      obtain ⟨Γ0, n0, b0, c0⟩ := C
      cases Γ0 with
      | nil =>
        have ih := cseq_targets ⟨[[(x, n0)]], n0 + 1, b0, c0⟩ b c (pos + ((cexpr [] 0 pos e) ++
          liN s2 (varAddr n0) ++ [Ins.sd a0 s2]).length) ss
        dsimp only at ih
        simp only [cseq]; simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
        simpa using ih
      | cons f g =>
        cases hl : f.lookup x with
        | some i =>
          have ih := cseq_targets ⟨f :: g, n0, b0, c0⟩ b c (pos + ((cexpr (f :: g) 0 pos e) ++
            liN s2 (varAddr i) ++ [Ins.sd a0 s2]).length) ss
          dsimp only at ih
          simp only [cseq, hl]; simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
          simpa using ih
        | none =>
          have ih := cseq_targets ⟨((x, n0) :: f) :: g, n0 + 1, b0, c0⟩ b c
            (pos + ((cexpr (f :: g) 0 pos e) ++ liN s2 (varAddr n0) ++ [Ins.sd a0 s2]).length) ss
          dsimp only at ih
          simp only [cseq, hl]; simp only [List.length_append, List.length_cons, List.length_nil] at ih ⊢
          simpa using ih
    · have hc : ∀ C' : Ctx, cseq C' pos (s :: ss) = ((cstmt C' pos s).1 ++
          (cseq { C' with next := (cstmt C' pos s).2 } (pos + (cstmt C' pos s).1.length) ss).1,
          (cseq { C' with next := (cstmt C' pos s).2 } (pos + (cstmt C' pos s).1.length) ss).2) := by
        intro C'
        cases s with
        | varDecl x i =>
          cases i with
          | some e => exact absurd ⟨x, e, rfl⟩ hd
          | none => rfl
        | _ => rfl
      rw [hc, hc]
      have h1 := cstmt_targets C b c pos s
      have ih := cseq_targets ⟨C.Γ, (cstmt C pos s).2, C.brk, C.cont⟩ b c
        (pos + (cstmt C pos s).1.length) ss
      dsimp only at ih ⊢
      rw [h1.1, h1.2]
      simp only [List.length_append]
      exact ⟨by rw [ih.1, h1.1], ih.2.1, ih.2.2⟩

end

end Vsa.Compiler
