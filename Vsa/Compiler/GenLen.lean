import Vsa.Compiler.CodeGen

/-!
# Code lengths do not depend on exit targets

The code generator computes the length of a loop body or function body with
placeholder exit targets and then compiles it with the real ones; the lengths
agree because only the frame counts of the exits enter the code's shape.
-/

namespace Vsa.Compiler

open Vsa.While

/-- Two contexts that differ at most in their exit targets. -/
structure GCtx.Sh (C C' : GCtx) : Prop where
  Γ : C.Γ = C'.Γ
  blk : C.blk = C'.blk
  brk : C.brk.map Prod.snd = C'.brk.map Prod.snd
  cont : C.cont.map Prod.snd = C'.cont.map Prod.snd
  ret : C.ret.map Prod.snd = C'.ret.map Prod.snd

theorem exitTo_length (blk pos pos' : Nat) (t t' : Option (Nat × Nat)) (h : t.map Prod.snd = t'.map Prod.snd) :
    (exitTo blk pos t).length = (exitTo blk pos' t').length := by
  cases t with
  | none => cases t' with
    | none => rfl
    | some _ => simp at h
  | some p => cases t' with
    | none => simp at h
    | some p' =>
      obtain ⟨a, b⟩ := p; obtain ⟨a', b'⟩ := p'
      simp at h; subst h
      simp [exitTo]

theorem GCtx.Sh.loop {C C' : GCtx} (h : C.Sh C') (b c b' c' : Nat) : (C.loop b c).Sh (C'.loop b' c') :=
  ⟨h.Γ, h.blk, by simp [GCtx.loop, h.blk], by simp [GCtx.loop, h.blk], h.ret⟩

theorem GCtx.Sh.enter {C C' : GCtx} (h : C.Sh C') (L : List String) : (C.enter L).Sh (C'.enter L) :=
  ⟨by simp [GCtx.enter, h.Γ], by simp [GCtx.enter, h.blk], h.brk, h.cont, h.ret⟩

theorem GCtx.Sh.swallow {C C' : GCtx} (h : C.Sh C') (t t' : Nat) : (C.swallow t).Sh (C'.swallow t') :=
  ⟨h.Γ, h.blk, by simp [GCtx.swallow, h.blk], by simp [GCtx.swallow, h.blk], by simp [GCtx.swallow, h.blk]⟩

mutual
theorem gstmt_len (T : List String) {C C' : GCtx} (h : C.Sh C') (pos : Nat) :
    ∀ s : Stmt, (gstmt T C pos s).length = (gstmt T C' pos s).length
  | .expr e => by simp only [gstmt, h.Γ]
  | .varDecl x i => by cases i <;> simp only [gstmt, h.Γ]
  | .block ss => by
    simp only [gstmt, List.length_append]
    rw [gseq_len T (h.enter _) _ ss]
  | .ifStmt c t none => by
    simp only [gstmt, List.length_append, h.Γ]
    rw [gstmt_len T h _ t]
  | .ifStmt c t (some e) => by
    simp only [gstmt, List.length_append, h.Γ]
    rw [gstmt_len T h _ t, gstmt_len T h _ e]
  | .whileStmt c b => by
    simp only [gstmt, List.length_append, h.Γ]
    rw [gstmt_len T (h.loop 0 0 0 0) _ b, gstmt_len T (h.loop _ _ _ _) _ b]
  | .forStmt none c st b => by
    have e2 : ∀ x y p, (gstmt T ((C.enter (forNames none b)).loop x y) p b).length =
        (gstmt T ((C'.enter (forNames none b)).loop x y) p b).length :=
      fun x y p => gstmt_len T ((h.enter _).loop x y x y) p b
    have eΓ : (C.enter (forNames none b)).Γ = (C'.enter (forNames none b)).Γ := (h.enter _).Γ
    cases c <;> cases st <;> simp only [gstmt, List.length_append, e2, eΓ]
  | .forStmt (some i) c st b => by
    have e1 : ∀ x p, (gstmt T ((C.enter (forNames (some i) b)).swallow x) p i).length =
        (gstmt T ((C'.enter (forNames (some i) b)).swallow x) p i).length :=
      fun x p => gstmt_len T ((h.enter _).swallow x x) p i
    have e2 : ∀ x y p, (gstmt T ((C.enter (forNames (some i) b)).loop x y) p b).length =
        (gstmt T ((C'.enter (forNames (some i) b)).loop x y) p b).length :=
      fun x y p => gstmt_len T ((h.enter _).loop x y x y) p b
    have eΓ : (C.enter (forNames (some i) b)).Γ = (C'.enter (forNames (some i) b)).Γ := (h.enter _).Γ
    cases c <;> cases st <;> simp only [gstmt, List.length_append, e1, e2, eΓ]
  | .ret none => by
    simp only [gstmt, List.length_append, h.blk]
    rw [exitTo_length _ _ _ _ _ h.ret]
  | .ret (some e) => by
    simp only [gstmt, List.length_append, h.blk, h.Γ]
    rw [exitTo_length _ _ _ _ _ h.ret]
  | .brk => by simp only [gstmt]; rw [h.blk]; exact exitTo_length _ _ _ _ _ h.brk
  | .cont => by simp only [gstmt]; rw [h.blk]; exact exitTo_length _ _ _ _ _ h.cont

theorem gseq_len (T : List String) {C C' : GCtx} (h : C.Sh C') (pos : Nat) :
    ∀ ss : List Stmt, (gseq T C pos ss).length = (gseq T C' pos ss).length
  | [] => rfl
  | s :: ss => by
    simp only [gseq, List.length_append]
    rw [gstmt_len T h pos s, gseq_len T h _ ss]
end

end Vsa.Compiler
