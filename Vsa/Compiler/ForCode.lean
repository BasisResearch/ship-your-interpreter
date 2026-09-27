import Vsa.Compiler.SimWhile

/-!
# The code of a `for` statement in pieces

`gstmt_for` names the positions of a `for` statement's code: the frame entry,
the initializer at `pos + 4`, the condition at `fHd`, the body at `fPb`, the
step at `fPs`, the back jump, and the frame exit at `fEx`.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

section
variable (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt) (cnd : Option Expr) (step : Option Expr)
  (b : Stmt)

def fC1 : GCtx := C.enter (forNames init b)

def fLi : Nat := match init with
  | some s => (gstmt T ((fC1 C init b).swallow 0) (pos + 4) s).length
  | none => 0

def fHd : Nat := pos + 4 + fLi T C pos init b

def fLc : Nat := match cnd with
  | some c => (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length + 3
  | none => 0

def fPb : Nat := fHd T C pos init b + fLc T C pos init cnd b

def fPs : Nat := fPb T C pos init cnd b + (gstmt T ((fC1 C init b).loop 0 0) (fPb T C pos init cnd b) b).length

def fCs : List Ins := match step with
  | some e => gexpr T (fC1 C init b).Γ 0 (fPs T C pos init cnd b) e
  | none => []

def fEx : Nat := fPs T C pos init cnd b + (fCs T C pos init cnd step b).length + 1

def fCi : List Ins := match init with
  | some s => gstmt T ((fC1 C init b).swallow (fHd T C pos init b)) (pos + 4) s
  | none => []

def fCc : List Ins := match cnd with
  | some c => gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c ++
      [Call (fHd T C pos init b + (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length) trPos] ++
      jmpIfZero (fHd T C pos init b + (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length + 1)
        (fEx T C pos init cnd step b)
  | none => []

theorem gstmt_for : gstmt T C pos (.forStmt init cnd step b) =
    enterFrame (forNames init b) pos ++ fCi T C pos init b ++ fCc T C pos init cnd step b ++
      gstmt T ((fC1 C init b).loop (fEx T C pos init cnd step b) (fPs T C pos init cnd b))
        (fPb T C pos init cnd b) b ++ fCs T C pos init cnd step b ++
      [J (fPs T C pos init cnd b + (fCs T C pos init cnd step b).length) (fHd T C pos init b), .ld envR envR] := by
  cases init <;> cases cnd <;> cases step <;> rfl

theorem fCi_length : (fCi T C pos init b).length = fLi T C pos init b := by
  cases init with
  | none => rfl
  | some s =>
    simp only [fCi, fLi]
    exact gstmt_len T (GCtx.Sh.swallow ⟨rfl, rfl, rfl, rfl, rfl⟩ _ 0) _ s

theorem fCc_length : (fCc T C pos init cnd step b).length = fLc T C pos init cnd b := by
  cases cnd with
  | none => rfl
  | some c => simp [fCc, fLc, jmpIfZero]

theorem fBody_length : (gstmt T ((fC1 C init b).loop (fEx T C pos init cnd step b) (fPs T C pos init cnd b))
    (fPb T C pos init cnd b) b).length = fPs T C pos init cnd b - fPb T C pos init cnd b := by
  rw [gstmt_len T (GCtx.Sh.loop ⟨rfl, rfl, rfl, rfl, rfl⟩ _ _ 0 0)]
  simp [fPs]

end

/-- The pieces of a `for` statement's code in place. -/
structure ForSegs (code : List Ins) (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt)
    (cnd step : Option Expr) (b : Stmt) : Prop where
  ent : Seg code pos (enterFrame (forNames init b) pos)
  ci : Seg code (pos + 4) (fCi T C pos init b)
  cc : Seg code (fHd T C pos init b) (fCc T C pos init cnd step b)
  body : Seg code (fPb T C pos init cnd b)
    (gstmt T ((fC1 C init b).loop (fEx T C pos init cnd step b) (fPs T C pos init cnd b)) (fPb T C pos init cnd b) b)
  cs : Seg code (fPs T C pos init cnd b) (fCs T C pos init cnd step b)
  jmp : Seg code (fEx T C pos init cnd step b - 1)
    [J (fPs T C pos init cnd b + (fCs T C pos init cnd step b).length) (fHd T C pos init b)]
  lv : Seg code (fEx T C pos init cnd step b) [.ld envR envR]

theorem for_len (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) :
    pos + (gstmt T C pos (.forStmt init cnd step b)).length = fEx T C pos init cnd step b + 1 := by
  rw [gstmt_for]
  simp only [List.length_append, fCi_length, fCc_length, fBody_length, List.length_cons, List.length_nil]
  have : (enterFrame (forNames init b) pos).length = 4 := rfl
  rw [this]
  have e1 : fHd T C pos init b = pos + 4 + fLi T C pos init b := rfl
  have e2 : fPb T C pos init cnd b = fHd T C pos init b + fLc T C pos init cnd b := rfl
  have e3 : fPs T C pos init cnd b = fPb T C pos init cnd b +
    (gstmt T ((fC1 C init b).loop 0 0) (fPb T C pos init cnd b) b).length := rfl
  have e4 : fEx T C pos init cnd step b = fPs T C pos init cnd b + (fCs T C pos init cnd step b).length + 1 := rfl
  omega

theorem for_order (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt) (cnd step : Option Expr)
    (b : Stmt) : pos + 4 ≤ fHd T C pos init b ∧ fHd T C pos init b ≤ fPb T C pos init cnd b ∧
      fPb T C pos init cnd b ≤ fPs T C pos init cnd b ∧ fPs T C pos init cnd b + (fCs T C pos init cnd step b).length + 1
        = fEx T C pos init cnd step b := by
  have e1 : fHd T C pos init b = pos + 4 + fLi T C pos init b := rfl
  have e2 : fPb T C pos init cnd b = fHd T C pos init b + fLc T C pos init cnd b := rfl
  have e3 : fPs T C pos init cnd b = fPb T C pos init cnd b +
    (gstmt T ((fC1 C init b).loop 0 0) (fPb T C pos init cnd b) b).length := rfl
  have e4 : fEx T C pos init cnd step b = fPs T C pos init cnd b + (fCs T C pos init cnd step b).length + 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem ForSegs.of {code : List Ins} {T : List String} {C : GCtx} {pos : Nat} {init : Option Stmt}
    {cnd step : Option Expr} {b : Stmt} (h : Seg code pos (gstmt T C pos (.forStmt init cnd step b))) :
    ForSegs code T C pos init cnd step b := by
  rw [gstmt_for] at h
  obtain ⟨h, hjl⟩ := h.append
  obtain ⟨h, hcs⟩ := h.append
  obtain ⟨h, hb⟩ := h.append
  obtain ⟨h, hcc⟩ := h.append
  obtain ⟨hent, hci⟩ := h.append
  have e4 : (enterFrame (forNames init b) pos).length = 4 := rfl
  have ho := for_order T C pos init cnd step b
  simp only [List.length_append, e4, fCi_length, fCc_length, fBody_length] at hci hcc hb hcs hjl
  obtain ⟨hj, hl⟩ := (show Seg code _ ([J (fPs T C pos init cnd b + (fCs T C pos init cnd step b).length)
    (fHd T C pos init b)] ++ [.ld envR envR]) from hjl).append
  simp only [List.length_singleton] at hl
  have e1 : fHd T C pos init b = pos + 4 + fLi T C pos init b := rfl
  have e2 : fPb T C pos init cnd b = fHd T C pos init b + fLc T C pos init cnd b := rfl
  have e3 : fPs T C pos init cnd b = fPb T C pos init cnd b +
    (gstmt T ((fC1 C init b).loop 0 0) (fPb T C pos init cnd b) b).length := rfl
  have e4 : fEx T C pos init cnd step b = fPs T C pos init cnd b + (fCs T C pos init cnd step b).length + 1 := rfl
  refine ⟨hent, hci, hcc.cast ?_, hb.cast ?_, hcs.cast ?_, hj.cast ?_, hl.cast ?_⟩ <;> omega

end Vsa.Compiler
