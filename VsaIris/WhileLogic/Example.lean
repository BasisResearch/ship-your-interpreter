import VsaIris.WhileLogic.Adequacy
import Vsa.While.Programs

/-!
# Worked example: the first loop of `tests/while.wl` prints `55`

```
var i = 0;
var sum = 0;
while (i < 10) {
    i = i + 1;
    sum = sum + i;
}
println(sum);
```

These are the first four statements of `whileWl` (`firstLoop_eq`). The loop is
verified with `wp_while` and the invariant `LoopInv k`: after `n` iterations
(`k = 10 - n`, the variant) the global frame binds `i = n` and
`sum = 0 + 1 + … + n`, and the console is still empty. Each iteration runs the
body block in a fresh frame whose parent is the global frame, so its two
assignments resolve `i` and `sum` through the parent (`wp_get_parent`,
`wp_set_parent`). The console is an exclusive resource; `println` extends it.
`firstLoop_spec` is the resulting triple and `firstLoop_bigStep` its big-step
consequence.
-/

namespace Vsa.While.Logic.Example

open Iris BI Vsa.While Vsa.While.Logic Vsa.While.Programs

/-- The first loop of `tests/while.wl`. -/
def firstLoop : Program := whileWl.take 4

def natives : List (String × Value) :=
  [("print", .native .print), ("println", .native .println), ("assert", .native .assert)]

/-- The global frame during the first loop. -/
def G (vi vs : Value) : Frame := ⟨none, natives ++ [("i", vi), ("sum", vs)]⟩
/-- `0 + 1 + … + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem sumTo_le : ∀ n, n ≤ 10 → sumTo n ≤ 55 := by decide

theorem G_set_i (a b c : Value) : (G a b).setVar "i" c = G c b := rfl
theorem G_set_sum (a b c : Value) : (G a b).setVar "sum" c = G a c := rfl

theorem wrap64_nat {m : Nat} (h : m ≤ 1000) : wrap64 (m : Int) = m :=
  wrap64_eq_self ⟨by omega, by omega⟩

/-- Loop state after `n` iterations, with variant `k = 10 - n`. -/
def LoopInv (k : Nat) : vProp :=
  iprop(∃ n : Nat, ⌜n ≤ 10 ∧ k = 10 - n⌝ ∗
    (0 ↦f G (.int n) (.int (sumTo n)) ∗ outIs ""))

def firstLoopBody : Stmt := .block [
  .expr (.assign "i" (.binary .add (.var "i") (.int 1))),
  .expr (.assign "sum" (.binary .add (.var "sum") (.var "i")))]

theorem body_spec (Φ : Status → vProp) (n : Nat) (hn : n < 10) (P : vProp)
    (hP : iprop(0 ↦f G (.int (n + 1 : Nat)) (.int (sumTo (n + 1))) ∗ outIs "") ⊢ P) :
    iprop(0 ↦f G (.int n) (.int (sumTo n)) ∗ outIs "") ⊢
      wpS 0 0 firstLoopBody (loopK Φ P) := by
  unfold firstLoopBody
  iintro ⟨H0, Ho⟩
  iapply wp_block
  iintro %a Ha
  -- i = i + 1
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_get_here (F := G (.int n) (.int (sumTo n))) rfl)
  isplit
  · iexact H0
  iapply wp_int
  iapply (wp_bin (v := .int (wrap64 (n + 1))) (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_set_here (F := G (.int n) (.int (sumTo n))) (v0 := .int n) rfl)
  isplitl [H0]
  · iexact H0
  iintro H0
  have hv : wrap64 ((n : Int) + 1) = ((n + 1 : Nat) : Int) := by
    rw [show ((n : Int) + 1) = ((n + 1 : Nat) : Int) by omega]; exact wrap64_nat (by omega)
  simp only [seqK, G_set_i, hv]
  -- sum = sum + i
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_get_here (F := G (.int (n + 1 : Nat)) (.int (sumTo n))) rfl)
  isplit
  · iexact H0
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_get_here (F := G (.int (n + 1 : Nat)) (.int (sumTo n))) rfl)
  isplit
  · iexact H0
  iapply (wp_bin (v := .int (wrap64 ((sumTo n : Int) + ((n + 1 : Nat) : Int)))) (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_set_here (F := G (.int (n + 1 : Nat)) (.int (sumTo n))) (v0 := .int (sumTo n)) rfl)
  isplitl [H0]
  · iexact H0
  iintro H0
  have hv2 : wrap64 ((sumTo n : Int) + ((n + 1 : Nat) : Int)) = ((sumTo (n + 1) : Nat) : Int) := by
    rw [show ((sumTo n : Int) + ((n + 1 : Nat) : Int)) = ((sumTo (n + 1) : Nat) : Int) by
      simp only [sumTo]; omega]
    exact wrap64_nat (by have := sumTo_le (n + 1) (by omega); omega)
  simp only [seqK, G_set_sum, hv2]
  iapply wp_seq_nil
  simp only [loopK]
  iapply hP
  isplitl [H0]
  · iexact H0
  · iexact Ho

def loopCond : Expr := .binary .lt (.var "i") (.int 10)

theorem firstLoop_eq : firstLoop = [
    .varDecl "i" (some (.int 0)),
    .varDecl "sum" (some (.int 0)),
    .whileStmt loopCond firstLoopBody,
    .expr (.call (.var "println") [.var "sum"])] := rfl

/-- The loop invariant/variant obligation of `wp_while`. -/
theorem loop_step (Φ : Status → vProp)
    (hexit : iprop(0 ↦f G (.int (10 : Nat)) (.int (sumTo 10)) ∗ outIs "") ⊢ Φ .normal) (k : Nat) :
    LoopInv k ⊢ wpE 0 0 loopCond (fun v => bif v.truthy
      then wpS 0 0 firstLoopBody (loopK Φ iprop(∃ k', ⌜k' < k⌝ ∧ LoopInv k'))
      else Φ .normal) := by
  unfold LoopInv loopCond
  iintro ⟨%n, %hn, H0, Ho⟩
  obtain ⟨hn, hk⟩ := hn
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := G (.int n) (.int (sumTo n))) rfl)
  isplit
  · iexact H0
  iapply wp_int
  iapply (wp_bin (v := .bool (decide ((n : Int) < 10))) (fun _ => rfl))
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · have hd : decide ((n : Int) < 10) = true := by simp; omega
    simp only [Value.truthy, hd, Bool.cond_true]
    have hP : iprop(0 ↦f G (.int (n + 1 : Nat)) (.int (sumTo (n + 1))) ∗ outIs "") ⊢
        iprop(∃ k', ⌜k' < k⌝ ∧ LoopInv k') := by
      unfold LoopInv
      iintro H
      iexists (10 - (n + 1))
      isplit
      · ipureintro; omega
      · iexists (n + 1)
        isplitr
        · ipureintro; omega
        · iexact H
    unfold LoopInv at hP
    iapply (body_spec Φ n hlt _ hP)
    isplitl [H0]
    · iexact H0
    · iexact Ho
  · have hd : decide ((n : Int) < 10) = false := by simp; omega
    have h10 : n = 10 := by omega
    subst h10
    simp only [Value.truthy, hd, Bool.cond_false]
    iapply hexit
    isplitl [H0]
    · iexact H0
    · iexact Ho

/-- The final `println(sum)`, followed by any continuation `rest`. -/
theorem println_spec (rest : List Stmt) (Φ : Status → vProp)
    (hrest : iprop(0 ↦f G (.int (10 : Nat)) (.int (sumTo 10)) ∗ outIs "55\n") ⊢
      wpSeq 0 0 rest Φ) :
    iprop(0 ↦f G (.int (10 : Nat)) (.int (sumTo 10)) ∗ outIs "") ⊢
      wpSeq 0 0 (.expr (.call (.var "println") [.var "sum"]) :: rest) Φ := by
  iintro ⟨H0, Ho⟩
  iapply wp_seq_cons
  iapply wp_expr
  iapply (wp_call _ _ (by decide))
  iapply wp_var
  iapply (wp_get_here (F := G (.int (10 : Nat)) (.int (sumTo 10))) (v := .native .println) rfl)
  isplit
  · iexact H0
  iapply wp_args_cons
  iapply wp_var
  iapply (wp_get_here (F := G (.int (10 : Nat)) (.int (sumTo 10))) rfl)
  isplit
  · iexact H0
  iapply wp_args_nil
  iapply (wp_println (by simp [NoClosure]))
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  have hs : "" ++ printArgs₀ [.int ((sumTo 10 : Nat) : Int)] ++ "\n" = "55\n" := by decide
  rw [hs]
  simp only [seqK]
  iapply hrest
  isplitl [H0]
  · iexact H0
  · iexact Ho

/-- The first loop followed by any continuation `rest`: `rest` starts with
`i = 10`, `sum = 55` in the global frame and `55\n` on the console. -/
theorem firstLoop_then (rest : List Stmt) (Φ : Status → vProp)
    (hrest : iprop(0 ↦f G (.int (10 : Nat)) (.int (sumTo 10)) ∗ outIs "55\n") ⊢
      wpSeq 0 0 rest Φ) :
    initOwn ⊢ wpSeq 0 0 (firstLoop ++ rest) Φ := by
  rw [firstLoop_eq]
  simp only [List.cons_append, List.nil_append]
  unfold initOwn
  iintro ⟨H0, Ho⟩
  -- var i = 0;
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  -- var sum = 0;
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  have hG : (globalFrame.defVar "i" (.int 0)).defVar "sum" (.int 0) =
      G (.int (0 : Nat)) (.int (sumTo 0)) := rfl
  rw [hG]
  -- the loop
  iapply wp_seq_cons
  iapply (wp_while (I := LoopInv) loopCond firstLoopBody
    (loop_step _ (by
      iintro ⟨H0, Ho⟩
      simp only [seqK]
      iapply (println_spec rest Φ hrest)
      isplitl [H0]
      · iexact H0
      · iexact Ho)) 10)
  unfold LoopInv
  iexists 0
  isplitr
  · ipureintro; omega
  · isplitl [H0]
    · iexact H0
    · iexact Ho

/-- **The first loop of `tests/while.wl` prints `55`.** -/
theorem firstLoop_spec : initOwn ⊢ wpSeq 0 0 firstLoop (PostOut (· = "55\n")) := by
  have h := firstLoop_then [] (PostOut (· = "55\n")) (by
    iintro ⟨_, Ho⟩
    iapply wp_seq_nil
    unfold PostOut
    isplit
    · ipureintro; rfl
    · iexists "55\n"
      isplit
      · ipureintro; rfl
      · iexact Ho)
  rwa [List.append_nil] at h

/-- Big-step consequence: `firstLoop` runs to completion printing exactly
`55\n`. -/
theorem firstLoop_bigStep : BigStep firstLoop "55\n" := by
  obtain ⟨out, h, rfl⟩ := adequacy_bigStep firstLoop_spec
  exact h

end Vsa.While.Logic.Example
