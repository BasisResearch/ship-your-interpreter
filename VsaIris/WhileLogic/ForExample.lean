import VsaIris.WhileLogic.WholeProgram

/-!
# Worked example: a `for` loop

```
var sum = 0;
for (var i = 1; i <= 100; i = i + 1) { sum = sum + i; }
println(sum);
```

The loop gets a fresh frame `o` holding `i` (`wp_for`); the initializer
defines `i` there. `ForInv o k` (variant `k = 100 - m`) binds `i = m + 1` in
`o` and `sum = 0 + … + m` in the global frame. The body's block reaches `i`
through one parent link and `sum` through two; the step `i = i + 1` runs in
`o`. `for_spec` proves the program prints `5050`.
-/

namespace Vsa.While.Logic.ForExample

open Iris BI Vsa.While Vsa.While.Logic Vsa.While.Logic.Example Vsa.While.Logic.Whole

/-- The global frame: the natives and `sum`. -/
def Gs (v : Value) : Frame := ⟨none, natives ++ [("sum", v)]⟩
/-- The loop's outer frame, holding `i`. -/
def Fo (v : Value) : Frame := ⟨some 0, [("i", v)]⟩

theorem Gs_set (a c : Value) : (Gs a).setVar "sum" c = Gs c := rfl
theorem Fo_set (a c : Value) : (Fo a).setVar "i" c = Fo c := rfl

theorem sumTo_le100 : ∀ m, m ≤ 100 → sumTo m ≤ 5050 := by decide

def cond : Expr := .binary .le (.var "i") (.int 100)
def step : Expr := .assign "i" (.binary .add (.var "i") (.int 1))
def body : Stmt := .block [.expr (.assign "sum" (.binary .add (.var "sum") (.var "i")))]

def prog : Program := [
  .varDecl "sum" (some (.int 0)),
  .forStmt (some (.varDecl "i" (some (.int 1)))) (some cond) (some step) body,
  .expr (.call (.var "println") [.var "sum"])]

/-- After `m` iterations of the loop running in frame `o`. -/
def ForInv (o k : Nat) : vProp :=
  iprop(∃ m : Nat, ⌜m ≤ 100 ∧ k = 100 - m⌝ ∗
    (o ↦f Fo (.int (m + 1 : Nat)) ∗ (0 ↦f Gs (.int (sumTo m)) ∗ outIs "")))

theorem iter_spec (o m : Nat) (hm : m < 100) (Φ : Status → vProp) (P : vProp)
    (hP : iprop(o ↦f Fo (.int (m + 1 + 1 : Nat)) ∗
      (0 ↦f Gs (.int (sumTo (m + 1))) ∗ outIs "")) ⊢ P) :
    iprop(o ↦f Fo (.int (m + 1 : Nat)) ∗ (0 ↦f Gs (.int (sumTo m)) ∗ outIs "")) ⊢
      wpS 0 o body (loopK Φ (stepK 0 o (some step) P)) := by
  unfold body step
  iintro ⟨Ho, H0, Hout⟩
  iapply wp_block
  iintro %g Hg
  -- sum = sum + i
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some o, []⟩) (p := o) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_parent (F := Fo (.int (m + 1 : Nat))) (p := 0) rfl rfl)
  isplit
  · iexact Ho
  iapply (wp_get_here (F := Gs (.int (sumTo m))) rfl)
  isplit
  · iexact H0
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some o, []⟩) (p := o) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_here (F := Fo (.int (m + 1 : Nat))) rfl)
  isplit
  · iexact Ho
  iapply (wp_bin (v := .int (wrap64 (((sumTo m : Nat) : Int) + ((m + 1 : Nat) : Int))))
    (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some o, []⟩) (p := o) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_set_parent (F := Fo (.int (m + 1 : Nat))) (p := 0) rfl rfl)
  isplit
  · iexact Ho
  iapply (wp_set_here (F := Gs (.int (sumTo m))) (v0 := .int (sumTo m)) rfl)
  isplitl [H0]
  · iexact H0
  iintro H0
  have hv : wrap64 (((sumTo m : Nat) : Int) + ((m + 1 : Nat) : Int)) =
      ((sumTo (m + 1) : Nat) : Int) := by
    rw [show (((sumTo m : Nat) : Int) + ((m + 1 : Nat) : Int)) = ((sumTo (m + 1) : Nat) : Int) by
      simp only [sumTo]; omega]
    exact wrap64_nat (by have := sumTo_le100 (m + 1) (by omega); omega)
  simp only [seqK, Gs_set, hv]
  iapply wp_seq_nil
  simp only [loopK, stepK]
  -- the step: i = i + 1
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := Fo (.int (m + 1 : Nat))) rfl)
  isplit
  · iexact Ho
  iapply wp_int
  iapply (wp_bin (v := .int (wrap64 (((m + 1 : Nat) : Int) + 1))) (fun _ => rfl))
  iapply (wp_set_here (F := Fo (.int (m + 1 : Nat))) (v0 := .int (m + 1 : Nat)) rfl)
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  have hv2 : wrap64 (((m + 1 : Nat) : Int) + 1) = ((m + 1 + 1 : Nat) : Int) := by
    rw [show (((m + 1 : Nat) : Int) + 1) = ((m + 1 + 1 : Nat) : Int) by omega]
    exact wrap64_nat (by omega)
  simp only [Fo_set, hv2]
  iapply hP
  isplitl [Ho]
  · iexact Ho
  isplitl [H0]
  · iexact H0
  · iexact Hout

theorem loop_step (o : Nat) (Φ : Status → vProp)
    (hexit : iprop(0 ↦f Gs (.int (sumTo 100)) ∗ outIs "") ⊢ Φ .normal) (k : Nat) :
    ForInv o k ⊢ condK 0 o Φ (some cond)
      (wpS 0 o body (loopK Φ (stepK 0 o (some step) iprop(∃ k', ⌜k' < k⌝ ∧ ForInv o k')))) := by
  have hP : ∀ m, k = 100 - m → m < 100 →
      iprop(o ↦f Fo (.int (m + 1 + 1 : Nat)) ∗ (0 ↦f Gs (.int (sumTo (m + 1))) ∗ outIs "")) ⊢
        iprop(∃ k', ⌜k' < k⌝ ∧ ForInv o k') := fun m hk hlt => by
    unfold ForInv
    iintro H
    iexists (100 - (m + 1))
    isplit
    · ipureintro; omega
    · iexists (m + 1)
      isplitr
      · ipureintro; omega
      · iexact H
  unfold ForInv at hP ⊢
  unfold cond
  simp only [condK]
  iintro ⟨%m, %hm, Ho, H0, Hout⟩
  obtain ⟨hm, hk⟩ := hm
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := Fo (.int (m + 1 : Nat))) rfl)
  isplit
  · iexact Ho
  iapply wp_int
  iapply (wp_bin (v := .bool (decide (((m + 1 : Nat) : Int) ≤ 100))) (fun _ => rfl))
  rcases Nat.lt_or_ge m 100 with hlt | hge
  · have hd : decide (((m + 1 : Nat) : Int) ≤ 100) = true := by simp; omega
    simp only [Value.truthy, hd, Bool.cond_true]
    iapply (iter_spec o m hlt Φ _ (hP m hk hlt))
    isplitl [Ho]
    · iexact Ho
    isplitl [H0]
    · iexact H0
    · iexact Hout
  · have hd : decide (((m + 1 : Nat) : Int) ≤ 100) = false := by simp; omega
    have h100 : m = 100 := by omega
    subst h100
    simp only [Value.truthy, hd, Bool.cond_false]
    iapply hexit
    isplitl [H0]
    · iexact H0
    · iexact Hout

/-- **The program prints `5050`.** -/
theorem for_spec : initOwn ⊢ wpSeq 0 0 prog (PostOut (· = "5050\n")) := by
  unfold prog initOwn
  iintro ⟨H0, Hout⟩
  -- var sum = 0;
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  have hG : globalFrame.defVar "sum" (.int 0) = Gs (.int (sumTo 0)) := rfl
  rw [hG]
  simp only [seqK]
  -- the loop
  iapply wp_seq_cons
  iapply wp_for
  iintro %o Ho
  simp only [initK]
  -- var i = 1; in the loop frame
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  have hF : Frame.defVar ⟨some 0, []⟩ "i" (.int 1) = Fo (.int (0 + 1 : Nat)) := rfl
  rw [hF]
  iapply (wp_for_loop (some cond) (some step) body (ForInv o) (loop_step o _ (by
    iintro ⟨H0, Hout⟩
    simp only [seqK]
    iapply (println_var_spec (Gs (.int (sumTo 100))) "sum" (sumTo 100) "" rfl rfl [] _ (by
      have hs : "" ++ intToString ((sumTo 100 : Nat) : Int) ++ "\n" = "5050\n" := by decide
      rw [hs]
      iintro ⟨_, Hout⟩
      iapply wp_seq_nil
      unfold PostOut
      isplit
      · ipureintro; rfl
      · iexists "5050\n"
        isplit
        · ipureintro; rfl
        · iexact Hout))
    isplitl [H0]
    · iexact H0
    · iexact Hout)) 100)
  unfold ForInv
  iexists 0
  isplitr
  · ipureintro; omega
  isplitl [Ho]
  · iexact Ho
  isplitl [H0]
  · iexact H0
  · iexact Hout

theorem for_bigStep : BigStep prog "5050\n" := by
  obtain ⟨out, h, rfl⟩ := adequacy_bigStep for_spec
  exact h

end Vsa.While.Logic.ForExample
