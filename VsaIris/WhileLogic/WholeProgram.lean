import VsaIris.WhileLogic.Example

/-!
# Worked example: all of `tests/while.wl`

`whileWl = firstLoop ++ rest` (`whileWl_eq`). The first loop is
`Example.firstLoop_then`. `rest` has two more loops:

```
var n = 0; var total = 0;
while (true) {
    n = n + 1;
    if (n > 100) { break; }
    if (n % 2 == 0) { continue; }
    total = total + n;
}
println(total);
var acc = 0; var a = 1;
while (a <= 3) {
    var b = 1;
    while (b <= 3) { acc = acc + a * b; b = b + 1; }
    a = a + 1;
}
println(acc);
```

The second loop's invariant `Inv2 k` (variant `k = 100 - m`) binds
`n = m` and `total = oddSum m`; its exit is the `break`, and its `continue`
re-establishes the invariant directly. The third loop nests a loop inside a
block that declares `b`: the inner invariant owns the block's frame and the
global frame, and the inner body resolves `acc` and `a` through two parent
links. `whileWl_spec` proves that the script prints exactly
`55\n2500\n36\n`.
-/

namespace Vsa.While.Logic.Whole

open Iris BI Vsa.While Vsa.While.Logic Vsa.While.Programs Vsa.While.Logic.Example

/-- Everything after the first loop. -/
def rest : Program := whileWl.drop 4

theorem whileWl_eq : whileWl = firstLoop ++ rest := (List.take_append_drop 4 whileWl).symm

/-! ## The second loop -/

/-- `1 + 3 + 5 + …` up to `m`. -/
def oddSum : Nat → Nat
  | 0 => 0
  | m + 1 => oddSum m + (if (m + 1) % 2 = 1 then m + 1 else 0)

theorem oddSum_le : ∀ m, m ≤ 100 → oddSum m ≤ 2500 := by decide

/-- The global frame during the second loop. -/
def G2 (vn vt : Value) : Frame :=
  ⟨none, natives ++ [("i", .int (10 : Nat)), ("sum", .int (sumTo 10)), ("n", vn), ("total", vt)]⟩

theorem G2_set_n (a b c : Value) : (G2 a b).setVar "n" c = G2 c b := rfl
theorem G2_set_total (a b c : Value) : (G2 a b).setVar "total" c = G2 a c := rfl

abbrev out2 : String := "55\n"

/-- State after `m` iterations; variant `k = 100 - m`. -/
def Inv2 (k : Nat) : vProp :=
  iprop(∃ m : Nat, ⌜m ≤ 100 ∧ k = 100 - m⌝ ∗
    (0 ↦f G2 (.int m) (.int (oddSum m)) ∗ outIs out2))

def body2 : Stmt := .block [
  .expr (.assign "n" (.binary .add (.var "n") (.int 1))),
  .ifStmt (.binary .gt (.var "n") (.int 100)) (.block [.brk]) none,
  .ifStmt (.binary .eq (.binary .mod (.var "n") (.int 2)) (.int 0)) (.block [.cont]) none,
  .expr (.assign "total" (.binary .add (.var "total") (.var "n")))]

theorem body2_spec (Φ : Status → vProp) (m : Nat) (hm : m ≤ 100) (P : vProp)
    (hP : m < 100 →
      iprop(0 ↦f G2 (.int (m + 1 : Nat)) (.int (oddSum (m + 1))) ∗ outIs out2) ⊢ P)
    (hexit : iprop(0 ↦f G2 (.int (100 + 1 : Nat)) (.int (oddSum 100)) ∗ outIs out2) ⊢
      Φ .normal) :
    iprop(0 ↦f G2 (.int m) (.int (oddSum m)) ∗ outIs out2) ⊢
      wpS 0 0 body2 (loopK Φ P) := by
  unfold body2
  iintro ⟨H0, Ho⟩
  iapply wp_block
  iintro %a Ha
  -- n = n + 1
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_get_here (F := G2 (.int m) (.int (oddSum m))) rfl)
  isplit
  · iexact H0
  iapply wp_int
  iapply (wp_bin (v := .int (wrap64 (m + 1))) (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_set_here (F := G2 (.int m) (.int (oddSum m))) (v0 := .int m) rfl)
  isplitl [H0]
  · iexact H0
  iintro H0
  have hv : wrap64 ((m : Int) + 1) = ((m + 1 : Nat) : Int) := by
    rw [show ((m : Int) + 1) = ((m + 1 : Nat) : Int) by omega]; exact wrap64_nat (by omega)
  simp only [seqK, G2_set_n, hv]
  -- if (n > 100) { break; }
  iapply wp_seq_cons
  iapply wp_if
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
  isplit
  · iexact Ha
  iapply (wp_get_here (F := G2 (.int (m + 1 : Nat)) (.int (oddSum m))) rfl)
  isplit
  · iexact H0
  iapply wp_int
  iapply (wp_bin (v := .bool (decide (((m + 1 : Nat) : Int) > 100))) (fun _ => rfl))
  rcases Nat.lt_or_ge m 100 with hlt | hge
  · have hd : decide (((m + 1 : Nat) : Int) > 100) = false := by simp; omega
    simp only [Value.truthy, hd, Bool.cond_false, seqK]
    -- if (n % 2 == 0) { continue; }
    iapply wp_seq_cons
    iapply wp_if
    iapply wp_binary
    iapply wp_binary
    iapply wp_var
    iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
    isplit
    · iexact Ha
    iapply (wp_get_here (F := G2 (.int (m + 1 : Nat)) (.int (oddSum m))) rfl)
    isplit
    · iexact H0
    iapply wp_int
    iapply (wp_bin (v := .int (wrap64 ((((m + 1 : Nat) : Int)).tmod 2))) (fun _ => rfl))
    iapply wp_int
    iapply (wp_bin (v := .bool (wrap64 ((((m + 1 : Nat) : Int)).tmod 2) == 0)) (fun _ => rfl))
    have hmod : wrap64 ((((m + 1 : Nat) : Int)).tmod 2) = (((m + 1) % 2 : Nat) : Int) := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega),
        show (((m + 1 : Nat) : Int) % 2) = (((m + 1) % 2 : Nat) : Int) by omega]
      exact wrap64_nat (by omega)
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with hev | hod
    · -- even: continue
      have hb : (wrap64 ((((m + 1 : Nat) : Int)).tmod 2) == 0) = true := by
        rw [hmod, hev]; rfl
      simp only [Value.truthy, hb, Bool.cond_true]
      iapply wp_block
      iintro %a' _
      iapply wp_seq_cons
      iapply wp_cont
      simp only [seqK, loopK]
      have hs : oddSum (m + 1) = oddSum m := by simp [oddSum, hev]
      iapply (hP hlt)
      rw [hs]
      isplitl [H0]
      · iexact H0
      · iexact Ho
    · -- odd: total = total + n
      have hb : (wrap64 ((((m + 1 : Nat) : Int)).tmod 2) == 0) = false := by
        rw [hmod, hod]; rfl
      simp only [Value.truthy, hb, Bool.cond_false, seqK]
      iapply wp_seq_cons
      iapply wp_expr
      iapply wp_assign
      iapply wp_binary
      iapply wp_var
      iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
      isplit
      · iexact Ha
      iapply (wp_get_here (F := G2 (.int (m + 1 : Nat)) (.int (oddSum m))) rfl)
      isplit
      · iexact H0
      iapply wp_var
      iapply (wp_get_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
      isplit
      · iexact Ha
      iapply (wp_get_here (F := G2 (.int (m + 1 : Nat)) (.int (oddSum m))) rfl)
      isplit
      · iexact H0
      iapply (wp_bin (v := .int (wrap64 (((oddSum m : Nat) : Int) + ((m + 1 : Nat) : Int))))
        (fun _ => rfl))
      iapply (wp_set_parent (F := ⟨some 0, []⟩) (p := 0) rfl rfl)
      isplit
      · iexact Ha
      iapply (wp_set_here (F := G2 (.int (m + 1 : Nat)) (.int (oddSum m)))
        (v0 := .int (oddSum m)) rfl)
      isplitl [H0]
      · iexact H0
      iintro H0
      have hs : oddSum (m + 1) = oddSum m + (m + 1) := by simp [oddSum, hod]
      have hv2 : wrap64 (((oddSum m : Nat) : Int) + ((m + 1 : Nat) : Int)) =
          ((oddSum (m + 1) : Nat) : Int) := by
        rw [hs, show (((oddSum m : Nat) : Int) + ((m + 1 : Nat) : Int)) =
          ((oddSum m + (m + 1) : Nat) : Int) by omega]
        exact wrap64_nat (by have := oddSum_le (m + 1) (by omega); omega)
      simp only [seqK, G2_set_total, hv2]
      iapply wp_seq_nil
      simp only [loopK]
      iapply (hP hlt)
      isplitl [H0]
      · iexact H0
      · iexact Ho
  · -- n = 101: break
    have hm100 : m = 100 := by omega
    subst hm100
    have hd : decide (((100 + 1 : Nat) : Int) > 100) = true := by decide
    simp only [Value.truthy, hd, Bool.cond_true]
    iapply wp_block
    iintro %a' _
    iapply wp_seq_cons
    iapply wp_brk
    simp only [seqK, loopK]
    iapply hexit
    isplitl [H0]
    · iexact H0
    · iexact Ho

theorem loop2_step (Φ : Status → vProp)
    (hexit : iprop(0 ↦f G2 (.int (100 + 1 : Nat)) (.int (oddSum 100)) ∗ outIs out2) ⊢
      Φ .normal) (k : Nat) :
    Inv2 k ⊢ wpE 0 0 (.bool true) (fun v => bif v.truthy
      then wpS 0 0 body2 (loopK Φ iprop(∃ k', ⌜k' < k⌝ ∧ Inv2 k'))
      else Φ .normal) := by
  have hP : ∀ m, k = 100 - m → m < 100 →
      iprop(0 ↦f G2 (.int (m + 1 : Nat)) (.int (oddSum (m + 1))) ∗ outIs out2) ⊢
        iprop(∃ k', ⌜k' < k⌝ ∧ Inv2 k') := fun m hk hlt => by
    unfold Inv2
    iintro H
    iexists (100 - (m + 1))
    isplit
    · ipureintro; omega
    · iexists (m + 1)
      isplitr
      · ipureintro; omega
      · iexact H
  unfold Inv2 at hP ⊢
  iintro ⟨%m, %hm, H0, Ho⟩
  obtain ⟨hm, hk⟩ := hm
  iapply wp_bool
  simp only [Value.truthy, Bool.cond_true]
  iapply (body2_spec Φ m hm _ (hP m hk) hexit)
  isplitl [H0]
  · iexact H0
  · iexact Ho

/-! ## `println(x)` of an integer variable of the global frame -/

theorem printArgs₀_int (n : Int) : printArgs₀ [.int n] = intToString n := rfl

theorem println_var_spec (F : Frame) (x : String) (n : Int) (o : String)
    (hF : F.find "println" = some (.native .println)) (hx : F.find x = some (.int n))
    (rest : List Stmt) (Φ : Status → vProp)
    (hrest : iprop(0 ↦f F ∗ outIs (o ++ intToString n ++ "\n")) ⊢ wpSeq 0 0 rest Φ) :
    iprop(0 ↦f F ∗ outIs o) ⊢
      wpSeq 0 0 (.expr (.call (.var "println") [.var x]) :: rest) Φ := by
  iintro ⟨H0, Ho⟩
  iapply wp_seq_cons
  iapply wp_expr
  iapply (wp_call _ _ (by simp [maxArgs]))
  iapply wp_var
  iapply (wp_get_here (F := F) hF)
  isplit
  · iexact H0
  iapply wp_args_cons
  iapply wp_var
  iapply (wp_get_here (F := F) hx)
  isplit
  · iexact H0
  iapply wp_args_nil
  iapply (wp_println (by simp [NoClosure]))
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  rw [printArgs₀_int]
  simp only [seqK]
  iapply hrest
  isplitl [H0]
  · iexact H0
  · iexact Ho

/-! ## The third loop (nested) -/

/-- The global frame during the third loop. -/
def G3 (vacc va : Value) : Frame :=
  ⟨none, natives ++ [("i", .int (10 : Nat)), ("sum", .int (sumTo 10)),
    ("n", .int (100 + 1 : Nat)), ("total", .int (oddSum 100)), ("acc", vacc), ("a", va)]⟩

theorem G3_set_acc (a b c : Value) : (G3 a b).setVar "acc" c = G3 c b := rfl
theorem G3_set_a (a b c : Value) : (G3 a b).setVar "a" c = G3 a c := rfl

/-- The outer body's frame, which declares `b`. -/
def B (vb : Value) : Frame := ⟨some 0, [("b", vb)]⟩

theorem B_set_b (a c : Value) : (B a).setVar "b" c = B c := rfl

def tri (n : Nat) : Nat := n * (n + 1) / 2

/-- `acc` before row `a`, column `b`. -/
def accOf (a b : Nat) : Nat := 6 * tri (a - 1) + a * tri (b - 1)

theorem acc_step : ∀ a, a ≤ 3 → ∀ b, b ≤ 3 → accOf a b + a * b = accOf a (b + 1) := by decide
theorem acc_row : ∀ a, a ≤ 3 → accOf a 4 = accOf (a + 1) 1 := by decide
theorem acc_le : ∀ a, a ≤ 4 → ∀ b, b ≤ 4 → accOf a b ≤ 100 := by decide

abbrev out3 : String := "55\n2500\n"

def body3inner : Stmt := .block [
  .expr (.assign "acc" (.binary .add (.var "acc") (.binary .mul (.var "a") (.var "b")))),
  .expr (.assign "b" (.binary .add (.var "b") (.int 1)))]

def cond3inner : Expr := .binary .le (.var "b") (.int 3)

def body3 : Stmt := .block [
  .varDecl "b" (some (.int 1)),
  .whileStmt cond3inner body3inner,
  .expr (.assign "a" (.binary .add (.var "a") (.int 1)))]

def cond3 : Expr := .binary .le (.var "a") (.int 3)

/-- Inner-loop state in the outer body's frame `f`, row `a`, after column
`b - 1`; variant `k = 4 - b`. -/
def Inv3i (f a k : Nat) : vProp :=
  iprop(∃ b : Nat, ⌜1 ≤ b ∧ b ≤ 4 ∧ k = 4 - b⌝ ∗
    (f ↦f B (.int b) ∗ (0 ↦f G3 (.int (accOf a b)) (.int a) ∗ outIs out3)))

theorem inner_body_spec (f a b : Nat) (ha : a ≤ 3) (hb : b ≤ 3) (Φ : Status → vProp) (P : vProp)
    (hP : iprop(f ↦f B (.int (b + 1 : Nat)) ∗
      (0 ↦f G3 (.int (accOf a (b + 1))) (.int a) ∗ outIs out3)) ⊢ P) :
    iprop(f ↦f B (.int b) ∗ (0 ↦f G3 (.int (accOf a b)) (.int a) ∗ outIs out3)) ⊢
      wpS 0 f body3inner (loopK Φ P) := by
  unfold body3inner
  iintro ⟨Hf, H0, Ho⟩
  iapply wp_block
  iintro %g Hg
  -- acc = acc + a * b
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_parent (F := B (.int b)) (p := 0) rfl rfl)
  isplit
  · iexact Hf
  iapply (wp_get_here (F := G3 (.int (accOf a b)) (.int a)) rfl)
  isplit
  · iexact H0
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_parent (F := B (.int b)) (p := 0) rfl rfl)
  isplit
  · iexact Hf
  iapply (wp_get_here (F := G3 (.int (accOf a b)) (.int a)) rfl)
  isplit
  · iexact H0
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_here (F := B (.int b)) rfl)
  isplit
  · iexact Hf
  iapply (wp_bin (v := .int (wrap64 ((a : Int) * (b : Int)))) (fun _ => rfl))
  have hv1 : wrap64 ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := by
    rw [show ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) by push_cast; rfl]
    exact wrap64_nat (Nat.le_trans (Nat.mul_le_mul ha hb) (by decide))
  simp only [hv1]
  iapply (wp_bin (v := .int (wrap64 (((accOf a b : Nat) : Int) + ((a * b : Nat) : Int))))
    (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_set_parent (F := B (.int b)) (p := 0) rfl rfl)
  isplit
  · iexact Hf
  iapply (wp_set_here (F := G3 (.int (accOf a b)) (.int a)) (v0 := .int (accOf a b)) rfl)
  isplitl [H0]
  · iexact H0
  iintro H0
  have hv2 : wrap64 (((accOf a b : Nat) : Int) + ((a * b : Nat) : Int)) =
      ((accOf a (b + 1) : Nat) : Int) := by
    rw [← acc_step a ha b hb, show (((accOf a b : Nat) : Int) + ((a * b : Nat) : Int)) =
      ((accOf a b + a * b : Nat) : Int) by omega]
    exact wrap64_nat (by
      rw [acc_step a ha b hb]; have := acc_le a (by omega) (b + 1) (by omega); omega)
  simp only [seqK, G3_set_acc, hv2]
  -- b = b + 1
  iapply wp_seq_cons
  iapply wp_expr
  iapply wp_assign
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_get_here (F := B (.int b)) rfl)
  isplit
  · iexact Hf
  iapply wp_int
  iapply (wp_bin (v := .int (wrap64 ((b : Int) + 1))) (fun _ => rfl))
  iapply (wp_set_parent (F := ⟨some f, []⟩) (p := f) rfl rfl)
  isplit
  · iexact Hg
  iapply (wp_set_here (F := B (.int b)) (v0 := .int b) rfl)
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  have hv3 : wrap64 ((b : Int) + 1) = ((b + 1 : Nat) : Int) := by
    rw [show ((b : Int) + 1) = ((b + 1 : Nat) : Int) by omega]; exact wrap64_nat (by omega)
  simp only [seqK, B_set_b, hv3]
  iapply wp_seq_nil
  simp only [loopK]
  iapply hP
  isplitl [Hf]
  · iexact Hf
  isplitl [H0]
  · iexact H0
  · iexact Ho

theorem inner_step (f a : Nat) (ha : a ≤ 3) (Φ : Status → vProp)
    (hexit : iprop(f ↦f B (.int (4 : Nat)) ∗
      (0 ↦f G3 (.int (accOf a 4)) (.int a) ∗ outIs out3)) ⊢ Φ .normal) (k : Nat) :
    Inv3i f a k ⊢ wpE 0 f cond3inner (fun v => bif v.truthy
      then wpS 0 f body3inner (loopK Φ iprop(∃ k', ⌜k' < k⌝ ∧ Inv3i f a k'))
      else Φ .normal) := by
  have hP : ∀ b, k = 4 - b → b ≤ 3 →
      iprop(f ↦f B (.int (b + 1 : Nat)) ∗
        (0 ↦f G3 (.int (accOf a (b + 1))) (.int a) ∗ outIs out3)) ⊢
        iprop(∃ k', ⌜k' < k⌝ ∧ Inv3i f a k') := fun b hk hb => by
    unfold Inv3i
    iintro H
    iexists (4 - (b + 1))
    isplit
    · ipureintro; omega
    · iexists (b + 1)
      isplitr
      · ipureintro; omega
      · iexact H
  unfold Inv3i at hP ⊢
  unfold cond3inner
  iintro ⟨%b, %hb, Hf, H0, Ho⟩
  obtain ⟨hb1, hb4, hk⟩ := hb
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := B (.int b)) rfl)
  isplit
  · iexact Hf
  iapply wp_int
  iapply (wp_bin (v := .bool (decide ((b : Int) ≤ 3))) (fun _ => rfl))
  rcases Nat.lt_or_ge b 4 with hlt | hge
  · have hd : decide ((b : Int) ≤ 3) = true := by simp; omega
    simp only [Value.truthy, hd, Bool.cond_true]
    iapply (inner_body_spec f a b ha (by omega) Φ _ (hP b hk (by omega)))
    isplitl [Hf]
    · iexact Hf
    isplitl [H0]
    · iexact H0
    · iexact Ho
  · have hd : decide ((b : Int) ≤ 3) = false := by simp; omega
    have h4 : b = 4 := by omega
    subst h4
    simp only [Value.truthy, hd, Bool.cond_false]
    iapply hexit
    isplitl [Hf]
    · iexact Hf
    isplitl [H0]
    · iexact H0
    · iexact Ho

theorem outer_body_spec (a : Nat) (ha : a ≤ 3) (Φ : Status → vProp) (P : vProp)
    (hP : iprop(0 ↦f G3 (.int (accOf (a + 1) 1)) (.int (a + 1 : Nat)) ∗ outIs out3) ⊢ P) :
    iprop(0 ↦f G3 (.int (accOf a 1)) (.int a) ∗ outIs out3) ⊢
      wpS 0 0 body3 (loopK Φ P) := by
  unfold body3
  iintro ⟨H0, Ho⟩
  iapply wp_block
  iintro %f Hf
  -- var b = 1;
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  have hB : (Frame.defVar ⟨some 0, []⟩ "b" (.int 1)) = B (.int (1 : Nat)) := rfl
  rw [hB]
  simp only [seqK]
  -- the inner loop
  iapply wp_seq_cons
  iapply (wp_while (I := Inv3i f a) cond3inner body3inner
    (inner_step f a ha _ (by
      -- a = a + 1
      iintro ⟨Hf, H0, Ho⟩
      simp only [seqK]
      iapply wp_seq_cons
      iapply wp_expr
      iapply wp_assign
      iapply wp_binary
      iapply wp_var
      iapply (wp_get_parent (F := B (.int (4 : Nat))) (p := 0) rfl rfl)
      isplit
      · iexact Hf
      iapply (wp_get_here (F := G3 (.int (accOf a 4)) (.int a)) rfl)
      isplit
      · iexact H0
      iapply wp_int
      iapply (wp_bin (v := .int (wrap64 ((a : Int) + 1))) (fun _ => rfl))
      iapply (wp_set_parent (F := B (.int (4 : Nat))) (p := 0) rfl rfl)
      isplit
      · iexact Hf
      iapply (wp_set_here (F := G3 (.int (accOf a 4)) (.int a)) (v0 := .int a) rfl)
      isplitl [H0]
      · iexact H0
      iintro H0
      have hv : wrap64 ((a : Int) + 1) = ((a + 1 : Nat) : Int) := by
        rw [show ((a : Int) + 1) = ((a + 1 : Nat) : Int) by omega]; exact wrap64_nat (by omega)
      simp only [seqK, G3_set_a, hv, acc_row a ha]
      iapply wp_seq_nil
      simp only [loopK]
      iapply hP
      isplitl [H0]
      · iexact H0
      · iexact Ho)) 3)
  unfold Inv3i
  iexists 1
  isplitr
  · ipureintro; omega
  isplitl [Hf]
  · iexact Hf
  isplitl [H0]
  · iexact H0
  · iexact Ho

/-- Outer-loop state before row `a`; variant `k = 4 - a`. -/
def Inv3 (k : Nat) : vProp :=
  iprop(∃ a : Nat, ⌜1 ≤ a ∧ a ≤ 4 ∧ k = 4 - a⌝ ∗
    (0 ↦f G3 (.int (accOf a 1)) (.int a) ∗ outIs out3))

theorem outer_step (Φ : Status → vProp)
    (hexit : iprop(0 ↦f G3 (.int (accOf 4 1)) (.int (4 : Nat)) ∗ outIs out3) ⊢ Φ .normal)
    (k : Nat) :
    Inv3 k ⊢ wpE 0 0 cond3 (fun v => bif v.truthy
      then wpS 0 0 body3 (loopK Φ iprop(∃ k', ⌜k' < k⌝ ∧ Inv3 k'))
      else Φ .normal) := by
  have hP : ∀ a, k = 4 - a → a ≤ 3 →
      iprop(0 ↦f G3 (.int (accOf (a + 1) 1)) (.int (a + 1 : Nat)) ∗ outIs out3) ⊢
        iprop(∃ k', ⌜k' < k⌝ ∧ Inv3 k') := fun a hk ha => by
    unfold Inv3
    iintro H
    iexists (4 - (a + 1))
    isplit
    · ipureintro; omega
    · iexists (a + 1)
      isplitr
      · ipureintro; omega
      · iexact H
  unfold Inv3 at hP ⊢
  unfold cond3
  iintro ⟨%a, %ha, H0, Ho⟩
  obtain ⟨ha1, ha4, hk⟩ := ha
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := G3 (.int (accOf a 1)) (.int a)) rfl)
  isplit
  · iexact H0
  iapply wp_int
  iapply (wp_bin (v := .bool (decide ((a : Int) ≤ 3))) (fun _ => rfl))
  rcases Nat.lt_or_ge a 4 with hlt | hge
  · have hd : decide ((a : Int) ≤ 3) = true := by simp; omega
    simp only [Value.truthy, hd, Bool.cond_true]
    iapply (outer_body_spec a (by omega) Φ _ (hP a hk (by omega)))
    isplitl [H0]
    · iexact H0
    · iexact Ho
  · have hd : decide ((a : Int) ≤ 3) = false := by simp; omega
    have h4 : a = 4 := by omega
    subst h4
    simp only [Value.truthy, hd, Bool.cond_false]
    iapply hexit
    isplitl [H0]
    · iexact H0
    · iexact Ho

/-! ## The whole script -/

theorem rest_eq : rest = [
    .varDecl "n" (some (.int 0)),
    .varDecl "total" (some (.int 0)),
    .whileStmt (.bool true) body2,
    .expr (.call (.var "println") [.var "total"]),
    .varDecl "acc" (some (.int 0)),
    .varDecl "a" (some (.int 1)),
    .whileStmt cond3 body3,
    .expr (.call (.var "println") [.var "acc"])] := rfl

/-- The output of `tests/while.wl`. -/
abbrev whileOut : String := "55\n2500\n36\n"

/-- The final `println(acc)`. -/
theorem after3_spec :
    iprop(0 ↦f G3 (.int (accOf 4 1)) (.int (4 : Nat)) ∗ outIs out3) ⊢
      wpSeq 0 0 [.expr (.call (.var "println") [.var "acc"])] (PostOut (· = whileOut)) := by
  refine println_var_spec (G3 (.int (accOf 4 1)) (.int (4 : Nat))) "acc" (accOf 4 1) out3
    rfl rfl [] _ ?_
  have ho : out3 ++ intToString ((accOf 4 1 : Nat) : Int) ++ "\n" = whileOut := by decide
  rw [ho]
  iintro ⟨_, Ho⟩
  iapply wp_seq_nil
  unfold PostOut
  isplit
  · ipureintro; rfl
  · iexists whileOut
    isplit
    · ipureintro; rfl
    · iexact Ho

/-- `println(total)` and the third loop. -/
theorem after2_spec :
    iprop(0 ↦f G2 (.int (100 + 1 : Nat)) (.int (oddSum 100)) ∗ outIs out2) ⊢
      wpSeq 0 0 [
        .expr (.call (.var "println") [.var "total"]),
        .varDecl "acc" (some (.int 0)),
        .varDecl "a" (some (.int 1)),
        .whileStmt cond3 body3,
        .expr (.call (.var "println") [.var "acc"])] (PostOut (· = whileOut)) := by
  refine println_var_spec (G2 (.int (100 + 1 : Nat)) (.int (oddSum 100))) "total" (oddSum 100)
    out2 rfl rfl _ _ ?_
  have ho : out2 ++ intToString ((oddSum 100 : Nat) : Int) ++ "\n" = out3 := by decide
  rw [ho]
  iintro ⟨H0, Ho⟩
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  have hG3 : ((G2 (.int (100 + 1 : Nat)) (.int (oddSum 100))).defVar "acc" (.int 0)).defVar
      "a" (.int 1) = G3 (.int (accOf 1 1)) (.int (1 : Nat)) := rfl
  rw [hG3]
  iapply wp_seq_cons
  iapply (wp_while (I := Inv3) cond3 body3 (outer_step _ (by
    iintro ⟨H0, Ho⟩
    simp only [seqK]
    iapply after3_spec
    isplitl [H0]
    · iexact H0
    · iexact Ho)) 3)
  unfold Inv3
  iexists 1
  isplitr
  · ipureintro; omega
  · isplitl [H0]
    · iexact H0
    · iexact Ho

theorem rest_spec :
    iprop(0 ↦f G (.int (10 : Nat)) (.int (sumTo 10)) ∗ outIs "55\n") ⊢
      wpSeq 0 0 rest (PostOut (· = whileOut)) := by
  rw [rest_eq]
  iintro ⟨H0, Ho⟩
  -- var n = 0; var total = 0;
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_int
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]
  have hG2 : ((G (.int (10 : Nat)) (.int (sumTo 10))).defVar "n" (.int 0)).defVar "total"
      (.int 0) = G2 (.int (0 : Nat)) (.int (oddSum 0)) := rfl
  rw [hG2]
  -- the second loop
  iapply wp_seq_cons
  iapply (wp_while (I := Inv2) (.bool true) body2 (loop2_step _ (by
    iintro ⟨H0, Ho⟩
    simp only [seqK]
    iapply after2_spec
    isplitl [H0]
    · iexact H0
    · iexact Ho)) 100)
  unfold Inv2
  iexists 0
  isplitr
  · ipureintro; omega
  · isplitl [H0]
    · iexact H0
    · iexact Ho

/-- **All of `tests/while.wl` prints `55\n2500\n36\n`.** -/
theorem whileWl_spec : initOwn ⊢ wpSeq 0 0 whileWl (PostOut (· = whileOut)) := by
  rw [whileWl_eq]
  exact firstLoop_then rest _ rest_spec

/-- Big-step consequence, proved through the logic (compare
`Validation.whileWl_valid`, which constructs the derivation directly). -/
theorem whileWl_bigStep : BigStep whileWl whileOut := by
  obtain ⟨out, h, rfl⟩ := adequacy_bigStep whileWl_spec
  exact h

end Vsa.While.Logic.Whole
