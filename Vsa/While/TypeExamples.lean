import Vsa.While.TypeProgress
import Vsa.While.TypeInfer
import Vsa.While.Programs

/-!
# Worked examples of the WHILE type system

* `whileWl_wellTyped`: the program linked into the ELF type-checks.
* The other validation programs `functionsWl`, `scopeWl`, `forWl`,
  `arithmeticWl` and `stringsWl` type-check, as does a directly recursive
  `fact` (`recProg_wellTyped`).
* `badSub_illTyped`, `badAssign_illTyped`: two programs rejected under every
  typing environment; `badSub_err` shows the first one does reach a runtime
  error.
* The type checker `whileTyped` (`Vsa/While/TypeInfer.lean`) accepts `whileWl`
  and the other validation programs and rejects `badSub`, `badAssign` and
  `recursionWl` (`recursionWl_untypable`).
* `divProg_wellTyped`, `divProg_err`: a well-typed program that reaches the
  division-by-zero error the type system leaves in place.

`recursionWl` is untypable: `is_even` refers to `is_odd` before `is_odd` is
declared, and the type system requires names referenced in a closure body to
be defined where the closure is created.

Positive examples are decided by the verified checker (`typeCheck_iff`,
`Vsa/While/TypeCheck.lean`) through `decide`. The rejections hold for every
typing environment, so they are proved by inverting the typing rules.
-/

namespace Vsa.While.Types

open Vsa.While

/-- A typing environment: the builtins, the listed names, and `int` for every
other name. -/
def mkΔ (l : List (String × Ty)) : TyEnv := fun x =>
  if x = "print" then .native .print else if x = "println" then .native .println
  else if x = "assert" then .native .assert
  else match l.find? (·.1 == x) with
    | some p => p.2
    | none => .int

theorem mkΔ_builtins (l : List (String × Ty)) : BuiltinsTyped (mkΔ l) := ⟨rfl, rfl, rfl⟩

/-- **`tests/while.wl`, the program in the ELF, is well-typed.** -/
theorem whileWl_wellTyped : WellTyped (mkΔ []) Programs.whileWl :=
  by decide

private abbrev ii : Ty := .fn [.int] .int

theorem functionsWl_wellTyped : WellTyped (mkΔ [("make_adder", .fn [.int] ii), ("add5", ii),
    ("apply_twice", .fn [ii, .int] .int), ("f", ii), ("make_counter", .fn [] (.fn [] .int)),
    ("c", .fn [] .int), ("c2", .fn [] .int), ("compose", .fn [ii, ii] ii), ("g", ii),
    ("inc", ii), ("dbl", ii)]) Programs.functionsWl :=
  by decide

theorem scopeWl_wellTyped : WellTyped (mkΔ [("shadow", ii)]) Programs.scopeWl :=
  by decide

theorem forWl_wellTyped : WellTyped (mkΔ [("line", .str)]) Programs.forWl :=
  by decide

theorem arithmeticWl_wellTyped : WellTyped (mkΔ []) Programs.arithmeticWl :=
  by decide

theorem stringsWl_wellTyped : WellTyped (mkΔ [("s", .str)]) Programs.stringsWl :=
  by decide

/-- `var fact = fn fact(n) { if (n <= 1) { return 1; } return n * fact(n - 1); };
println(fact(10));` -/
def recProg : Program := [
  .varDecl "fact" (some (.fn (some "fact") ["n"] [
    .ifStmt (.binary .le (.var "n") (.int 1)) (.block [.ret (some (.int 1))]) none,
    .ret (some (.binary .mul (.var "n") (.call (.var "fact")
      [.binary .sub (.var "n") (.int 1)])))])),
  .expr (.call (.var "println") [.call (.var "fact") [.int 10]])]

theorem recProg_wellTyped : WellTyped (mkΔ [("fact", ii)]) recProg :=
  by decide

/-! ## Rejected programs -/

/-- `"a" - 1;` -/
def badSub : Program := [.expr (.binary .sub (.str "a") (.int 1))]

theorem badSub_illTyped (Δ : TyEnv) : ¬ WellTyped Δ badSub := by
  rintro ⟨_, S', h⟩
  cases h with
  | cons _ _ _ _ _ _ _ hs _ =>
    cases hs with
    | expr _ _ _ _ _ he =>
      cases he with
      | binary _ _ _ _ _ _ _ hl _ hbt =>
        cases hl
        cases hbt with
        | cmpStr _ h => simp at h

/-- `badSub` does reach a runtime error (subtraction on a string). -/
theorem badSub_err : BigStepErr badSub :=
  .inl (.head _ _ _ _ _ (.expr _ _ _ _ (.binaryOp _ _ _ _ _ _ _ _ _ _
    (.str _ _ _ _) (.int _ _ _ _) rfl)))

theorem wtE_int_inv {Δ : TyEnv} {S : List String} {n : Int} {T : Ty}
    (h : WtE Δ S (.int n) T) : T = .int := by cases h; rfl

theorem wtE_str_inv {Δ : TyEnv} {S : List String} {s : String} {T : Ty}
    (h : WtE Δ S (.str s) T) : T = .str := by cases h; rfl

/-- `var x = 1; x = "s";` -/
def badAssign : Program := [.varDecl "x" (some (.int 1)), .expr (.assign "x" (.str "s"))]

theorem badAssign_illTyped (Δ : TyEnv) : ¬ WellTyped Δ badAssign := by
  rintro ⟨_, S', h⟩
  cases h with
  | cons _ _ _ _ _ _ _ hs₁ hrest =>
    cases hs₁ with
    | varInit _ _ _ _ _ hwe₁ =>
      have h₁ := wtE_int_inv hwe₁
      cases hrest with
      | cons _ _ _ _ _ _ _ hs₂ _ =>
        cases hs₂ with
        | expr _ _ _ _ _ he =>
          cases he with
          | assign _ _ _ _ hwe₂ =>
            have h₂ := wtE_str_inv hwe₂
            rw [h₁] at h₂
            cases h₂

/-! ## A well-typed program with a non-type error -/

/-- `println(1 / 0);` -/
def divProg : Program := [.expr (.call (.var "println") [.binary .div (.int 1) (.int 0)])]

theorem divProg_wellTyped : WellTyped (mkΔ []) divProg :=
  by decide

theorem divProg_err : ExecSeqErrN initSt 0 0 divProg :=
  .head _ _ _ _ _ (.expr _ _ _ _ (.callArgs _ _ _ _ _ _ _ (.var _ _ _ _ _ rfl) (by decide)
    (.head _ _ _ _ _ (.divZero _ _ _ _ _ _ _ _ _ (.inl rfl) (.int _ _ _ _) (.int _ _ _ _)))))

/-! ## The WHILE type checker -/

theorem whileWl_whileTyped : whileTyped Programs.whileWl = true :=
  whileTyped_iff.mpr ⟨_, whileWl_wellTyped⟩

theorem functionsWl_whileTyped : whileTyped Programs.functionsWl = true :=
  whileTyped_iff.mpr ⟨_, functionsWl_wellTyped⟩

theorem scopeWl_whileTyped : whileTyped Programs.scopeWl = true :=
  whileTyped_iff.mpr ⟨_, scopeWl_wellTyped⟩

theorem forWl_whileTyped : whileTyped Programs.forWl = true :=
  whileTyped_iff.mpr ⟨_, forWl_wellTyped⟩

theorem arithmeticWl_whileTyped : whileTyped Programs.arithmeticWl = true :=
  whileTyped_iff.mpr ⟨_, arithmeticWl_wellTyped⟩

theorem stringsWl_whileTyped : whileTyped Programs.stringsWl = true :=
  whileTyped_iff.mpr ⟨_, stringsWl_wellTyped⟩

theorem badSub_whileTyped : whileTyped badSub = false :=
  Bool.eq_false_iff.mpr fun h => by
    obtain ⟨Δ, hΔ⟩ := whileTyped_iff.mp h
    exact badSub_illTyped Δ hΔ

theorem badAssign_whileTyped : whileTyped badAssign = false :=
  Bool.eq_false_iff.mpr fun h => by
    obtain ⟨Δ, hΔ⟩ := whileTyped_iff.mp h
    exact badAssign_illTyped Δ hΔ

theorem isEven_body_bad {Δ : TyEnv} {S : List String} {R : Option Ty} {S' : List String}
    {b : List Stmt} (hS : "is_odd" ∉ S)
    (hb : b = [.ifStmt (.binary .eq (.var "n") (.int 0)) (.block [.ret (some (.bool true))]) none,
      .ret (some (.call (.var "is_odd") [.binary .sub (.var "n") (.int 1)]))]) :
    ¬ WtSeq Δ S R false b S' := by
  subst hb
  intro h
  cases h with
  | cons _ _ _ _ _ _ _ h1 h2 =>
    cases h1 with
    | ifNone =>
      cases h2 with
      | cons _ _ _ _ _ _ _ h3 _ =>
        cases h3 with
        | ret _ _ _ _ he =>
          cases he with
          | call _ _ _ _ _ _ hf _ _ _ =>
            cases hf with
            | var _ _ hx => exact hS hx

theorem recursionWl_untypable : ¬ Typable Programs.recursionWl := by
  rintro ⟨Δ, _, S', h⟩
  unfold Programs.recursionWl at h
  -- `fact`, `println(fact(10))`, `fib`, `println(fib(20))`
  cases h with | cons _ _ _ _ _ _ _ h₁ h =>
  cases declOut_of_wt h₁
  cases h with | cons _ _ _ _ _ _ _ h₂ h =>
  cases declOut_of_wt h₂
  cases h with | cons _ _ _ _ _ _ _ h₃ h =>
  cases declOut_of_wt h₃
  cases h with | cons _ _ _ _ _ _ _ h₄ h =>
  cases declOut_of_wt h₄
  -- `is_even` refers to `is_odd`, which is not yet declared
  cases h with | cons _ _ _ _ _ _ _ hs _ =>
  cases hs with
  | varInit _ _ _ _ _ he =>
    generalize Δ "is_even" = T at he
    cases he with
    | fn _ _ _ _ _ _ hb _ => exact isEven_body_bad (by decide) rfl hb
  | varRec _ _ _ _ _ _ _ _ _ hb _ _ => exact isEven_body_bad (by decide) rfl hb
theorem recursionWl_whileTyped : whileTyped Programs.recursionWl = false :=
  Bool.eq_false_iff.mpr fun h => recursionWl_untypable (whileTyped_iff.mp h)

end Vsa.While.Types
