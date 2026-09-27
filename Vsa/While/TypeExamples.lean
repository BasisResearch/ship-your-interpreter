import Vsa.While.TypeProgress
import Vsa.While.TypeCheck
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
* `divProg_wellTyped`, `divProg_err`: a well-typed program that reaches the
  division-by-zero error the type system leaves in place.

`recursionWl` is rejected: `is_even` refers to `is_odd` before `is_odd` is
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

end Vsa.While.Types
