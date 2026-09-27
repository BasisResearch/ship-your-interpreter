import Vsa.While.TypeProgress
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

Typing derivations are found by `wt_search`, which applies the typing rules
syntactically; `MustExitSeq` side conditions are decided by `mustExitSeqB`.
-/

namespace Vsa.While.Types

open Vsa.While

mutual
/-- Boolean decision procedure for `MustExit`. -/
def mustExitB : Stmt → Bool
  | .ret _ => true
  | .brk => true
  | .cont => true
  | .block ss => mustExitSeqB ss
  | .ifStmt _ t (some e) => mustExitB t && mustExitB e
  | _ => false
/-- Boolean decision procedure for `MustExitSeq`. -/
def mustExitSeqB : List Stmt → Bool
  | [] => false
  | s :: ss => mustExitB s || mustExitSeqB ss
end

mutual
theorem mustExit_of_b : ∀ {s : Stmt}, mustExitB s = true → MustExit s
  | .ret _, _ => .ret _
  | .brk, _ => .brk
  | .cont, _ => .cont
  | .block ss, h => .block ss (mustExitSeq_of_b (by simpa [mustExitB] using h))
  | .ifStmt c t (some e), h => by
    simp only [mustExitB, Bool.and_eq_true] at h
    exact .ite c t e (mustExit_of_b h.1) (mustExit_of_b h.2)
  | .ifStmt _ _ none, h => by simp [mustExitB] at h
  | .expr _, h => by simp [mustExitB] at h
  | .varDecl _ _, h => by simp [mustExitB] at h
  | .whileStmt _ _, h => by simp [mustExitB] at h
  | .forStmt _ _ _ _, h => by simp [mustExitB] at h
theorem mustExitSeq_of_b : ∀ {ss : List Stmt}, mustExitSeqB ss = true → MustExitSeq ss
  | [], h => by simp [mustExitSeqB] at h
  | s :: ss, h => by
    simp only [mustExitSeqB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .head s ss (mustExit_of_b h)
    · exact .tail s ss (mustExitSeq_of_b h)
end

/-- Proof search for typing derivations. -/
macro "wt_search" : tactic => `(tactic|
  repeat' (first
    | decide
    | exact Or.inl rfl
    | exact Or.inr (mustExitSeq_of_b (by decide))
    | apply WtS.varRec
    | constructor))


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
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.whileWl; wt_search⟩⟩

private abbrev ii : Ty := .fn [.int] .int

theorem functionsWl_wellTyped : WellTyped (mkΔ [("make_adder", .fn [.int] ii), ("add5", ii),
    ("apply_twice", .fn [ii, .int] .int), ("f", ii), ("make_counter", .fn [] (.fn [] .int)),
    ("c", .fn [] .int), ("c2", .fn [] .int), ("compose", .fn [ii, ii] ii), ("g", ii),
    ("inc", ii), ("dbl", ii)]) Programs.functionsWl :=
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.functionsWl; wt_search⟩⟩

theorem scopeWl_wellTyped : WellTyped (mkΔ [("shadow", ii)]) Programs.scopeWl :=
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.scopeWl; wt_search⟩⟩

theorem forWl_wellTyped : WellTyped (mkΔ [("line", .str)]) Programs.forWl :=
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.forWl; wt_search⟩⟩

theorem arithmeticWl_wellTyped : WellTyped (mkΔ []) Programs.arithmeticWl :=
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.arithmeticWl; wt_search⟩⟩

theorem stringsWl_wellTyped : WellTyped (mkΔ [("s", .str)]) Programs.stringsWl :=
  ⟨mkΔ_builtins _, ⟨_, by unfold Programs.stringsWl; wt_search⟩⟩

/-- `var fact = fn fact(n) { if (n <= 1) { return 1; } return n * fact(n - 1); };
println(fact(10));` -/
def recProg : Program := [
  .varDecl "fact" (some (.fn (some "fact") ["n"] [
    .ifStmt (.binary .le (.var "n") (.int 1)) (.block [.ret (some (.int 1))]) none,
    .ret (some (.binary .mul (.var "n") (.call (.var "fact")
      [.binary .sub (.var "n") (.int 1)])))])),
  .expr (.call (.var "println") [.call (.var "fact") [.int 10]])]

theorem recProg_wellTyped : WellTyped (mkΔ [("fact", ii)]) recProg :=
  ⟨mkΔ_builtins _, ⟨_, by unfold recProg; wt_search⟩⟩

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
  ⟨mkΔ_builtins _, ⟨_, by unfold divProg; wt_search⟩⟩

theorem divProg_err : ExecSeqErrN initSt 0 0 divProg :=
  .head _ _ _ _ _ (.expr _ _ _ _ (.callArgs _ _ _ _ _ _ _ (.var _ _ _ _ _ rfl) (by decide)
    (.head _ _ _ _ _ (.divZero _ _ _ _ _ _ _ _ _ (.inl rfl) (.int _ _ _ _) (.int _ _ _ _)))))

end Vsa.While.Types
