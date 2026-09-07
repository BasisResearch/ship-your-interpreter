import Vsa.Sim.ValueEqualSpec3
import Vsa.Sim.ConsoleStream

/-! Local representation failure after a console buffer update.
These theorems concern memory reads only. They do not assert a machine
execution, a complete Loaded witness, or failure of the final refinement.
-/

namespace Vsa.Sim.LoadedOutputAliasMutation

open Vsa.MemRepr
open Vsa.While

theorem cstring_functional {m : Mem} {p : Nat} {s t : String}
    (hs : CString m p s) (ht : CString m p t) : s = t := by
  rcases hs with ⟨cs, hcs, hs⟩
  rcases ht with ⟨ct, hct, ht⟩
  exact hs.trans ((congrArg String.ofList
    (Vsa.Sim.cstr_functional m p cs ct hcs hct)).trans ht.symm)

theorem cstring_empty {m : Mem} {p : Nat}
    (hz : m[p]? = some 0) : CString m p "" :=
  ⟨[], CStr.nil hz, rfl⟩

theorem cstring_newline {m : Mem} {p : Nat}
    (hbyte : m[p]? = some 10#8) (hnext : m[p + 1]? = some 0) :
    CString m p "\n" := by
  refine ⟨['\n'], ?_, rfl⟩
  exact CStr.cons hbyte (by decide) (by decide) (CStr.nil hnext)

theorem newline_not_empty {m : Mem} {p : Nat}
    (hbyte : m[p]? = some 10#8) (hnext : m[p + 1]? = some 0) :
    ¬ CString m p "" := by
  intro he
  have hbad := cstring_functional he (cstring_newline hbyte hnext)
  exact (by decide : "" ≠ "\n") hbad

/-- The byte immediately following the buffer belongs to the pinned stdout line field. -/
theorem buffer_next_is_stdoutLine :
    consoleBuf + 1 = consoleStdout + 120 := by decide

/-- An intact string-node header now represents LF, and cannot represent empty. -/
theorem expr_str_changed {m : Mem} {a : Nat}
    (htag : read32 m a = some 1)
    (hptr : read64 m (a + 8) = some consoleBuf)
    (hbyte : m[consoleBuf]? = some 10#8)
    (hnext : m[consoleBuf + 1]? = some 0) :
    ExprRepr m a (.str "\n") ∧ ¬ ExprRepr m a (.str "") := by
  refine ⟨ExprRepr.str htag hptr (cstring_newline hbyte hnext), ?_⟩
  intro h
  cases h with
  | str htag' hptr' hstr =>
    have hp := Option.some.inj (hptr'.symm.trans hptr)
    cases hp
    exact newline_not_empty hbyte hnext hstr

/-- Preserving the AST header alone does not preserve this expression representation. -/
theorem expr_str_not_surviving {m₀ m₁ : Mem} {a : Nat}
    (htag₀ : read32 m₀ a = some 1)
    (hptr₀ : read64 m₀ (a + 8) = some consoleBuf)
    (hzero : m₀[consoleBuf]? = some 0)
    (htag : read32 m₁ a = read32 m₀ a)
    (hptr : read64 m₁ (a + 8) = read64 m₀ (a + 8))
    (hbyte : m₁[consoleBuf]? = some 10#8)
    (hnext : m₁[consoleBuf + 1]? = some 0) :
    ExprRepr m₀ a (.str "") ∧
      ExprRepr m₁ a (.str "\n") ∧ ¬ ExprRepr m₁ a (.str "") := by
  exact ⟨ExprRepr.str htag₀ hptr₀ (cstring_empty hzero),
    expr_str_changed (htag.trans htag₀) (hptr.trans hptr₀) hbyte hnext⟩

#print axioms cstring_functional
#print axioms expr_str_changed
#print axioms expr_str_not_surviving

end Vsa.Sim.LoadedOutputAliasMutation
