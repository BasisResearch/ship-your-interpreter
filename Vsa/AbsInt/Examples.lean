import Vsa.AbsInt.ErrSound
import Vsa.AbsInt.Domains.Kinds
import Vsa.AbsInt.Domains.Sign
import Vsa.AbsInt.Domains.Product
import Vsa.While.Programs

/-!
# Worked examples on `whileWl`

`whileWl` (`Vsa/While/Programs.lean`) is the script embedded in the ELF.
Each analysis result below is computed by kernel reduction (`decide`), and
the soundness theorems turn it into a statement about every run.

* The kind domain `KSet` reports only a possible division by zero (the
  `n % 2`), so no run has a type error, an unbound variable, a call error, an
  assertion failure or an abrupt top-level completion.
* The reduced product `Const × Itv` with loop unrolling reports no alarm: no
  run has any runtime error. It also computes the final globals: `sum = 55`,
  `total = 2500`, `acc = 36`.
* Widening alone (`unroll := 0`), with narrowing, bounds the loop counters:
  `i = 10`, `n = 101`, `a = 4` at the end, and `sum` is an integer.
-/

namespace Vsa.AbsInt.Examples

open Vsa.While Vsa.While.Programs AbsDom

/-! ## Evaluation -/

/-- The kind domain: only `%` may fail. -/
example : alarms (A := KSet) {} whileWl = [.divZero] := by decide +kernel

/-- Constants with intervals: no alarm. -/
example : alarms (A := Const × Itv) {} whileWl = [] := by decide +kernel

/-- The kind analysis of the other validation programs. -/
example : (all.map fun (n, p) => (n, alarms (A := KSet) {} p)) =
    [("while", [.divZero]), ("arithmetic", [.divZero]), ("for", [.divZero]),
     ("functions", Kind.inCall), ("recursion", Kind.inCall),
     ("scope", Kind.inCall), ("strings", [])] := by decide +kernel

/-! ## Theorems about every run -/

/-- **No type errors in `whileWl`** (kind domain). -/
theorem whileWl_no_type_error : ¬ KindErr .type whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

/-- `whileWl` never looks up or assigns an unbound variable (kind domain). -/
theorem whileWl_no_unbound : ¬ KindErr .unbound whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

/-- `whileWl`'s calls never fail (kind domain). -/
theorem whileWl_no_call_error : ¬ KindErr .call whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

/-- **`whileWl` has no runtime error of any kind** (constants × intervals). -/
theorem whileWl_no_error : ¬ BigStepErr whileWl :=
  no_error_of_no_alarms (A := Const × Itv) {} (by decide +kernel)

/-- The final value of a global from a `Const × Itv` analysis result. -/
theorem global_of_const {cfg : Cfg} {p : Program} {st' : St}
    (h : ExecSeq initSt 0 0 p st' .normal) {x : String} {w : Value} {i : Itv}
    (hl : (analyze (A := Const × Itv) cfg p).norm.lookup x = ((.val w, i), false)) :
    st'.store.get? 0 x = some w := by
  obtain ⟨hs, hv⟩ := bigStep_global_some cfg h hl
  cases hx : st'.store.get? 0 x with
  | none => rw [hx] at hs; cases hs
  | some v =>
    have := (hv v hx).1
    simp only [AbsDom.Gam, Const.Gam] at this
    rw [this]

/-- **Final values of `whileWl`.** Every successful run ends with `sum = 55`,
`total = 2500` and `acc = 36` (constants × intervals, loops unrolled). -/
theorem whileWl_final {out : String} (h : BigStep whileWl out) :
    ∃ st', ExecSeq initSt 0 0 whileWl st' .normal ∧ st'.out = out ∧
      st'.store.get? 0 "sum" = some (.int 55) ∧
      st'.store.get? 0 "total" = some (.int 2500) ∧
      st'.store.get? 0 "acc" = some (.int 36) := by
  obtain ⟨st', hrun, hout⟩ := h
  exact ⟨st', hrun, hout, global_of_const (cfg := {}) hrun (i := .range (some 55) (some 55)) (by decide +kernel),
    global_of_const (cfg := {}) hrun (i := .range (some 2500) (some 2500)) (by decide +kernel),
    global_of_const (cfg := {}) hrun (i := .range (some 36) (some 36)) (by decide +kernel)⟩

/-- Widening and narrowing without unrolling: the loop counters are exact at
the end and `sum` is a 64-bit integer. -/
theorem whileWl_widening {st' : St} (h : ExecSeq initSt 0 0 whileWl st' .normal) :
    st'.store.get? 0 "i" = some (.int 10) ∧ st'.store.get? 0 "n" = some (.int 101) ∧
      ∀ v, st'.store.get? 0 "sum" = some v →
        Itv.Gam (.range (some (-2^63)) (some (2^63 - 1))) v := by
  refine ⟨global_of_const (cfg := { unroll := 0 }) h (i := .range (some 10) (some 10))
      (by decide +kernel),
    global_of_const (cfg := { unroll := 0 }) h (i := .range (some 101) (some 101)) (by decide +kernel),
    fun v hv => ?_⟩
  have hl : (analyze (A := Const × Itv) { unroll := 0 } whileWl).norm.lookup "sum" =
      ((.top, .range (some (-2^63)) (some (2^63 - 1))), false) := by decide +kernel
  exact ((bigStep_global_some _ h hl).2 v hv).2

end Vsa.AbsInt.Examples
