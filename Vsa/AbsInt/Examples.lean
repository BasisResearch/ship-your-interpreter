import Vsa.AbsInt.ErrSound
import Vsa.AbsInt.Domains.Kinds
import Vsa.AbsInt.Domains.Sign
import Vsa.AbsInt.Domains.Product
import Vsa.While.Programs

namespace Vsa.AbsInt.Examples

open Vsa.While Vsa.While.Programs AbsOps AbsDom

example : alarms (A := KSet) {} whileWl = [.divZero] := by decide +kernel

example : alarms (A := Const × Itv) {} whileWl = [] := by decide +kernel

example : (all.map fun (n, p) => (n, alarms (A := KSet) {} p)) =
    [("while", [.divZero]), ("arithmetic", [.divZero]), ("for", [.divZero]),
     ("functions", Kind.inCall), ("recursion", Kind.inCall),
     ("scope", Kind.inCall), ("strings", [])] := by decide +kernel

theorem whileWl_no_type_error : ¬ KindErr .type whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

theorem whileWl_no_unbound : ¬ KindErr .unbound whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

theorem whileWl_no_call_error : ¬ KindErr .call whileWl :=
  kind_sound (A := KSet) {} (by decide +kernel)

theorem whileWl_no_error : ¬ BigStepErr whileWl :=
  no_error_of_no_alarms (A := Const × Itv) {} (by decide +kernel)

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

theorem whileWl_final {out : String} (h : BigStep whileWl out) :
    ∃ st', ExecSeq initSt 0 0 whileWl st' .normal ∧ st'.out = out ∧
      st'.store.get? 0 "sum" = some (.int 55) ∧
      st'.store.get? 0 "total" = some (.int 2500) ∧
      st'.store.get? 0 "acc" = some (.int 36) := by
  obtain ⟨st', hrun, hout⟩ := h
  exact ⟨st', hrun, hout, global_of_const (cfg := {}) hrun (i := .range (some 55) (some 55)) (by decide +kernel),
    global_of_const (cfg := {}) hrun (i := .range (some 2500) (some 2500)) (by decide +kernel),
    global_of_const (cfg := {}) hrun (i := .range (some 36) (some 36)) (by decide +kernel)⟩

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
