import Vsa.Sim.rows.FlCondArmStagePre

namespace Vsa.Sim

open Vsa.While
open Vsa.Sim.ApproxArmReseat
open Vsa.Machine (Config)

/-- The current dispatch contract must supply environment validity at every
entry accepted by `FEntryC`. -/
theorem FlCondArmDispatch.envValid
    {cc : Expr} {step : Option Expr} {body : Stmt} {st : Vsa.While.St}
    {d : Nat} {env : Addr} {c : Config}
    (hDispatch : FlCondArmDispatch cc step body st d env c)
    (hEntry : FEntryC c st d env (some cc) step body) :
    EnvValid st env := by
  obtain ⟨c', hSteps, hPost⟩ := hDispatch hEntry c rfl
  obtain ⟨g, gpre, N, A, SL, phiF, phiC, sp, ra, interp, stmt, envPtr,
    ret, child, v8, v9, v18, v19, m0, ment, hValid, hRest⟩ := hPost
  exact hValid

/-- `FEntryC` omits its environment index. Thus a universal dispatch supplier
would accept an address just beyond the allocated frames. Reached validity
must enter through a stronger entry, before this contract can be supplied. -/
theorem flCondArmDispatch_not_total
    {cc : Expr} {step : Option Expr} {body : Stmt} {st : Vsa.While.St}
    {d : Nat} {env : Addr} {c : Config}
    (hEntry : FEntryC c st d env (some cc) step body) :
    ¬ (∀ env', FlCondArmDispatch cc step body st d env' c) := by
  intro hDispatch
  have hInvalidEntry :
      FEntryC c st d st.store.frames.size (some cc) step body := hEntry
  have hValid := (hDispatch st.store.frames.size).envValid hInvalidEntry
  exact Nat.lt_irrefl st.store.frames.size hValid

#print axioms flCondArmDispatch_not_total

end Vsa.Sim
