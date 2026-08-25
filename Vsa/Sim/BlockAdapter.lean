import Vsa.Sim.BlockMem
import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprSurvival

/-!
# `BlockAdapter` — the seams between block reflection and the domain proofs

The reflection lemmas (`block_mem_sound` / `bblock_sound_bt`) hand back a memory
in `writeLog`-fold form (`σ'.mem = writeLog m (wlogM body L lds)`) and a register
state as `GHolds σ' (runGM …)`. The domain proofs (`blockC_neg`, the leaf /
prologue / epilogue blocks) speak a different dialect: `read64`/`StoreRepr`/spill
facts on memory and `σ.regs.get?` on registers.

This file builds the memory-survival adapter once. The register-side seams are
handled at the call site by `gholds_lookup` (projection) plus the payload
normalisation lemmas near each domain proof; the genuinely-new, reusable piece is
turning a `writeLog` fold into `AgreeP` over any region disjoint from the store
windows — which then composes with the existing `read64_agreeP` / `read32_agreeP`
/ `StoreRepr`-survival machinery.

The hand proof did this by unfolding `σ'.mem` to a concrete `writeMap8`-tower and
peeling each layer with `getElem_writeMap8_disjoint` (EvalNegSim2.lean:762-789,
862-868). Here it is one fold induction, width-generic over `{1,4,8}`.
-/

open Vsa

namespace Vsa.Sim

/-- One write-log entry misses a byte disjoint from its `[addr, addr+width)`
window. Dispatches on the width literal (`sb`/`sw`/`sd`) into the existing
per-width disjoint lemmas; the `applyW` catch-all never fires because every real
`wentryM` has width `1`, `4`, or `8`. -/
theorem applyW_getElem_disjoint (m : Std.ExtHashMap Nat (BitVec 8)) (e : WEntry)
    (k : Nat) (hw : e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hdisj : k < e.1 ∨ e.1 + e.2.1 ≤ k) : (applyW m e)[k]? = m[k]? := by
  obtain ⟨a, w, d⟩ := e
  have hw' : w = 1 ∨ w = 4 ∨ w = 8 := hw
  have hdisj' : k < a ∨ a + w ≤ k := hdisj
  rcases hw' with h | h | h <;> subst h
  · show (m.insert a (sbData d))[k]? = m[k]?
    exact getElem_insert_ne m k a (sbData d) (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)
  · show (writeMap4 m a (swData d))[k]? = m[k]?
    exact getElem_writeMap4_disjoint m a k (swData d) (by omega)
  · show (writeMap8 m a (sdData_val d))[k]? = m[k]?
    exact getElem_writeMap8_disjoint m a k (sdData_val d) (by omega)

/-- The whole write-log fold misses a byte disjoint from every store window. One
induction over the log replaces the hand proof's per-store `getElem_writeMap8_disjoint`
peeling. Width-generic over the `{1,4,8}` a real block emits. -/
theorem writeLog_getElem_disjoint (k : Nat) :
    ∀ (log : List WEntry) (m : Std.ExtHashMap Nat (BitVec 8)),
      (∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8) →
      (∀ e ∈ log, k < e.1 ∨ e.1 + e.2.1 ≤ k) →
      (writeLog m log)[k]? = m[k]? := by
  intro log
  induction log with
  | nil => intro m _ _; rfl
  | cons e rest ih =>
    intro m hw hdisj
    have hstep : writeLog m (e :: rest) = writeLog (applyW m e) rest := by
      simp only [writeLog, List.foldl_cons]
    rw [hstep, ih (applyW m e) (fun e' he' => hw e' (List.mem_cons_of_mem _ he'))
        (fun e' he' => hdisj e' (List.mem_cons_of_mem _ he'))]
    exact applyW_getElem_disjoint m e k (hw e (List.mem_cons_self ..))
      (hdisj e (List.mem_cons_self ..))

/-- The reusable survival adapter: a `writeLog`-fold memory agrees with the entry
memory on every address a predicate `P` picks out, provided `P` avoids every store
window. Feeds directly into `read64_agreeP` / `read32_agreeP` and the
`StoreRepr`-survival premises the domain proofs discharge. -/
theorem writeLog_agreeP_disjoint (m : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (P : Nat → Prop)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hdisj : ∀ k, P k → ∀ e ∈ log, k < e.1 ∨ e.1 + e.2.1 ≤ k) :
    AgreeP P m (writeLog m log) :=
  fun k hk => (writeLog_getElem_disjoint k log m hw (hdisj k hk)).symm

end Vsa.Sim
