import VsaIris.Vsa.SnpTac
import VsaIris.Vsa.Stdio

/-!
# The frame of a `snprintf` run

A `snprintf` run owns three byte ranges: newlib's runtime data (`stdioFoot`,
read only: `_impure_ptr` and the locale), the stack scratch below the caller's
`sp`, and the destination window. Every byte it reads but does not own (the
format, the `%s` arguments, the decimal point `"."`) is in the data view,
a concatenation of `accAddrs` ranges; bytes a caller owns are promoted back
at the Iris layer (`LocalRun.promote`). Both memberships are interval
arithmetic, so `sx_side` decides them (`snp_side`).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Stdio

/-- The stack a `snprintf` call may use (`snprintfNeed`). -/
abbrev snpNeed : Nat := 1024

/-- The bytes a `snprintf` run owns: newlib's data, the scratch
`[s - 1024, s)` and the destination `[dst, dst + n)`. -/
def snpS (s dst n : Nat) (a : Nat) : Prop :=
  stdioFoot a ∨ (s - snpNeed ≤ a ∧ a < s) ∨ (dst ≤ a ∧ a < dst + n)

/-- The data view holds the range `[lo, hi)`. Runs carry one fact per read
range (the format, each `%s` argument, `"."`); `sx_side` applies them. -/
def InDA (DA : List Nat) (lo hi : Nat) : Prop := ∀ b, lo ≤ b → b < hi → b ∈ DA

theorem InDA.mem {DA : List Nat} {lo hi b : Nat} (h : InDA DA lo hi) (h1 : lo ≤ b) (h2 : b < hi) :
    b ∈ DA := h b h1 h2

open Lean Elab Tactic Meta in
/-- Close `b ∈ DA` from some `InDA DA lo hi` hypothesis and `omega`. -/
elab "snp_inda" : tactic => do
  let g ← getMainGoal
  let lctx ← g.withContext getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← g.withContext (instantiateMVars d.type)
    unless ty.getAppFn.isConstOf ``InDA do continue
    let saved ← saveState
    try
      let gs ← evalTacticAt (← `(tactic| (refine InDA.mem $(mkIdent d.userName) ?_ ?_ <;> omega))) g
      if gs.isEmpty then
        replaceMainGoal []
        return
      saved.restore
    catch _ => saved.restore
  throwError "snp_inda: no InDA fact covers the access"

/-- Data-view side conditions: some `InDA` fact covers the access. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; rw [mem_accAddrs_iff] at hb; sx_pre; sx_lits; sx_bv; sx_lits; snp_inda))

theorem toInt_ofNat_small {x : Nat} (h : x < 2 ^ 63) : (BitVec.ofNat 64 x).toInt = x := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

/-- Signed comparisons of small values (`blez`, `blt` on counts). -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro hc; simp (disch := omega) only [toInt_ofNat_small, BitVec.reduceToInt] at hc; omega))

/-- Owned-byte side conditions of a `snprintf` run. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, snpS, snpNeed, stdioFoot, InRange] at *; sx_addr))

end VsaIris.Sym
