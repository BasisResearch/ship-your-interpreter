import VsaIris.Vsa.SnpTac
import VsaIris.Vsa.Stdio
import VsaIris.Vsa.BvLits

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Stdio

abbrev snpNeed : Nat := 1024

def snpS (s dst n : Nat) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ (0x8001b970 ≤ a ∧ a < 0x8001b978)) ∨ (s - snpNeed ≤ a ∧ a < s) ∨
    (dst ≤ a ∧ a < dst + n)

def InDA (DA : List Nat) (lo hi : Nat) : Prop := ∀ b, lo ≤ b → b < hi → b ∈ DA

theorem InDA.mem {DA : List Nat} {lo hi b : Nat} (h : InDA DA lo hi) (h1 : lo ≤ b) (h2 : b < hi) :
    b ∈ DA := h b h1 h2

open Lean Elab Tactic Meta in

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

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; rw [mem_accAddrs_iff] at hb; sx_pre; sx_lits; sx_bv; sx_lits; snp_inda))

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro hc; simp (disch := omega) only [toInt_ofNat_small, BitVec.reduceToInt] at hc; omega))

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, snpS, snpNeed, stdioFoot, InRange] at *; sx_addr))

end VsaIris.Sym
