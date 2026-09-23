import VsaIris.Interp.Steps
import VsaIris.Vsa.AllocTac

/-!
# Driving the interpreter's step table

`ix_run h` runs the interpreter's code symbolically from an `IW … pc R Mt`
goal, the interpreter twin of `sx_run` (`AllocTac.lean`, lane H4). At each PC
literal it tries the step lemmas of that instruction in order — `it_<pc>`
(ALU, store, branch, jump, and a load from OWNED bytes), `itD_<pc>` (a load
from the persistent data view), `itT_<pc>` (a jump-table load) — and keeps the
first whose side conditions `sx_side` closes after `sx_norm`/`sx_mem`. A
branch whose condition `sx_side` refutes is pruned. The run stops at a branch
it cannot decide, at a listed PC (`ix_run h at pc…`: the `jal` of a call), at
a symbolic PC, or after the fuel (default 400 instructions). Undischarged side
conditions and the reached goals are left, side conditions first.

Callers extend `sx_side` with `macro_rules` for the facts of their run (the
values an AST node or a value slot pins).
-/

namespace VsaIris.Sym

open Lean Elab Tactic Meta

theorem mem_accAddrs_iff {a w b : Nat} : b ∈ accAddrs a w ↔ a ≤ b ∧ b < a + w :=
  ⟨of_mem_accAddrs, fun ⟨h1, h2⟩ => by
    have e : a + (b - a) = b := by omega
    rw [← e]; exact mem_accAddrs (by omega)⟩

/-- Byte-set side conditions (`∀ b ∈ accAddrs a w, b ∈ DA` or `S b`), when
the data addresses are a concatenation of `accAddrs` ranges and the owned set
is built from `InExt`: both become interval arithmetic for `omega`. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, List.mem_append, VsaIris.InExt] at *; sx_addr))

/-- Closed side conditions (a jump-table byte at a literal address is in
`interpRO`). -/
macro_rules
  | `(tactic| sx_side) => `(tactic| decide)

private def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s

/-- The normalizer run after every step and before every side condition:
register lookups, the caller's facts (`using`), store forwarding. -/
def ixNorm (facts : Array Term) : TacticM Syntax := do
  if facts.isEmpty then
    `(tactic| ((try sx_norm) <;> (try ix_tab) <;> (try sx_norm) <;> (try sx_mem)))
  else
    let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
    `(tactic| ((try sx_norm) <;> (try simp only [$lems,*]) <;> (try ix_tab) <;> (try sx_norm) <;> (try sx_mem)))

/-- Try `sx_side` (after the normalizers) on a goal; `true` when it closes. -/
def ixTrySide (norm : Syntax) (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| ($(⟨norm⟩) <;> sx_side))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Close a branch goal `C → IW …` when `sx_side` refutes `C`. -/
def ixTryPrune (norm : Syntax) (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt
      (← `(tactic| (intro hc; exfalso; ($(⟨norm⟩) <;> (revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- The step lemmas of the instruction at `pc`, in the order tried. -/
def ixCandidates (pc : Nat) : TacticM (List Name) := do
  let env ← getEnv
  let mk (p : String) := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "VsaIris") "Sym") s!"{p}_{hex8 pc}"
  return [mk "it", mk "itD", mk "itT", mk "itH"].filter env.contains

/-- Apply one candidate: the continuation goals (an `SWP` conclusion) and the
side conditions `sx_side` could not close; `none` when it does not apply. -/
def ixApply (norm : Syntax) (h : Syntax) (g : MVarId) (nm : Name) (strict : Bool) :
    TacticM (Option (List MVarId × List MVarId)) := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| apply $(mkIdent nm) $(⟨h⟩))) g
    let mut conts : List MVarId := []
    let mut pending : List MVarId := []
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
        conts := conts ++ [g]
      else if !(← ixTrySide norm g) then
        pending := pending ++ [g]
    if strict && !pending.isEmpty then
      saved.restore; return none
    return some (conts, pending)
  catch _ =>
    saved.restore; return none

/-- One step at a literal PC: the first candidate whose side conditions all
close; failing that, the first candidate that applies, with its side
conditions left pending. -/
def ixStep (norm : Syntax) (h : Syntax) (g : MVarId) :
    TacticM (Option (List MVarId × List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let cands ← ixCandidates pc
  for nm in cands do
    if let some r ← ixApply norm h g nm true then return some r
  for nm in cands do
    if let some r ← ixApply norm h g nm false then return some r
  return none

/-- `ix_run h`, `ix_run [n] h`, `ix_run h using [e,…]`, `ix_run h at pc…`. -/
syntax "ix_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| ix_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => do
    let budget := (n.map (·.getNat)).getD 400
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    let norm ← ixNorm facts
    let mut pending : List MVarId := []
    let mut cur ← getMainGoal
    let mut stuck : List MVarId := []
    for _ in [0:budget] do
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := [cur]; break
      let some (conts, pend) ← ixStep norm h cur | stuck := [cur]; break
      pending := pending ++ pend
      match conts with
      | [c] =>
        -- a havoc load's continuation holds for every loaded value
        let c ← do
          let ty ← c.withContext (do whnfR (← instantiateMVars (← c.getType)))
          if ty.isForall then
            match ← evalTacticAt (← `(tactic| intro _)) c with
            | [c'] => pure c'
            | _ => pure c
          else pure c
        let c ← do
          let saved ← saveState
          try
            match ← evalTacticAt norm c with
            | [c'] => pure c'
            | _ => saved.restore; pure c
          catch _ => saved.restore; pure c
        if (← c.withContext (do swpPC? (← c.getType))).isSome then
          cur := c
        else
          stuck := [c]; break
      | [t, f] =>
        if ← ixTryPrune norm t then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := [f]; break
          cur := f'
        else if ← ixTryPrune norm f then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := [t]; break
          cur := t'
        else
          stuck := [t, f]; break
      | cs => stuck := cs; break
    if stuck.isEmpty then stuck := [cur]
    setGoals (pending ++ stuck)

end VsaIris.Sym
