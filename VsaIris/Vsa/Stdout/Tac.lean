import VsaIris.Vsa.Stdout.Console
import VsaIris.Vsa.Stdout.Write
import VsaIris.Vsa.Stdout.Attr
import VsaIris.Vsa.BvLits
import VsaIris.Vsa.Dbm

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

def outS (s : BitVec 64) (need : Nat) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ impureW a) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨ (s.toNat - need ≤ a ∧ a < s.toNat)

namespace Stdout

scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; simp only [mem_accAddrs_iff, outS, stdioFoot, InRange, impureW] at *; sx_addr))
end Stdout

def updAll (R : Nat → BitVec 64) (v : Nat → BitVec 64) : List Nat → Nat → BitVec 64
  | [] => R
  | x :: xs => upd (updAll R v xs) x (v x)

theorem subw_add_ofNat {n : Nat} (hn : n < 2 ^ 31) (B : BitVec 64) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (B + BitVec.ofNat 64 n) - BitVec.extractLsb 31 0 B) =
      BitVec.ofNat 64 n := by
  have e : BitVec.extractLsb 31 0 (B + BitVec.ofNat 64 n) - BitVec.extractLsb 31 0 B =
      BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_zero]
    have hB := B.isLt
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem update_aligned (r : BitVec 64) (h : r.toNat % 4 = 0) : Sail.BitVec.update r 0 0#1 = r := by
  have e := ret_tgt r h
  rwa [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = 0#64 by decide,
    BitVec.add_zero] at e

theorem sext_zero32 : BitVec.signExtend 64 (0#32) = 0#64 := by decide

syntax "nx_console" : tactic
macro_rules
  | `(tactic| nx_console) => `(tactic| simp (disch := assumption) only
      [ldv_impDt, ConsoleMt.sinit, ConsoleMt.stdout, ConsoleMt.p, ConsoleMt.w,
       ConsoleMt.flagsU, ConsoleMt.flagsS, ConsoleMt.fd, ConsoleMt.base, ConsoleMt.bsize,
       ConsoleMt.lbf, ConsoleMt.cookie, ConsoleMt.writer, ConsoleMt.lock, ConsoleMt.lockMode])

syntax "nx_norm" (" at " ident)? : tactic
macro_rules
  | `(tactic| nx_norm at $h:ident) => `(tactic| simp_set nx_normh_set at $h:ident)
  | `(tactic| nx_norm) => `(tactic| simp_set nx_norm_set)

/-- Hook run before each normalisation of `nx_run`; `skip` by default. `open scoped Win` makes it
compact the register file. -/
syntax "nx_tidy" : tactic
macro_rules | `(tactic| nx_tidy) => `(tactic| skip)

section Leftover

open Lean Elab Tactic

/-- Clear the hypotheses a run introduced (decided branch conditions, forgotten bytes no longer
mentioned), so a leftover states only the reached machine state. -/
elab "nx_clean" : tactic => do
  let g ← getMainGoal
  let fs ← g.withContext do
    let lctx ← getLCtx
    return lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.userName.hasMacroScopes then acc.push d.fvarId else acc
  let g' ← g.tryClearMany fs
  replaceMainGoal [g']

/-- The run reached exactly one state: every branch was decided and no side goal is open. -/
elab "nx_one" : tactic => do
  let gs ← getUnsolvedGoals
  unless gs.length == 1 do
    throwError "nx_one: {gs.length} leftover goals (an undecided branch or an open side goal)"

end Leftover

open Lean Elab Tactic Meta in

def nxNorm (facts : Array Term) : TacticM Syntax := do
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
  `(tactic| ((try nx_tidy) <;> (try simp only [updAll] at ⊢) <;> (try simp only [nx_mt] at ⊢) <;> (try nx_norm) <;> (try simp only [$lems,*]) <;>
      (try nx_norm) <;> (try nx_mem) <;> (try nx_console) <;> (try simp only [$lems,*]) <;>
      (try nx_norm) <;> (try simp (disch := omega_dc) only [toInt_ofNat_small, BitVec.toInt_zero]) <;>
      (try simp (disch := decide) only [update_aligned]) <;>
      (try simp only [BitVec.sub_self, sext_zero32, BitVec.toInt_zero])))

open Lean Elab Tactic Meta in

def nxTryPrune (facts : Array Term) (norm : Syntax) (g : MVarId) : TacticM Bool := do
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
  let saved ← saveState
  try
    let gs ← evalTacticAt
      (← `(tactic| (intro hc; (try nx_norm at hc); (try simp only [$lems,*] at hc); (try nx_norm at hc); (try simp (disch := omega_dc) only [toInt_ofNat_small, BitVec.toInt_zero, BitVec.sub_self, sext_zero32] at hc); (try (exfalso; revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

open Lean Elab Tactic Meta in
def nxRunCore (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num)))
    (budgetPct : Nat := 0) :
    TacticM Unit := do
    let budget := (n.map (·.getNat)).getD 400
    let ctx ← readThe Core.Context
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    let norm ← nxNorm facts
    let mut pending : List MVarId := []
    let mut stuck : List MVarId := []
    let first ← getMainGoal

    let first ← do
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) first with
        | [c'] => pure c'
        | _ => saved.restore; pure first
      catch _ => saved.restore; pure first

    let mut work : List (MVarId × Nat) := [(first, budget)]
    while !work.isEmpty do
      let (cur, fuel) := work.head!
      work := work.tail!
      if fuel == 0 then stuck := stuck ++ [cur]; continue

      if budgetPct != 0 && ctx.maxHeartbeats != 0 then
        let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
        if used * 100 > ctx.maxHeartbeats * budgetPct then stuck := stuck ++ [cur]; continue
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := stuck ++ [cur]; continue
      let some (conts, pend) ← ixStep norm h cur | stuck := stuck ++ [cur]; continue
      pending := pending ++ pend
      match conts with
      | [c] =>

        let c ← do
          let ty ← c.withContext (do whnfR (← instantiateMVars (← c.getType)))
          if ty.isForall then
            match ← evalTacticAt (← `(tactic| intros)) c with
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
          work := (c, fuel - 1) :: work
        else
          stuck := stuck ++ [c]
      | [t, f] =>
        if ← nxTryPrune facts norm t then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [f]; continue
          work := (f', fuel - 1) :: work
        else if ← nxTryPrune facts norm f then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t]; continue
          work := (t', fuel - 1) :: work
        else if !explore then
          stuck := stuck ++ [t, f]
        else

          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t, f]; continue
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [t', f]; continue
          work := (t', fuel - 1) :: (f', fuel - 1) :: work
      | cs => stuck := stuck ++ cs
    setGoals (pending ++ stuck)

syntax "nx_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

syntax "nx_runB " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| nx_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => nxRunCore true n h fs stops
  | `(tactic| nx_runB $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => nxRunCore true n h fs stops 55

macro_rules | `(tactic| nx_addr) => `(tactic| (simp only [outS, stdioFoot, InRange, impureW] at ⊢; (try simp (disch := omega_dc) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); first | done | omega_dc))

namespace Stdout
scoped macro_rules | `(tactic| sx_side) => `(tactic| nx_addr)
end Stdout

syntax "nx_hb " ident : tactic
macro_rules
  | `(tactic| nx_hb $h) => `(tactic| simp (disch := omega_dc) only [mem_accAddrs_iff, toNat_add_lit,
      toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
      Nat.reduceAdd] at $h:ident)

namespace Stdout
scoped macro_rules | `(tactic| sx_side) => `(tactic| (intro b hb; (try nx_hb hb); nx_addr))
end Stdout

namespace Stdout

scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; apply List.mem_append_left; exact hb))
end Stdout

namespace Stdout

scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; first | (apply hc; assumption) | (apply absurd hc; assumption)))
end Stdout

abbrev callClob : List Nat := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

structure RetOK (R R' : Nat → BitVec 64) (a0 : BitVec 64) : Prop where
  a0 : R' 10 = a0
  keep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → R' x = R x

set_option hygiene false in

macro "nx_ret " h:ident : tactic => `(tactic| (
  have rk10 := ($h).a0
  have rk1 := ($h).keep 1 (by decide) (by decide) (by decide) (by decide)
  have rk2 := ($h).keep 2 (by decide) (by decide) (by decide) (by decide)
  have rk8 := ($h).keep 8 (by decide) (by decide) (by decide) (by decide)
  have rk9 := ($h).keep 9 (by decide) (by decide) (by decide) (by decide)
  have rk18 := ($h).keep 18 (by decide) (by decide) (by decide) (by decide)
  have rk19 := ($h).keep 19 (by decide) (by decide) (by decide) (by decide)
  have rk20 := ($h).keep 20 (by decide) (by decide) (by decide) (by decide)
  have rk21 := ($h).keep 21 (by decide) (by decide) (by decide) (by decide)
  have rk22 := ($h).keep 22 (by decide) (by decide) (by decide) (by decide)
  have rk23 := ($h).keep 23 (by decide) (by decide) (by decide) (by decide)
  have rk24 := ($h).keep 24 (by decide) (by decide) (by decide) (by decide)
  have rk25 := ($h).keep 25 (by decide) (by decide) (by decide) (by decide)
  have rk26 := ($h).keep 26 (by decide) (by decide) (by decide) (by decide)
  have rk27 := ($h).keep 27 (by decide) (by decide) (by decide) (by decide)
  simp only [upd_apply, updAll, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
    BitVec.reduceAdd] at rk1 rk2 rk8 rk9 rk10 rk18 rk19 rk20 rk21 rk22 rk23 rk24 rk25 rk26 rk27
  clear $h))

theorem retOK_of {R Rf : Nat → BitVec 64} {a0 : BitVec 64} (h10 : Rf 10 = a0)
    (hkeep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → Rf x = R x) : RetOK R Rf a0 :=
  ⟨h10, hkeep⟩

macro "ret_keep" : tactic => `(tactic| (
  intro x hx h32 h10 hc
  simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;>
    first
      | exact absurd rfl h32
      | exact absurd rfl h10
      | (simp only [Nat.reduceEqDiff, not_true_eq_false, not_false_eq_true, false_and, and_false,
          true_and, and_true] at hc; done)
      | (simp only [upd_apply, updAll, Nat.reduceEqDiff, ite_true, ite_false, *]; done)
      | simp_all [upd_apply]))

theorem updAll_apply (R v : Nat → BitVec 64) : ∀ (xs : List Nat) (x : Nat),
    updAll R v xs x = if x ∈ xs then v x else R x
  | [], x => by simp [updAll]
  | y :: ys, x => by
    simp only [updAll, upd_apply, updAll_apply R v ys x, List.mem_cons]
    by_cases h : x = y
    · subst h; simp
    · simp [h]

syntax "nx_disch" : tactic
macro_rules
  | `(tactic| nx_disch) => `(tactic| (fail_if_success show SWP _ _ _ _ _ _ _ _); first
      | assumption
      | (nx_norm; first | done | rfl | assumption)
      | (nx_mem; first | done | rfl | assumption | (nx_console; done))
      | (nx_norm; nx_mem; first | done | rfl | assumption | (nx_console; done))
      | nx_addr
      | (intro i hi; nx_addr))

section NxChain

open Lean Elab Command Term Meta

private def zeroLevelsN (e : Expr) : Expr :=
  e.replaceLevel fun l =>
    if l.hasMVar then some (l.replace fun | .mvar _ => some levelZero | _ => none) else none

syntax (name := nxChain) "#nx_chain " ident " := " "[" ident,+ "]" : command

@[command_elab nxChain] def elabNxChain : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let names ← stx[4].getSepArgs.mapM fun n => liftCoreM <| realizeGlobalConstNoOverload n
  liftTermElabM do
    let some first := names[0]? | throwError "#ix_chain: no pieces"
    let info0 ← getConstInfo first
    forallTelescope info0.type fun xs0 goal => do
      let nv ← pieceVars xs0
      let vars := xs0.extract 0 nv

      let rec exports (k : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
        let hs ← forallTelescope (← inferType (mkAppN (Lean.mkConst names[k]!) (vars ++ acc)))
          fun hs _ => hs.mapM inferType
        let mut out := #[]
        for h in hs.extract 1 hs.size do
          out := out.push (← mkForallFVars acc h)
        if k + 1 < names.size then
          let some cont := hs[0]? | throwError "#ix_chain: {names[k]!} has no leftover"
          let rest ← forallTelescope cont fun ys _ => exports (k + 1) (acc ++ ys)
          return out ++ rest
        else

          return (← hs.mapM fun h => mkForallFVars acc h)
      let exTys ← exports 0 #[]
      let exDecls := exTys.mapIdx fun j t => (Name.mkSimple s!"hx_{j + 1}", fun _ => pure t)
      withLocalDeclsD exDecls fun exs => do

        let rec build (k : Nat) (acc : Array Expr) (j : Nat) : MetaM Expr := do
          let c := mkAppN (Lean.mkConst names[k]!) (vars ++ acc)
          let hs ← forallTelescope (← inferType c) fun hs _ => hs.mapM inferType
          let nex := hs.size - (if k + 1 < names.size then 1 else 0)
          let exArgs := (List.range nex).toArray.map fun t => mkAppN exs[j + t]! acc
          if k + 1 < names.size then
            let rest ← forallTelescope hs[0]! fun ys _ => do
              mkLambdaFVars ys (← build (k + 1) (acc ++ ys) (j + nex))
            return mkAppN (mkApp c rest) exArgs
          else
            return mkAppN c exArgs
        let body ← build 0 #[] 0
        let val := zeroLevelsN (← instantiateMVars (← mkLambdaFVars (vars ++ exs) body))
        let ty := zeroLevelsN (← instantiateMVars (← mkForallFVars (vars ++ exs) goal))
        addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })

end NxChain

end VsaIris.Sym
