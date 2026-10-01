import VsaIris.Vsa.Stdout.Win

/-!
# Carry and address laws over the existing terms

At a piece boundary the next record is rebuilt from the run's register file (an `upd` chain), its
memory (a `writeLog` chain) and the incoming facts. `carry_close [facts]` closes such a field:
registers outside the updated literals read back through the chain (`upd_other`, side condition by
`decide`, by list membership or by `omega`), loads and bytes outside the stored entries read back
through the log (`ldv_store_miss`, `imgM_store_miss`, disjointness by the window keys `win_key`), loads
through a `Frame` whose region predicate unfolds to literal intervals (`hF.ldv` as a fact), and stack
addresses take one spelling (`s - K + k` to `s - (K - k)` / `s + (k - K)` under the window,
`x + c₁ + c₂` to `x + (c₁ + c₂)`). The facts are normalised the same way before use. `region_close`
closes region inclusions, `carry_arith` literal stack arithmetic.
-/
namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.MallocFast

theorem ne_of_mem_all {x k : Nat} {xs : List Nat} (hx : x ∈ xs) (h : (!xs.contains k) = true) : x ≠ k :=
  fun e => by subst e; simp_all

theorem mem_of_mem_all {x : Nat} {xs ys : List Nat} (hx : x ∈ xs) (h : xs.all (ys.contains ·) = true) :
    x ∈ ys := by
  simp only [List.all_eq_true, List.contains_iff_mem] at h; exact h x hx

theorem keep_eq {R R0 : Nat → BitVec 64} {xs : List Nat} {x : Nat} {v : BitVec 64}
    (h : ∀ y ∈ xs, R y = R0 y) (h0 : R0 x = v) (hx : x ∈ xs := by decide) : R x = v := (h x hx).trans h0

theorem Win.le_top {S : Nat → Prop} {s n m K : Nat} (hw : Win S s n m) (h : K ≤ n) : K ≤ s := by
  have := hw.rgn.lo; omega

theorem natK_add_le {s K k : Nat} (h1 : K ≤ s) (h2 : k ≤ K) : s - K + k = s - (K - k) := by omega
theorem natK_add_ge {s K k : Nat} (h1 : K ≤ s) (h2 : K ≤ k) : s - K + k = s + (k - K) := by omega

theorem imgM_store1_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 1, v)]) a = BitVec.setWidth 8 v := by
  have h := pin1_of_writeLog Mt [] [] a v trivial
  simp only [List.nil_append] at h
  unfold imgM
  rw [h, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb]

open Lean Elab Tactic Meta in
elab "carry_unfold " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let t ← instantiateMVars d.type
  let some c := t.getAppFn.constName? | throwError "carry_unfold: no head"
  evalTactic (← `(tactic| unfold $(mkIdent c):ident at $h:ident))

open Lean Meta in
partial def carrySplitOr (g : MVarId) (h : FVarId) : MetaM (List MVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← h.getType))
  if t.isAppOfArity ``Or 2 then
    let subs ← g.cases h
    let mut out := []
    for s in subs do
      out := out ++ (← carrySplitOr s.mvarId s.fields[0]!.fvarId!)
    return out
  else return [g]

open Lean Elab Tactic Meta in
/-- Close a region fact (`∀ b, lo ≤ b → b < hi → Reg b`, `∀ a, Reg a → Reg' a`, `¬ Reg a`) by
unfolding the region predicates and literal arithmetic. -/
elab "region_close" : tactic => do
  let (fvs, g) ← (← getMainGoal).intros
  let mut g := g
  let mut i := 0
  for fv in fvs do
    g ← g.rename fv (Name.mkSimple s!"carry_r{i}")
    i := i + 1
  replaceMainGoal [g]
  let unfoldHead (e : Expr) : TacticM (Option Name) := do
    let some c := e.getAppFn.constName? | return none
    if c == ``Not || (← getEnv).isProjectionFn c then return none
    let some (.defnInfo _) := (← getEnv).find? c | return none
    return some c
  withMainContext do
    let mut locs : Array Term := #[]
    for fv in fvs do
      let d ← fv.getDecl
      locs := locs.push (mkIdent d.userName)
      if let some c ← unfoldHead (← instantiateMVars d.type) then
        evalTactic (← `(tactic| unfold $(mkIdent c):ident at $(mkIdent d.userName):ident))
    if let some c ← unfoldHead (← instantiateMVars (← getMainTarget)) then
      evalTactic (← `(tactic| unfold $(mkIdent c):ident))
    evalTactic (← `(tactic| simp (config := {failIfUnchanged := false}) (disch := omega) only
      [toNat_add_lit] at $locs*  ⊢))
  let mut goals ← getGoals
  for k in [0:fvs.size] do
    let nm := Name.mkSimple s!"carry_r{k}"
    let mut next := []
    for gl in goals do
      match (← gl.withContext getLCtx).findFromUserName? nm with
      | some d => next := next ++ (← carrySplitOr gl d.fvarId)
      | none => next := next ++ [gl]
    goals := next
  setGoals goals
  evalTactic (← `(tactic| all_goals omega))

open Lean Elab Tactic Meta in
/-- The side conditions of the carry rules, dispatched on their shape. -/
elab "carry_disch" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let closed := !t.hasFVar && !t.hasMVar
  let tac ← if closed then `(tactic| decide)
    else if t.isAppOf ``Ne || t.isAppOf ``Not then
      `(tactic| first | exact ne_of_mem_all (by assumption) (by decide) | omega)
    else if t.isAppOf ``Membership.mem then
      `(tactic| first | exact mem_of_mem_all (by assumption) (by decide) | assumption)
    else if t.isForall then
      `(tactic| (
        with_unfolding_all intro j hj h
        simp only [widthOfM] at hj
        carry_unfold h
        simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h
        omega))
    else if t.isAppOf ``LE.le && (t.getArg! 3).isFVar then
      `(tactic| first | exact Win.le_top (by with_reducible assumption) (by decide) | omega)
    else `(tactic| first | win_key | omega | (simp only [widthOfM]; omega) | assumption)
  evalTactic tac

open Lean Elab Tactic Meta in
elab "carry_guard" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isForall || [``Eq, ``And, ``Or, ``LE.le, ``LT.lt, ``Ne, ``Not, ``Iff].any t.isAppOf do
    throwError "carry: not a fact goal"

syntax "carry_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| carry_norm $[$loc]?) => `(tactic| carry_norm [] $[$loc]?)
  | `(tactic| carry_norm [$ts,*] $[$loc]?) =>
    `(tactic| simp (config := {failIfUnchanged := false}) (disch := carry_disch) only
      [upd_same, upd_other, natK_add_le, natK_add_ge, Nat.reduceSub, Nat.reduceAdd, Nat.sub_zero, Nat.add_zero,
       toNat_ofNat_lt, imgM_store_miss, ldv_store_miss, ldv_ld_hit_eq, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
       imgM_store1_hit, BitVec.reduceSetWidth, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
       $ts,*]
      $[$loc]?)

syntax "carry_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- Literal stack arithmetic: fold `x + c₁ + c₂`, read `(x + c).toNat` as `x.toNat + c`, then `omega`. -/
syntax "carry_arith" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| carry_arith $[$loc]?) => `(tactic| (
      simp (config := {failIfUnchanged := false}) (disch := omega) only
        [BitVec.add_assoc, BitVec.reduceAdd, toNat_add_lit, BitVec.toNat_ofNat, Nat.zero_mod] $[$loc]?
      omega))

syntax "carry_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| carry_finish [$ts,*]) => `(tactic| (
      (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true])
      (try intros)
      carry_norm [$ts,*]
      all_goals (repeat' apply And.intro)
      all_goals first | exact True.intro | decide | with_reducible assumption | with_reducible rfl | carry_arith))

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| carry_close $[[$ts,*]]?) => do
    evalTactic (← `(tactic| carry_guard))
    let ls := (ts.map (·.getElems)).getD #[]
    let s0 ← saveState
    try
      evalTactic (← `(tactic| carry_finish [$ls,*]))
      return
    catch _ => s0.restore
    let mut out : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    let mut i := 0
    for l in ls do
      let t : Term := ⟨l.raw[2]⟩
      let n := mkIdent (Name.mkSimple s!"carry_h{i}")
      i := i + 1
      let s ← saveState
      try
        evalTactic (← `(tactic| have $n:ident := $t))
        evalTactic (← `(tactic| carry_norm at $n:ident))
        withMainContext do discard <| getLocalDeclFromUserName n.getId
        out := out.push (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
      catch _ =>
        s.restore
        out := out.push l
    evalTactic (← `(tactic| carry_finish [$out,*]))

end VsaIris.Sym
