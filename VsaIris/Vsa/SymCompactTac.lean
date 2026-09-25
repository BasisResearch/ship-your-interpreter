import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.SymCompact

/-!
# Compacting a symbolic run's state, as tactics (lane N3)

Over `SymCompact.lean`'s lemmas, for `SWP`/`SWPO` goals of any run:

* `nx_forget lo n`: forget the bytes `[lo, lo + n)` and erase the stores
  inside them;
* `nx_forget_sp lo`: forget the bytes from `lo` up to the current `sp` (dead
  by the ABI);
* `nx_forget_reg k₁ …`: forget dead registers' values;
* `nx_compactR`: the register file with one update per register.
-/

namespace VsaIris.Sym

theorem toNat_sub_lit {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64) (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have := x.isLt
  omega

/-- The address side conditions of `fillR_writeLog_in`/`_out`: `BitVec`
offsets from a base as `Nat` arithmetic. -/
syntax "nx_fdisch" : tactic
macro_rules
  | `(tactic| nx_fdisch) => `(tactic| (
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, toNat_sub_lit,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd])
      omega))

/-- Address side conditions with nested literal offsets (`sp + c₁ + c₂`),
as `nx_fdisch` normalizes them. -/
macro_rules | `(tactic| nx_addr) => `(tactic| nx_fdisch)

/-- `nx_forget lo n`: forget the bytes `[lo, lo + n)` (a dead stack region)
and erase the stores inside it (`swp_forget_region`). -/
syntax "nx_forget " term:max term:max : tactic
macro_rules
  | `(tactic| nx_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_fdisch) only [fillR_writeLog_in, fillR_writeLog_out])))

/-- `nx_forget_reg k₁ k₂ …`: forget dead registers' values
(`swp_forget_reg`). -/
syntax "nx_forget_reg " num+ : tactic
macro_rules
  | `(tactic| nx_forget_reg $ks*) => do
    let mut t ← `(tactic| skip)
    for k in ks do
      t ← `(tactic| ($t; apply swp_forget_reg $k; intro _))
    return t


/-! ## Compacting the register file -/

section CompactR

open Lean Elab Tactic Meta

/-- The updates of an `upd` chain, outermost first, one per register, and its
base. -/
partial def updChain (e : Expr) (seen : List Nat) (acc : Array (Expr × Expr)) :
    MetaM (Expr × Array (Expr × Expr)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``upd 3 then
    let args := e.getAppArgs
    let k := args[1]!
    let kn? ← match k.nat? with
      | some n => pure (some n)
      | none => (evalNat k).run
    let some kn := kn? | return (e, acc)
    if seen.contains kn then updChain args[0]! seen acc
    else updChain args[0]! (kn :: seen) (acc.push (k, args[2]!))
  else return (e, acc)

/-- Two register files agree on every owned register: one literal register at
a time. -/
macro "nx_regEq" : tactic => `(tactic| (
  intro r hr _
  simp only [iRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, reduceIte]))

/-- `nx_compactR`: replace the register file of an `SWP` goal by the same
function with one update per register (`swp_congr`, checked per owned
register). -/
elab "nx_compactR" : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "nx_compactR: not an SWP goal"
  let args := ty.getAppArgs
  let R := args[6]!
  let (base, ups) ← g.withContext (updChain R [] #[])
  let mut R' := base
  for (k, v) in ups.reverse do
    R' := mkAppN (mkConst ``upd) #[R', k, v]
  let R'stx ← g.withContext (Term.exprToSyntax R')
  evalTactic (← `(tactic| refine swp_congr (R' := $R'stx) ?_ ?_))
  evalTactic (← `(tactic| nx_regEq))

/-- `nx_forget_sp lo`: forget the bytes from `lo` up to the current stack
pointer (dead by the ABI), read off the goal's register file. -/
elab "nx_forget_sp " lo:term:max : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "nx_forget_sp: not an SWP goal"
  let R := ty.getAppArgs[6]!
  let (base, ups) ← g.withContext (updChain R [] #[])
  let spv ← match ← g.withContext (ups.findM? fun (k, _) => do
      return (← (evalNat k).run) == some 2 || k.nat? == some 2) with
    | some (_, v) => pure v
    | none => pure (mkApp base (mkNatLit 2))
  let spStx ← g.withContext (Term.exprToSyntax spv)
  evalTactic (← `(tactic| nx_forget $lo (($spStx).toNat - $lo)))

end CompactR

/-- Store forwarding (lane N1's `nx_mem`) through forgotten regions too. -/
macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, VsaIris.Interp.ldv_lw_miss, VsaIris.Interp.ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss, ldv_ld_fillR_miss, ldv_lw_fillR_miss,
      ldv_lwu_fillR_miss, ldv_lh_fillR_miss, ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])

open Lean Elab Tactic Meta in
/-- `nx_clear_conds`: clear the branch conditions a run accumulated (`hc✝`),
which only slow later side conditions down. -/
elab "nx_clear_conds" : tactic => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let lctx ← getLCtx
    return lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.userName.eraseMacroScopes == `hc then acc.push d.fvarId else acc
  let g ← g.tryClearMany fvs
  replaceMainGoal [g]

end VsaIris.Sym
