import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.SymCompact

namespace VsaIris.Sym

theorem toNat_sub_lit {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64) (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have := x.isLt
  omega

syntax "nx_fdisch" : tactic
macro_rules
  | `(tactic| nx_fdisch) => `(tactic| (
      (try simp only [BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.add_assoc, BitVec.reduceAdd])
      (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, toNat_sub_lit,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd])
      omega))

macro_rules | `(tactic| nx_addr) => `(tactic| nx_fdisch)

syntax "nx_forget " term:max term:max : tactic
macro_rules
  | `(tactic| nx_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_fdisch) only [fillR_writeLog_in, fillR_writeLog_out])))

syntax "nx_forget_reg " num+ : tactic
macro_rules
  | `(tactic| nx_forget_reg $ks*) => do
    let mut t ← `(tactic| skip)
    for k in ks do
      t ← `(tactic| ($t; apply swp_forget_reg $k; intro _))
    return t

section CompactR

open Lean Elab Tactic Meta

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

macro "nx_regEq" : tactic => `(tactic| (
  intro r hr _
  simp only [iRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, reduceIte]))

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

end CompactR

macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, VsaIris.Interp.ldv_lw_miss, VsaIris.Interp.ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss, ldv_ld_fillR_miss, ldv_lw_fillR_miss,
      ldv_lwu_fillR_miss, ldv_lh_fillR_miss, ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])

open Lean Elab Tactic Meta in

elab "nx_clear_conds" : tactic => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let lctx ← getLCtx
    return lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.userName.eraseMacroScopes == `hc then acc.push d.fvarId else acc
  let g ← g.tryClearMany fvs
  replaceMainGoal [g]

end VsaIris.Sym
