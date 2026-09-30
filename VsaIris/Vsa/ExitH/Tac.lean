import VsaIris.Vsa.ExitH.Loads
import VsaIris.Vsa.SymCompact

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast

namespace XH

scoped macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss,
      ldv_ld_fillR_miss, ldv_lw_fillR_miss, ldv_lwu_fillR_miss, ldv_lh_fillR_miss,
      ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])
end XH

section Compact

open Lean Elab Tactic Meta

elab "xh_clean" : tactic => do
  let g ← getMainGoal
  let fs ← g.withContext do
    let lctx ← getLCtx
    return lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.userName.hasMacroScopes then acc.push d.fvarId else acc
  let g' ← g.tryClearMany fs
  replaceMainGoal [g']

partial def xhUpdChain (e : Expr) (seen : List Nat) (acc : Array (Expr × Expr)) :
    MetaM (Expr × Array (Expr × Expr)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``upd 3 then
    let args := e.getAppArgs
    let k := args[1]!
    let kn? ← match k.nat? with
      | some n => pure (some n)
      | none => (evalNat k).run
    let some kn := kn? | return (e, acc)
    if seen.contains kn then xhUpdChain args[0]! seen acc
    else xhUpdChain args[0]! (kn :: seen) (acc.push (k, args[2]!))
  else return (e, acc)

macro "xh_regEq" : tactic => `(tactic| (
  intro r hr _
  simp only [iRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, reduceIte]))

elab "xh_compactR" : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "xh_compactR: not an SWP goal"
  let R := ty.getAppArgs[6]!
  let (base, ups) ← g.withContext (xhUpdChain R [] #[])
  let mut R' := base
  for (k, v) in ups.reverse do
    R' := mkAppN (mkConst ``upd) #[R', k, v]
  let R'stx ← g.withContext (Term.exprToSyntax R')
  evalTactic (← `(tactic| refine swp_congr (R' := $R'stx) ?_ ?_))
  evalTactic (← `(tactic| xh_regEq))

syntax "xh_forget " term:max term:max : tactic
macro_rules
  | `(tactic| xh_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_addr) only [fillR_writeLog_in, fillR_writeLog_out])))

elab "xh_forget_sp " lo:term:max : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "xh_forget_sp: not an SWP goal"
  let R := ty.getAppArgs[6]!
  let (base, ups) ← g.withContext (xhUpdChain R [] #[])
  let spv ← match ← g.withContext (ups.findM? fun (k, _) => do
      return (← (evalNat k).run) == some 2 || k.nat? == some 2) with
    | some (_, v) => pure v
    | none => pure (mkApp base (mkNatLit 2))
  let spStx ← g.withContext (Term.exprToSyntax spv)
  evalTactic (← `(tactic| xh_forget $lo (($spStx).toNat - $lo)))

end Compact

set_option hygiene false in

macro "xh_end" : tactic => `(tactic| (intros; xh_clean; xh_compactR; exact hk _ _ ⟨by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, h2, h8],
    by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, h8],
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]⟩))

end VsaIris.Sym
