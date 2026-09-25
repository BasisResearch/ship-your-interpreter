import VsaIris.Vsa.ExitH.Loads
import VsaIris.Vsa.SymCompact

/-!
# Driving `exit`'s interior in pieces (lane N4)

A long run is a chain of `#ix_piece`s, each `xh_step`: drop the previous
piece's branch hypotheses (`xh_clean`), forget the dead stack below `sp`
(`xh_forget_sp`, `SymCompact.swp_forget_region`), keep one update per
register (`xh_compactR`, `swp_congr`), then `nx_run` a bounded number of
steps. The compaction tactics are lane N3's (`SymCompact.lean`), over the
stdio step table's `iRegs`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast

/-- Store forwarding through a forgotten region (`fillR`) too. -/
macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss,
      ldv_ld_fillR_miss, ldv_lw_fillR_miss, ldv_lwu_fillR_miss, ldv_lh_fillR_miss,
      ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])

section Compact

open Lean Elab Tactic Meta

/-- `xh_clean`: clear every hypothesis a run introduced (inaccessible names:
the conditions of the branches it took, pruned or not). -/
elab "xh_clean" : tactic => do
  let g ← getMainGoal
  let fs ← g.withContext do
    let lctx ← getLCtx
    return lctx.foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.userName.hasMacroScopes then acc.push d.fvarId else acc
  let g' ← g.tryClearMany fs
  replaceMainGoal [g']

/-- The updates of an `upd` chain, outermost first, one per register, and its
base. -/
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

/-- Two register files agree on every owned register (`iRegs`): one literal
register at a time. -/
macro "xh_regEq" : tactic => `(tactic| (
  intro r hr _
  simp only [iRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, reduceIte]))

/-- `xh_compactR`: the register file of an `SWP` goal with one update per
register (`swp_congr`). -/
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

/-- `xh_forget lo n`: forget the bytes `[lo, lo + n)` and erase the stores
inside them (`swp_forget_region`). -/
syntax "xh_forget " term:max term:max : tactic
macro_rules
  | `(tactic| xh_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_addr) only [fillR_writeLog_in, fillR_writeLog_out])))

/-- `xh_forget_sp lo`: forget the bytes from `lo` up to the current `sp`
(dead by the ABI), read off the goal's register file. -/
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
/-- The last piece: the state at `0x80004788` meets `ExitEnd`, and the
continuation `hk` takes over. -/
macro "xh_end" : tactic => `(tactic| (intros; xh_clean; xh_compactR; exact hk _ _ ⟨by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, h2, h8],
    by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, h8],
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]⟩))

end VsaIris.Sym

namespace VsaIris.Sym

open Lean Meta Elab Command in
/-- `#xh_pcs p`: the PCs of the symbolic states in a piece's statement, its
leftovers first (a development aid). -/
elab "#xh_pcs " n:ident : command => liftTermElabM do
  let c ← getConstInfo (← realizeGlobalConstNoOverload n)
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .forallE _ d b _ => go b (go d acc)
    | _ => if e.getAppFn.isConstOf ``SWP || e.getAppFn.isConstOf ``NW then
        acc.push (if e.getAppFn.isConstOf ``NW then e.getAppArgs[5]! else e.getAppArgs[6]!) else acc
  let pcs := go c.type #[]
  let hex (p : Expr) : String :=
    match p.getAppArgs.back?.bind (·.nat?) with
    | some v => "0x" ++ String.ofList (Nat.toDigits 16 v)
    | none => toString p
  logInfo m!"{n}: {pcs.toList.map hex}"

end VsaIris.Sym
