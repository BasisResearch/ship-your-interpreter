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

/-! ### Register-file compaction by one kernel evaluation -/

/-- An `upd` chain as a list, newest first. -/
def updL (R : Nat → BitVec 64) : List (Nat × BitVec 64) → Nat → BitVec 64
  | [] => R
  | (k, v) :: t => upd (updL R t) k v

/-- Keep the newest update of each register. -/
def dedupL : List (Nat × BitVec 64) → List Nat → List (Nat × BitVec 64)
  | [], _ => []
  | (k, v) :: t, seen => bif seen.contains k then dedupL t seen else (k, v) :: dedupL t (k :: seen)

theorem updL_dedup (R : Nat → BitVec 64) :
    ∀ (L : List (Nat × BitVec 64)) (seen : List Nat) (r : Nat), r ∉ seen →
      updL R (dedupL L seen) r = updL R L r
  | [], _, _, _ => rfl
  | (k, v) :: t, seen, r, hr => by
    unfold dedupL
    cases hc : seen.contains k
    · simp only [Bool.cond_false, updL, upd]
      by_cases h : r = k
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact updL_dedup R t (k :: seen) r (by simp only [List.mem_cons, not_or]; exact ⟨h, hr⟩)
    · simp only [Bool.cond_true, updL, upd]
      have hk : k ∈ seen := List.contains_iff_mem.mp hc
      rw [if_neg (fun h => hr (by rw [h]; exact hk))]
      exact updL_dedup R t seen r hr

theorem swp_compact {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {Mt : Mem}
    (R : Nat → BitVec 64) (L : List (Nat × BitVec 64))
    (h : SWP live text rs S Q pc (updL R (dedupL L [])) Mt) : SWP live text rs S Q pc (updL R L) Mt :=
  swp_congr (fun r _ _ => updL_dedup R L [] r List.not_mem_nil) h

section CompactK
open Lean Elab Tactic Meta

/-- The chain of an `upd` term, newest first, with literal keys. -/
partial def xhUpdList (e : Expr) (acc : Array (Nat × Expr)) : MetaM (Expr × Array (Nat × Expr)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``upd 3 then
    let args := e.getAppArgs
    let kn? ← match args[1]!.nat? with
      | some n => pure (some n)
      | none => (evalNat args[1]!).run
    let some kn := kn? | return (e, acc)
    xhUpdList args[0]! (acc.push (kn, args[2]!))
  else return (e, acc)

/-- `xh_compactK`: drop the shadowed register updates. The equality of the two register files is
`updL_dedup`; the kernel evaluates `dedupL` on the literal keys. -/
elab "xh_compactK" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.getAppFn.isConstOf ``SWP do throwError "xh_compactK: not an SWP goal"
  let args := ty.getAppArgs
  let (base, ups) ← xhUpdList args[6]! #[]
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkApp (mkConst ``BitVec) (mkNatLit 64)]
  let mut L ← mkAppOptM ``List.nil #[pairTy]
  let mut R' := base
  let mut seen : Array Nat := #[]
  let mut kept : Array (Nat × Expr) := #[]
  for (k, v) in ups do
    unless seen.contains k do
      seen := seen.push k
      kept := kept.push (k, v)
  for (k, v) in ups.reverse do
    L ← mkAppM ``List.cons #[← mkAppM ``Prod.mk #[toExpr k, v], L]
  for (k, v) in kept.reverse do
    R' := mkApp3 (mkConst ``upd) R' (toExpr k) v
  let newTy := mkAppN ty.getAppFn (args.set! 6 R')
  let m ← mkFreshExprSyntheticOpaqueMVar newTy (← g.getTag)
  let pf := mkAppN (mkConst ``swp_compact) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[7]!, base, L, m]
  g.assign pf
  replaceMainGoal [m.mvarId!]

end CompactK

/-! ### One forgotten-stack layer -/

/-- The forgotten bytes of two nested forgets over the same base. -/
def mergeG (lo n' : Nat) (g' g : Nat → BitVec 8) : Nat → BitVec 8 :=
  fun a => if a < lo + n' then g' a else g a

theorem fillR_fillR_ge (M : Mem) {lo n n' : Nat} (g g' : Nat → BitVec 8) (h : n ≤ n') :
    fillR (fillR M lo n g) lo n' g' = fillR M lo n' g' := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get, fillR_get, fillR_get]
  by_cases h1 : lo ≤ k ∧ k < lo + n'
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_neg (show ¬ (lo ≤ k ∧ k < lo + n) by omega)]

theorem fillR_fillR_le (M : Mem) {lo n n' : Nat} (g g' : Nat → BitVec 8) (h : n' ≤ n) :
    fillR (fillR M lo n g) lo n' g' = fillR M lo n (mergeG lo n' g' g) := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get, fillR_get, fillR_get]
  by_cases h1 : lo ≤ k ∧ k < lo + n'
  · rw [if_pos h1, if_pos (show lo ≤ k ∧ k < lo + n by omega)]
    unfold mergeG; rw [if_pos h1.2]
  · rw [if_neg h1]
    by_cases h2 : lo ≤ k ∧ k < lo + n
    · rw [if_pos h2, if_pos h2]
      unfold mergeG; rw [if_neg (show ¬ k < lo + n' by omega)]
    · rw [if_neg h2, if_neg h2]

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

syntax "xh_forget " term:max term:max : tactic
macro_rules
  | `(tactic| xh_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_addr) only [fillR_writeLog_out, fillR_writeLog_in]) <;>
      (try simp (disch := nx_addr) only [fillR_fillR_ge, fillR_fillR_le])))

elab "xh_forget_sp " lo:term:max : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "xh_forget_sp: not an SWP goal"
  let R := ty.getAppArgs[6]!
  let (base, ups) ← g.withContext (xhUpdList R #[])
  let spv := match ups.find? (·.1 == 2) with
    | some (_, v) => v
    | none => mkApp base (mkNatLit 2)
  let spStx ← g.withContext (Term.exprToSyntax spv)
  evalTactic (← `(tactic| xh_forget $lo (($spStx).toNat - $lo)))

end Compact

open Lean Elab Tactic in
/-- The run reached exactly one state: every branch of the piece was decided. -/
elab "xh_one" : tactic => do
  let gs ← getUnsolvedGoals
  unless gs.length == 1 do
    throwError "xh_one: {gs.length} leftover goals (an undecided branch or an open side goal)"

/-- Facts every piece of the exit run normalises with: the entry registers, the FILE fields of
`CloseMt`, the tested bits of the console flags word (`ConFlags`), and the literal folders. -/
def xhFacts : Array Lean.Name := #[`h2, `h8, `h11, `hC.atexit, `hC.handler, `hC.glueNext, `hC.glueCount,
  `hC.glueFiles, `hC.sinit, `hC.in_flagsU, `hC.in_flags, `hC.in_fd, `hC.in_r, `hC.in_ur, `hC.in_cookie,
  `hC.in_close, `hC.in_ub, `hC.in_lb, `hC.in_lock, `hC.in_mode, `hC.out_flagsU, `hC.out_flags, `hC.out_fd,
  `hC.out_base, `hC.out_p, `hC.out_cookie, `hC.out_close, `hC.out_ub, `hC.out_lb, `hC.out_lock, `hC.out_mode,
  `hF.ne0, `hF.gt1, `hF.b200, `hF.b8, `hF.b3, `hF.b80,
  ``ne_eq, ``not_false_eq_true, ``BitVec.add_assoc, ``BitVec.reduceAnd, ``BitVec.reduceOr, ``BitVec.reduceSub, ``BitVec.reduceMul,
  ``BitVec.reduceShiftLeft, ``BitVec.reduceHShiftLeft, ``Nat.reducePow, ``Nat.reduceMod, ``BitVec.reduceOfNat]

set_option hygiene false in
open Lean in
/-- Run `n` instructions of the exit path with `xhFacts` plus the listed facts, then drop the
branch hypotheses of the explored prefix so the leftover states only the reached machine state.
Fails unless every branch was decided. -/
macro "xh_run " n:num " using " "[" fs:term,* "]" : tactic => do
  let all : Array Term := xhFacts.map (fun n => (mkIdent n : Term)) ++ fs.getElems
  `(tactic| (nx_run [$n] hlive using [$all,*] at 2147501960; all_goals xh_clean; xh_one))

set_option hygiene false in
/-- First piece: name the stack-pointer geometry, then run. -/
macro "xh_start " n:num " using " "[" fs:term,* "]" : tactic => `(tactic| (
    have hs1 := hs.lo; have hs2 := hs.hi; have hs3 := hs.align; have hs4 := hs.place
    xh_run $n using [$fs,*]))

set_option hygiene false in
/-- Later pieces: forget the dead stack below `sp` (one merged layer), compact the register file, then run. -/
macro "xh_step " n:num " using " "[" fs:term,* "]" : tactic => `(tactic| (intros; xh_clean; xh_forget_sp (s.toNat - 256); xh_compactK; xh_run $n using [$fs,*]))

section Branch

open Lean Elab Command Term Meta

/-- `#ix_branch name (h : H) … from prev by tac`: a piece that starts at `prev`'s leftover state
under additional hypotheses. Two runs that agree up to `prev` share the pieces up to `prev`
and each continue with its own `#ix_branch`. -/
syntax (name := ixBranch) "#ix_branch " ident bracketedBinder+ " from " ident " by " tacticSeq : command

@[command_elab ixBranch] def elabIxBranch : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let prev ← liftCoreM <| realizeGlobalConstNoOverload stx[4]
  liftTermElabM do
    let info ← getConstInfo prev
    forallTelescope info.type fun xs _ => do
      let nv ← pieceVars xs
      let some hk := xs[nv]? | throwError "#ix_branch: {prev} has no leftover"
      forallTelescope (← inferType hk) fun ys T => do
        Term.elabBinders stx[2].getArgs fun zs => do
          Term.synthesizeSyntheticMVarsNoPostponing
          ixAddPiece declName (xs.extract 0 nv ++ ys ++ zs) T stx[6] true (xs.extract nv xs.size)

end Branch

set_option hygiene false in

macro "xh_end" : tactic => `(tactic| (intros; xh_clean; xh_compactK; exact hk _ _ ⟨by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, h2, h8],
    by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, h8],
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]⟩))

end VsaIris.Sym
