import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.SymCompact
import VsaIris.Vsa.Dbm

namespace VsaIris.Sym

theorem toNat_sub_lit {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64) (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have := x.isLt
  omega

syntax "nx_fdisch" : tactic
macro_rules
  | `(tactic| nx_fdisch) => `(tactic| (
      (try simp_set nx_subneg_set)
      (try simp (disch := omega_dcn) only [toNat_add_lit, toNat_add_neg, toNat_sub_lit,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd])
      omega_dc))

attribute [nx_subneg_set] BitVec.sub_eq_add_neg BitVec.reduceNeg BitVec.add_assoc BitVec.reduceAdd

macro_rules | `(tactic| nx_addr) => `(tactic| nx_fdisch)

namespace Win

/-- Under `open scoped Win`, the forget discharger tries the window keys first. -/
scoped macro_rules | `(tactic| nx_fdisch) => `(tactic| win_key)

end Win

syntax "nx_forget " term:max term:max : tactic
macro_rules
  | `(tactic| nx_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := nx_fdisch) only [fillR_writeLog_out, fillR_writeLog_in]) <;>
      (try simp (disch := nx_fdisch) only [fillR_fillR_ge, fillR_fillR_le])))

open Lean Elab Tactic Meta in
/-- `nx_forget_sp lo`: forget the dead stack `[lo, sp)` below the current stack pointer. -/
elab "nx_forget_sp " lo:term:max : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext (do whnfR (← instantiateMVars (← g.getType)))
  unless ty.getAppFn.isConstOf ``SWP do throwError "nx_forget_sp: not an SWP goal"
  let R := ty.getAppArgs[6]!
  let (base, ups) ← g.withContext (updList R #[])
  let spv := match ups.find? (·.1 == 2) with
    | some (_, v) => v
    | none => mkApp base (mkNatLit 2)
  let spStx ← g.withContext (Term.exprToSyntax spv)
  evalTactic (← `(tactic| nx_forget $lo (($spStx).toNat - $lo)))

syntax "nx_forget_reg " num+ : tactic
macro_rules
  | `(tactic| nx_forget_reg $ks*) => do
    let mut t ← `(tactic| skip)
    for k in ks do
      t ← `(tactic| ($t; apply swp_forget_reg $k; intro _))
    return t

attribute [nx_mem_set] ldv_store_hit ldv_ld_hit_eq
      ldv_ld_miss VsaIris.Interp.ldv_lw_miss VsaIris.Interp.ldv_lw_store8 ldv_lw_hit ldv_lh_hit ldv_lhu_hit ldv_lbu_hit
      ldv_lh_miss ldv_lhu_miss ldv_lbu_miss ldv_lwu_miss ldv_ld_fillR_miss ldv_lw_fillR_miss
      ldv_lwu_fillR_miss ldv_lh_fillR_miss ldv_lhu_fillR_miss ldv_lbu_fillR_miss

macro_rules
  | `(tactic| nx_mem) => `(tactic| simp_set (disch := nx_addr) nx_mem_set)

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
