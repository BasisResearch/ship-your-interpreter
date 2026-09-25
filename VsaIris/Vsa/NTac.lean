import VsaIris.Vsa.NewlibSteps
import VsaIris.Vsa.SymCompact
import VsaIris.Interp.ITac
import VsaIris.Interp.Bridge

/-!
# Driving newlib's step table (lane N3)

`nx_run h` is `ix_run` (`VsaIris/Interp/ITac.lean`) over newlib's step table
(`nt_<pc>`, `ntD_`, `ntT_`, `ntH_`, `ntO_`; `scripts/gen_interp_steps.py
--target newlib`) from an `NW … pc R Mt` goal. Callers extend `sx_side` and
pass the facts of their run with `using`.
-/

namespace VsaIris.Sym

open Lean Elab Tactic Meta

open Vsa.Sim Vsa.MemRepr in
theorem ldv_lwu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lwu (writeLog Mt [(b, w, v)]) a = ldv .lwu Mt a := ldv_store_miss .lwu Mt v h

open Vsa.Sim Vsa.MemRepr in
theorem ldv_lh_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lh (writeLog Mt [(b, w, v)]) a = ldv .lh Mt a := ldv_store_miss .lh Mt v h

open Vsa.Sim Vsa.MemRepr in
theorem ldv_lhu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lhu (writeLog Mt [(b, w, v)]) a = ldv .lhu Mt a := ldv_store_miss .lhu Mt v h

open Vsa.Sim Vsa.MemRepr in
theorem ldv_lbu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 1 ≤ b ∨ b + w ≤ a) :
    ldv .lbu (writeLog Mt [(b, w, v)]) a = ldv .lbu Mt a := ldv_store_miss .lbu Mt v h

/-- Store forwarding for newlib runs: every load width through a disjoint
store, doubleword hits. -/
syntax "nx_mem" : tactic
macro_rules
  | `(tactic| nx_mem) =>
    `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss,
      ldv_lwu_miss, ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss] at *)

/-- The register file with one update per register, sorted. -/
syntax "nx_regs" : tactic

/-- Literal arithmetic folded, and a base plus literal offsets as one offset
(`s + c₁ + c₂` to `s + (c₁ + c₂)`), so addresses stay shallow for `omega`. -/
syntax "nx_arith" : tactic
macro_rules
  | `(tactic| nx_arith) =>
    `(tactic| simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul,
      BitVec.reduceOr, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceHShiftLeft,
      BitVec.reduceHShiftRight, BitVec.reduceShiftLeft, BitVec.reduceUShiftRight,
      BitVec.reduceShiftLeftShiftLeft, BitVec.add_zero] at *)

/-- `ix_run`'s normalizer with newlib's store forwarding, and the caller's
facts applied again after it (a fact about the entry memory applies once the
load is forwarded to it), everywhere: a branch condition is a hypothesis. Pass
facts as projections of one structure (`hF.x`), not as local hypotheses, which
`simp … at *` would rewrite to `True`. -/
def nxNorm (facts : Array Term) : TacticM Syntax := do
  if facts.isEmpty then
    `(tactic| ((try sx_norm) <;> (try nx_arith) <;> (try nx_tab) <;> (try sx_norm) <;> (try nx_mem) <;>
      (try sx_norm) <;> (try nx_arith) <;> nx_regs))
  else
    let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
    `(tactic| ((try sx_norm) <;> (try nx_arith) <;> (try simp only [$lems,*] at *) <;> (try nx_tab) <;>
      (try sx_norm) <;> (try nx_mem) <;> (try simp only [$lems,*] at *) <;> (try sx_norm) <;>
      (try nx_arith) <;> nx_regs))

/-- `nx_run h`, `nx_run [n] h`, `nx_run h using [e,…]`, `nx_run h at pc…`. -/
syntax "nx_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

/-- `nx_run1`: `nx_run` stopping at an undecided branch. -/
syntax "nx_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| nx_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) =>
    ixRunCore true n h fs stops ["nt", "ntD", "ntT", "ntH", "ntO"] nxNorm true 55
  | `(tactic| nx_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) =>
    ixRunCore false n h fs stops ["nt", "ntD", "ntT", "ntH", "ntO"] nxNorm true 55

/-! ## Halfword loads -/

section Half

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast LeanRV64DExecutable.Functions

theorem bytesAt2 (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 2 = [f a, f (a + 1)] := rfl

theorem toNat_append2 (f : Nat → BitVec 8) (a : Nat) :
    (((f (a + 1)).append (f a) : BitVec (8 * 2))).toNat = imgLE f a 2 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt
  have h1 := (f (a + 1)).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- An unsigned halfword load of a pinned field. -/
theorem ldv_lhu_readLE {m : Mem} {a v : Nat} (h : readLE m a 2 = some v) :
    ldv .lhu m a = BitVec.ofNat 64 v := by
  have hw := toNat_append2 (imgM m) a
  rw [show imgLE (imgM m) a 2 = v from readLE_memImg h] at hw
  have hv : v < 2 ^ 16 := by
    have := imgLE_lt (imgM m) a 2
    rw [show imgLE (imgM m) a 2 = v from readLE_memImg h] at this; omega
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [hw, BitVec.toNat_ofNat]

/-- A signed halfword load of a pinned field below `2^15`. -/
theorem ldv_lh_readLE {m : Mem} {a v : Nat} (h : readLE m a 2 = some v) (hv : v < 2 ^ 15) :
    ldv .lh m a = BitVec.ofNat 64 v := by
  have hw := toNat_append2 (imgM m) a
  rw [show imgLE (imgM m) a 2 = v from readLE_memImg h] at hw
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.toNat_signExtend]
  have hmsb : (((imgM m (a + 1)).append (imgM m a) : BitVec (8 * 2))).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hw, BitVec.toNat_ofNat]

theorem imgM_sh_lo (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 2, v)]) a = (shData v).extractLsb' 0 8 := by
  simp only [imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW]
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp), Std.ExtHashMap.getElem?_insert_self]
  rfl

theorem imgM_sh_hi (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 2, v)]) (a + 1) = (shData v).extractLsb' 8 8 := by
  simp only [imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW]
  rw [Std.ExtHashMap.getElem?_insert_self]
  rfl

/-- A halfword load at the address of the latest halfword store. -/
theorem ldv_lh_sh_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lh (writeLog Mt [(b, 2, v)]) a =
      sign_extend (m := 64) (((shData v).extractLsb' 8 8).append ((shData v).extractLsb' 0 8) :
        BitVec (8 * 2)) := by
  subst h
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ,
    imgM_sh_lo, imgM_sh_hi]

/-- An unsigned halfword load at the address of the latest halfword store. -/
theorem ldv_lhu_sh_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lhu (writeLog Mt [(b, 2, v)]) a =
      LeanRV64DExecutable.zero_extend (m := 64) (((shData v).extractLsb' 8 8).append ((shData v).extractLsb' 0 8) :
        BitVec (8 * 2)) := by
  subst h
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ,
    imgM_sh_lo, imgM_sh_hi]

end Half

/-- Store forwarding, extended with halfword hits (`sh` then `lh`/`lhu`). -/
macro_rules
  | `(tactic| nx_mem) =>
    `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss,
      ldv_lwu_miss, ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lh_sh_hit, ldv_lhu_sh_hit,
      Vsa.Sim.shData, BitVec.reduceExtractLsb', BitVec.reduceAppend, Sail.BitVec.extractLsb,
      BitVec.reduceExtractLsb, LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend,
      BitVec.reduceSetWidth, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.reduceOr, BitVec.reduceAnd] at *)

/-- Store forwarding, extended with the forgotten regions (`fillR`) of
`SymCompact.lean`. -/
macro_rules
  | `(tactic| nx_mem) =>
    `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss,
      ldv_lwu_miss, ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lh_sh_hit, ldv_lhu_sh_hit,
      ldv_ld_fillR_miss, ldv_lw_fillR_miss, ldv_lwu_fillR_miss, ldv_lh_fillR_miss,
      ldv_lhu_fillR_miss, ldv_lbu_fillR_miss,
      Vsa.Sim.shData, BitVec.reduceExtractLsb', BitVec.reduceAppend, Sail.BitVec.extractLsb,
      BitVec.reduceExtractLsb, LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend,
      BitVec.reduceSetWidth, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.reduceOr, BitVec.reduceAnd] at *)

/-- `nx_forget lo n`: forget the bytes `[lo, lo + n)` (a dead stack region)
and erase the stores inside it (`swp_forget_region`). -/
syntax "nx_forget " term:max term:max : tactic
macro_rules
  | `(tactic| nx_forget $lo $n) =>
    `(tactic| (apply swp_forget_region $lo $n <;> intro _ <;>
      (try simp (disch := sx_addr) only [fillR_writeLog_in, fillR_writeLog_out])))

/-- `nx_forget_reg k₁ k₂ …`: forget dead registers' values
(`swp_forget_reg`). -/
syntax "nx_forget_reg " num+ : tactic
macro_rules
  | `(tactic| nx_forget_reg $ks*) => do
    let mut t ← `(tactic| skip)
    for k in ks do
      t ← `(tactic| ($t; apply swp_forget_reg $k; intro _))
    return t

macro_rules
  | `(tactic| nx_regs) => `(tactic| try simp only [upd_upd_same, upd_upd_ne_same, upd_upd_lt])

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
  simp only [nRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
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

end VsaIris.Sym
