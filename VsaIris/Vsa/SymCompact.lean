import VsaIris.Vsa.SymRun

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

def fillR (M : Mem) (lo : Nat) : Nat → (Nat → BitVec 8) → Mem
  | 0, _ => M
  | n + 1, g => (fillR M lo n g).insert (lo + n) (g (lo + n))

theorem fillR_get (M : Mem) (lo : Nat) (g : Nat → BitVec 8) (k : Nat) :
    ∀ n, (fillR M lo n g)[k]? = if lo ≤ k ∧ k < lo + n then some (g k) else M[k]?
  | 0 => by simp only [fillR]; rw [if_neg (by omega)]
  | n + 1 => by
    simp only [fillR]
    rw [Std.ExtHashMap.getElem?_insert, fillR_get M lo g k n]
    by_cases h : lo + n = k
    · subst h; simp
    · simp only [beq_iff_eq, h, ite_false]
      by_cases h2 : lo ≤ k ∧ k < lo + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem fillR_writeLog_in (M : Mem) {lo n a w : Nat} (v : BitVec 64) (g : Nat → BitVec 8)
    (h : lo ≤ a ∧ a + w ≤ lo + n) :
    fillR (writeLog M [(a, w, v)]) lo n g = fillR M lo n g := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get, fillR_get]
  by_cases hk : lo ≤ k ∧ k < lo + n
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, writeLog_out _ _ _ (show OutL [(a, w, v)] k from ⟨show k < a ∨ a + w ≤ k by omega, trivial⟩)]

theorem fillR_writeLog_out (M : Mem) {lo n a w : Nat} (v : BitVec 64) (g : Nat → BitVec 8)
    (h : a + w ≤ lo ∨ lo + n ≤ a) :
    fillR (writeLog M [(a, w, v)]) lo n g = writeLog (fillR M lo n g) [(a, w, v)] := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get]
  by_cases hk : lo ≤ k ∧ k < lo + n
  · rw [if_pos hk, writeLog_out _ _ _ (show OutL [(a, w, v)] k from ⟨show k < a ∨ a + w ≤ k by omega, trivial⟩), fillR_get,
      if_pos hk]
  · rw [if_neg hk]
    rcases pointwise_writeLog [(a, w, v)] k with hp | ⟨b, hp⟩
    · rw [hp, hp, fillR_get, if_neg hk]
    · rw [hp, hp]

theorem imgM_fillR_out (M : Mem) {lo n k : Nat} (g : Nat → BitVec 8)
    (h : k < lo ∨ lo + n ≤ k) : imgM (fillR M lo n g) k = imgM M k := by
  unfold imgM; rw [fillR_get, if_neg (by omega)]

theorem imgM_fillR_in (M : Mem) {lo n k : Nat} (g : Nat → BitVec 8)
    (h : lo ≤ k ∧ k < lo + n) : imgM (fillR M lo n g) k = g k := by
  unfold imgM; rw [fillR_get, if_pos h]; rfl

theorem ldv_fillR_miss (k : MKind) (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + widthOfM k ≤ lo ∨ lo + n ≤ a) : ldv k (fillR M lo n g) a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  exact imgM_fillR_out M g (by omega)

theorem ldv_ld_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 8 ≤ lo ∨ lo + n ≤ a) : ldv .ld (fillR M lo n g) a = ldv .ld M a :=
  ldv_fillR_miss .ld M g h

theorem ldv_lw_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 4 ≤ lo ∨ lo + n ≤ a) : ldv .lw (fillR M lo n g) a = ldv .lw M a :=
  ldv_fillR_miss .lw M g h

theorem ldv_lwu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 4 ≤ lo ∨ lo + n ≤ a) : ldv .lwu (fillR M lo n g) a = ldv .lwu M a :=
  ldv_fillR_miss .lwu M g h

theorem ldv_lh_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 2 ≤ lo ∨ lo + n ≤ a) : ldv .lh (fillR M lo n g) a = ldv .lh M a :=
  ldv_fillR_miss .lh M g h

theorem ldv_lhu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 2 ≤ lo ∨ lo + n ≤ a) : ldv .lhu (fillR M lo n g) a = ldv .lhu M a :=
  ldv_fillR_miss .lhu M g h

theorem ldv_lbu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 1 ≤ lo ∨ lo + n ≤ a) : ldv .lbu (fillR M lo n g) a = ldv .lbu M a :=
  ldv_fillR_miss .lbu M g h

attribute [irreducible] fillR

section SWP

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem swp_forget_region {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (lo n : Nat)
    (h : ∀ g, SWP live text rs S Q pc R (fillR Mt lo n g)) : SWP live text rs S Q pc R Mt := by
  refine swp_congr_mem (fun a _ => ?_) (h (imgM Mt))
  by_cases ha : lo ≤ a ∧ a < lo + n
  · exact imgM_fillR_in Mt _ ha
  · exact imgM_fillR_out Mt _ (by omega)

theorem swp_forget_reg {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (k : Nat)
    (h : ∀ v, SWP live text rs S Q pc (upd R k v) Mt) : SWP live text rs S Q pc R Mt := by
  have := h (R k)
  rwa [upd_self_eq rfl] at this

end SWP

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
partial def updList (e : Expr) (acc : Array (Nat × Expr)) : MetaM (Expr × Array (Nat × Expr)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``upd 3 then
    let args := e.getAppArgs
    let kn? ← match args[1]!.nat? with
      | some n => pure (some n)
      | none => (evalNat args[1]!).run
    let some kn := kn? | return (e, acc)
    updList args[0]! (acc.push (kn, args[2]!))
  else return (e, acc)

/-- Drop the shadowed register updates of the main goal when the chain has at least `min`
updates. The equality of the two register files is `updL_dedup`; the kernel evaluates `dedupL`
on the literal keys. -/
def compactRegs (min : Nat) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.getAppFn.isConstOf ``SWP do throwError "nx_compactR: not an SWP goal"
  let args := ty.getAppArgs
  let (base, ups) ← updList args[6]! #[]
  if ups.size < min then return
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

/-- `nx_compactR`: drop the shadowed register updates of an `SWP` goal. -/
elab "nx_compactR" : tactic => compactRegs 0

/-- `nx_compactIf n`: as `nx_compactR`, only when the chain has at least `n` updates. -/
elab "nx_compactIf " n:num : tactic => compactRegs n.getNat

end CompactK

end VsaIris.Sym
