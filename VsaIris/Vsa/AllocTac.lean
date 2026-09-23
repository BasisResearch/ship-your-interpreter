import VsaIris.Vsa.AllocSteps

/-!
# Driving the step table

`sx_run h` runs the allocator's code symbolically from an `AW … pc R Mt`
goal. It applies the step lemma `st_<pc>` named by the goal's PC literal
(with `h : ∀ p ∈ allocText, live p.1`), and repeats on the continuation. Side
conditions go to `sx_side`, a tactic the caller extends with `macro_rules`.
By default it tries `decide`, then `simp` with the register-file lemmas, then
`omega`. A branch whose condition `sx_side` refutes is pruned. The run stops
at a branch it cannot decide, at a `ret` (PC `R 1`), or after the fuel
(default 400 instructions; `sx_run [n] h` sets it). It leaves the undischarged side conditions and
the reached goals.

`sx_norm` normalizes register-file lookups (`upd`) and `sign_extend` of
literals, which keeps the symbolic values readable.
-/

namespace VsaIris.Sym

open Lean Elab Tactic Meta

/-- Side-condition discharger. Extend with `macro_rules | `(tactic| sx_side) => …`. -/
syntax "sx_side" : tactic

/-- A register file read at a literal register. -/
theorem upd_apply (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) (r : Nat) :
    upd R k v r = if r = k then v else R r := rfl

/-! ### `toNat` of the allocator's masks -/

theorem toNat_and_m16 (x : BitVec 64) : (x &&& 18446744073709551600#64).toNat = x.toNat / 16 * 16 := by
  rw [show (18446744073709551600#64 : BitVec 64) = BitVec.allOnes 64 <<< 4 by decide,
    VsaIris.MallocFast.and_high_toNat x 4 (by decide)]

theorem toNat_and_m4 (x : BitVec 64) : (x &&& 18446744073709551612#64).toNat = x.toNat / 4 * 4 := by
  rw [show (18446744073709551612#64 : BitVec 64) = BitVec.allOnes 64 <<< 2 by decide,
    VsaIris.MallocFast.and_high_toNat x 2 (by decide)]

theorem toNat_and_m2 (x : BitVec 64) : (x &&& 18446744073709551614#64).toNat = x.toNat / 2 * 2 := by
  rw [show (18446744073709551614#64 : BitVec 64) = BitVec.allOnes 64 <<< 1 by decide,
    VsaIris.MallocFast.and_high_toNat x 1 (by decide)]

/-- Normalize register lookups (`upd` at literal registers), literal
immediates and Sail shifts, everywhere. -/
syntax "sx_norm" : tactic
macro_rules
  | `(tactic| sx_norm) =>
    `(tactic| simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        Sail.shift_bits_left, Sail.shift_bits_right, Sail.BitVec.extractLsb,
        BitVec.reduceExtractLsb, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
        BitVec.reduceShiftLeft, BitVec.reduceUShiftRight, BitVec.shiftLeft_eq',
        BitVec.ushiftRight_eq', BitVec.reduceToNat,
        BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, VsaIris.ra, Nat.reduceAdd,
        BitVec.reduceAppend] at *)

/-- Unfold the access predicates and fold literal immediates. -/
syntax "sx_pre" : tactic
macro_rules
  | `(tactic| sx_pre) =>
    `(tactic| try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        BitVec.add_zero, LdOK, StOK, StOKb, Vsa.Sim.tohostAddr, Vsa.Sim.DlHeap.heapStart,
        Vsa.Sim.DlHeap.heapEnd, Vsa.Sim.DlHeap.binAt, Vsa.Sim.DlHeap.avAddr,
        Vsa.Sim.DlHeap.chunkSize] at *)

/-- `BitVec` sums as `Nat` sums modulo `2^64`. `BitVec.toNat_add` goes
through `rw`: `simp` with it does not terminate on large literals. -/
syntax "sx_bv" : tactic
macro_rules
  | `(tactic| sx_bv) => `(tactic| repeat rw [BitVec.toNat_add] at *)

/-- Literal `toNat`s and powers. -/
syntax "sx_lits" : tactic
macro_rules
  | `(tactic| sx_lits) => `(tactic| try simp only [BitVec.reduceToNat, Nat.reducePow,
      toNat_and_m16, toNat_and_m4, toNat_and_m2, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at *)

/-- Addresses and unsigned comparisons as `Nat` arithmetic, then `omega`. -/
syntax "sx_addr" : tactic
macro_rules
  | `(tactic| sx_addr) => `(tactic| (sx_pre; sx_lits; sx_bv; sx_lits; sx_bv; omega))

macro_rules | `(tactic| sx_side) => `(tactic| sx_addr)

/-- A doubleword load through a disjoint store. -/
theorem ldv_ld_miss (Mt : Vsa.MemRepr.Mem) {a b w : Nat} (v : BitVec 64) (h : a + 8 ≤ b ∨ b + w ≤ a) :
    ldv .ld (Vsa.Sim.writeLog Mt [(b, w, v)]) a = ldv .ld Mt a :=
  ldv_store_miss .ld Mt v h

/-- A doubleword load at the address of the latest doubleword store. -/
theorem ldv_ld_hit_eq (Mt : Vsa.MemRepr.Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .ld (Vsa.Sim.writeLog Mt [(b, 8, v)]) a = v := by
  subst h; exact ldv_store_hit Mt a v

/-- Store forwarding: a doubleword load reads the latest store at its address,
through stores to disjoint addresses (`sx_addr` decides disjointness). -/
syntax "sx_mem" : tactic
macro_rules
  | `(tactic| sx_mem) => `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss] at *)

/-- The PC literal of an `SWP` goal, if any. -/
def swpPC? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  let ty := ty.consumeMData
  unless ty.getAppFn.isConstOf ``SWP do return none
  let args := ty.getAppArgs
  let some pc := args[5]? | return none
  match ← getBitVecValue? pc with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- Whether a goal is an `SWP` goal (a continuation). -/
def isSWP (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.consumeMData.getAppFn.isConstOf ``SWP

private def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s

/-- Try `sx_side` on a goal; `true` when it closes. -/
private def trySide (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| ((try sx_norm) <;> (try sx_mem) <;> sx_side))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Close a branch goal `C → AW …` when `sx_side` refutes `C`. -/
private def tryPrune (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| (intro hc; exfalso; ((try sx_norm) <;> (try sx_mem) <;> (revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- One step: apply `st_<pc>` to the main goal. Returns the new goals, the
continuation last, or `none` when the goal has no literal PC. -/
def sxStep (h : Syntax) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let nm := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "VsaIris") "Sym") s!"st_{hex8 pc}"
  unless (← getEnv).contains nm do return none
  let stx ← `(tactic| apply $(mkIdent nm) $(⟨h⟩))
  let gs ← evalTacticAt stx g
  return some gs

/-- `sx_run h`, `sx_run [n] h`, `sx_run h at pc…`: run until stuck, at most
`n` steps, stopping before any listed PC. -/
syntax "sx_run " ("[" num "] ")? term (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| sx_run $[[$n]]? $h $[at $stops*]?) => do
    let budget := (n.map (·.getNat)).getD 400
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let mut pending : List MVarId := []
    let mut cur ← getMainGoal
    let mut stuck : List MVarId := []
    for _ in [0:budget] do
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := [cur]; break
      let some gs ← sxStep h cur | stuck := [cur]; break
      -- classify: the goals whose type is an `SWP` goal (after intros) continue
      let mut conts : List MVarId := []
      for g in gs do
        let ty ← g.withContext (do instantiateMVars (← g.getType))
        if ← g.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
          conts := conts ++ [g]
        else if !(← trySide g) then
          pending := pending ++ [g]
      match conts with
      | [c] =>
        -- a plain step, or a continuation whose PC is symbolic; keep the
        -- register values in normal form as they are produced
        let c ← do
          let saved ← saveState
          try
            match ← evalTacticAt (← `(tactic| ((try sx_norm) <;> (try sx_mem)))) c with
            | [c'] => pure c'
            | _ => saved.restore; pure c
          catch _ => saved.restore; pure c
        if (← c.withContext (do swpPC? (← c.getType))).isSome then
          cur := c
        else
          stuck := [c]; break
      | [t, f] =>
        -- a branch: prune a refuted side, continue on the other
        if ← tryPrune t then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := [f]; break
          cur := f'
        else if ← tryPrune f then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := [t]; break
          cur := t'
        else
          stuck := [t, f]; break
      | cs => stuck := cs; break
    if stuck.isEmpty then stuck := [cur]
    setGoals (pending ++ stuck)

end VsaIris.Sym
