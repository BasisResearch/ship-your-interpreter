import VsaIris.Vsa.StepGen
import VsaIris.Vsa.Dbm

namespace VsaIris.Sym

open Lean Elab Tactic Meta

syntax "sx_side" : tactic

theorem upd_apply (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) (r : Nat) :
    upd R k v r = if r = k then v else R r := rfl

theorem toNat_and_m16 (x : BitVec 64) : (x &&& 18446744073709551600#64).toNat = x.toNat / 16 * 16 := by
  rw [show (18446744073709551600#64 : BitVec 64) = BitVec.allOnes 64 <<< 4 by decide,
    VsaIris.MallocFast.and_high_toNat x 4 (by decide)]

theorem toNat_and_m4 (x : BitVec 64) : (x &&& 18446744073709551612#64).toNat = x.toNat / 4 * 4 := by
  rw [show (18446744073709551612#64 : BitVec 64) = BitVec.allOnes 64 <<< 2 by decide,
    VsaIris.MallocFast.and_high_toNat x 2 (by decide)]

theorem toNat_and_m2 (x : BitVec 64) : (x &&& 18446744073709551614#64).toNat = x.toNat / 2 * 2 := by
  rw [show (18446744073709551614#64 : BitVec 64) = BitVec.allOnes 64 <<< 1 by decide,
    VsaIris.MallocFast.and_high_toNat x 1 (by decide)]

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
        BitVec.reduceAppend, not_true_eq_false] at *)

syntax "sx_pre" : tactic
macro_rules
  | `(tactic| sx_pre) =>
    `(tactic| try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        BitVec.add_zero, LdOK, StOK, StOKb, Vsa.Sim.tohostAddr, Vsa.Sim.DlHeap.heapStart,
        Vsa.Sim.DlHeap.heapEnd, Vsa.Sim.DlHeap.binAt, Vsa.Sim.DlHeap.avAddr,
        Vsa.Sim.DlHeap.chunkSize, and_true, true_and] at *)

syntax "sx_bv" : tactic
macro_rules
  | `(tactic| sx_bv) => `(tactic| repeat rw [BitVec.toNat_add] at *)

syntax "sx_lits" : tactic
macro_rules
  | `(tactic| sx_lits) => `(tactic| try simp only [BitVec.reduceToNat, Nat.reducePow,
      toNat_and_m16, toNat_and_m4, toNat_and_m2, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at *)

syntax "sx_addr" : tactic
macro_rules
  | `(tactic| sx_addr) => `(tactic| (sx_pre; sx_lits; sx_bv; sx_lits; sx_bv; first | done | omega_dc))

macro_rules | `(tactic| sx_side) => `(tactic| sx_addr)

macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; apply hc; apply BitVec.eq_of_toNat_eq; sx_addr))

macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; have hc' := congrArg BitVec.toNat hc; clear hc; revert hc'; sx_addr))

theorem ldv_ld_miss (Mt : Vsa.MemRepr.Mem) {a b w : Nat} (v : BitVec 64) (h : a + 8 ≤ b ∨ b + w ≤ a) :
    ldv .ld (Vsa.Sim.writeLog Mt [(b, w, v)]) a = ldv .ld Mt a :=
  ldv_store_miss .ld Mt v h

theorem ldv_ld_hit_eq (Mt : Vsa.MemRepr.Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .ld (Vsa.Sim.writeLog Mt [(b, 8, v)]) a = v := by
  subst h; exact ldv_store_hit Mt a v

theorem ldv_at {Mt : Vsa.MemRepr.Mem} {a' x : Nat} (h : Vsa.MemRepr.read64 Mt a' = some x) :
    ∀ a, a = a' → ldv .ld Mt a = BitVec.ofNat 64 x := by
  intro a he; subst he
  exact ldv_ld (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ h)])

theorem ldv_lw_miss (Mt : Vsa.MemRepr.Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lw (Vsa.Sim.writeLog Mt [(b, w, v)]) a = ldv .lw Mt a :=
  ldv_store_miss .lw Mt v h

theorem ldv_lw_zero_eq (Mt : Vsa.MemRepr.Mem) {a b : Nat} (h : a = b) :
    ldv .lw (Vsa.Sim.writeLog Mt [(b, 4, 0#64)]) a = 0#64 := by
  subst h
  obtain ⟨h0, h1, h2, h3⟩ := Vsa.Sim.pin4_of_writeLog Mt [] [] a 0#64 trivial
  simp only [List.nil_append] at h0 h1 h2 h3
  have hb : ∀ f : Nat → BitVec 8, bytesAt f a (Vsa.Sim.widthOfM .lw) = [f a, f (a + 1), f (a + 2), f (a + 3)] :=
    fun _ => rfl
  unfold ldv
  rw [hb]
  unfold VsaIris.MallocFast.imgM
  rw [h0, h1, h2, h3]
  decide

theorem read64_hit_eq (Mt : Vsa.MemRepr.Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    Vsa.MemRepr.read64 (Vsa.Sim.writeLog Mt [(b, 8, v)]) a = some v.toNat := by
  subst h; exact read64_store_hit Mt a v

theorem read64_miss (Mt : Vsa.MemRepr.Mem) {a b w : Nat} (v : BitVec 64) (h : a + 8 ≤ b ∨ b + w ≤ a) :
    Vsa.MemRepr.read64 (Vsa.Sim.writeLog Mt [(b, w, v)]) a = Vsa.MemRepr.read64 Mt a :=
  read64_store_miss Mt v h

syntax "sx_mem" : tactic
macro_rules
  | `(tactic| sx_mem) => `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss, ldv_lw_zero_eq] at *)

def swpPC? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  let ty := ty.consumeMData
  unless ty.getAppFn.isConstOf ``SWP do return none
  let args := ty.getAppArgs
  let some pc := args[5]? | return none
  match ← getBitVecValue? pc with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

def isSWP (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.consumeMData.getAppFn.isConstOf ``SWP

private def trySide (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| ((try sx_norm) <;> (try sx_mem) <;> sx_side))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

private def tryPrune (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| (intro hc; exfalso; ((try sx_norm) <;> (try sx_mem) <;> (revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

def sxStep (h : Syntax) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let t? ← g.withContext do StepGen.swpTbl? (← g.getType)
  let some nm ← StepGen.driverLemma? t? "st" pc | return none
  let stx ← `(tactic| apply $(mkCIdent nm) $(⟨h⟩))
  let gs ← evalTacticAt stx g
  return some gs

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

      let mut conts : List MVarId := []
      for g in gs do
        let ty ← g.withContext (do instantiateMVars (← g.getType))
        if ← g.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
          conts := conts ++ [g]
        else if !(← trySide g) then
          pending := pending ++ [g]
      match conts with
      | [c] =>

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
