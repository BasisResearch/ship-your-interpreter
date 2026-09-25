import VsaIris.Vsa.Stdout.Console
import VsaIris.Vsa.Stdout.Write
import VsaIris.Vsa.Stdout.Attr

/-!
# Driving stdout runs (lane N1)

A stdout call owns newlib's data, `errno` and its stack (`outS s need`: the
bytes below the call's `sp = s`). `ix_run` drives the stdio step table
(`Steps/*.lean`); this module extends its side-condition discharger with
`outS` (interval arithmetic) and its store forwarding with every load width
(`nx_mem`) and the boundary `stdout` fields (`ConsoleMt`).

A callee's summary is a transformer of printing symbolic runs whose
continuation is at the return address with `callRet R v a0`: `a0` the
result, the caller-saved temporaries and arguments at any values `v`, every
other register (`ra`, `sp`, the saved registers) as at the call.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The bytes a stdout call owns: newlib's data, `errno`, and `need` bytes
of stack below `s`. -/
def outS (s : BitVec 64) (need : Nat) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ impureW a) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨ (s.toNat - need ≤ a ∧ a < s.toNat)

namespace Stdout
/-- Footprint side goals over `outS`. The `sx_side` rules of this file are
scoped to `VsaIris.Sym.Stdout` (`open scoped VsaIris.Sym.Stdout` in each run
file): importers' `sx_side` goals never reach them. -/
scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; simp only [mem_accAddrs_iff, outS, stdioFoot, InRange, impureW] at *; sx_addr))
end Stdout

/-- Updating the registers `xs` to the values `v`. -/
def updAll (R : Nat → BitVec 64) (v : Nat → BitVec 64) : List Nat → Nat → BitVec 64
  | [] => R
  | x :: xs => upd (updAll R v xs) x (v x)

/-- `subw` of `(B + n) - B` (a buffer's fill count, `_p - _bf._base`). -/
theorem subw_add_ofNat {n : Nat} (hn : n < 2 ^ 31) (B : BitVec 64) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (B + BitVec.ofNat 64 n) - BitVec.extractLsb 31 0 B) =
      BitVec.ofNat 64 n := by
  have e : BitVec.extractLsb 31 0 (B + BitVec.ofNat 64 n) - BitVec.extractLsb 31 0 B =
      BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_zero]
    have hB := B.isLt
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem toInt_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

/-- An aligned jump target is its own `(_ & ~1)`. -/
theorem update_aligned (r : BitVec 64) (h : r.toNat % 4 = 0) : Sail.BitVec.update r 0 0#1 = r := by
  have e := ret_tgt r h
  rwa [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = 0#64 by decide,
    BitVec.add_zero] at e

theorem sext_zero32 : BitVec.signExtend 64 (0#32) = 0#64 := by decide

/-- The boundary `stdout` fields, where a load reaches the boundary memory. -/
syntax "nx_console" : tactic
macro_rules
  | `(tactic| nx_console) => `(tactic| simp (disch := assumption) only
      [ldv_impDt, ConsoleMt.sinit, ConsoleMt.stdout, ConsoleMt.p, ConsoleMt.w,
       ConsoleMt.flagsU, ConsoleMt.flagsS, ConsoleMt.fd, ConsoleMt.base, ConsoleMt.bsize,
       ConsoleMt.lbf, ConsoleMt.cookie, ConsoleMt.writer, ConsoleMt.lock, ConsoleMt.lockMode])

/-- `sx_norm` on the goal only (register lookups, literal immediates, shifts);
`nx_norm at h` on one hypothesis. -/
syntax "nx_norm" (" at " ident)? : tactic
macro_rules
  | `(tactic| nx_norm at $h:ident) =>
    `(tactic| simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        Sail.shift_bits_left, Sail.shift_bits_right, Sail.BitVec.extractLsb,
        BitVec.reduceExtractLsb, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
        BitVec.reduceShiftLeft, BitVec.reduceUShiftRight, BitVec.shiftLeft_eq',
        BitVec.ushiftRight_eq', BitVec.reduceToNat,
        BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, VsaIris.ra, Nat.reduceAdd,
        BitVec.reduceAppend, not_true_eq_false, BitVec.reduceAnd, BitVec.reduceOr] at $h:ident)
  | `(tactic| nx_norm) =>
    `(tactic| simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        Sail.shift_bits_left, Sail.shift_bits_right, Sail.BitVec.extractLsb,
        BitVec.reduceExtractLsb, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
        BitVec.reduceShiftLeft, BitVec.reduceUShiftRight, BitVec.shiftLeft_eq',
        BitVec.ushiftRight_eq', BitVec.reduceToNat,
        BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, VsaIris.ra, Nat.reduceAdd,
        BitVec.reduceAppend, not_true_eq_false, Nat.reducePow, Nat.reduceMod, BitVec.reduceAnd,
        BitVec.reduceOr])

open Lean Elab Tactic Meta in
/-- `nx_run`'s normalizer: `ix_run`'s (register lookups, the caller's facts),
then store forwarding at every width (`nx_mem`), the boundary `stdout` fields
(`nx_console`), and the facts again: a load through the run's own stores
reaches the entry memory, which the facts describe. -/
def nxNorm (facts : Array Term) : TacticM Syntax := do
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
  `(tactic| ((try simp only [updAll] at ⊢) <;> (try simp only [nx_mt] at ⊢) <;> (try nx_norm) <;> (try simp only [$lems,*]) <;>
      (try nx_norm) <;> (try nx_mem) <;> (try nx_console) <;> (try simp only [$lems,*]) <;>
      (try nx_norm) <;> (try simp (disch := omega) only [toInt_ofNat_small, BitVec.toInt_zero]) <;>
      (try simp (disch := decide) only [update_aligned]) <;>
      (try simp only [BitVec.sub_self, sext_zero32, BitVec.toInt_zero])))

open Lean Elab Tactic Meta in
/-- `ixTryPrune` that first rewrites the branch hypothesis with the run's
facts (a condition on a callee's returned register file `R'`). -/
def nxTryPrune (facts : Array Term) (norm : Syntax) (g : MVarId) : TacticM Bool := do
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
  let saved ← saveState
  try
    let gs ← evalTacticAt
      (← `(tactic| (intro hc; (try nx_norm at hc); (try simp only [$lems,*] at hc); (try nx_norm at hc); (try simp (disch := omega) only [toInt_ofNat_small, BitVec.toInt_zero, BitVec.sub_self, sext_zero32] at hc); (try (exfalso; revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

open Lean Elab Tactic Meta in
def nxRunCore (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num)))
    (budgetPct : Nat := 0) :
    TacticM Unit := do
    let budget := (n.map (·.getNat)).getD 400
    let ctx ← readThe Core.Context
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    let norm ← nxNorm facts
    let mut pending : List MVarId := []
    let mut stuck : List MVarId := []
    let first ← getMainGoal
    -- a start state from a call's return (`BitVec.ofNat 64 (i + 4)`) gets its literal PC
    let first ← do
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) first with
        | [c'] => pure c'
        | _ => saved.restore; pure first
      catch _ => saved.restore; pure first
    -- a worklist of paths, each with its own step budget
    let mut work : List (MVarId × Nat) := [(first, budget)]
    while !work.isEmpty do
      let (cur, fuel) := work.head!
      work := work.tail!
      if fuel == 0 then stuck := stuck ++ [cur]; continue
      -- lane N3: a budgeted run (a proof piece) stops once it used `budgetPct`% of
      -- the declaration's heartbeats
      if budgetPct != 0 && ctx.maxHeartbeats != 0 then
        let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
        if used * 100 > ctx.maxHeartbeats * budgetPct then stuck := stuck ++ [cur]; continue
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := stuck ++ [cur]; continue
      let some (conts, pend) ← ixStep norm h cur | stuck := stuck ++ [cur]; continue
      pending := pending ++ pend
      match conts with
      | [c] =>
        -- a havoc load's continuation holds for every loaded value
        let c ← do
          let ty ← c.withContext (do whnfR (← instantiateMVars (← c.getType)))
          if ty.isForall then
            match ← evalTacticAt (← `(tactic| intros)) c with
            | [c'] => pure c'
            | _ => pure c
          else pure c
        let c ← do
          let saved ← saveState
          try
            match ← evalTacticAt norm c with
            | [c'] => pure c'
            | _ => saved.restore; pure c
          catch _ => saved.restore; pure c
        if (← c.withContext (do swpPC? (← c.getType))).isSome then
          work := (c, fuel - 1) :: work
        else
          stuck := stuck ++ [c]
      | [t, f] =>
        if ← nxTryPrune facts norm t then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [f]; continue
          work := (f', fuel - 1) :: work
        else if ← nxTryPrune facts norm f then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t]; continue
          work := (t', fuel - 1) :: work
        else if !explore then
          stuck := stuck ++ [t, f]
        else
          -- undecided: explore both sides, taken side first
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t, f]; continue
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [t', f]; continue
          work := (t', fuel - 1) :: (f', fuel - 1) :: work
      | cs => stuck := stuck ++ cs
    setGoals (pending ++ stuck)


/-- `nx_run [n] h using [facts] at pc…`: `ix_run` over the stdio step table
with `nxNorm`; a continuation's binders (a callee's havoc values) are all
introduced. -/
syntax "nx_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

/-- `nx_runB …`: `nx_run` that stops at 55% of the declaration's heartbeat
budget (lane N3: one `#ix_piece` of a long run). -/
syntax "nx_runB " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| nx_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => nxRunCore true n h fs stops
  | `(tactic| nx_runB $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => nxRunCore true n h fs stops 55

/-- `nx_addr` for byte-ownership goals: unfold `outS` first. -/
macro_rules | `(tactic| nx_addr) => `(tactic| (simp only [outS, stdioFoot, InRange, impureW] at ⊢; (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); first | done | omega))

namespace Stdout
scoped macro_rules | `(tactic| sx_side) => `(tactic| nx_addr)
end Stdout
/-- The address-range hypothesis of a byte-set side condition, as arithmetic. -/
syntax "nx_hb " ident : tactic
macro_rules
  | `(tactic| nx_hb $h) => `(tactic| simp (disch := omega) only [mem_accAddrs_iff, toNat_add_lit,
      toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
      Nat.reduceAdd] at $h:ident)

namespace Stdout
scoped macro_rules | `(tactic| sx_side) => `(tactic| (intro b hb; (try nx_hb hb); nx_addr))
end Stdout

namespace Stdout
/-- A load from the data view's first block (`_impure_ptr`, in a view
`accAddrs 0x8001b970 8 ++ DAs` that also holds a string). -/
scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; exact List.mem_append_left _ hb))
end Stdout

namespace Stdout
/-- A branch refuted by a hypothesis of the run (a flag bit a summary assumes). -/
scoped macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; first | (apply hc; assumption) | (apply absurd hc; assumption)))
end Stdout

/-- The caller-saved registers other than `a0` and `ra`. -/
abbrev callClob : List Nat := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- The register file after a call returns `a0`: the caller-saved registers
(`callClob`) at `v`, everything else as at the call. -/
abbrev callRet (R v : Nat → BitVec 64) (a0 : BitVec 64) : Nat → BitVec 64 :=
  upd (updAll R v callClob) 10 a0

/-- A callee returned `a0`: the register file `R'` at its return address
keeps every register of the call's `R` outside `callClob`, `a0`, the PC. -/
structure RetOK (R R' : Nat → BitVec 64) (a0 : BitVec 64) : Prop where
  a0 : R' 10 = a0
  keep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → R' x = R x

set_option hygiene false in
/-- The facts a caller continues from after a call: `a0` and the kept
registers (`ra`, `sp`, `s0`–`s11`), named `rk<n>`, their values normalized. -/
macro "nx_ret " h:ident : tactic => `(tactic| (
  have rk10 := ($h).a0
  have rk1 := ($h).keep 1 (by decide) (by decide) (by decide) (by decide)
  have rk2 := ($h).keep 2 (by decide) (by decide) (by decide) (by decide)
  have rk8 := ($h).keep 8 (by decide) (by decide) (by decide) (by decide)
  have rk9 := ($h).keep 9 (by decide) (by decide) (by decide) (by decide)
  have rk18 := ($h).keep 18 (by decide) (by decide) (by decide) (by decide)
  have rk19 := ($h).keep 19 (by decide) (by decide) (by decide) (by decide)
  have rk20 := ($h).keep 20 (by decide) (by decide) (by decide) (by decide)
  have rk21 := ($h).keep 21 (by decide) (by decide) (by decide) (by decide)
  have rk22 := ($h).keep 22 (by decide) (by decide) (by decide) (by decide)
  have rk23 := ($h).keep 23 (by decide) (by decide) (by decide) (by decide)
  have rk24 := ($h).keep 24 (by decide) (by decide) (by decide) (by decide)
  have rk25 := ($h).keep 25 (by decide) (by decide) (by decide) (by decide)
  have rk26 := ($h).keep 26 (by decide) (by decide) (by decide) (by decide)
  have rk27 := ($h).keep 27 (by decide) (by decide) (by decide) (by decide)
  simp only [upd_apply, updAll, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc,
    BitVec.reduceAdd] at rk1 rk2 rk8 rk9 rk10 rk18 rk19 rk20 rk21 rk22 rk23 rk24 rk25 rk26 rk27
  clear $h))

/-- Closing a callee's run at its return: `RetOK` from the end register file. -/
theorem retOK_of {R Rf : Nat → BitVec 64} {a0 : BitVec 64} (h10 : Rf 10 = a0)
    (hkeep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → Rf x = R x) : RetOK R Rf a0 :=
  ⟨h10, hkeep⟩

/-- `RetOK`'s kept registers of an `upd` chain, one `simp` per register. -/
macro "ret_keep" : tactic => `(tactic| (
  intro x hx h32 h10 hc
  simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [upd_apply]))

theorem updAll_apply (R v : Nat → BitVec 64) : ∀ (xs : List Nat) (x : Nat),
    updAll R v xs x = if x ∈ xs then v x else R x
  | [], x => by simp [updAll]
  | y :: ys, x => by
    simp only [updAll, upd_apply, updAll_apply R v ys x, List.mem_cons]
    by_cases h : x = y
    · subst h; simp
    · simp [h]

/-- Closing a callee's run: its end register file agrees with `callRet` at
the values it ends with. -/
theorem callRet_of {R Rf : Nat → BitVec 64} {a0 : BitVec 64} (h10 : Rf 10 = a0)
    (hkeep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → Rf x = R x) :
    ∀ r ∈ iRegs, r ≠ VsaIris.PC → callRet R Rf a0 r = Rf r := by
  intro r hr hne
  simp only [upd_apply, updAll_apply]
  by_cases e : r = 10
  · subst e; simp [h10]
  · rw [if_neg e]
    by_cases hc : r ∈ callClob
    · rw [if_pos hc]
    · rw [if_neg hc, hkeep r hr hne e hc]

/-- A callee summary's side condition at a call site: a register value, a
load through the run's stores, an address bound, a literal fact. -/
syntax "nx_disch" : tactic
macro_rules
  | `(tactic| nx_disch) => `(tactic| (fail_if_success show SWP _ _ _ _ _ _ _ _); first
      | assumption
      | (nx_norm; first | done | rfl | assumption)
      | (nx_mem; first | done | rfl | assumption | (nx_console; done))
      | (nx_norm; nx_mem; first | done | rfl | assumption | (nx_console; done))
      | nx_addr
      | (intro i hi; nx_addr))

/-! ## `#nx_chain`: a chain whose last piece stops at a return

`#ix_chain` (`ITac.lean`) with the last piece's leftover goals exported as
hypotheses as well: a callee's run ends at its (symbolic) return address,
and the chain theorem takes that end state as a hypothesis, which the
callee's summary discharges from its explicit continuation. -/

section NxChain

open Lean Elab Command Term Meta

/-- Universe metavariables of a proof's library lemmas: any level (`ITac`'s). -/
private def zeroLevelsN (e : Expr) : Expr :=
  e.replaceLevel fun l =>
    if l.hasMVar then some (l.replace fun | .mvar _ => some levelZero | _ => none) else none

syntax (name := nxChain) "#nx_chain " ident " := " "[" ident,+ "]" : command

@[command_elab nxChain] def elabNxChain : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let names ← stx[4].getSepArgs.mapM fun n => liftCoreM <| realizeGlobalConstNoOverload n
  liftTermElabM do
    let some first := names[0]? | throwError "#ix_chain: no pieces"
    let info0 ← getConstInfo first
    forallTelescope info0.type fun xs0 goal => do
      let nv ← pieceVars xs0
      let vars := xs0.extract 0 nv
      -- pass 1: the exported leftovers' types, closed over the introduced locals
      let rec exports (k : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
        let hs ← forallTelescope (← inferType (mkAppN (Lean.mkConst names[k]!) (vars ++ acc)))
          fun hs _ => hs.mapM inferType
        let mut out := #[]
        for h in hs.extract 1 hs.size do
          out := out.push (← mkForallFVars acc h)
        if k + 1 < names.size then
          let some cont := hs[0]? | throwError "#ix_chain: {names[k]!} has no leftover"
          let rest ← forallTelescope cont fun ys _ => exports (k + 1) (acc ++ ys)
          return out ++ rest
        else
          -- `#nx_chain`: the last piece's leftovers are exported too
          return (← hs.mapM fun h => mkForallFVars acc h)
      let exTys ← exports 0 #[]
      let exDecls := exTys.mapIdx fun j t => (Name.mkSimple s!"hx_{j + 1}", fun _ => pure t)
      withLocalDeclsD exDecls fun exs => do
        -- pass 2: the proof
        let rec build (k : Nat) (acc : Array Expr) (j : Nat) : MetaM Expr := do
          let c := mkAppN (Lean.mkConst names[k]!) (vars ++ acc)
          let hs ← forallTelescope (← inferType c) fun hs _ => hs.mapM inferType
          let nex := hs.size - (if k + 1 < names.size then 1 else 0)
          let exArgs := (List.range nex).toArray.map fun t => mkAppN exs[j + t]! acc
          if k + 1 < names.size then
            let rest ← forallTelescope hs[0]! fun ys _ => do
              mkLambdaFVars ys (← build (k + 1) (acc ++ ys) (j + nex))
            return mkAppN (mkApp c rest) exArgs
          else
            return mkAppN c exArgs
        let body ← build 0 #[] 0
        let val := zeroLevelsN (← instantiateMVars (← mkLambdaFVars (vars ++ exs) body))
        let ty := zeroLevelsN (← instantiateMVars (← mkForallFVars (vars ++ exs) goal))
        addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })


end NxChain

end VsaIris.Sym
