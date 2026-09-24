import VsaIris.Interp.Arm
import VsaIris.Interp.ITacTree
import VsaIris.Interp.SpecValue

/-!
# The binary arm's shared facts (lane E2)

INTERP_DESIGN.md §6, §8 (family E2: `eval_expr`'s `EX_BINARY` arm, `eval_binary`
inlined). What every generated binary row (`scripts/iris_arms/arms.d/e2-binary.tsv`,
`VsaIris/Interp/Case/Binary*`) uses besides lane G's arm layer (`Arm.lean`):

* **`.rodata` tables deep in `interpRO`.** A jump-table or name-table load's
  side condition `(b, interpROImg b) ∈ interpRO`, decided in the run, walks the
  table list; past about 230 bytes the walk exceeds the recursion depth, and
  near it the run's budget. `Code.lean` proves it once per loaded word
  (`interpRO_acc*`, generated); `ix_run`'s `sx_side` tries those (`ix_ro`).
* **The comparison tail** (`0x80003698`–`0x800036c0`, `0x80003ae4`,
  `0x80003af8`): `cmp = (a > b) - (a < b)` as `subw` of two `slt`s
  (`cmpRaw`), then one bit per operator; `cmp_*_bit` read each as the source's
  `decide`.
-/

namespace VsaIris.Sym

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

open Lean Elab Tactic Meta in
/-- A table load's membership side condition `∀ b ∈ accAddrs a w, (b,
interpROImg b) ∈ interpRO` at literal `a`, `w`: the generated
`interpRO_acc{w}_{a}`. Any other goal fails at once (no reduction). -/
elab "ix_ro" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless (ty.find? (·.isConstOf ``interpROImg)).isSome do throwError "ix_ro: not a table goal"
  let some e := ty.find? (fun e => e.isAppOfArity ``accAddrs 2) | throwError "ix_ro: no accAddrs"
  let some an ← evalNat e.appFn!.appArg! |>.run | throwError "ix_ro: address not a literal"
  let some wn ← evalNat e.appArg! |>.run | throwError "ix_ro: width not a literal"
  let hex := String.ofList (Nat.toDigits 16 an)
  let hex := String.ofList (List.replicate (8 - hex.length) '0') ++ hex
  let nm := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "VsaIris") "Sym") s!"interpRO_acc{wn}_{hex}"
  unless (← getEnv).contains nm do throwError "ix_ro: no lemma {nm}"
  evalTactic (← `(tactic| exact $(mkIdent nm)))

macro_rules
  | `(tactic| sx_side) => `(tactic| ix_ro)

open Lean Elab Tactic Meta in
/-- `C → False` from a hypothesis `¬ C` (or `C = ¬ D` and a hypothesis `D`),
matched syntactically up to reducible unfolding; fails at once otherwise (no
decision procedure runs). -/
elab "ix_absurd" : tactic => do
  let g ← getMainGoal
  let (h, g) ← g.intro1
  g.withContext do
    let hty ← instantiateMVars (← h.getType)
    for d in ← getLCtx do
      if d.isImplementationDetail || d.fvarId == h then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Not 1 then
        if ← withReducible (isDefEq t.appArg! hty) then
          g.assign (mkApp d.toExpr (mkFVar h)); return
      if hty.isAppOfArity ``Not 1 then
        if ← withReducible (isDefEq hty.appArg! t) then
          g.assign (mkApp (mkFVar h) d.toExpr); return
    throwError "ix_absurd: no contradicting hypothesis"

/-- A branch on a value's kind word, decided by the row's kind fact
(`kL ≠ 2#64`, …) in the context. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro h; (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at h); revert h; ix_absurd))

/-! ## The comparison tail -/

theorem sltV_eq (a b : BitVec 64) : sltV a b = if a.toInt < b.toInt then 1#64 else 0#64 := by
  unfold sltV
  by_cases h : a.toInt < b.toInt <;> simp [h, zopz0zI_s, bool_to_bit] <;> rfl

/-- `cmp = (a > b) - (a < b)` as the arm computes it (`slt`, `slt`, `subw`). -/
abbrev cmpRaw (x y : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.extractLsb 31 0 (sltV y x) - BitVec.extractLsb 31 0 (sltV x y))

theorem cmpRaw_cases (x y : BitVec 64) :
    (x.toInt < y.toInt ∧ cmpRaw x y = 0xffffffffffffffff#64) ∨
    (x.toInt = y.toInt ∧ cmpRaw x y = 0#64) ∨ (y.toInt < x.toInt ∧ cmpRaw x y = 1#64) := by
  unfold cmpRaw
  rw [sltV_eq, sltV_eq]
  rcases Int.lt_trichotomy x.toInt y.toInt with h | h | h
  · left; refine ⟨h, ?_⟩; simp [h, show ¬ y.toInt < x.toInt by omega]
  · right; left; refine ⟨h, ?_⟩; simp [h]
  · right; right; refine ⟨h, ?_⟩; simp [h, show ¬ x.toInt < y.toInt by omega]

/-- `<`: `srli a1,a1,63`. -/
theorem cmp_lt_bit (x y : BitVec 64) : (cmpRaw x y >>> 63 != 0#64) = decide (x.toInt < y.toInt) := by
  rcases cmpRaw_cases x y with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · simp [h]
  · simp [h]
  · simp [show ¬ x.toInt < y.toInt by omega]

/-- `<=`: `slti a1,a1,1`. -/
theorem cmp_le_bit (x y : BitVec 64) :
    (sltiV (cmpRaw x y) 1#64 != 0#64) = decide (x.toInt ≤ y.toInt) := by
  rcases cmpRaw_cases x y with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · simp [show x.toInt ≤ y.toInt by omega]; decide
  · simp [show x.toInt ≤ y.toInt by omega]; decide
  · simp [show ¬ x.toInt ≤ y.toInt by omega]; decide

/-- `>`: `sgtz a1,a1`. -/
theorem cmp_gt_bit (x y : BitVec 64) :
    (sltV 0#64 (cmpRaw x y) != 0#64) = decide (x.toInt > y.toInt) := by
  rcases cmpRaw_cases x y with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · simp [show ¬ x.toInt > y.toInt by omega]; decide
  · simp [show ¬ x.toInt > y.toInt by omega]; decide
  · simp [show x.toInt > y.toInt by omega]; decide

/-- `>=`: `not a1,a1; srli a1,a1,63`. -/
theorem cmp_ge_bit (x y : BitVec 64) :
    ((cmpRaw x y ^^^ 0xffffffffffffffff#64) >>> 63 != 0#64) = decide (x.toInt ≥ y.toInt) := by
  rcases cmpRaw_cases x y with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · simp [show ¬ x.toInt ≥ y.toInt by omega]
  · simp [show x.toInt ≥ y.toInt by omega]
  · simp [show x.toInt ≥ y.toInt by omega]

end VsaIris.Sym

namespace VsaIris.Interp

open Vsa.While

/-- The rows of an operator whose operands must both be ints (`int_operand`
checks the left operand, then the right). -/
theorem intRows (lv rv : Value) :
    (∃ a b, lv = .int a ∧ rv = .int b) ∨ valTag lv ≠ 2 ∨ (∃ a, lv = .int a ∧ valTag rv ≠ 2) := by
  cases lv <;> cases rv <;> simp [valTag]

/-- A kind word read back from a value's first word (`lw` of the tag) is not
the int tag. -/
theorem kind_ne_int {w : BitVec 64} {v : Value} (h : w.toNat % 2 ^ 32 = valTag v) (hv : valTag v ≠ 2) :
    BitVec.ofNat 64 (w.toNat % 2 ^ 32) ≠ 2#64 := by
  rw [h]; cases v <;> simp [valTag] at hv ⊢ <;> decide

end VsaIris.Interp

/-- A load fact over a run's tracking memory, cheaply: the frame addresses are
first rewritten to plain sums by the arm's `hoff` (`evalSP_off`), then every
store is forwarded with `omega` alone on the goal (lane G's `ix_fwd` simps the
whole context at each store, which a long run's memory equation makes
expensive). -/
syntax "e2_fwd " term : tactic
macro_rules
  | `(tactic| e2_fwd $h) =>
    `(tactic| ((try simp (disch := decide) only [$h:term]); simp (disch := first | rfl | omega) only [VsaIris.Interp.slotWrite, VsaIris.Sym.ldv_store_hit, VsaIris.Sym.ldv_ld_hit_eq, VsaIris.Sym.ldv_ld_miss, VsaIris.Interp.ldv_lw_miss, VsaIris.Interp.ldv_lw_store8]))

namespace VsaIris.Interp

/-- A kind tag is small (a signed word load reads it back unchanged). -/
theorem valTag_lt (v : Vsa.While.Value) : valTag v < 2 ^ 31 := by cases v <;> simp [valTag]

end VsaIris.Interp
