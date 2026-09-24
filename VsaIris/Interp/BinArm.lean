import VsaIris.Interp.Arm
import VsaIris.Interp.ITacTree
import VsaIris.Interp.SpecValue
import VsaIris.Interp.SpecErr

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


namespace VsaIris.Sym

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## The comparison tail on a sign (`strcmp`'s result) -/

theorem toInt_neg_iff' (res : BitVec 64) : res.toInt < 0 ↔ 2 ^ 63 ≤ res.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
theorem sign_lt_bit (res : BitVec 64) : (res >>> 63 != 0#64) = decide (res.toInt < 0) := by
  simp only [decide_eq_decide.mpr (toInt_neg_iff' res)]
  have e : (res >>> 63).toNat = res.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt := res.isLt
  by_cases h : 2 ^ 63 ≤ res.toNat
  · have : res >>> 63 ≠ 0#64 := fun h0 => by
      have := congrArg BitVec.toNat h0; rw [e] at this; simp at this; omega
    simp [this, h]
  · have : res >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [e]; simp; omega
    simp [this, h]
theorem sign_le_bit (res : BitVec 64) : (sltiV res 1#64 != 0#64) = decide (res.toInt < 1) := by
  rw [show sltiV res 1#64 = sltV res 1#64 from rfl, sltV_eq]
  by_cases h : res.toInt < (1#64 : BitVec 64).toInt
  · have h' : res.toInt < 1 := by simpa using h
    simp [h']
  · have h' : ¬ res.toInt < 1 := by simpa using h
    simp [h']
theorem sign_gt_bit (res : BitVec 64) : (sltV 0#64 res != 0#64) = decide (0 < res.toInt) := by
  rw [sltV_eq]
  by_cases h : (0#64 : BitVec 64).toInt < res.toInt
  · have h' : 0 < res.toInt := by simpa using h
    simp [h']
  · have h' : ¬ 0 < res.toInt := by simpa using h
    simp [h']
theorem sign_ge_bit (res : BitVec 64) :
    ((res ^^^ 0xffffffffffffffff#64) >>> 63 != 0#64) = decide (0 ≤ res.toInt) := by
  rw [sign_lt_bit]
  have : (res ^^^ 0xffffffffffffffff#64).toInt < 0 ↔ ¬ res.toInt < 0 := by
    rw [toInt_neg_iff', toInt_neg_iff']
    rw [show (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes,
      BitVec.toNat_not]
    have := res.isLt; omega
  simp only [decide_eq_decide.mpr this]; simp

end VsaIris.Sym

namespace VsaIris.Interp

open Vsa.While VsaIris.Sym

/-- `<` on strings from `strcmp`'s sign. -/
theorem str_lt_bit {res : BitVec 64} {x y : String} (h : StrcmpSign res x y) :
    (res >>> 63 != 0#64) = decide (x < y) := by
  rw [sign_lt_bit]; exact decide_eq_decide.mpr h.lt

/-- `<=` on strings (`binOpSem`: `a < b || a == b`). -/
theorem str_le_bit {res : BitVec 64} {x y : String} (h : StrcmpSign res x y) :
    (sltiV res 1#64 != 0#64) = (decide (x < y) || x == y) := by
  rw [sign_le_bit]
  have e1 := h.eq; have e2 := h.lt
  by_cases h1 : res.toInt < 0
  · have : x < y := e2.mp h1
    simp [this, show res.toInt < 1 by omega]
  · by_cases h2 : res = 0#64
    · have : x = y := e1.mp h2
      subst h2; simp [this]
    · have hne : x ≠ y := fun e => h2 (e1.mpr e)
      have hlt : ¬ x < y := fun e => h1 (e2.mpr e)
      have : ¬ res.toInt < 1 := by
        intro h3
        have : res.toInt = 0 := by omega
        exact h2 (BitVec.eq_of_toInt_eq (by simpa using this))
      simp [this, hlt, hne]

/-- `>` on strings (`binOpSem`: `b < a`). -/
theorem str_gt_bit {res : BitVec 64} {x y : String} (h : StrcmpSign res x y) :
    (sltV 0#64 res != 0#64) = decide (y < x) := by
  rw [sign_gt_bit]; exact decide_eq_decide.mpr h.gt

/-- `>=` on strings (`binOpSem`: `b < a || a == b`). -/
theorem str_ge_bit {res : BitVec 64} {x y : String} (h : StrcmpSign res x y) :
    ((res ^^^ 0xffffffffffffffff#64) >>> 63 != 0#64) = (decide (y < x) || x == y) := by
  rw [sign_ge_bit]
  have e1 := h.eq; have e3 := h.gt
  by_cases h1 : 0 < res.toInt
  · have : y < x := e3.mp h1
    simp [this, show 0 ≤ res.toInt by omega]
  · by_cases h2 : res = 0#64
    · have : x = y := e1.mp h2
      subst h2; simp [this]
    · have hne : x ≠ y := fun e => h2 (e1.mpr e)
      have hlt : ¬ y < x := fun e => h1 (e3.mpr e)
      have : ¬ 0 ≤ res.toInt := by
        intro h3
        have : res.toInt = 0 := by omega
        exact h2 (BitVec.eq_of_toInt_eq (by simpa using this))
      simp [this, hlt, hne]

end VsaIris.Interp

namespace VsaIris.Interp

open Vsa.While

theorem small_ne_three {k : Nat} (hk : k < 2 ^ 31) (hv : k ≠ 3) :
    BitVec.ofNat 64 k + 18446744073709551613#64 ≠ 0#64 := by
  intro h0
  have e := congrArg BitVec.toNat h0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at e
  simp only [BitVec.toNat_ofNat] at e
  omega

/-- A kind word read back from a value's first word is not the string tag,
in the form the comparison arm tests it (`addi a5,a0,-3; bnez a5`). -/
theorem kind_ne_str {w : BitVec 64} {v : Value} (h : w.toNat % 2 ^ 32 = valTag v) (hv : valTag v ≠ 3) :
    BitVec.ofNat 64 (w.toNat % 2 ^ 32) + 18446744073709551613#64 ≠ 0#64 := by
  rw [h]; exact small_ne_three (valTag_lt v) hv

/-- The rows of a comparison (`<`, `<=`, `>`, `>=`), in the machine's order of
tests: two ints; two strings; a non-int left operand with the right one not a
string; a non-int, non-string left operand with a string right one; an int
left operand with a non-int, non-string right one; an int and a string. -/
theorem cmpRows (lv rv : Value) :
    (∃ a b, lv = .int a ∧ rv = .int b) ∨ (∃ x y, lv = .str x ∧ rv = .str y) ∨
    (valTag rv ≠ 3 ∧ valTag lv ≠ 2) ∨ (∃ y, rv = .str y ∧ valTag lv ≠ 2 ∧ valTag lv ≠ 3) ∨
    (∃ a, lv = .int a ∧ valTag rv ≠ 2 ∧ valTag rv ≠ 3) ∨ (∃ a y, lv = .int a ∧ rv = .str y) := by
  cases lv <;> cases rv <;> simp [valTag]

end VsaIris.Interp
