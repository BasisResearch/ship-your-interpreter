import Vsa.While.StringOrder
import Vsa.Sim.rows.StrCmpBlockC

/-!
# `StrCmpOrderClose` — machine marshalling of the spec order bridge

`Vsa/While/StringOrder.lean` lands the spec-layer order agreement between the C
`strcmp` sign (`Vsa.Sim.strcmpSpecSign`, byte-lexicographic) and Lean `String.<`
(`List.Lex` codepoint order).  This file marshals that agreement onto the MACHINE
side: it reduces each operator's boxed sign-tail word (`sTailWord op w`) to a sign
test on the `strcmp` return `w`, and — under the strcmp-post guarantee
`strcmpSign w = strcmpSpecSign csa csb` — proves the boxed boolean agrees with the
`binOpSem` source order (`.lt`/`.le`/`.gt`/`.ge` on `.str`).

## The corrected `StrCmpOrderBridge`

The originally-landed `StrCmpBlockC.StrCmpOrderBridge op bres := ∀ w sl sr,
(sTailWord op w != 0) = bres sl sr` is FALSE: `w` (the strcmp return) is
unconstrained, disconnected from `sl`/`sr` (machine-checked falsity — see
`experiments/observations.md`).  The honest bridge ties `w` to the operand strings
through the strcmp-post sign fact `strcmpSign w = strcmpSpecSign csa csb` and the
`CStr` char lists `csa`/`csb` (with `sl = ofList csa`, `sr = ofList csb`).
`StrCmpBlockC.StrCmpOrderBridge` is now (re)defined as that honest form; the four
`strCmpOrderBridge_*` theorems prove it for the exact `binOpSem` closures.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.While Vsa.Sim Sail LeanRV64DExecutable LeanRV64DExecutable.Functions

namespace Vsa.Sim

/-! ## The four boxed sign-tail words as sign tests on `w` -/

/-- `srli w 0x3f`: top (sign) bit — nonzero iff `2^63 ≤ w.toNat`. -/
theorem shr63_ne_iff (w : BitVec 64) : (w >>> (63 : Nat) != 0#64) = decide (2^63 ≤ w.toNat) := by
  by_cases h : 2^63 ≤ w.toNat
  · have hv : (w >>> (63 : Nat)).toNat = 1 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := w.isLt; omega
    have : (w >>> (63 : Nat)) ≠ 0#64 := fun hc => by rw [hc] at hv; simp at hv
    simp [this, h]
  · have hv : (w >>> (63 : Nat)).toNat = 0 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    have : (w >>> (63 : Nat)) = 0#64 := BitVec.eq_of_toNat_eq (by rw [hv]; rfl)
    simp [this, h]

/-- `zero_extend (bool_to_bit b)` is nonzero iff `b`. -/
theorem ze_bb_ne (b : Bool) : (zero_extend (m := 64) (bool_to_bit b) != 0#64) = b := by
  cases b <;> decide

/-- `w.toInt < 0 ↔ 2^63 ≤ w.toNat` (64-bit two's complement sign). -/
theorem toInt_neg_iff64 (w : BitVec 64) : w.toInt < 0 ↔ 2^63 ≤ w.toNat := by
  rw [BitVec.toInt_neg_iff]; omega

/-- `lt` fixup (`srli w 0x3f`): boxed nonzero iff `w` is signed-negative. -/
theorem lt_fix (w : BitVec 64) : (sTailWordLt w != 0#64) = decide (w.toInt < 0) := by
  unfold sTailWordLt shift_bits_right
  rw [show (Sail.BitVec.extractLsb (0x3f#6) 5 0) = (0x3f#6) from rfl,
      show (w >>> (0x3f#6)) = w >>> (63 : Nat) from rfl, shr63_ne_iff]
  exact decide_eq_decide.mpr (toInt_neg_iff64 w).symm

/-- `gt` fixup (`sgtz w`): boxed nonzero iff `0 <ₛ w`. -/
theorem gt_fix (w : BitVec 64) : (sTailWordGt w != 0#64) = decide (0 < w.toInt) := by
  unfold sTailWordGt; rw [ze_bb_ne]; unfold zopz0zI_s
  show decide ((0#64).toInt < w.toInt) = _
  rw [show (0#64).toInt = 0 from rfl]

/-- `le` fixup (`slti w 1`): boxed nonzero iff `w <ₛ 1` (i.e. `w ≤ₛ 0`). -/
theorem le_fix (w : BitVec 64) : (sTailWordLe w != 0#64) = decide (w.toInt < 1) := by
  unfold sTailWordLe; rw [ze_bb_ne]; unfold zopz0zI_s
  show decide (w.toInt < (sign_extend (m := 64) (0x001#12)).toInt) = _
  rw [show (sign_extend (m := 64) (0x001#12)).toInt = 1 from by decide]

/-- `ge` fixup (`not w; srli 0x3f`): boxed nonzero iff `0 ≤ₛ w`. -/
theorem ge_fix (w : BitVec 64) : (sTailWordGe w != 0#64) = decide (0 ≤ w.toInt) := by
  unfold sTailWordGe shift_bits_right
  rw [show (Sail.BitVec.extractLsb (0x3f#6) 5 0) = (0x3f#6) from rfl,
      show (w ^^^ sign_extend (m := 64) (0xfff#12)) = ~~~w from by
        rw [show (sign_extend (m := 64) (0xfff#12)) = BitVec.allOnes 64 from by decide,
            BitVec.xor_allOnes],
      show (~~~w >>> (0x3f#6)) = ~~~w >>> (63 : Nat) from rfl, shr63_ne_iff, BitVec.toNat_not]
  apply decide_eq_decide.mpr
  have hlt := w.isLt
  have hni := toInt_neg_iff64 w
  constructor
  · intro h; omega
  · intro h; omega

/-! ## `strcmpSign` sign-class extraction

`strcmpSign w = strcmpSpecSign csa csb` (strcmp post) pins `w`'s signed class from
the spec sign.  These extract `w.toInt`'s sign from the spec-side comparison. -/

theorem sign_neg_of (w : BitVec 64) (h : strcmpSign w = -1) : w.toInt < 0 := by
  unfold strcmpSign at h
  by_cases h0 : w = 0
  · subst h0; simp at h
  · rw [if_neg h0] at h; by_cases hn : w.toInt < 0
    · exact hn
    · rw [if_neg hn] at h; simp at h

theorem sign_pos_of (w : BitVec 64) (h : strcmpSign w = 1) : 0 < w.toInt := by
  unfold strcmpSign at h
  by_cases h0 : w = 0
  · subst h0; simp at h
  · rw [if_neg h0] at h; by_cases hn : w.toInt < 0
    · rw [if_pos hn] at h; simp at h
    · have hne : w.toInt ≠ 0 := fun hh => h0 (BitVec.toInt_inj.mp (by rw [hh]; rfl))
      omega

theorem sign_zero_of (w : BitVec 64) (h : strcmpSign w = 0) : w.toInt = 0 := by
  unfold strcmpSign at h
  by_cases h0 : w = 0
  · subst h0; rfl
  · rw [if_neg h0] at h; by_cases hn : w.toInt < 0 <;> simp [hn] at h

/-- `strcmpSpecSign` is trichotomous into the three spec-sign classes. -/
theorem specSign_trichotomy (csa csb : List Char) :
    strcmpSpecSign csa csb < 0 ∨ strcmpSpecSign csa csb = 0 ∨ 0 < strcmpSpecSign csa csb := by
  rcases Int.lt_trichotomy (strcmpSpecSign csa csb) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## `String` order ↔ `List.Lex` at `ofList` operands -/

/-- `String.<` unfolds to `List.Lex` on the char lists. -/
theorem string_lt_iff_lex (sl sr : String) :
    (sl < sr) ↔ List.Lex (·<·) sl.toList sr.toList := Iff.rfl

/-- `String.==` reflects string equality. -/
theorem string_beq_iff (sl sr : String) : (sl == sr) = true ↔ sl = sr :=
  ⟨eq_of_beq, fun h => by subst h; exact beq_self_eq_true' _⟩

/-! ## The four instances of the honest `StrCmpBlockC.StrCmpOrderBridge`

`StrCmpBlockC.StrCmpOrderBridge op bres` is (now) the honest tied form: for the
strcmp return `w` on two `CStr` char lists `csa`/`csb` (so `AllNonzero`), whenever
`strcmpSign w = strcmpSpecSign csa csb`, the op's boxed boolean equals the source
order `bres (ofList csa) (ofList csb)`.  The four theorems below PROVE it for the
exact `binOpSem` closures, discharging the `hOrder` legs of `strCmpCell_*_of`. -/

/-- `.lt` order bridge: boxed `srli`-top-bit agrees with `sl < sr`. -/
theorem strCmpOrderBridge_lt : StrCmpOrderBridge .lt (fun sl sr => sl < sr) := by
  intro w csa csb ha hb hsign
  show (sTailWord .lt w != 0#64) = decide (String.ofList csa < String.ofList csb)
  rw [show sTailWord .lt w = sTailWordLt w from rfl, lt_fix]
  apply decide_eq_decide.mpr
  rw [string_lt_iff_lex, String.toList_ofList, String.toList_ofList,
      ← strcmpSpecSign_neg_iff_lex csa csb ha hb]
  constructor
  · intro h
    -- w.toInt < 0 ⇒ strcmpSign w = -1 ⇒ strcmpSpecSign < 0
    have : strcmpSign w = -1 := by
      unfold strcmpSign
      rw [if_neg (fun h0 => by rw [h0] at h; simp at h), if_pos h]
    rw [this] at hsign; omega
  · intro h
    -- strcmpSpecSign < 0 ⇒ strcmpSign w = -1 ⇒ w.toInt < 0
    have : strcmpSign w = -1 := by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega
    exact sign_neg_of w this

/-- `.gt` order bridge: boxed `sgtz` agrees with `sr < sl`. -/
theorem strCmpOrderBridge_gt : StrCmpOrderBridge .gt (fun sl sr => sr < sl) := by
  intro w csa csb ha hb hsign
  show (sTailWord .gt w != 0#64) = decide (String.ofList csb < String.ofList csa)
  rw [show sTailWord .gt w = sTailWordGt w from rfl, gt_fix]
  apply decide_eq_decide.mpr
  rw [string_lt_iff_lex, String.toList_ofList, String.toList_ofList,
      ← strcmpSpecSign_pos_iff_lex csa csb ha hb]
  constructor
  · intro h
    have : strcmpSign w = 1 := by
      unfold strcmpSign
      rw [if_neg (fun h0 => by rw [h0] at h; simp at h), if_neg (by omega)]
    rw [this] at hsign; omega
  · intro h
    have : strcmpSign w = 1 := by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega
    exact sign_pos_of w this

/-- `.le` order bridge: boxed `slti w 1` agrees with `sl < sr || sl == sr`. -/
theorem strCmpOrderBridge_le : StrCmpOrderBridge .le (fun sl sr => sl < sr || sl == sr) := by
  intro w csa csb ha hb hsign
  show (sTailWord .le w != 0#64)
      = ((String.ofList csa < String.ofList csb) || (String.ofList csa == String.ofList csb))
  rw [show sTailWord .le w = sTailWordLe w from rfl, le_fix, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, string_beq_iff, string_lt_iff_lex,
    String.toList_ofList, String.ofList_inj]
  -- goal: (w.toInt < 1) ↔ (List.Lex … csa csb ∨ csa = csb)
  rw [← strcmpSpecSign_neg_iff_lex csa csb ha hb]
  rcases specSign_trichotomy csa csb with hneg | hz | hpos
  · have hwlt : w.toInt < 0 := sign_neg_of w (by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega)
    exact ⟨fun _ => Or.inl hneg, fun _ => by omega⟩
  · have hw0 : w.toInt = 0 := sign_zero_of w (by rw [hsign]; exact hz)
    exact ⟨fun _ => Or.inr (eq_of_strcmpSpecSign_zero_ascii csa csb ha hb hz), fun _ => by omega⟩
  · have hwpos : 0 < w.toInt := sign_pos_of w (by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega)
    refine ⟨fun h => by omega, ?_⟩
    rintro (h | h)
    · omega
    · rw [h, strcmpSpecSign_self_zero csb hb] at hpos; omega

/-- `.ge` order bridge: boxed `not;srli` agrees with `sr < sl || sl == sr`. -/
theorem strCmpOrderBridge_ge : StrCmpOrderBridge .ge (fun sl sr => sr < sl || sl == sr) := by
  intro w csa csb ha hb hsign
  show (sTailWord .ge w != 0#64)
      = ((String.ofList csb < String.ofList csa) || (String.ofList csa == String.ofList csb))
  rw [show sTailWord .ge w = sTailWordGe w from rfl, ge_fix, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, string_beq_iff, string_lt_iff_lex,
    String.toList_ofList, String.ofList_inj]
  -- goal: (0 ≤ w.toInt) ↔ (List.Lex … csb csa ∨ csa = csb)
  rw [← strcmpSpecSign_pos_iff_lex csa csb ha hb]
  rcases specSign_trichotomy csa csb with hneg | hz | hpos
  · have hwlt : w.toInt < 0 := sign_neg_of w (by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega)
    refine ⟨fun h => by omega, ?_⟩
    rintro (h | h)
    · omega
    · rw [h, strcmpSpecSign_self_zero csb hb] at hneg; omega
  · have hw0 : w.toInt = 0 := sign_zero_of w (by rw [hsign]; exact hz)
    exact ⟨fun _ => Or.inr (eq_of_strcmpSpecSign_zero_ascii csa csb ha hb hz), fun _ => by omega⟩
  · have hwpos : 0 < w.toInt := sign_pos_of w (by rw [hsign]; rcases strcmpSpecSign_range csa csb with h|h|h <;> omega)
    exact ⟨fun _ => Or.inl hpos, fun _ => by omega⟩

#print axioms strCmpOrderBridge_lt
#print axioms strCmpOrderBridge_gt
#print axioms strCmpOrderBridge_le
#print axioms strCmpOrderBridge_ge

end Vsa.Sim
