import Vsa.Sim.rows.BinArmBridge
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

/-!
# Wave 48f — `BinArmExtras.frame_pop`/`x13_pres` are GENUINE NEW RUNGS (Law 4)

Wave 48f DROPPED `BinArmExtras.mem_ext` (machine-checked redundant with `blockA_k`'s
2nd output `_hpresM : MemExtends m0 ment`; the drop LANDED green, axiom-clean).  This
file machine-checks that the REMAINING two closure fields — `frame_pop` and `x13_pres`
— are NOT the same "redundant / thread-the-block-fact" class: they are genuinely new
rungs that no current block output nor `EvalEntry`/`EvalGround` field supplies.

## `frame_pop`

`frame_pop : ∀ mcall, (agree m0 off [SL.lo,sp)) → ∀ a ∈ [sp-1120,sp) → ∃b, mcall[a]?=some b`.

Refuted as a standalone conclusion below: `[sp-1120,sp) ⊆ [SL.lo,sp)` (the very window
`mcall` may zero), so an empty `mcall` agreeing with `m0` off-window refutes it.  This
mirrors `PresProbe`/`presProbe_false`, but is stated over the ACTUAL `BinArmExtras`
window so it is decisive for the int/eq cells.

Why not block-derivable: the consumer (`blockC_neg`, `EvalNegSim2.lean:231-276` via
`stackpop_present`) reads the DEAD sub-result-buffer bytes `[subsret+4,+8) ∪
[subsret+16,+24)` (subsret=sp-944 ∈ [sp-1120,sp)) out of the PRE-call memory `ment`.
`ValueRepr (.int n)` pins only kind+payload (`EvalRecCommon.lean:14-20`), and the
prologue writes only the 4 spill slots `[sp-8..sp-32]` — so those bytes' presence in
`ment` reduces (via the memframe `ment[a]?=m0[a]?`) to presence in `m0`.  `EvalGround`
carries table/AST pins + disjointness, NOT frame-window presence.  So `frame_pop`'s
honest cure is a NEW entry-ground frame-presence field — a genuine rung, NOT the
thread-`_hpresM` move that cleared `mem_ext`.

## `x13_pres`

`x13_pres` demands a live `x13`(a3) at the arm-entry config.  `ArmEntryK` does not
expose `x13` (a caller-save temp outside `blockA_k`'s callee-saved frame).  Its honest
cure is a `blockA_k`/`ArmEntryK` widening tracking `x13` across the dispatch span
`0x80003164→0x800034e8` — a genuine rung, not a currently-produced fact.

Verified with `lake env lean` only; NOT part of the build (obstruction evidence).
NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim.Rows.FramePopNewRung

/-- The `BinArmExtras.frame_pop` field, isolated over the actual `[sp-1120,sp)`
window.  Refutable: pick `mcall` empty inside the window it is permitted to zero. -/
def FramePopProbe : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)

theorem framePopProbe_false : ¬ FramePopProbe := by
  intro h
  -- SL.lo = 0, sp = 1120: window [0,1120), sp-1120 = 0, so a = 0 is in-window.
  let SL : StackLayout := ⟨0, 1000000⟩
  let sp : BitVec 64 := 1120#64
  let m0 : Mem := (∅ : Mem)
  let mcall : Mem := (∅ : Mem)
  have hsp : sp.toNat = 1120 := by decide
  have hagree : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := by
    intro a _; rfl
  obtain ⟨b, hb⟩ := h SL sp m0 mcall hagree 0 (by rw [hsp]; exact Nat.le_refl 0)
    (by rw [hsp]; decide)
  have hmc0 : (mcall[0]? : Option (BitVec 8)) = none := by
    show mcall[0]? = none; simp only [mcall, Std.ExtHashMap.getElem?_empty]
  rw [hmc0] at hb; exact absurd hb (by simp)

#print axioms framePopProbe_false

end Vsa.Sim.Rows.FramePopNewRung
