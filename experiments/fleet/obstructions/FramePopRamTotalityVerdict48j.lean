import Vsa.Sim.rows.BinArmBridge
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

/-!
# Wave 48j — the RAM-totality supplier is a FALSE PREMISE for map-presence (Law 4 STOP)

Task 48j proposed: back `frame_pop`'s presence field `∀a∈[sp-K,sp), ∃b, m0[a]?=some b`
by a "RAM-totality supplier" from the zero-init-RAM memory model (unmapped ⇒ read 0).

MACHINE-CHECKED VERDICT (this file): the premise conflates two DISTINCT facts.

1. The model's `readByte` IS total: it returns `(map.get? a).getD 0`
   (`Sail/ConcurrencyInterfaceV1.lean:218-222`, "Unmapped addresses read as zero").
   So a load NEVER fails on presence — an unmapped byte reads as `0`.

2. But `frame_pop`'s field (and every BlockMem load lemma, e.g. `exec_lbu_bm`'s
   `h0 : σ.mem[a]? = some b0`, `vmem_read_data_one:650`) demands HASHMAP presence
   `m0[a]? = some b`.  For the callee's OWN unwritten entry frame `[sp-1120,sp)`
   these bytes are genuinely absent from the map (never loaded from ELF, not yet
   written) — so `m0[a]? = none`, and the field is FALSE, exactly as
   `framePopProbe_false` shows.  `.getD 0` totality does NOT imply map-presence.

Below: the two facts, machine-checked, to make the gap decisive.
NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim.Rows.FramePopRamTotality48j

/-- **FACT 1 (model read is total).**  `readByte` on the empty map returns `0`, not a
throw: the read is defined everywhere via `.getD 0`.  This is what "zero-init RAM"
actually buys — a total *read value*, `some 0#8` as an Option-of-value. -/
theorem readByte_total_on_empty :
    ((∅ : Mem)[(0 : Nat)]?).getD (0#8) = (0#8 : BitVec 8) := by
  rw [show ((∅ : Mem)[(0 : Nat)]?) = none from Std.ExtHashMap.getElem?_empty]
  rfl

/-- **FACT 2 (map-presence is NOT total).**  The very same address is ABSENT from the
map: `m0[a]? = none`.  So the `∃b, m0[a]? = some b` presence conclusion that
`frame_pop` (and every load lemma) needs is FALSE for an unwritten byte — the
`.getD 0` totality of FACT 1 supplies a *value*, never map-*presence*. -/
theorem map_presence_not_total :
    ¬ (∃ b, (∅ : Mem)[(0 : Nat)]? = some b) := by
  rintro ⟨b, hb⟩
  rw [show ((∅ : Mem)[(0 : Nat)]?) = none from Std.ExtHashMap.getElem?_empty] at hb
  exact absurd hb (by simp)

/-- **VERDICT.**  A "RAM-totality supplier" of the shape `∀a, ∃b, m0[a]?=some b`
would be OUTRIGHT FALSE (instantiate at `a=0` on any map missing `0`), so it cannot
be a *verified* supplier — adding it as an `EvalEntry` field would inject a new
falsity, precisely the census's guard.  The two facts above are not the same fact:
totality lives at the READ (`.getD 0`), presence lives in the MAP. `frame_pop`'s
field asks for the latter and cannot get it from the former. -/
theorem ramTotality_is_not_a_map_presence_supplier :
    (∀ a : Nat, ((∅ : Mem)[a]?).getD (0#8) = (0#8))  -- FACT-1-style totality holds
    ∧ ¬ (∀ a : Nat, ∃ b, (∅ : Mem)[a]? = some b) := by  -- yet map-presence FAILS
  refine ⟨fun a => ?_, fun h => ?_⟩
  · rw [show ((∅ : Mem)[a]?) = none from Std.ExtHashMap.getElem?_empty]; rfl
  · obtain ⟨b, hb⟩ := h 0
    rw [show ((∅ : Mem)[(0 : Nat)]?) = none from Std.ExtHashMap.getElem?_empty] at hb
    exact absurd hb (by simp)

#print axioms readByte_total_on_empty
#print axioms map_presence_not_total
#print axioms ramTotality_is_not_a_map_presence_supplier

end Vsa.Sim.Rows.FramePopRamTotality48j
