import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

/-!
# Joint / interlock validation fixtures (smt_check.py `--joint`)

Hermetic, encodable-fragment models of the int/eq arm's interlock — the target
structures whose CONJUNCTS the wave-48e/48f/48g history proved a per-field filter
mishandles.  Each `*Extras` structure below is a named-field `structure … : Prop`
carrying exactly the interlock-relevant conjuncts in the SMT fragment
(stack-window presence, deep-recursion headroom, x13 liveness modelled as a
presence bit).  The joint acceptance (gates a–d) runs `--joint-inhabit`,
`--producer-check`, `--consumer-check` against these.

These are ANALYSIS fixtures, NOT part of the build (Vsa/ untouched).  We model:
* `frame_pop`  — the dead sub-result-buffer bytes `[sp-1120,sp) ⊆ [SL.lo,sp)`
  present in the pre-call `mcall` (the 48f "ground field").
* `x13_live`   — a3 liveness at arm entry, modelled as a presence flag on a
  sentinel address `x13slot` (blockB spills it via `sd a3,0(sp)`).
* `sproom`     — deep-recursion headroom `SL.lo + 4352 ≤ sp.toNat`.
* `slot6`      — a static jump-table pin, modelled as presence of the pin word.
-/

namespace JointFix

/-- ENTRY carrier (the 48e cure-A "entry-carry"): what `EvalEntry` actually pins
in the fragment — the deep-recursion headroom + the jump-table slot word.  It
does NOT pin the scribble-window frame bytes nor x13 (the 48e insufficiency). -/
structure EntryPins (SL : StackLayout) (sp : BitVec 64) (m0 : Mem)
    (slotAddr : Nat) : Prop where
  sproom  : SL.lo + 4352 ≤ sp.toNat
  slot6   : ∃ b, m0[slotAddr]? = some b

/-! ## (a) pre-48f BinArmExtras + 48e cure-A (entry-carry ONLY)
The extras still carry `frame_pop` (dead-byte presence) + `x13_live`; the entry
carry supplies only headroom + slot.  Producer = the entry pins alone. -/
structure ExtrasA (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat) : Prop where
  sproom    : SL.lo + 4352 ≤ sp.toNat
  slot6     : ∃ b, m0[slotAddr]? = some b
  -- dead sub-result buffer present in the pre-call memory (a3 is spilled here)
  frame_pop : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
  -- a3 liveness at arm entry, modelled as presence on the x13 sentinel slot
  x13_live  : ∃ w, mcall[x13slot]? = some w

def TargetA : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat),
    EntryPins SL sp m0 slotAddr →
    ExtrasA SL sp m0 mcall slotAddr x13slot

/-! ## (b) the 48f frame_pop GROUND-FIELD cure
Proposes discharging `frame_pop` from a NEW `EvalGround` "frame_present" field
that claims `m0` totality on the whole scribble window `[SL.lo, sp)`.  The
producer that is actually available (entry pins) does not supply that totality —
producer-check must FAIL on the totality conjunct (the falsity-in-waiting). -/
structure ExtrasB (SL : StackLayout) (sp : BitVec 64) (m0 : Mem)
    (slotAddr : Nat) : Prop where
  sproom        : SL.lo + 4352 ≤ sp.toNat
  slot6         : ∃ b, m0[slotAddr]? = some b
  -- the UNVERIFIED m0-totality supplier the 48f ground field would need
  frame_present : ∀ a : Nat, SL.lo ≤ a → a < sp.toNat → (∃ b, m0[a]? = some b)

def TargetB : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem) (slotAddr : Nat),
    EntryPins SL sp m0 slotAddr →
    ExtrasB SL sp m0 slotAddr

/-! ## (c) x13_pres-DELETION candidate
Deletes the `x13_live` conjunct from the extras.  A live consumer (`blockB_binary`
spills a3: it DEMANDS x13 presence).  consumer-check must FAIL that demand. -/
structure ExtrasC (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat) : Prop where
  sproom    : SL.lo + 4352 ≤ sp.toNat
  slot6     : ∃ b, m0[slotAddr]? = some b
  frame_pop : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
  -- x13_live DELETED

def TargetC : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat),
    ExtrasC SL sp m0 mcall slotAddr x13slot

/-! ## (d) the recorded 48g three-cure recipe (best encodable)
frame_pop discharged INSIDE the sim cone (SubEvalReturn buffer-write presence),
x13 discharged by a blockA_k widening emitting `∃w, x13 = some w`, entry-carry for
headroom+slot.  The RECIPE-consistent producer supplies ALL conjuncts.  Joint
must be SAT and no producer/consumer failure in-fragment. -/
structure ExtrasD (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat) : Prop where
  sproom    : SL.lo + 4352 ≤ sp.toNat
  slot6     : ∃ b, m0[slotAddr]? = some b
  frame_pop : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
  x13_live  : ∃ w, mcall[x13slot]? = some w

def TargetD : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem)
    (slotAddr x13slot : Nat),
    ExtrasD SL sp m0 mcall slotAddr x13slot

end JointFix


set_option pp.fullNames false in
#check @ExtrasD.mk
