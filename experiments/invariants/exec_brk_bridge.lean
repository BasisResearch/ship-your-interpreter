/- Hermetic relational-bridge candidate for the exec `brk` arm entry (ANALYSIS
ONLY; stage-5/6 draft, NOTHING here enters a proof).

Mined by scripts/mine_relational.py from the machine dispatch trace × the spec
`kindOfStmt` trace on while.wl.  The candidate encodes the two mined conjuncts
as a ghost structure in the repo idiom (named fields), so the fuzzer can probe
it via `--file --struct`:

  * `kindTag  : read low byte of the stmt node = 7`         (the StmtRepr bridge)
  * `armRoute : jump-table slot 7 routes to execArmBrk`     (the StmtSlotPinned bridge)

This is a self-contained toy model (no repo imports) whose SHAPE mirrors the
landed `stmtRepr_kind` (ExecDispatch.lean) + `StmtTablePins.slot7`
(ExecEntry.lean).  A CORRECT candidate is self-consistent (fuzzer SURVIVES); a
mutant that mis-tags the slot is refutable by witness (fuzzer REFUTES). -/

namespace ExecBrkBridge

/-- Toy stmt-node model: the kind byte (ℕ) + a signed (base, slotWord)
jump-table pin on ℤ (the real slot word is a sign-extended, negative offset). -/
structure BrkArmEntry (kindByte : Nat) (slotWord armPC base : Int) : Prop where
  /-- the represented brk node's kind byte is the brk tag 7 -/
  kindTag  : kindByte = 7
  /-- the jump-table slot 7 word, added to the base, lands on the brk arm PC -/
  armRoute : base + slotWord = armPC

/-- The mined instance: base = stmtJumpTableBase (0x80019fb8), brk arm PC
0x80004098, slot word = armPC - base (a negative offset, faithfully on ℤ). -/
def brkArmMined : Prop :=
  BrkArmEntry 7 (0x80004098 - 0x80019fb8) 0x80004098 0x80019fb8

/-- A MUTANT: mis-tags the slot as the cont arm (0x800040b8), so armRoute is
false against the brk arm PC — the CTI the fuzzer must refute. -/
def brkArmMutant : Prop :=
  BrkArmEntry 7 (0x800040b8 - 0x80019fb8) 0x80004098 0x80019fb8

/-- The correct candidate is inhabited (self-consistent). -/
theorem brkArmMined_ok : brkArmMined := ⟨rfl, by decide⟩

end ExecBrkBridge
