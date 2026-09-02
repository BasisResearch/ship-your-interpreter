import Vsa.Sim.EntryGround
import Vsa.Sim.rows.Field_hStr
import Vsa.Sim.rows.ExecCaseGeom
import Vsa.Sim.rows.LayoutJumpTableGen
import Vsa.Sim.rows.LayoutStmtTableGen

/-!
# `EntryGroundRows` — record-fill discharges from the batched `ground` bundle

The consumer half of `EntryGround.lean` (wave 47h): machine-checks that once
`EvalEntry.ground`/`ExecEntry.ground` are inserted (the mapped fan-out,
`experiments/entry-needs-audit.md` §D), the audited needs discharge as record
fills — no new proof will be needed at insertion time:

* `strAstRegionBody_of_ground` — the EXACT ∃-body of `EvalEntryStrAstRegion`
  (`rows/Field_hStr.lean`); post-insertion `field_hStr_of_astRegion` closes
  `hStr` with `fun … hc => strAstRegionBody_of_ground hc.ground`.
* `execGround_caseGeom_brk`/`_cont` — the slot-pin + table-disjointness
  conjuncts of `ExecCaseGeom` (the WHOLE entry-suppliable half; the widener
  half is audit class X3, a block re-land).  `execGround_slot_window` is the
  generic-k window narrowing all nine exec arms share.
* `kindTablePins_of_bytes`/`stmtTablePins_of_bytes` — the M6 suppliers: the
  generated `groundSlot_0..10`/`groundStmtSlot_0..8` assembled into the
  bundles from the raw rodata byte pins of the loaded image.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.Rows

/-! ## The `hStr` discharge shape -/

/-- **The `EvalEntryStrAstRegion` ∃-body, from the ground bundle** — the
`.str`-root projection of `EvalGround.ast`.  `StrPayloadIn`'s strict payload
bound comes from `StrIn`'s NUL-inclusive bound via `exprIn_str_payload`. -/
theorem strAstRegionBody_of_ground {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {s : String}
    (hg : Vsa.Sim.EvalGround m SL A sp sret aExpr (.str s)) :
    ∃ lo hi,
      StrPayloadIn m lo hi aExpr s ∧
      (hi ≤ SL.lo ∨ SL.hi ≤ lo) ∧
      (hi ≤ sret.toNat ∨ sret.toNat + 24 ≤ lo) := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  exact ⟨lo, hi, ⟨Vsa.Sim.exprIn_str_payload spec.nodes⟩,
    spec.stack_disjoint, spec.sret_disjoint⟩

/-! ## The exec-arm entry-suppliable halves -/

/-- Generic slot-window narrowing: the whole-table stack disjunct gives every
slot's 4-byte-window disjunct. -/
theorem execGround_slot_window {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : Vsa.Sim.ExecGround m SL A sp aRet aStmt s) (k : Nat) (hk : k < 9) :
    Vsa.Sim.stmtJumpTableBase + 4 * k + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * k := by
  rcases hg.table_stack with h | h
  · exact Or.inl (by simp only [Vsa.Sim.stmtJumpTableBase] at h ⊢; omega)
  · exact Or.inr (by simp only [Vsa.Sim.stmtJumpTableBase] at h ⊢; omega)

/-- **`ExecCaseGeom`'s entry-suppliable half for `brk` (tag 7)**: the slot pin
and the table disjunct discharge from the ground; ONLY the widener (audit X3)
remains. -/
theorem execGround_caseGeom_brk {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat}
    (hg : Vsa.Sim.ExecGround m SL A sp aRet aStmt .brk) :
    Vsa.Sim.StmtSlotPinned 7 Vsa.Sim.execArmBrk m ∧
    (Vsa.Sim.stmtJumpTableBase + 4 * 7 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 7) :=
  ⟨hg.table.slot7, execGround_slot_window hg 7 (by omega)⟩

/-- **`ExecCaseGeom`'s entry-suppliable half for `cont` (tag 8).** -/
theorem execGround_caseGeom_cont {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat}
    (hg : Vsa.Sim.ExecGround m SL A sp aRet aStmt .cont) :
    Vsa.Sim.StmtSlotPinned 8 Vsa.Sim.execArmCont m ∧
    (Vsa.Sim.stmtJumpTableBase + 4 * 8 + 4 ≤ SL.lo ∨
      sp.toNat ≤ Vsa.Sim.stmtJumpTableBase + 4 * 8) :=
  ⟨hg.table.slot8, execGround_slot_window hg 8 (by omega)⟩

/-! ## The M6 suppliers — generated pins assembled into the bundles -/

/-- `StmtTablePins` from the raw 36 rodata byte pins of the loaded image (the
generated `groundStmtSlot_k` per slot).  ONE hypothesis: the byte at every
table offset matches the ELF (`stmtTableByte`, the generated values). -/
def stmtTableBytes : List (Nat × Nat) :=
  [(0x00, 0xb8), (0x01, 0xa1), (0x02, 0xfe), (0x03, 0xff),
   (0x04, 0x20), (0x05, 0xa1), (0x06, 0xfe), (0x07, 0xff),
   (0x08, 0xd4), (0x09, 0xa1), (0x0a, 0xfe), (0x0b, 0xff),
   (0x0c, 0x30), (0x0d, 0xa2), (0x0e, 0xfe), (0x0f, 0xff),
   (0x10, 0x84), (0x11, 0xa0), (0x12, 0xfe), (0x13, 0xff),
   (0x14, 0x7c), (0x15, 0xa2), (0x16, 0xfe), (0x17, 0xff),
   (0x18, 0x68), (0x19, 0xa1), (0x1a, 0xfe), (0x1b, 0xff),
   (0x1c, 0xe0), (0x1d, 0xa0), (0x1e, 0xfe), (0x1f, 0xff),
   (0x20, 0x00), (0x21, 0xa1), (0x22, 0xfe), (0x23, 0xff)]

theorem stmtTablePins_of_bytes {m : Mem}
    (h : ∀ off b, (off, b) ∈ stmtTableBytes →
      m[(Vsa.Sim.stmtJumpTableBase + off : Nat)]? = some (BitVec.ofNat 8 b)) :
    Vsa.Sim.StmtTablePins m where
  slot0 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_0
    (h 0x00 0xb8 (by decide)) (h 0x01 0xa1 (by decide))
    (h 0x02 0xfe (by decide)) (h 0x03 0xff (by decide))
  slot1 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_1
    (h 0x04 0x20 (by decide)) (h 0x05 0xa1 (by decide))
    (h 0x06 0xfe (by decide)) (h 0x07 0xff (by decide))
  slot2 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_2
    (h 0x08 0xd4 (by decide)) (h 0x09 0xa1 (by decide))
    (h 0x0a 0xfe (by decide)) (h 0x0b 0xff (by decide))
  slot3 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_3
    (h 0x0c 0x30 (by decide)) (h 0x0d 0xa2 (by decide))
    (h 0x0e 0xfe (by decide)) (h 0x0f 0xff (by decide))
  slot4 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_4
    (h 0x10 0x84 (by decide)) (h 0x11 0xa0 (by decide))
    (h 0x12 0xfe (by decide)) (h 0x13 0xff (by decide))
  slot5 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_5
    (h 0x14 0x7c (by decide)) (h 0x15 0xa2 (by decide))
    (h 0x16 0xfe (by decide)) (h 0x17 0xff (by decide))
  slot6 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_6
    (h 0x18 0x68 (by decide)) (h 0x19 0xa1 (by decide))
    (h 0x1a 0xfe (by decide)) (h 0x1b 0xff (by decide))
  slot7 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_7
    (h 0x1c 0xe0 (by decide)) (h 0x1d 0xa0 (by decide))
    (h 0x1e 0xfe (by decide)) (h 0x1f 0xff (by decide))
  slot8 := Vsa.Sim.LayoutStmtTableGen.groundStmtSlot_8
    (h 0x20 0x00 (by decide)) (h 0x21 0xa1 (by decide))
    (h 0x22 0xfe (by decide)) (h 0x23 0xff (by decide))

/-- `KindTablePins` from the raw 44 rodata byte pins (generated
`groundSlot_k` per slot; byte values = the `LayoutJumpTableGen` table). -/
def kindTableBytes : List (Nat × Nat) :=
  [(0x00, 0xb0), (0x01, 0x94), (0x02, 0xfe), (0x03, 0xff),
   (0x04, 0xbc), (0x05, 0x94), (0x06, 0xfe), (0x07, 0xff),
   (0x08, 0xc8), (0x09, 0x94), (0x0a, 0xfe), (0x0b, 0xff),
   (0x0c, 0xd4), (0x0d, 0x94), (0x0e, 0xfe), (0x0f, 0xff),
   (0x10, 0xdc), (0x11, 0x94), (0x12, 0xfe), (0x13, 0xff),
   (0x14, 0x24), (0x15, 0x95), (0x16, 0xfe), (0x17, 0xff),
   (0x18, 0x90), (0x19, 0x95), (0x1a, 0xfe), (0x1b, 0xff),
   (0x1c, 0x04), (0x1d, 0x96), (0x1e, 0xfe), (0x1f, 0xff),
   (0x20, 0x88), (0x21, 0x96), (0x22, 0xfe), (0x23, 0xff),
   (0x24, 0x58), (0x25, 0x92), (0x26, 0xfe), (0x27, 0xff),
   (0x28, 0x6c), (0x29, 0x94), (0x2a, 0xfe), (0x2b, 0xff)]

theorem kindTablePins_of_bytes {m : Mem}
    (h : ∀ off b, (off, b) ∈ kindTableBytes →
      m[(Vsa.Sim.jumpTableBase + off : Nat)]? = some (BitVec.ofNat 8 b)) :
    Vsa.Sim.KindTablePins m where
  slot0 := Vsa.Sim.LayoutJumpTableGen.groundSlot_0
    (h 0x00 0xb0 (by decide)) (h 0x01 0x94 (by decide))
    (h 0x02 0xfe (by decide)) (h 0x03 0xff (by decide))
  slot1 := Vsa.Sim.LayoutJumpTableGen.groundSlot_1
    (h 0x04 0xbc (by decide)) (h 0x05 0x94 (by decide))
    (h 0x06 0xfe (by decide)) (h 0x07 0xff (by decide))
  slot2 := Vsa.Sim.LayoutJumpTableGen.groundSlot_2
    (h 0x08 0xc8 (by decide)) (h 0x09 0x94 (by decide))
    (h 0x0a 0xfe (by decide)) (h 0x0b 0xff (by decide))
  slot3 := Vsa.Sim.LayoutJumpTableGen.groundSlot_3
    (h 0x0c 0xd4 (by decide)) (h 0x0d 0x94 (by decide))
    (h 0x0e 0xfe (by decide)) (h 0x0f 0xff (by decide))
  slot4 := Vsa.Sim.LayoutJumpTableGen.groundSlot_4
    (h 0x10 0xdc (by decide)) (h 0x11 0x94 (by decide))
    (h 0x12 0xfe (by decide)) (h 0x13 0xff (by decide))
  slot5 := Vsa.Sim.LayoutJumpTableGen.groundSlot_5
    (h 0x14 0x24 (by decide)) (h 0x15 0x95 (by decide))
    (h 0x16 0xfe (by decide)) (h 0x17 0xff (by decide))
  slot6 := Vsa.Sim.LayoutJumpTableGen.groundSlot_6
    (h 0x18 0x90 (by decide)) (h 0x19 0x95 (by decide))
    (h 0x1a 0xfe (by decide)) (h 0x1b 0xff (by decide))
  slot7 := Vsa.Sim.LayoutJumpTableGen.groundSlot_7
    (h 0x1c 0x04 (by decide)) (h 0x1d 0x96 (by decide))
    (h 0x1e 0xfe (by decide)) (h 0x1f 0xff (by decide))
  slot8 := Vsa.Sim.LayoutJumpTableGen.groundSlot_8
    (h 0x20 0x88 (by decide)) (h 0x21 0x96 (by decide))
    (h 0x22 0xfe (by decide)) (h 0x23 0xff (by decide))
  slot9 := Vsa.Sim.LayoutJumpTableGen.groundSlot_9
    (h 0x24 0x58 (by decide)) (h 0x25 0x92 (by decide))
    (h 0x26 0xfe (by decide)) (h 0x27 0xff (by decide))
  slot10 := Vsa.Sim.LayoutJumpTableGen.groundSlot_10
    (h 0x28 0x6c (by decide)) (h 0x29 0x94 (by decide))
    (h 0x2a 0xfe (by decide)) (h 0x2b 0xff (by decide))

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.strAstRegionBody_of_ground
#print axioms Vsa.Sim.Rows.execGround_caseGeom_brk
#print axioms Vsa.Sim.Rows.execGround_caseGeom_cont
#print axioms Vsa.Sim.Rows.stmtTablePins_of_bytes
#print axioms Vsa.Sim.Rows.kindTablePins_of_bytes
