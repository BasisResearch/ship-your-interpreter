import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.MemRegion

/-!
# `EntryGround` — the complete entry-need bundle (wave 47h, the fourth-wave factor)

Three serial `EvalEntry` amendments (47e/f/g) each added ONE need class; the
audit (`experiments/entry-needs-audit.md`) collected the COMPLETE remaining
entry-suppliable set — N1 (full eval jump-table pins), N2 (stmt jump-table
pins + disjointness), N3 (AST region), N4 (arena geometry), N5 (result-slot
whole-stack membership) — so the NEXT entry amendment inserts ONE field per
entry and is the LAST:

* `EvalEntry` gains `ground : EvalGround c.σ.mem SL A sp sret aExpr.toNat e`
* `ExecEntry` gains `ground : ExecGround c.σ.mem SL A sp aRet aStmt.toNat s`

Everything here is transport-closed under stack∪result-slot-confined writes
(ONE `survive_stack` call per conduit seam — the practiced 47f `NBSPins`
threading shape; the seam list is `grep -rln NBSPins Vsa/`), and children are
projections (`ExprIn`/`StmtIn` clauses apply directly to payload reads).

Suppliers: `LayoutJumpTableGen.groundSlot_0..10` and
`LayoutStmtTableGen.groundStmtSlot_0..8` (both GENERATED from the ELF rodata)
ground the tables from the loaded image at M6; the AST region is the M6
parse-arena Layout fact (47g verdict).  Consumers: the record-fill discharge
theorems live in `rows/EntryGroundRows.lean` — `hStr` and every exec arm's
slot/table conjuncts discharge the moment the fields land.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-! ## N1 — the full eval jump-table pin bundle (tags 0-10)

Arm PCs are the generated table (`LayoutJumpTableGen` header); the per-wave
trickle fields (`int_slot` tag 0, `nbs_pins` slots 1-3) stay for their landed
consumers — this bundle is the COMPLETE set every remaining arm projects from. -/

structure KindTablePins (m : Mem) : Prop where
  slot0 : KindSlotPinned 0 (0x80003408#64) m   -- EX_INT
  slot1 : KindSlotPinned 1 (0x80003414#64) m   -- EX_STR
  slot2 : KindSlotPinned 2 (0x80003420#64) m   -- EX_BOOL
  slot3 : KindSlotPinned 3 (0x8000342c#64) m   -- EX_NULL
  slot4 : KindSlotPinned 4 (0x80003434#64) m   -- EX_VAR
  slot5 : KindSlotPinned 5 (0x8000347c#64) m   -- EX_ASSIGN
  slot6 : KindSlotPinned 6 (0x800034e8#64) m   -- EX_BINARY
  slot7 : KindSlotPinned 7 (0x8000355c#64) m   -- EX_LOGICAL
  slot8 : KindSlotPinned 8 (0x800035e0#64) m   -- EX_UNARY
  slot9 : KindSlotPinned 9 (0x800031b0#64) m   -- EX_CALL
  slot10 : KindSlotPinned 10 (0x800033c4#64) m -- EX_FN

/-- One slot's pin survives agreement on its own 4-byte window. -/
theorem kindSlotPinned_agree {k : Nat} {armPC : BitVec 64} {m m' : Mem}
    (h : KindSlotPinned k armPC m)
    (ha : ∀ a, jumpTableBase + 4 * k ≤ a → a < jumpTableBase + 4 * k + 4 →
      m[a]? = m'[a]?) :
    KindSlotPinned k armPC m' := by
  obtain ⟨t0, t1, t2, t3, h0, h1, h2, h3, he⟩ := h
  exact ⟨t0, t1, t2, t3,
    (ha _ (by omega) (by omega)).symm.trans h0,
    (ha _ (by omega) (by omega)).symm.trans h1,
    (ha _ (by omega) (by omega)).symm.trans h2,
    (ha _ (by omega) (by omega)).symm.trans h3, he⟩

/-- `KindTablePins` transport: agreement on the whole 44-byte table window. -/
theorem KindTablePins.transport {m m' : Mem} (h : KindTablePins m)
    (ha : ∀ a, jumpTableBase ≤ a → a < jumpTableBase + 44 → m[a]? = m'[a]?) :
    KindTablePins m' where
  slot0 := kindSlotPinned_agree h.slot0 (fun a h1 h2 => ha a (by omega) (by omega))
  slot1 := kindSlotPinned_agree h.slot1 (fun a h1 h2 => ha a (by omega) (by omega))
  slot2 := kindSlotPinned_agree h.slot2 (fun a h1 h2 => ha a (by omega) (by omega))
  slot3 := kindSlotPinned_agree h.slot3 (fun a h1 h2 => ha a (by omega) (by omega))
  slot4 := kindSlotPinned_agree h.slot4 (fun a h1 h2 => ha a (by omega) (by omega))
  slot5 := kindSlotPinned_agree h.slot5 (fun a h1 h2 => ha a (by omega) (by omega))
  slot6 := kindSlotPinned_agree h.slot6 (fun a h1 h2 => ha a (by omega) (by omega))
  slot7 := kindSlotPinned_agree h.slot7 (fun a h1 h2 => ha a (by omega) (by omega))
  slot8 := kindSlotPinned_agree h.slot8 (fun a h1 h2 => ha a (by omega) (by omega))
  slot9 := kindSlotPinned_agree h.slot9 (fun a h1 h2 => ha a (by omega) (by omega))
  slot10 := kindSlotPinned_agree h.slot10 (fun a h1 h2 => ha a (by omega) (by omega))

/-! ## N2 — the stmt jump-table pin bundle (tags 0-8) -/

structure StmtTablePins (m : Mem) : Prop where
  slot0 : StmtSlotPinned 0 execArmExpr m
  slot1 : StmtSlotPinned 1 execArmVarDecl m
  slot2 : StmtSlotPinned 2 execArmBlock m
  slot3 : StmtSlotPinned 3 execArmIf m
  slot4 : StmtSlotPinned 4 execArmWhile m
  slot5 : StmtSlotPinned 5 execArmFor m
  slot6 : StmtSlotPinned 6 execArmRet m
  slot7 : StmtSlotPinned 7 execArmBrk m
  slot8 : StmtSlotPinned 8 execArmCont m

/-- One stmt slot's pin survives agreement on its own 4-byte window. -/
theorem stmtSlotPinned_agree {k : Nat} {armPC : BitVec 64} {m m' : Mem}
    (h : StmtSlotPinned k armPC m)
    (ha : ∀ a, stmtJumpTableBase + 4 * k ≤ a → a < stmtJumpTableBase + 4 * k + 4 →
      m[a]? = m'[a]?) :
    StmtSlotPinned k armPC m' := by
  obtain ⟨⟨t0, t1, t2, t3, h0, h1, h2, h3, he⟩⟩ := h
  exact ⟨⟨t0, t1, t2, t3,
    (ha _ (by omega) (by omega)).symm.trans h0,
    (ha _ (by omega) (by omega)).symm.trans h1,
    (ha _ (by omega) (by omega)).symm.trans h2,
    (ha _ (by omega) (by omega)).symm.trans h3, he⟩⟩

/-- `StmtTablePins` transport: agreement on the whole 36-byte table window. -/
theorem StmtTablePins.transport {m m' : Mem} (h : StmtTablePins m)
    (ha : ∀ a, stmtJumpTableBase ≤ a → a < stmtJumpTableBase + 36 → m[a]? = m'[a]?) :
    StmtTablePins m' where
  slot0 := stmtSlotPinned_agree h.slot0 (fun a h1 h2 => ha a (by omega) (by omega))
  slot1 := stmtSlotPinned_agree h.slot1 (fun a h1 h2 => ha a (by omega) (by omega))
  slot2 := stmtSlotPinned_agree h.slot2 (fun a h1 h2 => ha a (by omega) (by omega))
  slot3 := stmtSlotPinned_agree h.slot3 (fun a h1 h2 => ha a (by omega) (by omega))
  slot4 := stmtSlotPinned_agree h.slot4 (fun a h1 h2 => ha a (by omega) (by omega))
  slot5 := stmtSlotPinned_agree h.slot5 (fun a h1 h2 => ha a (by omega) (by omega))
  slot6 := stmtSlotPinned_agree h.slot6 (fun a h1 h2 => ha a (by omega) (by omega))
  slot7 := stmtSlotPinned_agree h.slot7 (fun a h1 h2 => ha a (by omega) (by omega))
  slot8 := stmtSlotPinned_agree h.slot8 (fun a h1 h2 => ha a (by omega) (by omega))

/-! ## N3 — the AST-region bundle (the 47g `ast_region` proposal, both sides) -/

/-- The AST region for the expression tree at `aExpr`: nodes hereditarily in
`[lo, hi)` (`MemRegion.ExprIn`), region in RAM above HTIF, disjoint from the
WHOLE stack region (transport-closed — child scribbles and in-stack sub-srets
are absorbed, the 47g form), from the result buffer, and from the arena. -/
structure AstRegionSpec (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Expr) (lo hi : Nat) : Prop where
  nodes : ExprIn m lo hi aExpr e
  lo_ram : 0x80000000 ≤ lo
  hi_ram : hi ≤ 0x100000000
  win : tohostAddr + 16 ≤ lo
  stack_disjoint : hi ≤ SL.lo ∨ SL.hi ≤ lo
  sret_disjoint : hi ≤ sret ∨ sret + 24 ≤ lo
  arena_disjoint : hi ≤ A.lo ∨ A.hi ≤ lo

/-- The ∃-packaged eval AST-region pin (a `Prop` structure cannot carry the
`lo`/`hi` data fields — 47g `StrPayloadIn` precedent). -/
structure AstRegionPins (m : Mem) (SL : StackLayout) (A : Arena)
    (sret aExpr : Nat) (e : Expr) : Prop where
  region : ∃ lo hi, AstRegionSpec m SL A sret aExpr e lo hi

/-- The statement-side twin (result slot = the `retslot` at `aRet`). -/
structure StmtRegionSpec (m : Mem) (SL : StackLayout) (A : Arena)
    (aRet aStmt : Nat) (s : Stmt) (lo hi : Nat) : Prop where
  nodes : StmtIn m lo hi aStmt s
  lo_ram : 0x80000000 ≤ lo
  hi_ram : hi ≤ 0x100000000
  win : tohostAddr + 16 ≤ lo
  stack_disjoint : hi ≤ SL.lo ∨ SL.hi ≤ lo
  ret_disjoint : hi ≤ aRet ∨ aRet + 24 ≤ lo
  arena_disjoint : hi ≤ A.lo ∨ A.hi ≤ lo

structure StmtRegionPins (m : Mem) (SL : StackLayout) (A : Arena)
    (aRet aStmt : Nat) (s : Stmt) : Prop where
  region : ∃ lo hi, StmtRegionSpec m SL A aRet aStmt s lo hi

/-- `AstRegionSpec` transports along agreement on `[lo, hi)` (only `nodes`
touches `m`; `exprIn_agreeP` carries it). -/
theorem AstRegionSpec.transport {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sret aExpr : Nat} {e : Expr} {lo hi : Nat}
    (h : AstRegionSpec m SL A sret aExpr e lo hi)
    (ha : ∀ a, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    AstRegionSpec m' SL A sret aExpr e lo hi where
  nodes := exprIn_agreeP (fun a hp => ha a hp.1 hp.2) e h.nodes
  lo_ram := h.lo_ram
  hi_ram := h.hi_ram
  win := h.win
  stack_disjoint := h.stack_disjoint
  sret_disjoint := h.sret_disjoint
  arena_disjoint := h.arena_disjoint

theorem StmtRegionSpec.transport {m m' : Mem} {SL : StackLayout} {A : Arena}
    {aRet aStmt : Nat} {s : Stmt} {lo hi : Nat}
    (h : StmtRegionSpec m SL A aRet aStmt s lo hi)
    (ha : ∀ a, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    StmtRegionSpec m' SL A aRet aStmt s lo hi where
  nodes := stmtIn_agreeP (fun a hp => ha a hp.1 hp.2) s h.nodes
  lo_ram := h.lo_ram
  hi_ram := h.hi_ram
  win := h.win
  stack_disjoint := h.stack_disjoint
  ret_disjoint := h.ret_disjoint
  arena_disjoint := h.arena_disjoint

/-! ## N5 — the exec result-slot (`retslot`) geometry -/

/-- The `retslot` is a proper 24-byte `Value` slot: 8-aligned, in RAM above
HTIF, disjoint from the stack scribble `[SL.lo, sp)`, and INSIDE the whole
stack region (the caller's local — the exec twin of `NegExtras.sret_inSL`). -/
structure RetSlotGeom (SL : StackLayout) (sp aRet : BitVec 64) : Prop where
  align : aRet.toNat % 8 = 0
  ram : 0x80000000 ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ 0x100000000
  win : tohostAddr + 16 ≤ aRet.toNat
  scribble_disjoint : aRet.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRet.toNat
  inSL : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi

/-! ## The batched bundles — ONE field per entry -/

/-- **The complete eval entry-ground bundle** (audit classes N1/N3/N4/N5).
Inserted as `EvalEntry.ground`; transported by `survive_stack`; children by
`ExprIn` projection. -/
structure EvalGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp sret : BitVec 64) (aExpr : Nat) (e : Expr) : Prop where
  table : KindTablePins m
  ast : AstRegionPins m SL A sret.toNat aExpr e
  arena_stack : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  arena_vi : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sret_table_disjoint : sret.toNat + 24 ≤ 0x80019f58 ∨ 0x80019f58 + 44 ≤ sret.toNat

/-- **The complete exec entry-ground bundle** (audit classes N2/N3/N4/N5). -/
structure ExecGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet : BitVec 64) (aStmt : Nat) (s : Stmt) : Prop where
  table : StmtTablePins m
  table_stack : stmtJumpTableBase + 36 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase
  ast : StmtRegionPins m SL A aRet.toNat aStmt s
  arena_stack : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ execStmtEntry ∨ execStmtEnd ≤ A.lo
  aret : RetSlotGeom SL sp aRet
  aret_table_disjoint : aRet.toNat + 24 ≤ stmtJumpTableBase ∨
    stmtJumpTableBase + 36 ≤ aRet.toNat

/-- **`EvalGround` survives any memory change confined to the stack scribble
`[SL.lo, sp)` ∪ the sret window** — the standard entry→child-entry write
footprint.  Needs the entry's whole-table stack disjointness (the 47f
`table_stack_disjoint` literal) for the table half; the AST region and the
literals are self-contained. -/
theorem EvalGround.survive_stack {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hsp : sp.toNat ≤ SL.hi)
    (hag : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → m[k]? = m'[k]?) :
    EvalGround m' SL A sp sret aExpr e where
  table := h.table.transport (fun a h1 h2 => by
    have hj : jumpTableBase = 0x80019f58 := rfl
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases htb with ht | ht <;> omega
    · rcases h.sret_table_disjoint with hs | hs <;> omega)
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, spec.transport (fun a h1 h2 => ?_)⟩
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases spec.stack_disjoint with hs | hs
      · omega
      · have := h.sret_inSL; omega
    · rcases spec.sret_disjoint with hs | hs <;> omega⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_vi := h.arena_vi
  sret_inSL := h.sret_inSL
  sret_table_disjoint := h.sret_table_disjoint

/-- **`ExecGround` survives any memory change confined to the stack scribble
`[SL.lo, sp)` ∪ the retslot window.**  Self-contained: the table/retslot
disjointness literals ride in the bundle. -/
theorem ExecGround.survive_stack {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hag : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24) → m[k]? = m'[k]?) :
    ExecGround m' SL A sp aRet aStmt s where
  table := h.table.transport (fun a h1 h2 => by
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases h.table_stack with ht | ht <;> omega
    · rcases h.aret_table_disjoint with hs | hs <;> omega)
  table_stack := h.table_stack
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, spec.transport (fun a h1 h2 => ?_)⟩
    refine hag a (fun hcon => ?_) (fun hcon => ?_)
    · rcases spec.stack_disjoint with hs | hs
      · omega
      · have := h.aret.inSL; omega
    · rcases spec.ret_disjoint with hs | hs <;> omega⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  aret := h.aret
  aret_table_disjoint := h.aret_table_disjoint

end Vsa.Sim
