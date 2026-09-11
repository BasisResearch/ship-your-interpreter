import Vsa.Sim.rows.IHClause_FootprintPayloadOwned
import Vsa.Sim.rows.IHClause_FootprintPayloadOwnedSlack

/-!
# `StrCmpCellsOwnedClosed` — the four string-comparison cells from the product clause

`ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned` (`StrCmpCellClauses.lean`) take two
clause recursions and two index premises.  This module supplies them from the
generated product clause (`scripts/ih_clauses.tsv`, `Vsa/Sim/IHClauseGenericProduct.lean`):

* the LEFT-operand premise is the clause's `of_residuals`; the RIGHT-operand one is
  the same recursion with the coverage conjunct dropped (`EvalIHFPO.forgetCov`);
* the clause is GUARDED by `IHClauseGeneric.noAllocExpr`, because `hAssign`, `hFn`,
  `hCall` and `.add`-with-a-string write the arena and are false at `noArenaFoot`.
  The cells therefore close at `BinStrCmpCellNA` — the `BinDispatchRow` field
  restricted to operands that do not allocate.  Lifting that restriction needs the
  allocating footprint family over the allocator ledger (task 2:
  `MallocReturnAt.allocFoot`, `HeapOwned.pushClosure`);
* two versions, at the two indices.  At `stdShared` (`_closed`) the surviving
  premise `SharedTopSlackAll stdShared` is FALSE (`not_sharedTopSlackAll_std`), so
  those four are vacuous as stated; at the repaired index `stdSharedSlack`
  (`_closedSlack`) the slack is a theorem and the one surviving entry-layer Layout
  fact is `ArenaSlack`.  `AstRegionSlack` is discharged by `astRegionSlack_holds`,
  since `AstRegionSpec.hi_ram` was amended to `hi + 8 ≤ 0x100000000`; by
  `astRegionSlack_forced` that amendment was forced, because under the old bound
  NO index satisfies both `OwnedIndex` and the slack.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.TermCaseBundle (TermCases)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## 1. At the canonical index `stdShared` -/

/-- The clause residuals at `stdShared`: the variable leaf and the binary arm. -/
theorem productResiduals_std (L : Layout) (hVar : VarProductStep stdShared)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (htop : SharedTopSlackAll stdShared) :
    IHClause.FootprintPayloadOwned.Residuals L :=
  IHClause.FootprintPayloadOwned.Residuals.ofUnwired L
    (fun st d env x v a _hOld _hg => hVar st d env x v a)
    (IHClauseGenericProduct.hBinary stdShared ownedIndex_std htop hDivOv hEq hNe)

/-- The guarded product clause over every derivation, at `stdShared`. -/
theorem productClause_std (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwned.Residuals L) :
    FootprintPayloadOwnedClauseNA stdShared :=
  fun st d env e st' v hg t =>
    IHClause.FootprintPayloadOwned.of_residuals B R t hg

theorem ScaffoldRows.field_hStrLt_closed (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwned.Residuals L)
    (htop : SharedTopSlackAll stdShared) :
    BinStrCmpCellNA .lt (fun sl sr => sl < sr) :=
  binStrCmpCell_of_ownedNA strCmpLt strCmpLt_cert stdShared ownedIndex_std htop
    (productClause_std B L R) (footprintOwnedClauseNA_of_payload (productClause_std B L R))

theorem ScaffoldRows.field_hStrLe_closed (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwned.Residuals L)
    (htop : SharedTopSlackAll stdShared) :
    BinStrCmpCellNA .le (fun sl sr => sl < sr || sl == sr) :=
  binStrCmpCell_of_ownedNA strCmpLe strCmpLe_cert stdShared ownedIndex_std htop
    (productClause_std B L R) (footprintOwnedClauseNA_of_payload (productClause_std B L R))

theorem ScaffoldRows.field_hStrGt_closed (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwned.Residuals L)
    (htop : SharedTopSlackAll stdShared) :
    BinStrCmpCellNA .gt (fun sl sr => sr < sl) :=
  binStrCmpCell_of_ownedNA strCmpGt strCmpGt_cert stdShared ownedIndex_std htop
    (productClause_std B L R) (footprintOwnedClauseNA_of_payload (productClause_std B L R))

theorem ScaffoldRows.field_hStrGe_closed (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwned.Residuals L)
    (htop : SharedTopSlackAll stdShared) :
    BinStrCmpCellNA .ge (fun sl sr => sr < sl || sl == sr) :=
  binStrCmpCell_of_ownedNA strCmpGe strCmpGe_cert stdShared ownedIndex_std htop
    (productClause_std B L R) (footprintOwnedClauseNA_of_payload (productClause_std B L R))

/-! ## 2. At the repaired index `stdSharedSlack` -/

/-- The clause residuals at `stdSharedSlack`: the variable leaf, the string leaf
(its ownership needs the index, hence `ArenaSlack`) and the binary arm.
The RAM-top slack is a theorem here, so no false premise survives. -/
theorem productResiduals_slack (L : Layout)
    (hArena : ArenaSlack)
    (hVar : VarProductStep stdSharedSlack)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)) :
    IHClause.FootprintPayloadOwnedSlack.Residuals L :=
  IHClause.FootprintPayloadOwnedSlack.Residuals.ofUnwired L
    (fun st d env s hOld _hg =>
      IHClauseGenericProduct.hStr stdSharedSlack (ownedIndex_stdSlack astRegionSlack_holds hArena) st d env s hOld)
    (fun st d env x v a _hOld _hg => hVar st d env x v a)
    (IHClauseGenericProduct.hBinary stdSharedSlack (ownedIndex_stdSlack astRegionSlack_holds hArena)
      sharedTopSlackAll_stdSlack hDivOv hEq hNe)

/-- The guarded product clause over every derivation, at `stdSharedSlack`. -/
theorem productClause_slack (B : TermCases) (L : Layout)
    (R : IHClause.FootprintPayloadOwnedSlack.Residuals L) :
    FootprintPayloadOwnedClauseNA stdSharedSlack :=
  fun st d env e st' v hg t =>
    IHClause.FootprintPayloadOwnedSlack.of_residuals B R t hg

theorem ScaffoldRows.field_hStrLt_closedSlack (B : TermCases) (L : Layout)
    (hArena : ArenaSlack)
    (R : IHClause.FootprintPayloadOwnedSlack.Residuals L) :
    BinStrCmpCellNA .lt (fun sl sr => sl < sr) :=
  binStrCmpCell_of_ownedNA strCmpLt strCmpLt_cert stdSharedSlack
    (ownedIndex_stdSlack astRegionSlack_holds hArena) sharedTopSlackAll_stdSlack
    (productClause_slack B L R) (footprintOwnedClauseNA_of_payload (productClause_slack B L R))

theorem ScaffoldRows.field_hStrLe_closedSlack (B : TermCases) (L : Layout)
    (hArena : ArenaSlack)
    (R : IHClause.FootprintPayloadOwnedSlack.Residuals L) :
    BinStrCmpCellNA .le (fun sl sr => sl < sr || sl == sr) :=
  binStrCmpCell_of_ownedNA strCmpLe strCmpLe_cert stdSharedSlack
    (ownedIndex_stdSlack astRegionSlack_holds hArena) sharedTopSlackAll_stdSlack
    (productClause_slack B L R) (footprintOwnedClauseNA_of_payload (productClause_slack B L R))

theorem ScaffoldRows.field_hStrGt_closedSlack (B : TermCases) (L : Layout)
    (hArena : ArenaSlack)
    (R : IHClause.FootprintPayloadOwnedSlack.Residuals L) :
    BinStrCmpCellNA .gt (fun sl sr => sr < sl) :=
  binStrCmpCell_of_ownedNA strCmpGt strCmpGt_cert stdSharedSlack
    (ownedIndex_stdSlack astRegionSlack_holds hArena) sharedTopSlackAll_stdSlack
    (productClause_slack B L R) (footprintOwnedClauseNA_of_payload (productClause_slack B L R))

theorem ScaffoldRows.field_hStrGe_closedSlack (B : TermCases) (L : Layout)
    (hArena : ArenaSlack)
    (R : IHClause.FootprintPayloadOwnedSlack.Residuals L) :
    BinStrCmpCellNA .ge (fun sl sr => sr < sl || sl == sr) :=
  binStrCmpCell_of_ownedNA strCmpGe strCmpGe_cert stdSharedSlack
    (ownedIndex_stdSlack astRegionSlack_holds hArena) sharedTopSlackAll_stdSlack
    (productClause_slack B L R) (footprintOwnedClauseNA_of_payload (productClause_slack B L R))

/-! ## 3. The four cells as one bundle, from the named premises -/

/-- The four string-comparison cells of `BinDispatchRow`, restricted to
non-allocating operands. -/
structure StrCmpCellsNA : Prop where
  lt : BinStrCmpCellNA .lt (fun sl sr => sl < sr)
  le : BinStrCmpCellNA .le (fun sl sr => sl < sr || sl == sr)
  gt : BinStrCmpCellNA .gt (fun sl sr => sr < sl)
  ge : BinStrCmpCellNA .ge (fun sl sr => sr < sl || sl == sr)

/-- **The four cells at the repaired index, from named premises only.**  Every
hypothesis is either the case bundle, the census `Layout`, or a named premise
with its supplier in its doc comment; none is false.  `AstRegionSlack` is no
longer among them: it is the theorem `astRegionSlack_holds`. -/
theorem strCmpCellsNA_slack (B : TermCases) (L : Layout)
    (hArena : ArenaSlack)
    (hVar : VarProductStep stdSharedSlack)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)) :
    StrCmpCellsNA :=
  let R := productResiduals_slack L hArena hVar hDivOv hEq hNe
  { lt := ScaffoldRows.field_hStrLt_closedSlack B L hArena R
    le := ScaffoldRows.field_hStrLe_closedSlack B L hArena R
    gt := ScaffoldRows.field_hStrGt_closedSlack B L hArena R
    ge := ScaffoldRows.field_hStrGe_closedSlack B L hArena R }

/-- The same at `stdShared`, where `SharedTopSlackAll stdShared` is FALSE
(`not_sharedTopSlackAll_std`): kept because it is the index the landed
`ownedIndex_std` discharges, and vacuous until that premise is replaced by the
repaired index above. -/
theorem strCmpCellsNA_std (B : TermCases) (L : Layout)
    (hVar : VarProductStep stdShared)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (htop : SharedTopSlackAll stdShared) :
    StrCmpCellsNA :=
  let R := productResiduals_std L hVar hDivOv hEq hNe htop
  { lt := ScaffoldRows.field_hStrLt_closed B L R htop
    le := ScaffoldRows.field_hStrLe_closed B L R htop
    gt := ScaffoldRows.field_hStrGt_closed B L R htop
    ge := ScaffoldRows.field_hStrGe_closed B L R htop }

#print axioms strCmpCellsNA_slack
#print axioms strCmpCellsNA_std
#print axioms productResiduals_std
#print axioms productClause_std
#print axioms ScaffoldRows.field_hStrLt_closed
#print axioms ScaffoldRows.field_hStrLe_closed
#print axioms ScaffoldRows.field_hStrGt_closed
#print axioms ScaffoldRows.field_hStrGe_closed
#print axioms productResiduals_slack
#print axioms productClause_slack
#print axioms ScaffoldRows.field_hStrLt_closedSlack
#print axioms ScaffoldRows.field_hStrLe_closedSlack
#print axioms ScaffoldRows.field_hStrGt_closedSlack
#print axioms ScaffoldRows.field_hStrGe_closedSlack

end Vsa.Sim
