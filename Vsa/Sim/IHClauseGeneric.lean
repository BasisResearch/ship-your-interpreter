import Vsa.Sim.ExitFootprint
import Vsa.Sim.EvalLeafD
import Vsa.Sim.EvalStrSim
import Vsa.Sim.rows.EvalVarRow
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.StrCmpCellFootprint
import Vsa.Sim.rows.EvalLtRowFootprint

/-!
# `IHClauseGeneric` — the generic per-case steps of the `Footprint` clause (IH tower, Level 2)

The `Footprint` clause (`scripts/ih_clauses.tsv`, module
`Vsa/Sim/rows/IHClause_Footprint.lean`) is the child contract
`EvalIHF noArenaFoot` (`ExitFootprint.lean`): the child writes only its stack
window `[SL.lo, sp)` and its result slot `[sret, sret + 24)`.  This file holds
the clause's per-case step lemmas in the namespace the generator's hook expects
(`Vsa.Sim.IHClauseGeneric.footprint.<case>`), each stated at the EXACT field
type the generator emits once the clause predicate is
`extra := footExtra noArenaFoot` with the motive
`mEvalE st d env e st' v _ := EvalIHWithM extra st d env e st' v` (the
`EvalIHWithM` form of `L1-interface.md`; `EvalIHF noArenaFoot` is that abbrev):

```
<case> : ∀ <constructor binders>,
    Vsa.Sim.TermSimAssembly.mEvalE <child_i> →        -- old child IHs (unused)
    Vsa.Sim.TermSimAssembly.mEvalE <parent> →         -- old parent (unused)
    EvalIHF noArenaFoot <child_i> →                   -- clause child IHs
    EvalIHF noArenaFoot <parent>
```

* Leaves `hInt`, `hBool`, `hNull`, `hStr` are CLOSED: the landed pinned leaf
  sims (`evalIntSimP`, `evalBoolSimP`, `evalNullSimP`, `evalStrSimP_exact`)
  retain `LeafMemPin`, which IS the `noArenaFoot` footprint
  (`leafExitF_of_pinned`); the callee geometry is projected off the amended
  `EvalEntry` (`nbs_pins`, the widened disjointness literals, and the AST
  region of `EvalGround` for the string payload — the same facts the closed
  fields `Rows.field_hBool`/`field_hNull`/`field_hStr` use, restated here so the
  module depends only on the leaf sims, not on the assembly rows).
* `hVar` reduces to the landed var residual plus ONE named premise,
  `VarPinnedSim` (the pinned sibling of `evalVarSim`).
* `hNeg`, `hNot`, `hOrTrue`, `hOrFalse`, `hAndFalse`, `hAndTrue` reduce to the
  arm's footprint row contract (`NegRowF`, `NotRowF`, `OrTrueRowF`, …): the
  `EvalIHF noArenaFoot` sibling of the landed closed field, to be produced by
  the arm's `F` row exactly as `binRow_ltF` / `binRow_strcmpF` were (Level 1B).
* `hBinary` is the dispatcher over per-cell footprint contracts
  (`BinaryFootprintCells`, mirroring `eval_binary_row`); `.lt` and the four
  string comparisons are supplied from the two Level-1 pilots
  (`intCellF_lt`, `binStrCmpCellF_of`).  The two string-concatenation cells
  ALLOCATE, so at `noArenaFoot` they are unsatisfiable: `hBinary_of_cells`
  takes them as explicit premises, and the guarded clause below excludes them.
* The allocating cases `hAssign`, `hCall`, `hFn` are FALSE at `noArenaFoot`
  (they write the arena); the guarded motive `noAllocExpr e = true → EvalIHF
  noArenaFoot …` (`footprintNA`) closes them vacuously and is the clause shape
  that admits a closed `of_residuals`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## Leaves: the pinned exit is the `noArenaFoot` exit -/

/-- A pinned leaf exit (`EvalExit ∧ LeafMemPin`) is the footprint exit at
`noArenaFoot`: `LeafMemPin.agree` is exactly the footprint's `agree`. -/
theorem leafExitF_of_pinned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hx : EvalExitPinned g N A SL φf φc st v sp r sret m0 c)
    (hW : LeafWidenP g N A SL φf φc st v sp r sret m0)
    (hwords : ValueWordsTotal m0 sret.toNat) :
    EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
      st v sp r sret m0 c :=
  ⟨evalExitD_of_pinnedExit hx hW hwords,
    ⟨fun k hk => hx.2.agree k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))⟩⟩

/-- The `.bool` callee entry from the recursor entry (geometry off `nbs_pins` and
the widened disjointness literals, as `Rows.boolLeafGeom_discharged`). -/
theorem evalBoolEntry_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr} {b : Bool}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d env (.bool b) sp r sret aEnv aExpr m0 c) :
    EvalBoolEntry g N A SL φf φc st d env b sp r sret aEnv aExpr m0 c :=
    { good := hc.good, tick := hc.tick, pc := hc.pc, a0 := hc.a0, a1 := hc.a1, a2 := hc.a2,
      ra := hc.ra, ra_align := hc.ra_align, spReg := hc.spReg, stackOK := hc.stackOK,
      stackBudget := hc.stackBudget, expr_bodies := hc.expr_bodies,
      store_bodies := hc.store_bodies, minstret := hc.minstret, mem := hc.mem,
      code := hc.code, expr := hc.expr, store := hc.store,
      store_survives := hc.store_survives, out := hc.out, frame := hc.frame,
      code_stack_disjoint := hc.code_stack_disjoint,
      expr_stack_disjoint := hc.expr_stack_disjoint, expr_ram := hc.expr_ram,
      expr_win := hc.expr_win, sret_align := hc.sret_align,
      sret_ram := hc.sret_ram, sret_win := hc.sret_win,
      sret_vicode_disjoint := hc.sret_vicode_disjoint_int,
      sret_stack_disjoint := hc.sret_stack_disjoint,
      sret_evalcode_disjoint := hc.sret_evalcode_disjoint, stack_ram := hc.stack_ram,
      stack_win := hc.stack_win, spill_defined := hc.spill_defined,
      x13_defined := hc.x13_defined, envReg := hc.envReg,
      sret_vboolcode_disjoint := by
        rcases hc.sret_vicode_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega),
      vboolcode_stack_disjoint := by
        rcases hc.vicode_stack_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega),
      value_bool_code := hc.nbs_pins.bool_code, bool_slot := hc.nbs_pins.bool_slot,
      table_stack_disjoint := by
        rcases hc.table_stack_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega) }

/-- The `.null` callee entry from the recursor entry (as `Rows.nullLeafGeom_discharged`). -/
theorem evalNullEntry_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d env .null sp r sret aEnv aExpr m0 c) :
    EvalNullEntry g N A SL φf φc st d env sp r sret aEnv aExpr m0 c :=
    { good := hc.good, tick := hc.tick, pc := hc.pc, a0 := hc.a0, a1 := hc.a1, a2 := hc.a2,
      ra := hc.ra, ra_align := hc.ra_align, spReg := hc.spReg, stackOK := hc.stackOK,
      stackBudget := hc.stackBudget, expr_bodies := hc.expr_bodies,
      store_bodies := hc.store_bodies, minstret := hc.minstret, mem := hc.mem,
      code := hc.code, expr := hc.expr, store := hc.store,
      store_survives := hc.store_survives, out := hc.out, frame := hc.frame,
      code_stack_disjoint := hc.code_stack_disjoint,
      expr_stack_disjoint := hc.expr_stack_disjoint, expr_ram := hc.expr_ram,
      expr_win := hc.expr_win, sret_align := hc.sret_align,
      sret_ram := hc.sret_ram, sret_win := hc.sret_win,
      sret_vicode_disjoint := hc.sret_vicode_disjoint_int,
      sret_stack_disjoint := hc.sret_stack_disjoint,
      sret_evalcode_disjoint := hc.sret_evalcode_disjoint, stack_ram := hc.stack_ram,
      stack_win := hc.stack_win, spill_defined := hc.spill_defined,
      x13_defined := hc.x13_defined, envReg := hc.envReg,
      sret_vnullcode_disjoint := by
        rcases hc.sret_vicode_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega),
      vnullcode_stack_disjoint := by
        rcases hc.vicode_stack_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega),
      value_null_code := hc.nbs_pins.null_code, null_slot := hc.nbs_pins.null_slot,
      table_stack_disjoint := by
        rcases hc.table_stack_disjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega) }

/-- The `.str` payload geometry from the entry ground's AST region (the
`.str` case of `Rows.strPayloadGeom_of_astRegion`, off `EvalGround.ast`). -/
theorem strPayload_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr} {s : String}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c) :
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + s.length < SL.lo ∨ sp.toNat ≤ p) ∧
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat)) := by
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.str s) := hc.mem ▸ hc.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  obtain ⟨-, hsphi, -⟩ := hc.stackOK
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hp0 : read64 m0 (aExpr.toNat + 8) = some p := by rw [← hc.mem]; exact hp
    obtain ⟨-, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
    rcases spec.stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · have hp0 : read64 m0 (aExpr.toNat + 8) = some p := by rw [← hc.mem]; exact hp
    obtain ⟨hnz, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
    refine ⟨hnz, ?_⟩
    rcases spec.sret_disjoint with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- The `.str` callee entry from the recursor entry (as `Rows.field_hStr`). -/
theorem evalStrEntry_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr} {s : String}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c) :
    EvalStrEntry g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c := by
  obtain ⟨hssd, hsrd⟩ := strPayload_of_entry hc
  refine EvalStrEntry.of_entry hc hssd hsrd ?_ ?_ hc.nbs_pins.str_code hc.nbs_pins.str_slot ?_
  · rcases hc.sret_vicode_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.vicode_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.table_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-! ## Named premises (Level 1B rollout targets) -/

/-- **NAMED PREMISE — the pinned var leaf.**  `evalVarSim` (`EvalVarSim.lean`)
lands `EvalExit` only; its pinned sibling (`EvalExit ∧ LeafMemPin`, as
`evalIntSimP` for the int leaf) retains that `env_get`'s copy writes only the
callee frame below `sp` and the result slot.  Supplier: the pinned re-land of
`evalVarSim` over `env_get_hit_tail`'s write log (Level 1B). -/
def VarPinnedSim : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d env (.var x) st v →
    Triple (EvalVarEntry g N A SL φf φc st d env x v sp r sret aEnv aExpr m0)
      (EvalExitPinned g N A SL φf φc st v sp r sret m0)

/-- **NAMED PREMISE — the negation arm at `EvalIHF noArenaFoot`** (the `F` sibling
of `Rows.NegResid`, supplied by the footprint re-land of `evalNegSim`:
`blockB_unary` with footprint ≫ `blockC_neg_footprint` ≫ `blockD_v_rec_footprint`). -/
def NegRowF : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int),
    EvalE st d env e st' (.int n) →
    EvalIHF noArenaFoot st d env e st' (.int n) →
    EvalIHF noArenaFoot st d env (.unary .neg e) st' (.int (wrap64 (-n)))

/-- **NAMED PREMISE — the logical-not arm at `EvalIHF noArenaFoot`** (the `F`
sibling of `Rows.NotResid`; `value_truthy` reads only, the box is the result slot). -/
def NotRowF : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
    EvalE st d env e st' v →
    EvalIHF noArenaFoot st d env e st' v →
    EvalIHF noArenaFoot st d env (.unary .not e) st' (.bool (!v.truthy))

/-- **NAMED PREMISE — a short-circuit logical arm at `EvalIHF noArenaFoot`**
(`op = .or, b = true, res = true` is `orTrue`; `op = .and, b = false, res =
false` is `andFalse`; the `F` sibling of `Rows.OrTrueResid`/`AndFalseResid`). -/
def LogicalShortRowF (op : LogOp) (b res : Bool) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value),
    EvalE st d env l st' lv → lv.truthy = b →
    EvalIHF noArenaFoot st d env l st' lv →
    EvalIHF noArenaFoot st d env (.logical op l r) st' (.bool res)

/-- **NAMED PREMISE — a fall-through logical arm at `EvalIHF noArenaFoot`**
(`op = .or, b = false` is `orFalse`; `op = .and, b = true` is `andTrue`; the `F`
sibling of `Rows.OrFalseResid`/`AndTrueResid`). -/
def LogicalFallRowF (op : LogOp) (b : Bool) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
    EvalE st d env l st' lv → lv.truthy = b → EvalE st' d env r st'' rv →
    EvalIHF noArenaFoot st d env l st' lv →
    EvalIHF noArenaFoot st' d env r st'' rv →
    EvalIHF noArenaFoot st d env (.logical op l r) st'' (.bool rv.truthy)

/-- An integer binary cell at `EvalIHF noArenaFoot` (the whole-node form of
`BinIntCell`; `binRow_<op>F` supplies it from `BinIntCell op Resid guard`). -/
def IntCellF (op : BinOp) (res : Int → Int → Value) (guard : Int → Int → Prop) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st' st'' : SpecSt) (a b : Int),
    EvalE st d env el st' (.int a) → EvalE st' d env er st'' (.int b) →
    EvalIHF noArenaFoot st d env el st' (.int a) →
    EvalIHF noArenaFoot st' d env er st'' (.int b) →
    guard a b →
    EvalIHF noArenaFoot st d env (.binary op el er) st'' (res a b)

/-- The division-overflow cell at `EvalIHF noArenaFoot` (the whole-node form of
`BinDivOverflowCell`, `rows/BinDispatchRow.lean`).  `IntCellF .div` is guarded only
by `b ≠ 0` — exactly the guard `binOpSem` imposes — so, as in `eval_binary_row`,
the `INT64_MIN / -1` subcase is a separate cell; `intCellF_div`
(`IHClauseGenericSupply.lean`) splits on it. -/
def DivOverflowCellF : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st' st'' : SpecSt) (a b : Int),
    EvalE st d env el st' (.int a) → EvalE st' d env er st'' (.int b) →
    EvalIHF noArenaFoot st d env el st' (.int a) →
    EvalIHF noArenaFoot st' d env er st'' (.int b) →
    a = -2^63 → b = -1 →
    EvalIHF noArenaFoot st d env (.binary .div el er) st''
      (.int (wrap64 ((-2^63 : Int).tdiv (-1))))

/-- An equality cell at `EvalIHF noArenaFoot` (the whole-node form of `BinEqCell`). -/
def EqCellF (op : BinOp) (res : Value → Value → Value) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st' st'' : SpecSt) (lv rv : Value),
    EvalE st d env el st' lv → EvalE st' d env er st'' rv →
    EvalIHF noArenaFoot st d env el st' lv →
    EvalIHF noArenaFoot st' d env er st'' rv →
    EvalIHF noArenaFoot st d env (.binary op el er) st'' (res lv rv)

/-- The left-string concatenation cell at `EvalIHF noArenaFoot`.  UNSATISFIABLE:
the cell allocates the result payload in the arena; it is admitted only by a
clause whose family includes fresh arena bytes (task 2, `PROOF_CLOSURE_PLAN.md`). -/
def StrAddLCellF : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st' st'' : SpecSt)
    (sl : String) (rv : Value),
    EvalE st d env el st' (.str sl) → EvalE st' d env er st'' rv →
    EvalIHF noArenaFoot st d env el st' (.str sl) →
    EvalIHF noArenaFoot st' d env er st'' rv →
    EvalIHF noArenaFoot st d env (.binary .add el er) st''
      (.str ((Value.str sl).catDisplay st''.store ++ rv.catDisplay st''.store))

/-- The right-string concatenation cell at `EvalIHF noArenaFoot` (UNSATISFIABLE,
as `StrAddLCellF`). -/
def StrAddRCellF : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr) (st' st'' : SpecSt)
    (lv : Value) (sr : String),
    NonStringValue lv →
    EvalE st d env el st' lv → EvalE st' d env er st'' (.str sr) →
    EvalIHF noArenaFoot st d env el st' lv →
    EvalIHF noArenaFoot st' d env er st'' (.str sr) →
    EvalIHF noArenaFoot st d env (.binary .add el er) st''
      (.str (lv.catDisplay st''.store ++ (Value.str sr).catDisplay st''.store))

/-- **The non-allocating binary cells at `EvalIHF noArenaFoot`** — one field per
cell of `eval_binary_row` except the two string-concatenation cells. -/
structure BinaryFootprintCells : Prop where
  add : IntCellF .add (fun a b => .int (wrap64 (a + b))) (fun _ _ => True)
  sub : IntCellF .sub (fun a b => .int (wrap64 (a - b))) (fun _ _ => True)
  mul : IntCellF .mul (fun a b => .int (wrap64 (a * b))) (fun _ _ => True)
  div : IntCellF .div (fun a b => .int (wrap64 (a.tdiv b))) (fun _ b => b ≠ 0)
  mod : IntCellF .mod (fun a b => .int (wrap64 (a.tmod b))) (fun _ b => b ≠ 0)
  lt : IntCellF .lt (fun a b => .bool (a < b)) (fun _ _ => True)
  le : IntCellF .le (fun a b => .bool (a ≤ b)) (fun _ _ => True)
  gt : IntCellF .gt (fun a b => .bool (a > b)) (fun _ _ => True)
  ge : IntCellF .ge (fun a b => .bool (a ≥ b)) (fun _ _ => True)
  eq : EqCellF .eq (fun l r => .bool (l.equal r))
  ne : EqCellF .ne (fun l r => .bool (!(l.equal r)))
  strLt : BinStrCmpCellF .lt (fun sl sr => sl < sr)
  strLe : BinStrCmpCellF .le (fun sl sr => sl < sr || sl == sr)
  strGt : BinStrCmpCellF .gt (fun sl sr => sr < sl)
  strGe : BinStrCmpCellF .ge (fun sl sr => sr < sl || sl == sr)

/-- **`.lt` from pilot B**: `binRow_ltF` at the landed residual supplier. -/
theorem intCellF_lt (hILt : BinIntCell .lt Vsa.Sim.LtResid (fun _ _ => True)) :
    IntCellF .lt (fun a b => .bool (a < b)) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  have hP := hILt g N A SL φf φc st st' st'' d env el er a b hEl hEr ihL.forget ihR.forget
    trivial sp r sret aEnv aExpr m0 c hc
  exact binRow_ltF (binaryHeadFootprintSupply _ _) g N A SL φf φc st st' st'' d env el er a b
    sp r sret aEnv aExpr m0 hEl ihL ihR
    (EvalE.binary st d env .lt el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))
    hP c hc

/-! ## The guarded (non-allocating) expression predicate -/

namespace IHClauseGeneric

/-- Syntactically non-allocating expressions: no assignment, call, function
literal, or `+` (string concatenation allocates; the operand kinds are dynamic). -/
def noAllocExpr : Expr → Bool
  | .int _ => true
  | .str _ => true
  | .bool _ => true
  | .null => true
  | .var _ => true
  | .assign _ _ => false
  | .binary .add _ _ => false
  | .binary _ l r => noAllocExpr l && noAllocExpr r
  | .logical _ l r => noAllocExpr l && noAllocExpr r
  | .unary _ e => noAllocExpr e
  | .call _ _ => false
  | .fn _ _ _ => false

theorem noAllocExpr_binary {op : BinOp} {l r : Expr}
    (h : noAllocExpr (.binary op l r) = true) :
    op ≠ .add ∧ noAllocExpr l = true ∧ noAllocExpr r = true := by
  cases op <;> simp [noAllocExpr] at h ⊢ <;> exact h

theorem noAllocExpr_logical {op : LogOp} {l r : Expr}
    (h : noAllocExpr (.logical op l r) = true) :
    noAllocExpr l = true ∧ noAllocExpr r = true := by
  simpa [noAllocExpr] using h

theorem noAllocExpr_unary {op : UnOp} {e : Expr}
    (h : noAllocExpr (.unary op e) = true) : noAllocExpr e = true := by
  simpa [noAllocExpr] using h

/-! ## The generic steps at the generator's field types -/

namespace footprint

/-- `hInt`: CLOSED. -/
theorem hInt :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n) →
      EvalIHF noArenaFoot st d env (Expr.int n) st (Value.int n) := by
  intro st d env n _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨c', hs, hx⟩ := evalIntSimP g N A SL φf φc st d env n sp r sret aEnv aExpr m0 c hc
  exact ⟨c', hs, leafExitF_of_pinned hx (leafWidenP_of_entry hc) (hc.mem ▸ hc.sret_words)⟩

/-- `hStr`: CLOSED (payload geometry from `EvalGround.ast`). -/
theorem hStr :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s) →
      EvalIHF noArenaFoot st d env (Expr.str s) st (Value.str s) := by
  intro st d env s _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨c', hs, hExit, hPin⟩ :=
    evalStrSimP_exact g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c
      (evalStrEntry_of_entry hc)
  exact ⟨c', hs, leafExitF_of_pinned ⟨hExit, hPin.memory⟩ (leafWidenP_of_entry hc)
    (hc.mem ▸ hc.sret_words)⟩

/-- `hBool`: CLOSED. -/
theorem hBool :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.bool b) st (Value.bool b) (EvalE.bool st d env b) →
      EvalIHF noArenaFoot st d env (Expr.bool b) st (Value.bool b) := by
  intro st d env b _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨c', hs, hx⟩ :=
    evalBoolSimP g N A SL φf φc st d env b sp r sret aEnv aExpr m0 c (evalBoolEntry_of_entry hc)
  exact ⟨c', hs, leafExitF_of_pinned hx (leafWidenP_of_entry hc) (hc.mem ▸ hc.sret_words)⟩

/-- `hNull`: CLOSED. -/
theorem hNull :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      Vsa.Sim.TermSimAssembly.mEvalE st d env Expr.null st Value.null (EvalE.null st d env) →
      EvalIHF noArenaFoot st d env Expr.null st Value.null := by
  intro st d env _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨c', hs, hx⟩ :=
    evalNullSimP g N A SL φf φc st d env sp r sret aEnv aExpr m0 c (evalNullEntry_of_entry hc)
  exact ⟨c', hs, leafExitF_of_pinned hx (leafWidenP_of_entry hc) (hc.mem ▸ hc.sret_words)⟩

/-- `hVar`: from the landed var residual (the `env_get_found` linkage) and the
pinned var sim. -/
theorem hVar_of (hR : ∀ st x v, Rows.VarLeafResid st x v) (hPin : VarPinnedSim) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
      (a : st.store.get? env x = some v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a) →
      EvalIHF noArenaFoot st d env (Expr.var x) st v := by
  intro st d env x v hlookup _
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨hvsd, hsad, hegc, hegsd, hvs, htsd, hfound, _⟩ :=
    hR st x v g N A SL φf φc d env sp r sret aEnv aExpr m0 c hlookup hc
  have hEntry : EvalVarEntry g N A SL φf φc st d env x v sp r sret aEnv aExpr m0 c :=
    { good := hc.good, tick := hc.tick, pc := hc.pc, a0 := hc.a0, a1 := hc.a1, a2 := hc.a2,
      ra := hc.ra, ra_align := hc.ra_align, spReg := hc.spReg, stackOK := hc.stackOK,
      stackBudget := hc.stackBudget, expr_bodies := hc.expr_bodies,
      store_bodies := hc.store_bodies, minstret := hc.minstret, mem := hc.mem,
      code := hc.code, expr := hc.expr, store := hc.store,
      store_survives := hc.store_survives, out := hc.out, frame := hc.frame,
      code_stack_disjoint := hc.code_stack_disjoint,
      expr_stack_disjoint := hc.expr_stack_disjoint,
      expr_ram := hc.expr_ram, expr_win := hc.expr_win,
      sret_align := hc.sret_align, sret_ram := hc.sret_ram, sret_win := hc.sret_win,
      sret_vicode_disjoint := hc.sret_vicode_disjoint_int,
      sret_stack_disjoint := hc.sret_stack_disjoint,
      sret_evalcode_disjoint := hc.sret_evalcode_disjoint, stack_ram := hc.stack_ram,
      stack_win := hc.stack_win, spill_defined := hc.spill_defined,
      x13_defined := hc.x13_defined, envReg := hc.envReg,
      var_stack_disjoint := hvsd, sret_arena_disjoint := hsad, env_get_code := hegc,
      env_get_stack_disjoint := hegsd, var_slot := hvs, table_stack_disjoint := htsd,
      env_get_found := hfound }
  obtain ⟨c', hs, hx⟩ := hPin g N A SL φf φc st d env x v sp r sret aEnv aExpr m0
    (EvalE.var st d env x v hlookup) c hEntry
  exact ⟨c', hs, leafExitF_of_pinned hx (leafWidenP_of_entry hc) (hc.mem ▸ hc.sret_words)⟩

/-- `hNeg`: from the arm's footprint row. -/
theorem hNeg_of (h : NegRowF) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)
      (a : EvalE st d env e st' (Value.int n)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' (Value.int n) a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.neg e) st'
        (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a) →
      EvalIHF noArenaFoot st d env e st' (Value.int n) →
      EvalIHF noArenaFoot st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) :=
  fun st d env e st' n a _ _ ih => h st d env e st' n a ih

/-- `hNot`: from the arm's footprint row. -/
theorem hNot_of (h : NotRowF) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.not e) st'
        (Value.bool !v.truthy) (EvalE.not st d env e st' v a) →
      EvalIHF noArenaFoot st d env e st' v →
      EvalIHF noArenaFoot st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) :=
  fun st d env e st' v a _ _ ih => h st d env e st' v a ih

/-- `hOrTrue`: from the short-circuit row. -/
theorem hOrTrue_of (h : LogicalShortRowF .or true true) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st'
        (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st' (Value.bool true) :=
  fun st d env l r st' lv a a_1 _ _ ih => h st d env l r st' lv a a_1 ih

/-- `hAndFalse`: from the short-circuit row. -/
theorem hAndFalse_of (h : LogicalShortRowF .and false false) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st'
        (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st' (Value.bool false) :=
  fun st d env l r st' lv a a_1 _ _ ih => h st d env l r st' lv a a_1 ih

/-- `hOrFalse`: from the fall-through row. -/
theorem hOrFalse_of (h : LogicalFallRowF .or false) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st''
        (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 _ _ _ ihL ihR =>
    h st d env l r st' st'' lv rv a a_1 a_2 ihL ihR

/-- `hAndTrue`: from the fall-through row. -/
theorem hAndTrue_of (h : LogicalFallRowF .and true) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st''
        (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 _ _ _ ihL ihR =>
    h st d env l r st' st'' lv rv a a_1 a_2 ihL ihR

/-- **`hBinary` dispatcher** over the non-allocating cells; the two allocating
string-concatenation cells are demanded only when `op = .add` (the guarded
clause supplies `op ≠ .add`; the full clause must supply both, which is
impossible at `noArenaFoot`). -/
theorem hBinary_of_cells (C : BinaryFootprintCells) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      (op = .add → StrAddLCellF ∧ StrAddRCellF) →
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_1 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.binary op l r) st'' v := by
  intro st d env op el er st' st'' lv rv v hEl hEr hsem hadd _ _ _ ihL ihR
  cases op with
  | add =>
    match lv, rv, hsem with
    | .str sl, rv, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).1 st d env el er st' st'' sl rv hEl hEr ihL ihR
    | .int a, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).2 st d env el er st' st'' (.int a) sr trivial hEl hEr ihL ihR
    | .bool bb, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).2 st d env el er st' st'' (.bool bb) sr trivial hEl hEr ihL ihR
    | .null, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).2 st d env el er st' st'' .null sr trivial hEl hEr ihL ihR
    | .closure aa, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).2 st d env el er st' st'' (.closure aa) sr trivial hEl hEr ihL ihR
    | .native ff, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact (hadd rfl).2 st d env el er st' st'' (.native ff) sr trivial hEl hEr ihL ihR
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.add st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | sub =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.sub st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | mul =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.mul st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | div =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem
      by_cases hb0 : b = 0
      · subst hb0; simp at hsem
      · rw [if_neg (by simpa using hb0)] at hsem; cases hsem
        exact C.div st d env el er st' st'' a b hEl hEr ihL ihR hb0
  | mod =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem
      by_cases hb0 : b = 0
      · subst hb0; simp at hsem
      · rw [if_neg (by simpa using hb0)] at hsem; cases hsem
        exact C.mod st d env el er st' st'' a b hEl hEr ihL ihR hb0
  | lt =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.strLt st d env el er st' st'' sl sr hEl hEr ihL ihR
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.lt st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | le =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.strLe st d env el er st' st'' sl sr hEl hEr ihL ihR
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.le st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | gt =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.strGt st d env el er st' st'' sl sr hEl hEr ihL ihR
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.gt st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | ge =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.strGe st d env el er st' st'' sl sr hEl hEr ihL ihR
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact C.ge st d env el er st' st'' a b hEl hEr ihL ihR trivial
  | eq =>
    simp only [binOpSem] at hsem; cases hsem
    exact C.eq st d env el er st' st'' lv rv hEl hEr ihL ihR
  | ne =>
    simp only [binOpSem] at hsem; cases hsem
    exact C.ne st d env el er st' st'' lv rv hEl hEr ihL ihR

end footprint

/-! ## The guarded clause: `noAllocExpr e = true → EvalIHF noArenaFoot …`

The motive shape that admits a closed `of_residuals`: the allocating cases are
vacuous and the concatenation cells are excluded by the guard.  Field types
are the generator's with every clause motive replaced by
`noAllocExpr <e> = true → EvalIHF noArenaFoot <…>`. -/

namespace footprintNA

theorem hAssign :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value)
      (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out }
        v (EvalE.assign st d env x e st' v store'' a a_1) →
      (noAllocExpr e = true → EvalIHF noArenaFoot st d env e st' v) →
      (noAllocExpr (Expr.assign x e) = true →
        EvalIHF noArenaFoot st d env (Expr.assign x e) { store := store'', out := st'.out } v) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

theorem hFn :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String)
      (body : List Stmt) (store' : Store) (a : Addr)
      (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } =
        (store', a)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.fn name params body)
        { store := store', out := st.out } (Value.closure a)
        (EvalE.fn st d env name params body store' a a_1) →
      (noAllocExpr (Expr.fn name params body) = true →
        EvalIHF noArenaFoot st d env (Expr.fn name params body)
          { store := store', out := st.out } (Value.closure a)) :=
  fun _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

theorem hCall :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt)
      (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv)
      (a_1 : args.length ≤ maxArgs) (a_2 : EvalArgs st' d env args st'' vs)
      (a_3 : Call st'' d fv vs st''' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env f st' fv a →
      Vsa.Sim.TermSimAssembly.mEvalArgs st' d env args st'' vs a_2 →
      Vsa.Sim.TermSimAssembly.mCall st'' d fv vs st''' v a_3 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (f.call args) st''' v
        (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3) →
      (noAllocExpr f = true → EvalIHF noArenaFoot st d env f st' fv) →
      True → True →
      (noAllocExpr (f.call args) = true → EvalIHF noArenaFoot st d env (f.call args) st''' v) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

theorem hBinary (C : BinaryFootprintCells) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_1 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) →
      (noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (noAllocExpr r = true → EvalIHF noArenaFoot st' d env r st'' rv) →
      (noAllocExpr (Expr.binary op l r) = true →
        EvalIHF noArenaFoot st d env (Expr.binary op l r) st'' v) := by
  intro st d env op l r st' st'' lv rv v a a_1 a_2 o1 o2 o3 ihL ihR hna
  obtain ⟨hne, hl, hr⟩ := noAllocExpr_binary hna
  exact footprint.hBinary_of_cells C st d env op l r st' st'' lv rv v a a_1 a_2
    (fun h => absurd h hne) o1 o2 o3 (ihL hl) (ihR hr)

theorem hNeg (h : NegRowF) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)
      (a : EvalE st d env e st' (Value.int n)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' (Value.int n) a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.neg e) st'
        (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a) →
      (noAllocExpr e = true → EvalIHF noArenaFoot st d env e st' (Value.int n)) →
      (noAllocExpr (Expr.unary UnOp.neg e) = true →
        EvalIHF noArenaFoot st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n)))) :=
  fun st d env e st' n a o1 o2 ih hna =>
    footprint.hNeg_of h st d env e st' n a o1 o2 (ih (noAllocExpr_unary hna))

theorem hNot (h : NotRowF) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.not e) st'
        (Value.bool !v.truthy) (EvalE.not st d env e st' v a) →
      (noAllocExpr e = true → EvalIHF noArenaFoot st d env e st' v) →
      (noAllocExpr (Expr.unary UnOp.not e) = true →
        EvalIHF noArenaFoot st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy)) :=
  fun st d env e st' v a o1 o2 ih hna =>
    footprint.hNot_of h st d env e st' v a o1 o2 (ih (noAllocExpr_unary hna))

theorem hOrTrue (h : LogicalShortRowF .or true true) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st'
        (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1) →
      (noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (noAllocExpr (Expr.logical LogOp.or l r) = true →
        EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st' (Value.bool true)) :=
  fun st d env l r st' lv a a_1 o1 o2 ih hna =>
    footprint.hOrTrue_of h st d env l r st' lv a a_1 o1 o2 (ih (noAllocExpr_logical hna).1)

theorem hAndFalse (h : LogicalShortRowF .and false false) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st'
        (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1) →
      (noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (noAllocExpr (Expr.logical LogOp.and l r) = true →
        EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st' (Value.bool false)) :=
  fun st d env l r st' lv a a_1 o1 o2 ih hna =>
    footprint.hAndFalse_of h st d env l r st' lv a a_1 o1 o2 (ih (noAllocExpr_logical hna).1)

theorem hOrFalse (h : LogicalFallRowF .or false) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st''
        (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2) →
      (noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (noAllocExpr r = true → EvalIHF noArenaFoot st' d env r st'' rv) →
      (noAllocExpr (Expr.logical LogOp.or l r) = true →
        EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy)) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 o3 ihL ihR hna =>
    footprint.hOrFalse_of h st d env l r st' st'' lv rv a a_1 a_2 o1 o2 o3
      (ihL (noAllocExpr_logical hna).1) (ihR (noAllocExpr_logical hna).2)

theorem hAndTrue (h : LogicalFallRowF .and true) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st''
        (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2) →
      (noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (noAllocExpr r = true → EvalIHF noArenaFoot st' d env r st'' rv) →
      (noAllocExpr (Expr.logical LogOp.and l r) = true →
        EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy)) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 o3 ihL ihR hna =>
    footprint.hAndTrue_of h st d env l r st' st'' lv rv a a_1 a_2 o1 o2 o3
      (ihL (noAllocExpr_logical hna).1) (ihR (noAllocExpr_logical hna).2)

end footprintNA

end IHClauseGeneric

#print axioms leafExitF_of_pinned
#print axioms evalStrEntry_of_entry
#print axioms IHClauseGeneric.footprint.hInt
#print axioms IHClauseGeneric.footprint.hStr
#print axioms IHClauseGeneric.footprint.hBool
#print axioms IHClauseGeneric.footprint.hNull
#print axioms IHClauseGeneric.footprint.hVar_of
#print axioms IHClauseGeneric.footprint.hBinary_of_cells
#print axioms intCellF_lt
#print axioms IHClauseGeneric.footprintNA.hBinary
#print axioms IHClauseGeneric.footprintNA.hCall

end Vsa.Sim
