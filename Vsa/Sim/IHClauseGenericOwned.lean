import Vsa.Sim.OwnedPayloadClause
import Vsa.Sim.TermCaseBundle
import Vsa.Sim.EvalLeafD
import Vsa.Sim.EvalStrSim

/-!
# `IHClauseGenericOwned` — the per-case steps of the `OwnedPayload` clause (IH tower, Level 2)

One step per recursor case, at the EXACT field type
`scripts/gen_ih_clause.py` emits for the clause `OwnedPayload`
(`ownedExtra stdShared`, `Vsa/Sim/OwnedPayloadClause.lean`).

* **eleven CLOSED steps** — `hInt`, `hStr`, `hBool`, `hNull`, `hNeg`, `hNot`,
  the four logical cases and `hFn`.  Ten of them are one call of
  `evalIHO_of_return`: their result is `.int`/`.bool`/`.null`/`.closure`, which
  satisfies `OwnedSlot` definitionally, so the clause parent follows from the
  OLD motive with no re-derivation of any row.  `hStr` is the only leaf with a
  real payload: the literal returns its AST pointer (`evalStrSimP_exact`'s
  `StrReturnPin`), and the index's `ast` field says the pinned AST region is
  shared.
* **`hBinary`** — closed for every operator except `.add` by
  `binOpSem_payloadFree` (integer and comparison results are `.int`/`.bool`);
  `.add` over a string operand allocates a fresh payload and is the named
  premise `OwnedConcatStep`.
* **four NAMED premises** — `OwnedVarStep`, `OwnedAssignStep`,
  `OwnedConcatStep`, `OwnedCallStep`, each with the supplier named in its doc
  comment (`PROOF_CLOSURE_PLAN.md` task 2).

The consumer adapter for the string-comparison cells is
`ownedOperands_of_clause`: the two `RuntimeOwnership.ValueOwned` facts and the
three `SharedGeom` fields the cells' residual needs, from the clause holding at
the two operand children.  See the module's last section for the obstruction
that keeps `StrCmpOwnedOperands` itself (`StrCmpCellClauses.lean`) out of reach.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (SharedCString ValueOwned)

namespace Vsa.Sim

namespace IHClauseGenericOwned

local notation "SpecSt" => Vsa.While.St

/-! ## 1. The semantic side condition: which results can carry a payload -/

/-- Every binary operator except `.add` returns an integer or a boolean, so its
result carries no payload.  (`.add` over a string operand returns a freshly
concatenated string — the `OwnedConcatStep` premise.) -/
theorem binOpSem_payloadFree {s : Store} {op : BinOp} {lv rv v : Value}
    (h : binOpSem s op lv rv = some v) (hop : op ≠ .add) : PayloadFree v := by
  cases op
  case add => exact absurd rfl hop
  all_goals
    (cases lv <;> cases rv <;>
      simp only [binOpSem, Option.some.injEq, reduceCtorEq] at h <;>
      (try split at h) <;> (try cases h) <;> (try subst h) <;> trivial)

/-! ## 2. The named premises (the four steps a payload can survive through) -/

/-- **NAMED PREMISE — the variable leaf.**  `env_get` copies a store value into
the result slot, so its payload is the store's, not the caller's.  Supplier
(task 2): `HeapOwned`/`StoreOwned` (`RuntimeOwnership.lean`) — every value in a
represented store is `ValueOwned` at the ledger's shared set — plus
`ValueOwned.copy_total` (`RuntimeOwnershipCopy.lean`) for the three-word copy. -/
def OwnedVarStep (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value),
    st.store.get? env x = some v →
    EvalReturnIH TrivialOwned st d env (.var x) st v →
    EvalIHO S st d env (.var x) st v

/-- **NAMED PREMISE — the assignment arm.**  The arm re-copies the child's
result into the parent's slot and stores it into the frame; the payload pointer
is the child's.  Supplier (task 2): `ValueOwned.copy_total`
(`RuntimeOwnershipCopy.lean`) at the actual copy, with the arena writes
excluded from the shared set by `Reserved.outsideFresh`/`Reserved.outsidePrivate`. -/
def OwnedAssignStep (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
    (v : Value) (store'' : Store),
    EvalE st d env e st' v → st'.store.set? env x v = some store'' →
    EvalReturnIH TrivialOwned st d env e st' v →
    EvalReturnIH TrivialOwned st d env (.assign x e) ⟨store'', st'.out⟩ v →
    EvalIHO S st d env e st' v →
    EvalIHO S st d env (.assign x e) ⟨store'', st'.out⟩ v

/-- **NAMED PREMISE — string concatenation (`.add` with a string operand).**  The
arm mallocs a fresh buffer and copies both payloads into it.  Supplier (task 2):
`MallocRun` for the fresh extent, `Reserved.outsideFresh` for its exclusion from
the live shared bytes, and the index's `arena` field (`ArenaShared`) to place the
fresh payload inside the shared set. -/
def OwnedConcatStep (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt)
    (lv rv v : Value),
    EvalE st d env l st' lv → EvalE st' d env r st'' rv →
    binOpSem st''.store .add lv rv = some v →
    EvalReturnIH TrivialOwned st d env l st' lv →
    EvalReturnIH TrivialOwned st' d env r st'' rv →
    EvalReturnIH TrivialOwned st d env (.binary .add l r) st'' v →
    EvalIHO S st d env l st' lv →
    EvalIHO S st' d env r st'' rv →
    EvalIHO S st d env (.binary .add l r) st'' v

/-- **NAMED PREMISE — the call arm.**  The returned value is the callee's, and
the clause has no motive for `Call`/`ExecSeq` (the generator's other relations
are `True` here).  Supplier (task 2): the statement-side clause motives over
`EnvNewContract`/`EnvDefineContract` — the body's frame and bindings are
allocator objects, the returned payload is the body's `ret` value. -/
def OwnedCallStep (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
    (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value),
    EvalE st d env f st' fv → args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs → Call st'' d fv vs st''' v →
    EvalReturnIH TrivialOwned st d env f st' fv →
    EvalReturnIH TrivialOwned st d env (f.call args) st''' v →
    EvalIHO S st d env f st' fv →
    EvalIHO S st d env (f.call args) st''' v

/-! ## 3. The string leaf's entry conversion

`Rows.field_hStr` (`rows/EntryGroundRows.lean`) and
`IHClauseGeneric.evalStrEntry_of_entry` both perform this conversion; both sit
in import closures this module deliberately avoids (the assembly rows and the
footprint clause reach the binary and logical sims).  DUPLICATION NOTE: when the
tower is wired, `strPayload_of_entry`/`evalStrEntry_of_entry` belong in
`EvalStrSim.lean` beside `EvalStrEntry.of_entry`, and all three consumers should
take them from there. -/

/-- The `.str` payload geometry from the entry ground's AST region. -/
theorem ownedStrPayload_of_entry
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

/-- The `.str` callee entry from the recursor entry. -/
theorem ownedStrEntry_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr} {s : String}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}
    (hc : EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c) :
    EvalStrEntry g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c := by
  obtain ⟨hssd, hsrd⟩ := ownedStrPayload_of_entry hc
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

/-! ## 4. The fifteen steps at the generator's field types -/

namespace owned

variable (S : SharedFam)

theorem hInt :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),
      EvalReturnIH TrivialOwned st d env (.int n) st (.int n) →
      EvalIHO S st d env (.int n) st (.int n) :=
  fun _ _ _ _ hOld => evalIHO_of_return trivial hOld

theorem hBool :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool),
      EvalReturnIH TrivialOwned st d env (.bool b) st (.bool b) →
      EvalIHO S st d env (.bool b) st (.bool b) :=
  fun _ _ _ _ hOld => evalIHO_of_return trivial hOld

theorem hNull :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      EvalReturnIH TrivialOwned st d env .null st .null →
      EvalIHO S st d env .null st .null :=
  fun _ _ _ hOld => evalIHO_of_return trivial hOld

theorem hFn :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String)
      (body : List Stmt) (store' : Store) (a : Addr),
      st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
      EvalReturnIH TrivialOwned st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) →
      EvalIHO S st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) :=
  fun _ _ _ _ _ _ _ _ _ hOld => evalIHO_of_return trivial hOld

theorem hNeg :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int),
      EvalE st d env e st' (.int n) →
      EvalReturnIH TrivialOwned st d env e st' (.int n) →
      EvalReturnIH TrivialOwned st d env (.unary .neg e) st' (.int (wrap64 (-n))) →
      EvalIHO S st d env e st' (.int n) →
      EvalIHO S st d env (.unary .neg e) st' (.int (wrap64 (-n))) :=
  fun _ _ _ _ _ _ _ _ hOld _ => evalIHO_of_return trivial hOld

theorem hNot :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v →
      EvalReturnIH TrivialOwned st d env e st' v →
      EvalReturnIH TrivialOwned st d env (.unary .not e) st' (.bool !v.truthy) →
      EvalIHO S st d env e st' v →
      EvalIHO S st d env (.unary .not e) st' (.bool !v.truthy) :=
  fun _ _ _ _ _ _ _ _ hOld _ => evalIHO_of_return trivial hOld

theorem hOrTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true →
      EvalReturnIH TrivialOwned st d env l st' lv →
      EvalReturnIH TrivialOwned st d env (.logical .or l r) st' (.bool true) →
      EvalIHO S st d env l st' lv →
      EvalIHO S st d env (.logical .or l r) st' (.bool true) :=
  fun _ _ _ _ _ _ _ _ _ _ hOld _ => evalIHO_of_return trivial hOld

theorem hAndFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false →
      EvalReturnIH TrivialOwned st d env l st' lv →
      EvalReturnIH TrivialOwned st d env (.logical .and l r) st' (.bool false) →
      EvalIHO S st d env l st' lv →
      EvalIHO S st d env (.logical .and l r) st' (.bool false) :=
  fun _ _ _ _ _ _ _ _ _ _ hOld _ => evalIHO_of_return trivial hOld

theorem hOrFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalE st' d env r st'' rv →
      EvalReturnIH TrivialOwned st d env l st' lv →
      EvalReturnIH TrivialOwned st' d env r st'' rv →
      EvalReturnIH TrivialOwned st d env (.logical .or l r) st'' (.bool rv.truthy) →
      EvalIHO S st d env l st' lv →
      EvalIHO S st' d env r st'' rv →
      EvalIHO S st d env (.logical .or l r) st'' (.bool rv.truthy) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hOld _ _ => evalIHO_of_return trivial hOld

theorem hAndTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalE st' d env r st'' rv →
      EvalReturnIH TrivialOwned st d env l st' lv →
      EvalReturnIH TrivialOwned st' d env r st'' rv →
      EvalReturnIH TrivialOwned st d env (.logical .and l r) st'' (.bool rv.truthy) →
      EvalIHO S st d env l st' lv →
      EvalIHO S st' d env r st'' rv →
      EvalIHO S st d env (.logical .and l r) st'' (.bool rv.truthy) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hOld _ _ => evalIHO_of_return trivial hOld

/-- **The string literal.**  The only closed step with a real payload: the leaf
returns its AST pointer (`StrReturnPin.pointer`), and the index's `ast` field
makes the pinned AST/rodata region shared. -/
theorem hStr (hI : OwnedIndex S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String),
      EvalReturnIH TrivialOwned st d env (.str s) st (.str s) →
      EvalIHO S st d env (.str s) st (.str s) := by
  intro st d env s _hOld
  refine ⟨?_⟩
  intro g N A SL φf φc sp r sret aEnv aExpr m0 c hc
  obtain ⟨c', hs, hExit, hPin⟩ :=
    evalStrSimP_exact g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c
      (ownedStrEntry_of_entry hc)
  have hW := leafWidenP_of_entry (v := .str s) hc
  have hD := evalExitD_of_pinnedExit ⟨hExit, hPin.memory⟩ hW (hc.mem ▸ hc.sret_words)
  refine ⟨c', hs, hD, ?_⟩
  intro tag _htag _hts
  obtain ⟨_φc', _, hval⟩ := hExit.result
  obtain ⟨_htag3, p, hp, _hnz, hcs⟩ := hval
  have hp0 : read64 m0 (aExpr.toNat + 8) = some p := hPin.pointer.symm.trans hp
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.str s) := hc.mem ▸ hc.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  obtain ⟨-, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
  refine ⟨p, s, hp, hcs, ?_⟩
  intro k hk
  exact hI.ast SL A m0 sret.toNat aExpr.toNat (.str s) lo hi spec (p + k)
    (by omega) (by omega)

/-- **The binary arm.**  Closed for every operator whose result is an integer or
a boolean (all the integer cells and all four comparison cells, string
comparison included); `.add` is the `OwnedConcatStep` premise. -/
theorem hBinary (hAdd : OwnedConcatStep S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = some v →
      EvalReturnIH TrivialOwned st d env l st' lv →
      EvalReturnIH TrivialOwned st' d env r st'' rv →
      EvalReturnIH TrivialOwned st d env (.binary op l r) st'' v →
      EvalIHO S st d env l st' lv →
      EvalIHO S st' d env r st'' rv →
      EvalIHO S st d env (.binary op l r) st'' v := by
  intro st d env op l r st' st'' lv rv v hl hr hsem old1 old2 hOld ih1 ih2
  cases op
  case add => exact hAdd st d env l r st' st'' lv rv v hl hr hsem old1 old2 hOld ih1 ih2
  all_goals exact evalIHO_of_return (binOpSem_payloadFree hsem (by decide)) hOld

/-- The variable leaf, from its named premise. -/
theorem hVar (h : OwnedVarStep S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value),
      st.store.get? env x = some v →
      EvalReturnIH TrivialOwned st d env (.var x) st v →
      EvalIHO S st d env (.var x) st v := h

/-- The assignment arm, from its named premise. -/
theorem hAssign (h : OwnedAssignStep S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
      (v : Value) (store'' : Store),
      EvalE st d env e st' v → st'.store.set? env x v = some store'' →
      EvalReturnIH TrivialOwned st d env e st' v →
      EvalReturnIH TrivialOwned st d env (.assign x e) ⟨store'', st'.out⟩ v →
      EvalIHO S st d env e st' v →
      EvalIHO S st d env (.assign x e) ⟨store'', st'.out⟩ v := h

/-- The call arm, from its named premise.  The generated field hands over the
OLD `EvalArgs`/`Call` motives (real contracts) and the clause's own ones (`True`,
since no clause motive is declared for those relations); the step uses neither. -/
theorem hCall (h : OwnedCallStep S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value)
      (_a : EvalE st d env f st' fv) (_a_1 : args.length ≤ maxArgs)
      (a_2 : EvalArgs st' d env args st'' vs) (a_3 : Call st'' d fv vs st''' v),
      EvalReturnIH TrivialOwned st d env f st' fv →
      Vsa.Sim.TermSimAssembly.mEvalArgs st' d env args st'' vs a_2 →
      Vsa.Sim.TermSimAssembly.mCall st'' d fv vs st''' v a_3 →
      EvalReturnIH TrivialOwned st d env (f.call args) st''' v →
      EvalIHO S st d env f st' fv → True → True →
      EvalIHO S st d env (f.call args) st''' v :=
  fun st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3 old1 _ _ hOld ih1 _ _ =>
    h st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3 old1 hOld ih1

end owned

/-! ## 5. The string-comparison consumer

`StrCmpOwnedOperands` (`StrCmpCellClauses.lean`) is stated over an ARBITRARY
configuration satisfying `TwoSubReturn` — no execution relates it to the entry —
so a fact proved at the children's ACTUAL returns cannot reach it (see the
module doc of `ih-tower/R2F-owned.md`).  What the cells need at their actual
return is exactly this: -/

/-- The three facts `strCmpOperandsAt_of_owned` (`StrCmpCellClauses.lean`)
consumes, field for field with `Vsa.Sim.OwnedOperands` (whose `geom` is
`SharedGeom.mk g.ram g.htif g.stack` for this record's `geom`). -/
structure OwnedOperandFacts (shared : Nat → Prop) (SL : StackLayout) (sp : BitVec 64)
    (m : Mem) (sl sr : String) : Prop where
  geom : OwnedGeom shared SL
  left : ValueOwned m shared (sp.toNat - 968) (.str sl)
  right : ValueOwned m shared (sp.toNat - 944) (.str sr)

/-- **The operand facts from the clause.**  At the memory of the binary arm's
two-children return, the clause fact at each operand slot plus the operand's
`ValueRepr` give the two `RuntimeOwnership.ValueOwned` hypotheses of
`strCmpOperandsAt_of_owned`, and the index plus the RAM-top slack give the three
`SharedGeom` fields. -/
theorem ownedOperands_of_clause {S : SharedFam} {SL : StackLayout} {A : Arena}
    {N : NativeAddrs} {φl φr : Addr → Nat} {sp : BitVec 64} {m : Mem} {sl sr : String}
    (hI : OwnedIndex S) (htop : SharedTopSlack S SL A)
    (hOL : OwnedSlot m (S SL A) (sp.toNat - 968))
    (hOR : OwnedSlot m (S SL A) (sp.toNat - 944))
    (hvl : ValueRepr m N φl (sp.toNat - 968) (.str sl))
    (hvr : ValueRepr m N φr (sp.toNat - 944) (.str sr)) :
    OwnedOperandFacts (S SL A) SL sp m sl sr where
  geom := ownedGeom_of_index hI htop
  left := valueOwned_of_ownedSlot hOL hvl
  right := valueOwned_of_ownedSlot hOR hvr

#print axioms binOpSem_payloadFree
#print axioms ownedStrEntry_of_entry
#print axioms owned.hInt
#print axioms owned.hStr
#print axioms owned.hBool
#print axioms owned.hNull
#print axioms owned.hNeg
#print axioms owned.hNot
#print axioms owned.hOrTrue
#print axioms owned.hOrFalse
#print axioms owned.hAndFalse
#print axioms owned.hAndTrue
#print axioms owned.hFn
#print axioms owned.hBinary
#print axioms owned.hVar
#print axioms owned.hAssign
#print axioms owned.hCall
#print axioms ownedOperands_of_clause

end IHClauseGenericOwned

end Vsa.Sim
