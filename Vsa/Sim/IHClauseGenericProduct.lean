import Vsa.Sim.IHClauseGenericSupply
import Vsa.Sim.IHClauseGenericOwned

/-!
# `IHClauseGenericProduct` — the per-case steps of the PRODUCT clause (IH tower, Level 2)

The four string-comparison cells consume two clause-shaped premises
(`StrCmpCellClauses.lean`, `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned`):
`FootprintPayloadOwnedClause S` for the left operand (footprint AND payload
coverage AND ownership at the child's actual return) and
`FootprintOwnedClause S` for the right one (footprint AND ownership).  Neither
follows from the landed clauses: `FootprintCov` is the footprint/coverage pair
WITHOUT ownership and `OwnedPayload` is the ownership WITHOUT the footprint, and
two separate `EvalIHWithM` recursions each existentially quantify their own
reached configuration, so their posts cannot be conjoined without machine
determinism.  The steps are therefore proved directly at the conjunction, over
the same row theorems the three landed families use.

* **`EvalIHWithM.monoD`** — the missing combinator: strengthen the retained fact
  using the child's OWN exit (`EvalExitD`), not only the old fact.  Every
  payload-free result gets its `OwnedSlot` and its `ValuePayloadCovered` this
  way, off the exit's `ValueRepr`, with no re-derivation of any row
  (`EvalIHFPO.of_footprint_payloadFree`, `EvalIHFO.of_footprint_payloadFree`).
* **`EvalIHFPO.forgetCov`** — the right-operand premise `EvalIHFO` is the left
  one with the coverage conjunct dropped, so ONE recursion (at `EvalIHFPO`)
  supplies both cell premises.  A second recursion at `EvalIHFO` could not close
  its own `hBinary`: the string-comparison cell needs the left child's coverage,
  which `EvalIHFO` drops.
* **`evalStrProductIHF`** — the string literal, the only leaf with a real
  payload: one run of `evalStrSimP_exact`, whose `StrReturnPin` pins the returned
  pointer inside the entry's AST region, giving the footprint, the coverage and
  the ownership at ONE configuration.
* **`binaryFootprintNA_of_product`** — the binary dispatcher under the guard
  (`op ≠ .add`): the scalar cells are the landed `IntCellF`/`EqCellF` suppliers at
  the children's footprints, and the four string comparisons are
  `binStrCmpCellFPO` — `binRow_strcmpF_owned` at the step's OWN child IHs, which
  is where the left child's coverage and both operands' ownership are available.
* **`BinStrCmpCellNA`** — the string-comparison cell restricted to non-allocating
  operands, the shape a guarded clause can supply.

The clause is guarded by `IHClauseGeneric.noAllocExpr` exactly as `FootprintNA`
is: `hAssign`/`hFn`/`hCall` and `.add` write the arena, so they are false at
`noArenaFoot`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.RuntimeOwnership (SharedCString)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## 1. Reading the extra fact off the child's own exit -/

/-- **The product combinator.**  `EvalIHWithM.mono` sees only the retained fact;
this sees the child's `EvalExitD` at the SAME reached configuration, which is
what a fact about the returned value (`ValueRepr` at the result slot) needs. -/
theorem EvalIHWithM.monoD {Extra Extra' : EvalExtraM}
    {st st' : SpecSt} {d env : Nat} {e : Expr} {v : Value}
    (himp : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret : BitVec 64) (m0 : Mem) (c : Config),
      EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size st' v sp r sret m0 c →
      Extra N A SL φf φc sp sret m0 c → Extra' N A SL φf φc sp sret m0 c)
    (h : EvalIHWithM Extra st d env e st' v) : EvalIHWithM Extra' st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    (h.run g N A SL φf φc sp r sret aEnv aExpr m0).conseq (fun _ hp => hp)
      (fun c hp => ⟨hp.result, himp g N A SL φf φc sp r sret m0 c hp.result hp.extra⟩)

/-- A value with no indirect payload is covered by every byte set. -/
theorem valuePayloadCovered_of_payloadFree {P : Nat → Prop} {m : Mem} {a : Nat} {v : Value}
    (hpf : PayloadFree v) : ValuePayloadCovered P m a v := by
  cases v
  case str s => exact False.elim hpf
  case native f => exact False.elim hpf
  all_goals exact True.intro

/-- **The payload-free product step.**  A footprint child contract whose result
carries no indirect payload is the full product: the coverage half is `True` and
the ownership half is definitional at the exit's own `ValueRepr`. -/
theorem EvalIHFPO.of_footprint_payloadFree {S : SharedFam} {F : FootFam} {st st' : SpecSt}
    {d env : Nat} {e : Expr} {v : Value} (hpf : PayloadFree v)
    (h : EvalIHF F st d env e st' v) : EvalIHFPO S F st d env e st' v :=
  EvalIHWithM.monoD
    (fun _g _N _A _SL _φf _φc _sp _r _sret _m0 _c hD hf => by
      obtain ⟨_φc', _, hval⟩ := hD.1.result
      exact ⟨hf, valuePayloadCovered_of_payloadFree hpf, OwnedSlot.of_payloadFree hval hpf⟩)
    h

/-- The right-operand product for a payload-free result. -/
theorem EvalIHFO.of_footprint_payloadFree {S : SharedFam} {F : FootFam} {st st' : SpecSt}
    {d env : Nat} {e : Expr} {v : Value} (hpf : PayloadFree v)
    (h : EvalIHF F st d env e st' v) : EvalIHFO S F st d env e st' v :=
  EvalIHWithM.monoD
    (fun _g _N _A _SL _φf _φc _sp _r _sret _m0 _c hD hf => by
      obtain ⟨_φc', _, hval⟩ := hD.1.result
      exact ⟨hf, OwnedSlot.of_payloadFree hval hpf⟩)
    h

/-- The RIGHT operand's premise from the LEFT one: drop the coverage conjunct. -/
theorem EvalIHFPO.forgetCov {S : SharedFam} {F : FootFam} {st st' : SpecSt}
    {d env : Nat} {e : Expr} {v : Value} (h : EvalIHFPO S F st d env e st' v) :
    EvalIHFO S F st d env e st' v :=
  EvalIHWithM.mono (fun _ _ _ _ _ _ _ _ _ hp => ⟨hp.1, hp.2.2⟩) h

/-- The footprint half of the product. -/
theorem EvalIHFPO.footprint {S : SharedFam} {F : FootFam} {st st' : SpecSt}
    {d env : Nat} {e : Expr} {v : Value} (h : EvalIHFPO S F st d env e st' v) :
    EvalIHF F st d env e st' v :=
  EvalIHWithM.mono (fun _ _ _ _ _ _ _ _ _ hp => hp.1) h

/-! ## 2. The string literal at the product clause -/

/-- **The string leaf.**  One run of `evalStrSimP_exact`: its `LeafMemPin` is the
`noArenaFoot` footprint, and its `StrReturnPin` says the returned pointer is the
entry's AST pointer, which the AST region places both outside the whole stack
(coverage) and inside the shared set (ownership, through the index's `ast`
field).  All three conjuncts at ONE configuration. -/
theorem evalStrProductIHF (S : SharedFam) (hI : OwnedIndex S)
    (st : SpecSt) (d env : Nat) (s : String) :
    EvalIHFPO S noArenaFoot st d env (.str s) st (.str s) where
  run := by
    intro g N A SL φf φc sp r sret aEnv aExpr m0 c hc
    obtain ⟨c', hs, hExit, hPin⟩ :=
      evalStrSimP_exact g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c
        (evalStrEntry_of_entry hc)
    have hW := leafWidenP_of_entry (v := .str s) hc
    have hD := evalExitD_of_pinnedExit ⟨hExit, hPin.memory⟩ hW (hc.mem ▸ hc.sret_words)
    have hg : EvalGround m0 SL A sp sret aExpr.toNat (.str s) := hc.mem ▸ hc.ground
    obtain ⟨lo, hi, spec⟩ := hg.ast.region
    refine ⟨c', hs, hD,
      ⟨fun k hk => hPin.memory.agree k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))⟩,
      ?_, ?_⟩
    · change ∀ p, read64 c'.σ.mem (sret.toNat + 8) = some p →
        ∀ k, k ≤ s.length → ¬ (SL.lo ≤ p + k ∧ p + k < SL.hi)
      intro p hp k hk hstack
      have hp0 : read64 m0 (aExpr.toNat + 8) = some p := hPin.pointer.symm.trans hp
      obtain ⟨_, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
      rcases spec.stack_disjoint with hd | hd <;> omega
    · intro tag _htag _hts
      obtain ⟨_φc', _, hval⟩ := hExit.result
      obtain ⟨_htag3, p, hp, _hnz, hcs⟩ := hval
      have hp0 : read64 m0 (aExpr.toNat + 8) = some p := hPin.pointer.symm.trans hp
      obtain ⟨-, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
      refine ⟨p, s, hp, hcs, ?_⟩
      intro k hk
      exact hI.ast SL A m0 sret.toNat aExpr.toNat (.str s) lo hi spec (p + k)
        (by omega) (by omega)

/-! ## 3. The string-comparison cell at the product child hypotheses -/

/-- A string-comparison cell whose LEFT child is at the product clause and whose
RIGHT child is at the ownership-carrying footprint clause — the shapes
`binRow_strcmpF_owned` consumes.  This is the cell the clause's own `hBinary`
step discharges, using the step's child IHs. -/
def BinStrCmpCellFPO (S : SharedFam) (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr)
    (st' st'' : SpecSt) (sl sr : String),
    EvalE st d env el st' (.str sl) →
    EvalE st' d env er st'' (.str sr) →
    EvalIHFPO S noArenaFoot st d env el st' (.str sl) →
    EvalIHFO S noArenaFoot st' d env er st'' (.str sr) →
    EvalIHF noArenaFoot st d env (.binary op el er) st'' (.bool (bres sl sr))

/-- The cell from the ownership head (`binRow_strcmpF_owned`): no operand supply
is quantified over an unreachable configuration. -/
theorem binStrCmpCellFPO (D : StrCmpOp) (C : D.Cert) (S : SharedFam)
    (hI : OwnedIndex S) (htop : SharedTopSlackAll S) : BinStrCmpCellFPO S D.op D.bres :=
  fun st d env el er st' st'' sl sr hEl hEr ihL ihR =>
    EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
      binRow_strcmpF_owned D C S hI htop g N A SL φf φc st st' st'' d env el er sl sr
        sp r sret aEnv aExpr m0 hEl ihL ihR
        (EvalE.binary st d env D.op el er st' st'' (.str sl) (.str sr) _ hEl hEr (C.sem _ _ _)))

theorem strLtCellFPO (S : SharedFam) (hI : OwnedIndex S) (htop : SharedTopSlackAll S) :
    BinStrCmpCellFPO S .lt (fun sl sr => sl < sr) :=
  binStrCmpCellFPO strCmpLt strCmpLt_cert S hI htop

theorem strLeCellFPO (S : SharedFam) (hI : OwnedIndex S) (htop : SharedTopSlackAll S) :
    BinStrCmpCellFPO S .le (fun sl sr => sl < sr || sl == sr) :=
  binStrCmpCellFPO strCmpLe strCmpLe_cert S hI htop

theorem strGtCellFPO (S : SharedFam) (hI : OwnedIndex S) (htop : SharedTopSlackAll S) :
    BinStrCmpCellFPO S .gt (fun sl sr => sr < sl) :=
  binStrCmpCellFPO strCmpGt strCmpGt_cert S hI htop

theorem strGeCellFPO (S : SharedFam) (hI : OwnedIndex S) (htop : SharedTopSlackAll S) :
    BinStrCmpCellFPO S .ge (fun sl sr => sr < sl || sl == sr) :=
  binStrCmpCellFPO strCmpGe strCmpGe_cert S hI htop

/-! ## 4. The binary dispatcher under the guard -/

/-- **The binary node's footprint from the product child IHs.**  `op ≠ .add`
(the clause guard), so no cell allocates: the nine integer cells and the equality
pair are the landed suppliers at the children's footprints, and the four string
comparisons are `binStrCmpCellFPO` at the step's own child IHs — the left child's
coverage and both operands' ownership are exactly what the ownership head
`binRow_strcmpF_owned` needs, and they are available HERE and nowhere else. -/
theorem binaryFootprintNA_of_product (S : SharedFam)
    (hI : OwnedIndex S) (htop : SharedTopSlackAll S)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    {st : SpecSt} {d : Nat} {env : Addr} {op : BinOp} {el er : Expr} {st' st'' : SpecSt}
    {lv rv v : Value}
    (hEl : EvalE st d env el st' lv) (hEr : EvalE st' d env er st'' rv)
    (hsem : binOpSem st''.store op lv rv = some v) (hopne : op ≠ .add)
    (ihL : EvalIHFPO S noArenaFoot st d env el st' lv)
    (ihR : EvalIHFPO S noArenaFoot st' d env er st'' rv) :
    EvalIHF noArenaFoot st d env (.binary op el er) st'' v := by
  have ihLF : EvalIHF noArenaFoot st d env el st' lv := EvalIHFPO.footprint ihL
  have ihRF : EvalIHF noArenaFoot st' d env er st'' rv := EvalIHFPO.footprint ihR
  have ihRO : EvalIHFO S noArenaFoot st' d env er st'' rv := EvalIHFPO.forgetCov ihR
  cases op with
  | add => exact absurd rfl hopne
  | sub =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_sub st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | mul =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_mul st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | div =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem
      by_cases hb0 : b = 0
      · subst hb0; simp at hsem
      · rw [if_neg (by simpa using hb0)] at hsem; cases hsem
        exact intCellF_div hDivOv st d env el er st' st'' a b hEl hEr ihLF ihRF hb0
  | mod =>
    match lv, rv, hsem with
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem
      by_cases hb0 : b = 0
      · subst hb0; simp at hsem
      · rw [if_neg (by simpa using hb0)] at hsem; cases hsem
        exact intCellF_mod st d env el er st' st'' a b hEl hEr ihLF ihRF hb0
  | lt =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact strLtCellFPO S hI htop st d env el er st' st'' sl sr hEl hEr ihL ihRO
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_lt_closed st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | le =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact strLeCellFPO S hI htop st d env el er st' st'' sl sr hEl hEr ihL ihRO
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_le st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | gt =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact strGtCellFPO S hI htop st d env el er st' st'' sl sr hEl hEr ihL ihRO
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_gt st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | ge =>
    match lv, rv, hsem with
    | .str sl, .str sr, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact strGeCellFPO S hI htop st d env el er st' st'' sl sr hEl hEr ihL ihRO
    | .int a, .int b, hsem =>
      simp only [binOpSem] at hsem; cases hsem
      exact intCellF_ge st d env el er st' st'' a b hEl hEr ihLF ihRF trivial
  | eq =>
    simp only [binOpSem] at hsem; cases hsem
    exact eqCellF_of hEq st d env el er st' st'' lv rv hEl hEr ihLF ihRF
  | ne =>
    simp only [binOpSem] at hsem; cases hsem
    exact neCellF_of hNe st d env el er st' st'' lv rv hEl hEr ihLF ihRF

/-! ## 5. The fifteen steps at the generator's field types

The clause `FootprintPayloadOwned` (`scripts/ih_clauses.tsv`) is
`EvalIHFPO stdShared noArenaFoot` under the guard
`IHClauseGeneric.noAllocExpr e = true`.  The leaves and the six one-child arms are
stated WITHOUT the guard (the generator's `unguarded` tag lifts them); the three
allocating cases are vacuous under it; `hVar` and `hBinary` stay residual. -/

namespace IHClauseGenericProduct

open IHClauseGeneric (noAllocExpr)

/-- `hInt`: CLOSED (payload-free result). -/
theorem hInt (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n) →
      EvalIHFPO S noArenaFoot st d env (Expr.int n) st (Value.int n) :=
  fun st d env n hOld =>
    EvalIHFPO.of_footprint_payloadFree trivial (IHClauseGeneric.footprint.hInt st d env n hOld)

/-- `hStr`: CLOSED — the literal's payload is its own AST region. -/
theorem hStr (S : SharedFam) (hI : OwnedIndex S) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s) →
      EvalIHFPO S noArenaFoot st d env (Expr.str s) st (Value.str s) :=
  fun st d env s _ => evalStrProductIHF S hI st d env s

/-- `hBool`: CLOSED (payload-free result). -/
theorem hBool (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.bool b) st (Value.bool b)
        (EvalE.bool st d env b) →
      EvalIHFPO S noArenaFoot st d env (Expr.bool b) st (Value.bool b) :=
  fun st d env b hOld =>
    EvalIHFPO.of_footprint_payloadFree trivial (IHClauseGeneric.footprint.hBool st d env b hOld)

/-- `hNull`: CLOSED (payload-free result). -/
theorem hNull (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      Vsa.Sim.TermSimAssembly.mEvalE st d env Expr.null st Value.null (EvalE.null st d env) →
      EvalIHFPO S noArenaFoot st d env Expr.null st Value.null :=
  fun st d env hOld =>
    EvalIHFPO.of_footprint_payloadFree trivial (IHClauseGeneric.footprint.hNull st d env hOld)

/-- `hNeg`: CLOSED (payload-free result; the child's coverage is dropped). -/
theorem hNeg (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)
      (a : EvalE st d env e st' (Value.int n)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' (Value.int n) a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.neg e) st'
        (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a) →
      EvalIHFPO S noArenaFoot st d env e st' (Value.int n) →
      EvalIHFPO S noArenaFoot st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) :=
  fun st d env e st' n a o1 hOld ih =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hNeg st d env e st' n a o1 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ih))

/-- `hNot`: CLOSED (payload-free result). -/
theorem hNot (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.not e) st'
        (Value.bool !v.truthy) (EvalE.not st d env e st' v a) →
      EvalIHFPO S noArenaFoot st d env e st' v →
      EvalIHFPO S noArenaFoot st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) :=
  fun st d env e st' v a o1 hOld ih =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hNot st d env e st' v a o1 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ih))

/-- `hOrTrue`: CLOSED (payload-free result). -/
theorem hOrTrue (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st'
        (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1) →
      EvalIHFPO S noArenaFoot st d env l st' lv →
      EvalIHFPO S noArenaFoot st d env (Expr.logical LogOp.or l r) st' (Value.bool true) :=
  fun st d env l r st' lv a a_1 o1 hOld ih =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hOrTrue st d env l r st' lv a a_1 o1 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ih))

/-- `hAndFalse`: CLOSED (payload-free result). -/
theorem hAndFalse (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st'
        (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1) →
      EvalIHFPO S noArenaFoot st d env l st' lv →
      EvalIHFPO S noArenaFoot st d env (Expr.logical LogOp.and l r) st' (Value.bool false) :=
  fun st d env l r st' lv a a_1 o1 hOld ih =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hAndFalse st d env l r st' lv a a_1 o1 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ih))

/-- `hOrFalse`: CLOSED (payload-free result). -/
theorem hOrFalse (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st''
        (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHFPO S noArenaFoot st d env l st' lv →
      EvalIHFPO S noArenaFoot st' d env r st'' rv →
      EvalIHFPO S noArenaFoot st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld ihL ihR =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hOrFalse st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ihL)
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ihR))

/-- `hAndTrue`: CLOSED (payload-free result). -/
theorem hAndTrue (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st''
        (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHFPO S noArenaFoot st d env l st' lv →
      EvalIHFPO S noArenaFoot st' d env r st'' rv →
      EvalIHFPO S noArenaFoot st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld ihL ihR =>
    EvalIHFPO.of_footprint_payloadFree trivial
      (IHClauseGeneric.footprint.hAndTrue st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ihL)
        (EvalIHFPO.footprint (S := S) (F := noArenaFoot) ihR))

/-- `hAssign`: vacuous under the guard (the arm writes the arena). -/
theorem hAssign (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value)
      (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out }
        v (EvalE.assign st d env x e st' v store'' a a_1) →
      (noAllocExpr e = true → EvalIHFPO S noArenaFoot st d env e st' v) →
      (noAllocExpr (Expr.assign x e) = true →
        EvalIHFPO S noArenaFoot st d env (Expr.assign x e)
          { store := store'', out := st'.out } v) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

/-- `hFn`: vacuous under the guard (the closure is allocated). -/
theorem hFn (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String)
      (body : List Stmt) (store' : Store) (a : Addr)
      (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } =
        (store', a)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.fn name params body)
        { store := store', out := st.out } (Value.closure a)
        (EvalE.fn st d env name params body store' a a_1) →
      (noAllocExpr (Expr.fn name params body) = true →
        EvalIHFPO S noArenaFoot st d env (Expr.fn name params body)
          { store := store', out := st.out } (Value.closure a)) :=
  fun _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

/-- `hCall`: vacuous under the guard (the callee allocates). -/
theorem hCall (S : SharedFam) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value)
      (a : EvalE st d env f st' fv) (a_1 : args.length ≤ maxArgs)
      (a_2 : EvalArgs st' d env args st'' vs) (a_3 : Call st'' d fv vs st''' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env f st' fv a →
      Vsa.Sim.TermSimAssembly.mEvalArgs st' d env args st'' vs a_2 →
      Vsa.Sim.TermSimAssembly.mCall st'' d fv vs st''' v a_3 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (f.call args) st''' v
        (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3) →
      (noAllocExpr f = true → EvalIHFPO S noArenaFoot st d env f st' fv) →
      True → True →
      (noAllocExpr (f.call args) = true →
        EvalIHFPO S noArenaFoot st d env (f.call args) st''' v) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noAllocExpr] at h

/-- **`hBinary`** — the residual step, at the generator's guarded field type.  The
guard supplies `op ≠ .add` and both children's guards; the string branches consume
the children's own product IHs, so no operand supply is quantified over an
unreachable configuration. -/
theorem hBinary (S : SharedFam) (hI : OwnedIndex S) (htop : SharedTopSlackAll S)
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_1 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) →
      (noAllocExpr l = true → EvalIHFPO S noArenaFoot st d env l st' lv) →
      (noAllocExpr r = true → EvalIHFPO S noArenaFoot st' d env r st'' rv) →
      (noAllocExpr (Expr.binary op l r) = true →
        EvalIHFPO S noArenaFoot st d env (Expr.binary op l r) st'' v) := by
  intro st d env op el er st' st'' lv rv v hEl hEr hsem _o1 _o2 _hOld ihL ihR hg
  obtain ⟨hopne, hgl, hgr⟩ := IHClauseGeneric.noAllocExpr_binary hg
  exact EvalIHFPO.of_footprint_payloadFree
    (IHClauseGenericOwned.binOpSem_payloadFree hsem hopne)
    (binaryFootprintNA_of_product S hI htop hDivOv hEq hNe hEl hEr hsem hopne
      (ihL hgl) (ihR hgr))

end IHClauseGenericProduct

/-! ## 6. The clause premises and the guarded cells -/

/-- The guarded product clause for the LEFT operand: the closed clause recursion
restricted to non-allocating expressions. -/
def FootprintPayloadOwnedClauseNA (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
    IHClauseGeneric.noAllocExpr e = true → EvalE st d env e st' v →
    EvalIHFPO S noArenaFoot st d env e st' v

/-- The guarded clause for the RIGHT operand, DERIVED from the left one by
dropping the coverage conjunct: one recursion supplies both cell premises. -/
def FootprintOwnedClauseNA (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
    IHClauseGeneric.noAllocExpr e = true → EvalE st d env e st' v →
    EvalIHFO S noArenaFoot st d env e st' v

theorem footprintOwnedClauseNA_of_payload {S : SharedFam}
    (h : FootprintPayloadOwnedClauseNA S) : FootprintOwnedClauseNA S :=
  fun st d env e st' v hg t => EvalIHFPO.forgetCov (h st d env e st' v hg t)

/-! ### The RAM-top slack: `stdShared` is the wrong index

`SharedTopSlackAll S` (`StrCmpCellClauses.lean`) is what the `strcmp` word loop's
8-byte read needs.  At the canonical index it is FALSE, not merely unproven:
`stdShared` is the geometric envelope `k < 0x100000000`, which contains the top
eight bytes of the address space (`not_sharedTopSlackAll_std`).  And no index can
repair this while `AstRegionSpec.hi_ram` is `hi ≤ 0x100000000`: `OwnedIndex.ast`
puts every byte of every entry's AST region into `S`, so the slack forces
`hi + 7 ≤ 0x100000000` on every such region (`astRegionSlack_forced`), a fact the
entry does not carry.

`stdSharedSlack` is the repaired index: the same envelope with the slack built
in.  `SharedTopSlackAll` is then a theorem, and `OwnedIndex` reduces to the two
entry-layer premises below, whose supplier is the concrete Layout (the pinned
AST/rodata region and the arena both end far below `0x100000000`) — the same
supplier `AstRegionSpec.hi_ram` has.  Amending `hi_ram` to `hi + 8 ≤
0x100000000` discharges `AstRegionSlack` outright. -/

theorem not_sharedTopSlackAll_std : ¬ SharedTopSlackAll stdShared := by
  intro h
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hk : stdShared ⟨0, 0⟩ ⟨0, 0⟩ 0xFFFFFFFF :=
    ⟨by rw [ht]; omega, by omega, Or.inr (Nat.zero_le _)⟩
  have hle := h ⟨0, 0⟩ ⟨0, 0⟩ 0xFFFFFFFF hk
  omega

/-- **The obstruction, machine-checked.**  `OwnedIndex S` and `SharedTopSlackAll S`
together say exactly that every entry's AST region ends 7 bytes below the RAM top
— a strengthening of `AstRegionSpec.hi_ram`, which gives only `hi ≤ 0x100000000`.
So the two premises of the string-comparison cells cannot both be discharged for
ANY index until the entry carries the slack. -/
theorem astRegionSlack_forced {S : SharedFam} (hI : OwnedIndex S)
    (htop : SharedTopSlackAll S) {m : Mem} {SL : StackLayout} {A : Arena}
    {sret aExpr : Nat} {e : Expr} {lo hi : Nat}
    (spec : AstRegionSpec m SL A sret aExpr e lo hi) (hne : lo < hi) :
    hi + 7 ≤ 0x100000000 := by
  have hs : S SL A (hi - 1) :=
    hI.ast SL A m sret aExpr e lo hi spec (hi - 1) (by omega) (by omega)
  have := htop SL A (hi - 1) hs
  omega

/-- The repaired index: the canonical envelope with the `strcmp` word loop's
8-byte slack below the RAM top. -/
def stdSharedSlack : SharedFam := fun SL _ k =>
  tohostAddr + 16 ≤ k ∧ k + 8 ≤ 0x100000000 ∧ (k < SL.lo ∨ SL.hi ≤ k)

theorem sharedTopSlackAll_stdSlack : SharedTopSlackAll stdSharedSlack :=
  fun _ _ _ hk => hk.2.1

/-- Every entry's pinned AST/rodata region ends 8 bytes below the RAM top.
DISCHARGED by `astRegionSlack_holds`: this is exactly `AstRegionSpec.hi_ram`
(`Vsa/Sim/InterpEntry.lean`) since that field was amended from
`hi ≤ 0x100000000` to `hi + 8 ≤ 0x100000000`. -/
def AstRegionSlack : Prop :=
  ∀ (m : Mem) (SL : StackLayout) (A : Arena) (sret aExpr : Nat) (e : Expr) (lo hi : Nat),
    AstRegionSpec m SL A sret aExpr e lo hi → hi + 8 ≤ 0x100000000

/-- `AstRegionSlack` is the amended `AstRegionSpec.hi_ram` field verbatim. -/
theorem astRegionSlack_holds : AstRegionSlack :=
  fun _ _ _ _ _ _ _ _ h => h.hi_ram

/-- **NAMED PREMISE** — a well-placed arena ends 8 bytes below the RAM top.
Supplier: the allocator ledger's concrete arena bounds (task 2), exactly as for
`ArenaShared.top`. -/
def ArenaSlack : Prop :=
  ∀ (SL : StackLayout) (A : Arena), ArenaShared SL A → A.hi + 8 ≤ 0x100000000

theorem ownedIndex_stdSlack (hAst : AstRegionSlack) (hArena : ArenaSlack) :
    OwnedIndex stdSharedSlack where
  ram := by
    intro _ _ k hk
    have ht : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨h1, h2, _⟩ := hk
    rw [ht] at h1
    exact ⟨by omega, by omega⟩
  htif := by
    intro _ _ k hk
    exact hk.1
  stack := by
    intro _ _ k hk
    exact hk.2.2
  ast := by
    intro SL A m sret aExpr e lo hi spec k hlo hhi
    have hw := spec.win
    have hr := hAst m SL A sret aExpr e lo hi spec
    refine ⟨by omega, by omega, ?_⟩
    rcases spec.stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  arena := by
    intro SL A hA k hlo hhi
    have hht := hA.htif
    have htp := hArena SL A hA
    refine ⟨by omega, by omega, ?_⟩
    rcases hA.stack with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **NAMED PREMISE — the variable leaf at the product clause.**  `env_get` copies
a store value into the result slot, so all three conjuncts are the store's, not
the caller's.  Suppliers: the footprint half needs `VarPinnedSim` +
`Rows.VarLeafResid` (`IHClauseGeneric.footprint.hVar_of`, Level 1B); the coverage
and ownership halves need the store's own ownership (`HeapOwned`/`StoreOwned`
through `ValueOwned.copy_total`, `PROOF_CLOSURE_PLAN.md` task 2), exactly as the
landed `IHClauseGenericOwned.OwnedVarStep` does. -/
def VarProductStep (S : SharedFam) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value),
    st.store.get? env x = some v → EvalIHFPO S noArenaFoot st d env (.var x) st v

/-- **The string-comparison cell for non-allocating operands** — the shape a
guarded clause supplies.  Lifting the guard needs the allocating family over the
allocator ledger (`MallocReturnAt.allocFoot`, `HeapOwned.pushClosure`). -/
def BinStrCmpCellNA (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr)
    (st' st'' : SpecSt) (sl sr : String),
    IHClauseGeneric.noAllocExpr el = true → IHClauseGeneric.noAllocExpr er = true →
    EvalE st d env el st' (.str sl) →
    EvalE st' d env er st'' (.str sr) →
    EvalIH st d env el st' (.str sl) →
    EvalIH st' d env er st'' (.str sr) →
    EvalIH st d env (.binary op el er) st'' (.bool (bres sl sr))

/-- **The cell from the guarded clause.**  `binStrCmpCell_of_owned`
(`StrCmpCellClauses.lean`) at the guarded clause premises. -/
theorem binStrCmpCell_of_ownedNA (D : StrCmpOp) (C : D.Cert) (S : SharedFam)
    (hI : OwnedIndex S) (htop : SharedTopSlackAll S)
    (hCL : FootprintPayloadOwnedClauseNA S) (hCR : FootprintOwnedClauseNA S) :
    BinStrCmpCellNA D.op D.bres := by
  intro st d env el er st' st'' sl sr hgl hgr hEl hEr _ _
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact binRow_strcmpF_owned D C S hI htop g N A SL φf φc st st' st'' d env el er sl sr
    sp r sret aEnv aExpr m0 hEl (hCL st d env el st' (.str sl) hgl hEl)
    (hCR st' d env er st'' (.str sr) hgr hEr)
    (EvalE.binary st d env D.op el er st' st'' (.str sl) (.str sr) _ hEl hEr (C.sem _ _ _))
    |>.conseq (fun _ hp => hp) (fun _ hp => hp.result)

#print axioms EvalIHWithM.monoD
#print axioms valuePayloadCovered_of_payloadFree
#print axioms EvalIHFPO.of_footprint_payloadFree
#print axioms EvalIHFO.of_footprint_payloadFree
#print axioms EvalIHFPO.forgetCov
#print axioms EvalIHFPO.footprint
#print axioms evalStrProductIHF
#print axioms binStrCmpCellFPO
#print axioms binaryFootprintNA_of_product
#print axioms IHClauseGenericProduct.hInt
#print axioms IHClauseGenericProduct.hStr
#print axioms IHClauseGenericProduct.hBool
#print axioms IHClauseGenericProduct.hNull
#print axioms IHClauseGenericProduct.hNeg
#print axioms IHClauseGenericProduct.hNot
#print axioms IHClauseGenericProduct.hOrTrue
#print axioms IHClauseGenericProduct.hAndFalse
#print axioms IHClauseGenericProduct.hOrFalse
#print axioms IHClauseGenericProduct.hAndTrue
#print axioms IHClauseGenericProduct.hAssign
#print axioms IHClauseGenericProduct.hFn
#print axioms IHClauseGenericProduct.hCall
#print axioms IHClauseGenericProduct.hBinary
#print axioms not_sharedTopSlackAll_std
#print axioms astRegionSlack_forced
#print axioms sharedTopSlackAll_stdSlack
#print axioms ownedIndex_stdSlack
#print axioms footprintOwnedClauseNA_of_payload
#print axioms binStrCmpCell_of_ownedNA

end Vsa.Sim
