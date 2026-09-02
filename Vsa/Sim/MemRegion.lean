import Vsa.Sim.ReprSurvival

/-!
# `MemRegion` — the hereditary AST-region invariant (wave 47h, entry audit N3)

The 47g Law-4 verdict (`strpayloadgeom-supplier-verdict`) machine-checked that
NOTHING on main relates AST-node/string-payload addresses to `SL`/`sp`/`sret`:
`ExprRepr` is region-free, `StoreRepr` pins frames/closures only, the Layout is
abstract.  Every `*Extras`/`*Resid` bundle re-states per-node region facts by
hand (`NegExtras.op_lo/op_hi/op_stk/expr24_stk`, `StrLeafResid`'s payload
conjuncts, `BinArmExtras`' operand geometry, …) — the audited need class N3
(`experiments/entry-needs-audit.md`).

This module defines the ONE hereditary predicate those facts project from:

* `ExprIn m lo hi a e` / `StmtIn m lo hi a s` — every node of the tree rooted
  at machine address `a`, every array cell, and every string payload lies in
  `[lo, hi)`, 8-aligned.  Defined by STRUCTURAL recursion on the AST (the
  `bodiesBound` recursion shape), with all memory reads CONDITIONAL
  (`∀ p, read64 m … = some p → …`), so:
  - child extraction is DIRECT (apply the clause to the `ExprRepr`-witnessed
    payload read — no read-determinism lemma needed), and
  - the predicate never asserts reads succeed (`ExprRepr` supplies those).
* the transport theorems: agreement on `[lo, hi)` carries the whole invariant
  (`exprIn_agreeP`/`stmtIn_agreeP`).  NOTE the relation to the LANDED
  `AstTransport.lean`: `ExprFp`/`exprRepr_agreeP` transport the REPRESENTATION
  along its exact read footprint; `ExprIn` is the transport-closed REGION BOUND
  an entry can carry.  `NegExtras.expr_survives`-class residuals discharge by
  chaining them: `ExprIn` bounds the footprint inside `[lo, hi)`
  (`ExprFp ⊆ [lo,hi)` — the ONE bridging lemma, a bounded follow-up), then
  `exprRepr_agreeP` transports.
* the `.str`-root projection feeding `EvalEntryStrAstRegion`
  (`rows/Field_hStr.lean`) is in `EntryGround.lean` (needs the entry layer).

Region facts are PURE ARITHMETIC (`NodeIn`/`CellIn`/`StrIn` mention no
memory), so consumers get their disjointness/alignment conjuncts by `omega`
from the bundle bounds; only the tree-walk itself touches `m`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim

/-- A 40-byte AST node slot (`sizeof(Expr) = sizeof(Stmt) = 40`, `ast.h`
LP64: kind@0, line@4, union@8 with the widest arm `fn`/`for` ending at 40)
inside `[lo, hi)`, 8-aligned. -/
structure NodeIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 40 ≤ hi
  align : a % 8 = 0

/-- An 8-byte pointer-array cell inside `[lo, hi)`, 8-aligned. -/
structure CellIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 8 ≤ hi
  align : a % 8 = 0

/-- A NUL-terminated string payload of `s` at `p` inside `[lo, hi)`:
nonzero pointer, all `s.length` bytes AND the NUL inside the region. -/
structure StrIn (lo hi p : Nat) (s : String) : Prop where
  ne_zero : p ≠ 0
  lo_le : lo ≤ p
  hi_ge : p + s.length + 1 ≤ hi

/-- Parameter-name array (`char **`): each cell and each name string in
region. List-structural; no Expr/Stmt recursion. -/
def ParamsIn (m : Mem) (lo hi : Nat) : Nat → List String → Prop
  | _, [] => True
  | a, x :: xs =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StrIn lo hi p x) ∧
    ParamsIn m lo hi (a + 8) xs

mutual

/-- **Every node reachable from the `Expr` at `a` lives in `[lo, hi)`** —
node slots, array cells, string payloads, `.fn` bodies included.  Reads are
conditional; pair with `ExprRepr` for the actual pointer witnesses. -/
def ExprIn (m : Mem) (lo hi : Nat) : Nat → Expr → Prop
  | a, .int _ => NodeIn lo hi a
  | a, .str s => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p s)
  | a, .bool _ => NodeIn lo hi a
  | a, .null => NodeIn lo hi a
  | a, .var x => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x)
  | a, .assign x e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ExprIn m lo hi q e)
  | a, .binary _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .logical _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .unary _ e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p e)
  | a, .call f args => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p f) ∧
      (∀ q, read64 m (a + 16) = some q → ExprsIn m lo hi q args)
  | a, .fn ox ps ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → p ≠ 0 →
        ∀ x, ox = some x → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ParamsIn m lo hi q ps) ∧
      -- the body pointer holds a block node (`StmtRepr m body (.block ss)`):
      -- its node slot + statement array are in region, hereditarily.
      (∀ b, read64 m (a + 32) = some b → NodeIn lo hi b ∧
        (∀ q, read64 m (b + 8) = some q → StmtsIn m lo hi q ss))

/-- `Expr **` argument array: cells + pointed trees in region. -/
def ExprsIn (m : Mem) (lo hi : Nat) : Nat → List Expr → Prop
  | _, [] => True
  | a, e :: es =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → ExprIn m lo hi p e) ∧
    ExprsIn m lo hi (a + 8) es

/-- Optional expression stored as a pointer AT `addr` (the `OptExprRepr`
shape): `some e` ⇒ the pointed tree is in region. -/
def OptExprIn (m : Mem) (lo hi addr : Nat) : Option Expr → Prop
  | none => True
  | some e => ∀ p, read64 m addr = some p → p ≠ 0 → ExprIn m lo hi p e

/-- **Every node reachable from the `Stmt` at `a` lives in `[lo, hi)`.** -/
def StmtIn (m : Mem) (lo hi : Nat) : Nat → Stmt → Prop
  | a, .expr e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p e)
  | a, .varDecl x oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      OptExprIn m lo hi (a + 16) oe
  | a, .block ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StmtsIn m lo hi p ss)
  | a, .ifStmt c t oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p t) ∧
      OptStmtIn m lo hi (a + 24) oe
  | a, .whileStmt c b => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p b)
  | a, .forStmt oi oc os b => NodeIn lo hi a ∧
      OptStmtIn m lo hi (a + 8) oi ∧
      OptExprIn m lo hi (a + 16) oc ∧
      OptExprIn m lo hi (a + 24) os ∧
      (∀ p, read64 m (a + 32) = some p → StmtIn m lo hi p b)
  | a, .ret oe => NodeIn lo hi a ∧ OptExprIn m lo hi (a + 8) oe
  | a, .brk => NodeIn lo hi a
  | a, .cont => NodeIn lo hi a

/-- `Stmt **` array: cells + pointed trees in region. -/
def StmtsIn (m : Mem) (lo hi : Nat) : Nat → List Stmt → Prop
  | _, [] => True
  | a, s :: ss =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StmtIn m lo hi p s) ∧
    StmtsIn m lo hi (a + 8) ss

/-- Optional statement stored as a pointer AT `addr`. -/
def OptStmtIn (m : Mem) (lo hi addr : Nat) : Option Stmt → Prop
  | none => True
  | some s => ∀ p, read64 m addr = some p → p ≠ 0 → StmtIn m lo hi p s

end

/-! ## Transport: agreement on `[lo, hi)` carries the whole invariant

The read pointers in every clause target windows INSIDE `[lo, hi)` (node
fields by `NodeIn`, cells by `CellIn`), so all reads transfer by
`read64_agreeP` and the region facts themselves are memory-free. -/

/-- The region footprint as an `AgreeP` predicate. -/
def regionP (lo hi : Nat) : Nat → Prop := fun a => lo ≤ a ∧ a < hi

theorem read64_region {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') {a : Nat}
    (hlo : lo ≤ a) (hhi : a + 8 ≤ hi) : read64 m a = read64 m' a :=
  read64_agreeP h (fun k hk => ⟨by omega, by omega⟩)

/-- `ParamsIn` transports along region agreement. -/
theorem paramsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} {ps : List String}, ParamsIn m lo hi a ps → ParamsIn m' lo hi a ps
  | _, [], _ => trivial
  | a, _ :: _, ⟨hc, hs, hrest⟩ =>
    ⟨hc, fun p hp => hs p (by rwa [read64_region h hc.lo_le hc.hi_ge]),
      paramsIn_agreeP h hrest⟩

mutual

/-- **`ExprIn` transports along region agreement** (the region-bound twin of
`AstTransport.exprRepr_agreeP`, which transports the representation itself). -/
theorem exprIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (e : Expr), ExprIn m lo hi a e → ExprIn m' lo hi a e
  | _, .int _, hn => hn
  | _, .str _, ⟨hn, hs⟩ =>
    ⟨hn, fun p hp => hs p (by
      rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
        (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)⟩
  | _, .bool _, hn => hn
  | _, .null, hn => hn
  | _, .var _, ⟨hn, hs⟩ =>
    ⟨hn, fun p hp => hs p (by
      rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
        (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)⟩
  | _, .assign _ e, ⟨hn, hs, he⟩ =>
    ⟨hn, fun p hp => hs p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp),
      fun q hq => exprIn_agreeP h e (he q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq))⟩
  | _, .binary _ l r, ⟨hn, hl, hr⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h l (hl p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => exprIn_agreeP h r (hr p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .logical _ l r, ⟨hn, hl, hr⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h l (hl p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => exprIn_agreeP h r (hr p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .unary _ e, ⟨hn, he⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .call f args, ⟨hn, hf, ha⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h f (hf p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun q hq => exprsIn_agreeP h args (ha q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq))⟩
  | _, .fn _ ps ss, ⟨hn, hx, hps, hb⟩ =>
    ⟨hn, fun p hp hpne x hox => hx p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp) hpne x hox,
      fun q hq => paramsIn_agreeP h (hps q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq)),
      fun b hb' => by
        have hb0 := hb b (by
          rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
            (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hb')
        exact ⟨hb0.1, fun q hq => stmtsIn_agreeP h ss (hb0.2 q (by
          rw [read64_region h (show lo ≤ _ by have := hb0.1.lo_le; omega)
            (show _ + 8 ≤ hi by have := hb0.1.hi_ge; omega)]; exact hq))⟩⟩

theorem exprsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (es : List Expr), ExprsIn m lo hi a es → ExprsIn m' lo hi a es
  | _, [], _ => trivial
  | _, e :: es, ⟨hc, he, hrest⟩ =>
    ⟨hc, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h hc.lo_le hc.hi_ge]; exact hp)),
      exprsIn_agreeP h es hrest⟩

theorem optExprIn_agreeP {lo hi addr : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m')
    (hlo : lo ≤ addr) (hhi : addr + 8 ≤ hi) :
    ∀ (oe : Option Expr), OptExprIn m lo hi addr oe → OptExprIn m' lo hi addr oe
  | none, _ => trivial
  | some e, he => fun p hp hpne =>
      exprIn_agreeP h e (he p (by rw [read64_region h hlo hhi]; exact hp) hpne)

theorem stmtIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (s : Stmt), StmtIn m lo hi a s → StmtIn m' lo hi a s
  | _, .expr e, ⟨hn, he⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .varDecl _ oe, ⟨hn, hs, hoe⟩ =>
    ⟨hn, fun p hp => hs p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp),
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .block ss, ⟨hn, hss⟩ =>
    ⟨hn, fun p hp => stmtsIn_agreeP h ss (hss p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .ifStmt c t oe, ⟨hn, hcnd, ht, hoe⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h c (hcnd p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => stmtIn_agreeP h t (ht p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      optStmtIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .whileStmt c b, ⟨hn, hcnd, hb⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h c (hcnd p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => stmtIn_agreeP h b (hb p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .forStmt oi oc os b, ⟨hn, hoi, hoc, hos, hb⟩ =>
    ⟨hn,
      optStmtIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oi hoi,
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oc hoc,
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) os hos,
      fun p hp => stmtIn_agreeP h b (hb p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .ret oe, ⟨hn, hoe⟩ =>
    ⟨hn, optExprIn_agreeP h (by have := hn.lo_le; omega)
      (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .brk, hn => hn
  | _, .cont, hn => hn

theorem stmtsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (ss : List Stmt), StmtsIn m lo hi a ss → StmtsIn m' lo hi a ss
  | _, [], _ => trivial
  | _, s :: ss, ⟨hc, hs, hrest⟩ =>
    ⟨hc, fun p hp => stmtIn_agreeP h s (hs p (by
        rw [read64_region h hc.lo_le hc.hi_ge]; exact hp)),
      stmtsIn_agreeP h ss hrest⟩

theorem optStmtIn_agreeP {lo hi addr : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m')
    (hlo : lo ≤ addr) (hhi : addr + 8 ≤ hi) :
    ∀ (os : Option Stmt), OptStmtIn m lo hi addr os → OptStmtIn m' lo hi addr os
  | none, _ => trivial
  | some s, hs => fun p hp hpne =>
      stmtIn_agreeP h s (hs p (by rw [read64_region h hlo hhi]; exact hp) hpne)

end

/-! ## Root projections (the audited consumers' shapes)

Child projections for the recursive arms (`unary`/`binary`/…) are DIRECT
applications of the corresponding clause — no lemma needed; stated here only
for the shapes the landed rows consume. -/

/-- The `.str`-root payload facts — exactly the `StrPayloadIn` shape of
`rows/Field_hStr.lean` (its `p + s.length < hi` is implied by `StrIn`'s
NUL-inclusive bound). -/
theorem exprIn_str_payload {m : Mem} {lo hi a : Nat} {s : String}
    (h : ExprIn m lo hi a (.str s)) :
    ∀ p, read64 m (a + 8) = some p → p ≠ 0 ∧ lo ≤ p ∧ p + s.length < hi := by
  intro p hp
  have := h.2 p hp
  exact ⟨this.ne_zero, this.lo_le, by have := this.hi_ge; omega⟩

/-- The `.var`-root name-string facts (the `VarLeafResid` conjunct-1 shape). -/
theorem exprIn_var_payload {m : Mem} {lo hi a : Nat} {x : String}
    (h : ExprIn m lo hi a (.var x)) :
    ∀ p, read64 m (a + 8) = some p → p ≠ 0 ∧ lo ≤ p ∧ p + x.length < hi := by
  intro p hp
  have := h.2 p hp
  exact ⟨this.ne_zero, this.lo_le, by have := this.hi_ge; omega⟩

/-- The `.unary`-root operand projection (the `NegExtras` operand-geometry
shape): the operand node is a region-pinned tree. -/
theorem exprIn_unary_child {m : Mem} {lo hi a : Nat} {op : UnOp} {e : Expr}
    (h : ExprIn m lo hi a (.unary op e)) :
    ∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p e :=
  h.2

/-- Root node region facts for any expression (all 11 constructors carry a
leading `NodeIn`). -/
theorem exprIn_node {m : Mem} {lo hi a : Nat} {e : Expr}
    (h : ExprIn m lo hi a e) : NodeIn lo hi a := by
  cases e with
  | int _ => exact h
  | str _ => exact h.1
  | bool _ => exact h
  | null => exact h
  | var _ => exact h.1
  | assign _ _ => exact h.1
  | binary _ _ _ => exact h.1
  | logical _ _ _ => exact h.1
  | unary _ _ => exact h.1
  | call _ _ => exact h.1
  | fn _ _ _ => exact h.1

/-- Root node region facts for any statement. -/
theorem stmtIn_node {m : Mem} {lo hi a : Nat} {s : Stmt}
    (h : StmtIn m lo hi a s) : NodeIn lo hi a := by
  cases s with
  | expr _ => exact h.1
  | varDecl _ _ => exact h.1
  | block _ => exact h.1
  | ifStmt _ _ _ => exact h.1
  | whileStmt _ _ => exact h.1
  | forStmt _ _ _ _ => exact h.1
  | ret _ => exact h.1
  | brk => exact h
  | cont => exact h

end Vsa.Sim
