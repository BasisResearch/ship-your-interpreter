import Vsa.MemRepr
import Vsa.Sim.MemRegion
import Vsa.Sim.ReprSurvival

/-!
# Layer-2 — AST-representation transport under memory agreement

`ExprRepr`/`StmtRepr` (and every relation the mutual block recurses through:
`ExprArrayRepr`, `ParamsRepr`, `OptStmtRepr`, `OptExprRepr`, `StmtArrayRepr`)
are conjunctions of byte-level `read32`/`read64`/`CString`/child-`Repr` facts.
Any memory change that **agrees byte-for-byte on the addresses the derivation
actually reads** leaves the whole tree intact.

This is the AST analogue of `Vsa/Sim/ReprSurvival.lean`'s `valueRepr_agreeP` /
`storeRepr_agreeP`: it discharges the recurring `exprRepr_agreeP` /
`stmtRepr_agreeP` residual that nearly every recursive expression/statement
case carries (the AST survives the memory writes a sub-call performs, because
the AST region is disjoint from the runtime write windows).

## The footprint

The footprint of a representation is not a single contiguous window: nested
sub-`Expr`/`Stmt` nodes and dereferenced `char*` strings live at pointers read
out of `m`, and may sit anywhere in the loaded image. We therefore define the
footprint as an inductive membership predicate `ExprFp m a e` (and its six
siblings), mirroring each constructor's reads exactly:

* the node's own `read32`/`read64` tag/pointer/count windows `[a+off, a+off+k)`;
* for string-carrying nodes, the dereferenced `char*` byte range
  `[p, p + s.length]` (through the NUL), where `p = read64 m (a+8)` etc.;
* recursively, the footprint of every child, rooted at the child pointer the
  node reads out of `m`.

`AgreeP P m m'` (from `ReprSurvival`) plus `∀ addr, ExprFp m a e addr → P addr`
then transports `ExprRepr m a e` to `ExprRepr m' a e`.

## How callers consume it

The cases carry agreement over the complement of a contiguous runtime write
window `W` — `AgreeP (fun a => ¬ (W.lo ≤ a ∧ a < W.hi)) m m'`. When the AST
region is disjoint from `W` (the AST lives in `.rodata`/heap, the writes land
on the stack/arena), `∀ addr, ExprFp m a e addr → ¬ (W.lo ≤ addr ∧ addr < W.hi)`
follows from that disjointness, and the transport lemma delivers the survived
`ExprRepr`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.MemRepr
open Vsa.While

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## Footprint membership predicates

For a fixed source memory `m`, `ExprFp m a e addr` says `addr` is one of the
bytes `ExprRepr m a e`'s derivation reads. Pointer/count values are taken from
`m` (via the same `read*` the constructor uses), so the footprint is exactly
the set the representation touches. -/

mutual

inductive ExprStrAt8 : Expr → String → Prop where
  | str (s) : ExprStrAt8 (.str s) s
  | var (x) : ExprStrAt8 (.var x) x
  | assign (x) (e) : ExprStrAt8 (.assign x e) x
  | fnNamed (x) (ps) (ss) : ExprStrAt8 (.fn (some x) ps ss) x

inductive ExprChildAt8 : Expr → Expr → Prop where
  | call (f) (args) : ExprChildAt8 (.call f args) f

inductive ExprChildAt16 : Expr → Expr → Prop where
  | assign (x) (e) : ExprChildAt16 (.assign x e) e
  | binary (op) (l) (r) : ExprChildAt16 (.binary op l r) l
  | logical (op) (l) (r) : ExprChildAt16 (.logical op l r) l
  | unary (op) (e) : ExprChildAt16 (.unary op e) e

inductive ExprChildAt24 : Expr → Expr → Prop where
  | binary (op) (l) (r) : ExprChildAt24 (.binary op l r) r
  | logical (op) (l) (r) : ExprChildAt24 (.logical op l r) r

inductive ExprArgsAt16 : Expr → List Expr → Prop where
  | call (f) (args) : ExprArgsAt16 (.call f args) args

inductive ExprParamsAt16 : Expr → List String → Prop where
  | fn (name) (ps) (ss) : ExprParamsAt16 (.fn name ps ss) ps

inductive ExprBodyAt32 : Expr → List Stmt → Prop where
  | fn (name) (ps) (ss) : ExprBodyAt32 (.fn name ps ss) ss

inductive StmtStrAt8 : Stmt → String → Prop where
  | varDecl (x) (oe) : StmtStrAt8 (.varDecl x oe) x

inductive StmtExprAt8 : Stmt → Expr → Prop where
  | expr (e) : StmtExprAt8 (.expr e) e
  | ifStmt (c) (t) (oe) : StmtExprAt8 (.ifStmt c t oe) c
  | whileStmt (c) (b) : StmtExprAt8 (.whileStmt c b) c
  | ret (e) : StmtExprAt8 (.ret (some e)) e

inductive StmtExprAt16 : Stmt → Expr → Prop where
  | varDecl (x) (e) : StmtExprAt16 (.varDecl x (some e)) e

inductive StmtChildAt16 : Stmt → Stmt → Prop where
  | ifStmt (c) (t) (oe) : StmtChildAt16 (.ifStmt c t oe) t
  | whileStmt (c) (b) : StmtChildAt16 (.whileStmt c b) b

inductive StmtChildAt24 : Stmt → Stmt → Prop where
  | ifStmt (c) (t) (e) : StmtChildAt24 (.ifStmt c t (some e)) e

inductive StmtChildAt32 : Stmt → Stmt → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtChildAt32 (.forStmt oi oc os b) b

inductive StmtBlockAt8 : Stmt → List Stmt → Prop where
  | block (ss) : StmtBlockAt8 (.block ss) ss

inductive StmtOptStmtAt8 : Stmt → Option Stmt → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptStmtAt8 (.forStmt oi oc os b) oi

inductive StmtOptExprAt16 : Stmt → Option Expr → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptExprAt16 (.forStmt oi oc os b) oc

inductive StmtOptExprAt24 : Stmt → Option Expr → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptExprAt24 (.forStmt oi oc os b) os

end

mutual

/-- `addr` is read by `ExprRepr m a e`. -/
inductive ExprFp (m : Mem) : Nat → Expr → Nat → Prop where
  | tag {a : Nat} {e : Expr} {k : Nat} : k < 4 → ExprFp m a e (a + k)
  -- payload / pointer / count windows (offset 8, plus 16/24/32 for children)
  | off8 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 8 + k)
  | off16 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 16 + k)
  | off24 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 24 + k)
  | off32 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 32 + k)
  -- string bytes for a `char*` at offset 8 (str/var/assign-name/fn-name)
  | str8 {a : Nat} {e : Expr} {s : String} {p k : Nat} :
    ExprStrAt8 e s → read64 m (a + 8) = some p → k ≤ s.length →
    ExprFp m a e (p + k)
  -- child expr at offset 8 (call fn), 16 (assign/binary/logical/unary l), 24 (binary/logical r)
  | child8 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt8 e ec → read64 m (a + 8) = some p →
    ExprFp m p ec addr → ExprFp m a e addr
  | child16 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt16 e ec → read64 m (a + 16) = some p →
    ExprFp m p ec addr → ExprFp m a e addr
  | child24 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt24 e ec → read64 m (a + 24) = some p →
    ExprFp m p ec addr → ExprFp m a e addr
  -- call arg array at offset 16
  | argArr {a : Nat} {e : Expr} {args argc addr : Nat} {es : List Expr} :
    ExprArgsAt16 e es → read64 m (a + 16) = some args →
    ExprArrayFp m args argc es addr → ExprFp m a e addr
  -- fn params array at offset 16, body block at offset 32
  | paramsArr {a : Nat} {e : Expr} {params paramc addr : Nat} {ps : List String} :
    ExprParamsAt16 e ps → read64 m (a + 16) = some params →
    ParamsFp m params paramc ps addr → ExprFp m a e addr
  | body32 {a : Nat} {e : Expr} {body addr : Nat} {ss : List Stmt} :
    ExprBodyAt32 e ss → read64 m (a + 32) = some body →
    StmtFp m body (.block ss) addr → ExprFp m a e addr

/-- `addr` is read by `ExprArrayRepr m a n es`. -/
inductive ExprArrayFp (m : Mem) : Nat → Nat → List Expr → Nat → Prop where
  | slot {a n : Nat} {e : Expr} {es : List Expr} {k : Nat} : k < 8 →
    ExprArrayFp m a (n + 1) (e :: es) (a + k)
  | elem {a p n addr : Nat} {e : Expr} {es : List Expr} :
    read64 m a = some p → ExprFp m p e addr →
    ExprArrayFp m a (n + 1) (e :: es) addr
  | tail {a n addr : Nat} {e : Expr} {es : List Expr} :
    ExprArrayFp m (a + 8) n es addr → ExprArrayFp m a (n + 1) (e :: es) addr

/-- `addr` is read by `ParamsRepr m a n xs`. -/
inductive ParamsFp (m : Mem) : Nat → Nat → List String → Nat → Prop where
  | slot {a n : Nat} {x : String} {xs : List String} {k : Nat} : k < 8 →
    ParamsFp m a (n + 1) (x :: xs) (a + k)
  | str {a p n k : Nat} {x : String} {xs : List String} :
    read64 m a = some p → k ≤ x.length →
    ParamsFp m a (n + 1) (x :: xs) (p + k)
  | tail {a n addr : Nat} {x : String} {xs : List String} :
    ParamsFp m (a + 8) n xs addr → ParamsFp m a (n + 1) (x :: xs) addr

/-- `addr` is read by `StmtRepr m a s`. -/
inductive StmtFp (m : Mem) : Nat → Stmt → Nat → Prop where
  | tag {a : Nat} {s : Stmt} {k : Nat} : k < 4 → StmtFp m a s (a + k)
  | off8 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 8 + k)
  | off16 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 16 + k)
  | off24 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 24 + k)
  | off32 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 32 + k)
  -- name string for a `char*` at offset 8 (var decl)
  | str8 {a : Nat} {s : Stmt} {x : String} {p k : Nat} :
    StmtStrAt8 s x → read64 m (a + 8) = some p → k ≤ x.length →
    StmtFp m a s (p + k)
  -- expr children at offsets 8 (if/while cond, expr stmt), 16 (var-init value)
  | expr8 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    StmtExprAt8 s e → read64 m (a + 8) = some p →
    ExprFp m p e addr → StmtFp m a s addr
  | expr16 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    StmtExprAt16 s e → read64 m (a + 16) = some p →
    ExprFp m p e addr → StmtFp m a s addr
  -- stmt children at offsets 8 (block array via count@16), 16 (if-then, while body),
  -- 24 (if-else), 32 (for body)
  | stmt16 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt16 s t → read64 m (a + 16) = some p →
    StmtFp m p t addr → StmtFp m a s addr
  | stmt24 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt24 s t → read64 m (a + 24) = some p →
    StmtFp m p t addr → StmtFp m a s addr
  | stmt32 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt32 s t → read64 m (a + 32) = some p →
    StmtFp m p t addr → StmtFp m a s addr
  -- block: stmt array at offset 8, count at offset 16
  | blockArr {a : Nat} {s : Stmt} {stmts count addr : Nat} {ss : List Stmt} :
    StmtBlockAt8 s ss → read64 m (a + 8) = some stmts →
    StmtArrayFp m stmts count ss addr → StmtFp m a s addr
  -- for-loop optional init (stmt) at offset 8, optional cond/step (expr) at 16/24
  | optStmt8 {a : Nat} {s : Stmt} {os : Option Stmt} {addr : Nat} :
    StmtOptStmtAt8 s os → OptStmtFp m (a + 8) os addr → StmtFp m a s addr
  | optExpr16 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    StmtOptExprAt16 s oe → OptExprFp m (a + 16) oe addr → StmtFp m a s addr
  | optExpr24 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    StmtOptExprAt24 s oe → OptExprFp m (a + 24) oe addr → StmtFp m a s addr

/-- `addr` is read by `OptStmtRepr m a os`. -/
inductive OptStmtFp (m : Mem) : Nat → Option Stmt → Nat → Prop where
  | ptr {a : Nat} {os : Option Stmt} {k : Nat} : k < 8 → OptStmtFp m a os (a + k)
  | child {a p addr : Nat} {s : Stmt} :
    read64 m a = some p → StmtFp m p s addr → OptStmtFp m a (some s) addr

/-- `addr` is read by `OptExprRepr m a oe`. -/
inductive OptExprFp (m : Mem) : Nat → Option Expr → Nat → Prop where
  | ptr {a : Nat} {oe : Option Expr} {k : Nat} : k < 8 → OptExprFp m a oe (a + k)
  | child {a p addr : Nat} {e : Expr} :
    read64 m a = some p → ExprFp m p e addr → OptExprFp m a (some e) addr

/-- `addr` is read by `StmtArrayRepr m a n ss`. -/
inductive StmtArrayFp (m : Mem) : Nat → Nat → List Stmt → Nat → Prop where
  | slot {a n : Nat} {s : Stmt} {ss : List Stmt} {k : Nat} : k < 8 →
    StmtArrayFp m a (n + 1) (s :: ss) (a + k)
  | elem {a p n addr : Nat} {s : Stmt} {ss : List Stmt} :
    read64 m a = some p → StmtFp m p s addr →
    StmtArrayFp m a (n + 1) (s :: ss) addr
  | tail {a n addr : Nat} {s : Stmt} {ss : List Stmt} :
    StmtArrayFp m (a + 8) n ss addr → StmtArrayFp m a (n + 1) (s :: ss) addr

end

/-! ## The representation footprint is contained in its hereditary region -/

private def R1 (m : Mem) (lo hi : Nat) :
    (a : Nat) → (e : Expr) → (addr : Nat) → ExprFp m a e addr → Prop :=
  fun a e addr _ => ExprIn m lo hi a e → lo ≤ addr ∧ addr < hi
private def R2 (m : Mem) (lo hi : Nat) :
    (a n : Nat) → (es : List Expr) → (addr : Nat) → ExprArrayFp m a n es addr → Prop :=
  fun a _ es addr _ => ExprsIn m lo hi a es → lo ≤ addr ∧ addr < hi
private def R3 (m : Mem) (lo hi : Nat) :
    (a n : Nat) → (xs : List String) → (addr : Nat) → ParamsFp m a n xs addr → Prop :=
  fun a _ xs addr _ => ParamsIn m lo hi a xs → lo ≤ addr ∧ addr < hi
private def R4 (m : Mem) (lo hi : Nat) :
    (a : Nat) → (s : Stmt) → (addr : Nat) → StmtFp m a s addr → Prop :=
  fun a s addr _ => StmtIn m lo hi a s → lo ≤ addr ∧ addr < hi
private def R5 (m : Mem) (lo hi : Nat) :
    (a : Nat) → (os : Option Stmt) → (addr : Nat) → OptStmtFp m a os addr → Prop :=
  fun a os addr _ => OptStmtIn m lo hi a os → lo ≤ addr ∧ addr < hi
private def R6 (m : Mem) (lo hi : Nat) :
    (a : Nat) → (oe : Option Expr) → (addr : Nat) → OptExprFp m a oe addr → Prop :=
  fun a oe addr _ => OptExprIn m lo hi a oe → lo ≤ addr ∧ addr < hi
private def R7 (m : Mem) (lo hi : Nat) :
    (a n : Nat) → (ss : List Stmt) → (addr : Nat) → StmtArrayFp m a n ss addr → Prop :=
  fun a _ ss addr _ => StmtsIn m lo hi a ss → lo ≤ addr ∧ addr < hi

/-- Every byte read by a statement representation lies in its hereditary AST
region. The shared mutual recursor proves the corresponding internal facts for
expression children, arrays, parameters, and optional children. -/
theorem stmtFp_region {m : Mem} {lo hi a addr : Nat} {s : Stmt}
    (hfp : StmtFp m a s addr) (hin : StmtIn m lo hi a s) :
    lo ≤ addr ∧ addr < hi := by
  have key : R4 m lo hi a s addr hfp := by
    refine hfp.rec
      (motive_1 := R1 m lo hi) (motive_2 := R2 m lo hi)
      (motive_3 := R3 m lo hi) (motive_4 := R4 m lo hi)
      (motive_5 := R5 m lo hi) (motive_6 := R6 m lo hi)
      (motive_7 := R7 m lo hi)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [R1, R2, R3, R4, R5, R6, R7]
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e str p k hkind hp hk hin
      cases hkind with
      | str s =>
          rcases hin.2 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | var x =>
          rcases hin.2 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | assign x e =>
          rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | fnNamed x ps ss =>
          rcases hin.2.1 _ hp _ rfl with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind
      exact ih (hin.2.1 _ hp)
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind with
      | assign x e => exact ih (hin.2.2 _ hp)
      | binary op l r => exact ih (hin.2.1 _ hp)
      | logical op l r => exact ih (hin.2.1 _ hp)
      | unary op e => exact ih (hin.2 _ hp)
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind <;> simp only [ExprIn] at hin
      all_goals exact ih (hin.2.2 _ hp)
    · intro a e args argc addr es hkind hp ha ih hin
      cases hkind
      exact ih (hin.2.2 _ hp)
    · intro a e params paramc addr ps hkind hp hps ih hin
      cases hkind
      exact ih (hin.2.2.1 _ hp)
    · intro a e body addr ss hkind hp hb ih hin
      cases hkind
      have hbody := hin.2.2.2 _ hp
      exact ih ⟨hbody.1, hbody.2⟩
    · intro a n e es k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n addr e es hp he ih hin
      exact ih (hin.2.1 _ hp)
    · intro a n addr e es ht ih hin
      exact ih hin.2.2
    · intro a n x xs k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n k x xs hp hk hin
      rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a n addr x xs ht ih hin
      exact ih hin.2.2
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s x p k hkind hp hk hin
      cases hkind
      rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s p addr e hkind hp he ih hin
      cases hkind with
      | expr e => exact ih (hin.2 _ hp)
      | ifStmt c t oe => exact ih (hin.2.1 _ hp)
      | whileStmt c b => exact ih (hin.2.1 _ hp)
      | ret e => exact ih (hin.2.2 _ hp)
    · intro a s p addr e hkind hp he ih hin
      cases hkind
      exact ih (hin.2.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind with
      | ifStmt c t oe => exact ih (hin.2.2.1 _ hp)
      | whileStmt c b => exact ih (hin.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind
      exact ih (hin.2.2.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind
      exact ih (hin.2.2.2.2 _ hp)
    · intro a s stmts count addr ss hkind hp hss ih hin
      cases hkind
      exact ih (hin.2 _ hp)
    · intro a s os addr hkind ho ih hin
      cases hkind
      exact ih hin.2.1
    · intro a s oe addr hkind ho ih hin
      cases hkind
      exact ih hin.2.2.1
    · intro a s oe addr hkind ho ih hin
      cases hkind
      exact ih hin.2.2.2.1
    · intro a os k hk hin
      cases os with
      | none => rcases hin with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
      | some s => rcases hin.1 with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · intro a p addr s hp hs ih hin
      exact ih (hin.2 _ hp)
    · intro a oe k hk hin
      cases oe with
      | none => rcases hin with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
      | some e => rcases hin.1 with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · intro a p addr e hp he ih hin
      exact ih (hin.2 _ hp)
    · intro a n s ss k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n addr s ss hp hs ih hin
      exact ih (hin.2.1 _ hp)
    · intro a n addr s ss ht ih hin
      exact ih hin.2.2
  exact key hin

/-- Every byte read by an expression representation lies in its hereditary
AST region. This is the expression-root projection of the same mutual
footprint recursion used by `stmtFp_region`. -/
theorem exprFp_region {m : Mem} {lo hi a addr : Nat} {e : Expr}
    (hfp : ExprFp m a e addr) (hin : ExprIn m lo hi a e) :
    lo ≤ addr ∧ addr < hi := by
  have key : R1 m lo hi a e addr hfp := by
    refine hfp.rec
      (motive_1 := R1 m lo hi) (motive_2 := R2 m lo hi)
      (motive_3 := R3 m lo hi) (motive_4 := R4 m lo hi)
      (motive_5 := R5 m lo hi) (motive_6 := R6 m lo hi)
      (motive_7 := R7 m lo hi)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [R1, R2, R3, R4, R5, R6, R7]
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e k hk hin
      rcases exprIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a e str p k hkind hp hk hin
      cases hkind with
      | str s =>
          rcases hin.2 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | var x =>
          rcases hin.2 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | assign x e =>
          rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
      | fnNamed x ps ss =>
          rcases hin.2.1 _ hp _ rfl with ⟨_, hlo, hhi⟩
          exact ⟨by omega, by omega⟩
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind
      exact ih (hin.2.1 _ hp)
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind with
      | assign x e => exact ih (hin.2.2 _ hp)
      | binary op l r => exact ih (hin.2.1 _ hp)
      | logical op l r => exact ih (hin.2.1 _ hp)
      | unary op e => exact ih (hin.2 _ hp)
    · intro a e ec p addr hkind hp hc ih hin
      cases hkind <;> simp only [ExprIn] at hin
      all_goals exact ih (hin.2.2 _ hp)
    · intro a e args argc addr es hkind hp ha ih hin
      cases hkind
      exact ih (hin.2.2 _ hp)
    · intro a e params paramc addr ps hkind hp hps ih hin
      cases hkind
      exact ih (hin.2.2.1 _ hp)
    · intro a e body addr ss hkind hp hb ih hin
      cases hkind
      have hbody := hin.2.2.2 _ hp
      exact ih ⟨hbody.1, hbody.2⟩
    · intro a n e es k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n addr e es hp he ih hin
      exact ih (hin.2.1 _ hp)
    · intro a n addr e es ht ih hin
      exact ih hin.2.2
    · intro a n x xs k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n k x xs hp hk hin
      rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a n addr x xs ht ih hin
      exact ih hin.2.2
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s k hk hin
      rcases stmtIn_node hin with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s x p k hkind hp hk hin
      cases hkind
      rcases hin.2.1 _ hp with ⟨_, hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a s p addr e hkind hp he ih hin
      cases hkind with
      | expr e => exact ih (hin.2 _ hp)
      | ifStmt c t oe => exact ih (hin.2.1 _ hp)
      | whileStmt c b => exact ih (hin.2.1 _ hp)
      | ret e => exact ih (hin.2.2 _ hp)
    · intro a s p addr e hkind hp he ih hin
      cases hkind
      exact ih (hin.2.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind with
      | ifStmt c t oe => exact ih (hin.2.2.1 _ hp)
      | whileStmt c b => exact ih (hin.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind
      exact ih (hin.2.2.2.2 _ hp)
    · intro a s p addr t hkind hp ht ih hin
      cases hkind
      exact ih (hin.2.2.2.2 _ hp)
    · intro a s stmts count addr ss hkind hp hss ih hin
      cases hkind
      exact ih (hin.2 _ hp)
    · intro a s os addr hkind ho ih hin
      cases hkind
      exact ih hin.2.1
    · intro a s oe addr hkind ho ih hin
      cases hkind
      exact ih hin.2.2.1
    · intro a s oe addr hkind ho ih hin
      cases hkind
      exact ih hin.2.2.2.1
    · intro a os k hk hin
      cases os with
      | none => rcases hin with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
      | some s => rcases hin.1 with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · intro a p addr s hp hs ih hin
      exact ih (hin.2 _ hp)
    · intro a oe k hk hin
      cases oe with
      | none => rcases hin with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
      | some e => rcases hin.1 with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · intro a p addr e hp he ih hin
      exact ih (hin.2 _ hp)
    · intro a n s ss k hk hin
      rcases hin.1 with ⟨hlo, hhi⟩
      exact ⟨by omega, by omega⟩
    · intro a p n addr s ss hp hs ih hin
      exact ih (hin.2.1 _ hp)
    · intro a n addr s ss ht ih hin
      exact ih hin.2.2
  exact key hin

/-! ## Transport lemmas

The single mutual induction over the `*Repr` derivations. Each motive says:
"given `AgreeP P m m'` and that `P` covers this node's footprint, the `*Repr`
transfers to `m'`". The read-window side conditions are discharged by
`read32_agreeP`/`read64_agreeP`/`cstring_agreeP` on the appropriate footprint
constructor; child obligations come from the recursor's IHs.

`astTransport_all` bundles all seven motives (one per relation) and is proved by
a single pass over the shared minor premises; the public single-relation lemmas
`exprRepr_agreeP` (motive 1) and `stmtRepr_agreeP` (motive 4) are its
projections. -/

section Transport

variable {P : Nat → Prop} {m m' : Mem}

/-- The seven motives of the mutual recursor, packaged so `ExprRepr.rec` and its
siblings can share one minor-premise bundle. Each says: *if `P` covers this
relation's footprint, the relation transfers to `m'`.* -/
private def M1 (_h : AgreeP P m m') : (a : Nat) → (e : Expr) → ExprRepr m a e → Prop :=
  fun a e _ => (∀ addr, ExprFp m a e addr → P addr) → ExprRepr m' a e
private def M2 (_h : AgreeP P m m') : (a n : Nat) → (es : List Expr) → ExprArrayRepr m a n es → Prop :=
  fun a n es _ => (∀ addr, ExprArrayFp m a n es addr → P addr) → ExprArrayRepr m' a n es
private def M3 (_h : AgreeP P m m') : (a n : Nat) → (xs : List String) → ParamsRepr m a n xs → Prop :=
  fun a n xs _ => (∀ addr, ParamsFp m a n xs addr → P addr) → ParamsRepr m' a n xs
private def M4 (_h : AgreeP P m m') : (a : Nat) → (s : Stmt) → StmtRepr m a s → Prop :=
  fun a s _ => (∀ addr, StmtFp m a s addr → P addr) → StmtRepr m' a s
private def M5 (_h : AgreeP P m m') : (a : Nat) → (os : Option Stmt) → OptStmtRepr m a os → Prop :=
  fun a os _ => (∀ addr, OptStmtFp m a os addr → P addr) → OptStmtRepr m' a os
private def M6 (_h : AgreeP P m m') : (a : Nat) → (oe : Option Expr) → OptExprRepr m a oe → Prop :=
  fun a oe _ => (∀ addr, OptExprFp m a oe addr → P addr) → OptExprRepr m' a oe
private def M7 (_h : AgreeP P m m') : (a n : Nat) → (ss : List Stmt) → StmtArrayRepr m a n ss → Prop :=
  fun a n ss _ => (∀ addr, StmtArrayFp m a n ss addr → P addr) → StmtArrayRepr m' a n ss

/-- **`ExprRepr` transport under memory agreement.** If `m` and `m'` agree on
every address `ExprRepr m a e`'s derivation reads (its footprint `ExprFp m a e`),
then `ExprRepr m' a e`. Discharges the recursive expression cases'
`exprRepr_agreeP` residual. Proved by `ExprRepr.rec` over the seven mutual
motives; every `read32`/`read64`/`readI64`/`CString` fact transfers via the
matching footprint constructor and every child via its IH. -/
theorem exprRepr_agreeP (h : AgreeP P m m') {a : Nat} {e : Expr}
    (hfp : ∀ addr, ExprFp m a e addr → P addr) (he : ExprRepr m a e) :
    ExprRepr m' a e := by
  have key : M1 h a e he := by
    refine he.rec
      (motive_1 := M1 h) (motive_2 := M2 h) (motive_3 := M3 h) (motive_4 := M4 h)
      (motive_5 := M5 h) (motive_6 := M6 h) (motive_7 := M7 h)
      ?exprInt ?exprStr ?exprBoolT ?exprBoolF ?exprNull ?exprVar ?exprAssign
      ?exprBinary ?exprLogical ?exprUnary ?exprCall ?exprFnNamed ?exprFnAnon
      ?arrNil ?arrCons ?parNil ?parCons
      ?stExpr ?stVarInit ?stVarNull ?stBlock ?stIfElse ?stIfNoElse ?stWhile ?stFor
      ?stRetSome ?stRetNone ?stBrk ?stCont
      ?optSNone ?optSSome ?optENone ?optESome ?saNil ?saCons
    all_goals (simp only [M1, M2, M3, M4, M5, M6, M7])
    case exprInt =>
      intro a n hk hn
      intro hfp
      exact ExprRepr.int
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← readI64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hn)
    case exprStr =>
      intro a p s hk hp hcs
      intro hfp
      exact ExprRepr.str
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
    case exprBoolT =>
      intro a b hk hb hbne
      intro hfp
      exact ExprRepr.boolTrue
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hb) hbne
    case exprBoolF =>
      intro a hk hb
      intro hfp
      exact ExprRepr.boolFalse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hb)
    case exprNull =>
      intro a hk
      intro hfp
      exact ExprRepr.null (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    case exprVar =>
      intro a p x hk hp hcs
      intro hfp
      exact ExprRepr.var
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
    case exprAssign =>
      intro a p q x ee hk hp hcs hq hee ih
      intro hfp
      exact ExprRepr.assign
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
        (ih (fun addr ha => hfp _ (.child16 (by constructor) hq ha)))
    case exprBinary =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.binary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 (by constructor) hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 (by constructor) hr ha)))
    case exprLogical =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.logical
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 (by constructor) hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 (by constructor) hr ha)))
    case exprUnary =>
      intro a p op ee hk hop hp hee ih
      intro hfp
      exact ExprRepr.unary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.child16 (by constructor) hp ha)))
    case exprCall =>
      intro a f args argc ef es hk hf hef hargs hargc hargcSigned harr ihf iharr
      intro hfp
      exact ExprRepr.call
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hf)
        (ihf (fun addr ha => hfp _ (.child8 (by constructor) hf ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hargs)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hargc)
        hargcSigned
        (iharr (fun addr ha => hfp _ (.argArr (by constructor) hargs ha)))
    case exprFnNamed =>
      intro a p params paramc body x ps ss hk hp hpne hcs hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnNamed
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr (by constructor) hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 (by constructor) hbody ha)))
    case exprFnAnon =>
      intro a params paramc body ps ss hk hp hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnAnon
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr (by constructor) hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 (by constructor) hbody ha)))
    -- ===== ExprArrayRepr =====
    case arrNil => intro _ _; exact ExprArrayRepr.nil
    case arrCons =>
      intro a p n ee es hp hee harr ih ihtail
      intro hfp
      exact ExprArrayRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.elem hp ha)))
        (ihtail (fun addr ha => hfp _ (.tail ha)))
    -- ===== ParamsRepr =====
    case parNil => intro _ _; exact ParamsRepr.nil
    case parCons =>
      intro a p n x xs hp hcs hpr ih
      intro hfp
      exact ParamsRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str hp (by omega))))
        (ih (fun addr ha => hfp _ (.tail ha)))
    -- ===== StmtRepr =====
    case stExpr =>
      intro a p ee hk hp hee ih
      intro hfp
      exact StmtRepr.expr
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.expr8 (by constructor) hp ha)))
    case stVarInit =>
      intro a p q x ee hk hp hcs hq hqne hee ih
      intro hfp
      exact StmtRepr.varInit
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq) hqne
        (ih (fun addr ha => hfp _ (.expr16 (by constructor) hq ha)))
    case stVarNull =>
      intro a p x hk hp hcs hq
      intro hfp
      exact StmtRepr.varNull
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
    case stBlock =>
      intro a stmts count ss hk hstmts hcount harr ih
      intro hfp
      exact StmtRepr.block
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hstmts)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off16 (by omega)))]; exact hcount)
        (ih (fun addr ha => hfp _ (.blockArr (by constructor) hstmts ha)))
    case stIfElse =>
      intro a c t e ec st se hk hc hec ht hst he hene hse ihc iht ihe
      intro hfp
      exact StmtRepr.ifElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 (by constructor) ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he) hene
        (ihe (fun addr ha => hfp _ (.stmt24 (by constructor) he ha)))
    case stIfNoElse =>
      intro a c t ec st hk hc hec ht hst he ihc iht
      intro hfp
      exact StmtRepr.ifNoElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 (by constructor) ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he)
    case stWhile =>
      intro a c b ec sb hk hc hec hb hsb ihc ihb
      intro hfp
      exact StmtRepr.whileS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt16 (by constructor) hb ha)))
    case stFor =>
      intro a b oinit ocond ostep sb hk hinit hcond hstep hb hsb ihinit ihcond ihstep ihb
      intro hfp
      exact StmtRepr.forS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (ihinit (fun addr ha => hfp _ (.optStmt8 (by constructor) ha)))
        (ihcond (fun addr ha => hfp _ (.optExpr16 (by constructor) ha)))
        (ihstep (fun addr ha => hfp _ (.optExpr24 (by constructor) ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt32 (by constructor) hb ha)))
    case stRetSome =>
      intro a p ee hk hp hpne hee ih
      intro hfp
      exact StmtRepr.retSome
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.expr8 (by constructor) hp ha)))
    case stRetNone =>
      intro a hk hp
      intro hfp
      exact StmtRepr.retNone
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
    case stBrk =>
      intro a hk
      intro hfp
      exact StmtRepr.brk (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    case stCont =>
      intro a hk
      intro hfp
      exact StmtRepr.cont (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    -- ===== OptStmtRepr =====
    case optSNone =>
      intro a hp
      intro hfp
      exact OptStmtRepr.none (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp)
    case optSSome =>
      intro a p s hp hpne hs ih
      intro hfp
      exact OptStmtRepr.some
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.child hp ha)))
    -- ===== OptExprRepr =====
    case optENone =>
      intro a hp
      intro hfp
      exact OptExprRepr.none (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp)
    case optESome =>
      intro a p e hp hpne he ih
      intro hfp
      exact OptExprRepr.some
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.child hp ha)))
    -- ===== StmtArrayRepr =====
    case saNil => intro _ _; exact StmtArrayRepr.nil
    case saCons =>
      intro a p n s ss hp hs harr ih ihtail
      intro hfp
      exact StmtArrayRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.elem hp ha)))
        (ihtail (fun addr ha => hfp _ (.tail ha)))
  exact key hfp


/-- **`StmtRepr` transport under memory agreement.** If `m` and `m'` agree on
every address `StmtRepr m a s`'s derivation reads (its footprint `StmtFp m a s`,
which recurses through `ExprFp` for embedded expressions and through
`StmtFp`/`StmtArrayFp` for nested statements), then `StmtRepr m' a s`. Same
seven-motive recursor pass, entered at `StmtRepr.rec`. -/
theorem stmtRepr_agreeP (h : AgreeP P m m') {a : Nat} {s : Stmt}
    (hfp : ∀ addr, StmtFp m a s addr → P addr) (hs : StmtRepr m a s) :
    StmtRepr m' a s := by
  have key : M4 h a s hs := by
    refine hs.rec
      (motive_1 := M1 h) (motive_2 := M2 h) (motive_3 := M3 h) (motive_4 := M4 h)
      (motive_5 := M5 h) (motive_6 := M6 h) (motive_7 := M7 h)
      ?exprInt ?exprStr ?exprBoolT ?exprBoolF ?exprNull ?exprVar ?exprAssign
      ?exprBinary ?exprLogical ?exprUnary ?exprCall ?exprFnNamed ?exprFnAnon
      ?arrNil ?arrCons ?parNil ?parCons
      ?stExpr ?stVarInit ?stVarNull ?stBlock ?stIfElse ?stIfNoElse ?stWhile ?stFor
      ?stRetSome ?stRetNone ?stBrk ?stCont
      ?optSNone ?optSSome ?optENone ?optESome ?saNil ?saCons
    all_goals (simp only [M1, M2, M3, M4, M5, M6, M7])
    case exprInt =>
      intro a n hk hn
      intro hfp
      exact ExprRepr.int
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← readI64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hn)
    case exprStr =>
      intro a p s hk hp hcs
      intro hfp
      exact ExprRepr.str
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
    case exprBoolT =>
      intro a b hk hb hbne
      intro hfp
      exact ExprRepr.boolTrue
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hb) hbne
    case exprBoolF =>
      intro a hk hb
      intro hfp
      exact ExprRepr.boolFalse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hb)
    case exprNull =>
      intro a hk
      intro hfp
      exact ExprRepr.null (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    case exprVar =>
      intro a p x hk hp hcs
      intro hfp
      exact ExprRepr.var
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
    case exprAssign =>
      intro a p q x ee hk hp hcs hq hee ih
      intro hfp
      exact ExprRepr.assign
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
        (ih (fun addr ha => hfp _ (.child16 (by constructor) hq ha)))
    case exprBinary =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.binary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 (by constructor) hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 (by constructor) hr ha)))
    case exprLogical =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.logical
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 (by constructor) hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 (by constructor) hr ha)))
    case exprUnary =>
      intro a p op ee hk hop hp hee ih
      intro hfp
      exact ExprRepr.unary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.child16 (by constructor) hp ha)))
    case exprCall =>
      intro a f args argc ef es hk hf hef hargs hargc hargcSigned harr ihf iharr
      intro hfp
      exact ExprRepr.call
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hf)
        (ihf (fun addr ha => hfp _ (.child8 (by constructor) hf ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hargs)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hargc)
        hargcSigned
        (iharr (fun addr ha => hfp _ (.argArr (by constructor) hargs ha)))
    case exprFnNamed =>
      intro a p params paramc body x ps ss hk hp hpne hcs hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnNamed
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr (by constructor) hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 (by constructor) hbody ha)))
    case exprFnAnon =>
      intro a params paramc body ps ss hk hp hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnAnon
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr (by constructor) hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 (by constructor) hbody ha)))
    -- ===== ExprArrayRepr =====
    case arrNil => intro _ _; exact ExprArrayRepr.nil
    case arrCons =>
      intro a p n ee es hp hee harr ih ihtail
      intro hfp
      exact ExprArrayRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.elem hp ha)))
        (ihtail (fun addr ha => hfp _ (.tail ha)))
    -- ===== ParamsRepr =====
    case parNil => intro _ _; exact ParamsRepr.nil
    case parCons =>
      intro a p n x xs hp hcs hpr ih
      intro hfp
      exact ParamsRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str hp (by omega))))
        (ih (fun addr ha => hfp _ (.tail ha)))
    -- ===== StmtRepr =====
    case stExpr =>
      intro a p ee hk hp hee ih
      intro hfp
      exact StmtRepr.expr
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.expr8 (by constructor) hp ha)))
    case stVarInit =>
      intro a p q x ee hk hp hcs hq hqne hee ih
      intro hfp
      exact StmtRepr.varInit
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq) hqne
        (ih (fun addr ha => hfp _ (.expr16 (by constructor) hq ha)))
    case stVarNull =>
      intro a p x hk hp hcs hq
      intro hfp
      exact StmtRepr.varNull
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 (by constructor) hp (by omega))))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
    case stBlock =>
      intro a stmts count ss hk hstmts hcount harr ih
      intro hfp
      exact StmtRepr.block
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hstmts)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off16 (by omega)))]; exact hcount)
        (ih (fun addr ha => hfp _ (.blockArr (by constructor) hstmts ha)))
    case stIfElse =>
      intro a c t e ec st se hk hc hec ht hst he hene hse ihc iht ihe
      intro hfp
      exact StmtRepr.ifElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 (by constructor) ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he) hene
        (ihe (fun addr ha => hfp _ (.stmt24 (by constructor) he ha)))
    case stIfNoElse =>
      intro a c t ec st hk hc hec ht hst he ihc iht
      intro hfp
      exact StmtRepr.ifNoElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 (by constructor) ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he)
    case stWhile =>
      intro a c b ec sb hk hc hec hb hsb ihc ihb
      intro hfp
      exact StmtRepr.whileS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 (by constructor) hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt16 (by constructor) hb ha)))
    case stFor =>
      intro a b oinit ocond ostep sb hk hinit hcond hstep hb hsb ihinit ihcond ihstep ihb
      intro hfp
      exact StmtRepr.forS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (ihinit (fun addr ha => hfp _ (.optStmt8 (by constructor) ha)))
        (ihcond (fun addr ha => hfp _ (.optExpr16 (by constructor) ha)))
        (ihstep (fun addr ha => hfp _ (.optExpr24 (by constructor) ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt32 (by constructor) hb ha)))
    case stRetSome =>
      intro a p ee hk hp hpne hee ih
      intro hfp
      exact StmtRepr.retSome
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.expr8 (by constructor) hp ha)))
    case stRetNone =>
      intro a hk hp
      intro hfp
      exact StmtRepr.retNone
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
    case stBrk =>
      intro a hk
      intro hfp
      exact StmtRepr.brk (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    case stCont =>
      intro a hk
      intro hfp
      exact StmtRepr.cont (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
    -- ===== OptStmtRepr =====
    case optSNone =>
      intro a hp
      intro hfp
      exact OptStmtRepr.none (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp)
    case optSSome =>
      intro a p s hp hpne hs ih
      intro hfp
      exact OptStmtRepr.some
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.child hp ha)))
    -- ===== OptExprRepr =====
    case optENone =>
      intro a hp
      intro hfp
      exact OptExprRepr.none (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp)
    case optESome =>
      intro a p e hp hpne he ih
      intro hfp
      exact OptExprRepr.some
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.ptr hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.child hp ha)))
    -- ===== StmtArrayRepr =====
    case saNil => intro _ _; exact StmtArrayRepr.nil
    case saCons =>
      intro a p n s ss hp hs harr ih ihtail
      intro hfp
      exact StmtArrayRepr.cons
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.slot hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.elem hp ha)))
        (ihtail (fun addr ha => hfp _ (.tail ha)))
  exact key hfp

end Transport

/-- Region agreement transports an expression representation whose hereditary
region is known. -/
theorem exprRepr_agree_region {m m' : Mem} {lo hi a : Nat} {e : Expr}
    (hag : AgreeP (regionP lo hi) m m')
    (hin : ExprIn m lo hi a e) (hr : ExprRepr m a e) :
    ExprRepr m' a e :=
  exprRepr_agreeP hag (fun _ hfp => exprFp_region hfp hin) hr

/-- Region agreement transports a statement representation whose hereditary
region is known. -/
theorem stmtRepr_agree_region {m m' : Mem} {lo hi a : Nat} {s : Stmt}
    (hag : AgreeP (regionP lo hi) m m')
    (hin : StmtIn m lo hi a s) (hr : StmtRepr m a s) :
    StmtRepr m' a s :=
  stmtRepr_agreeP hag (fun _ hfp => stmtFp_region hfp hin) hr

end Vsa.Sim
