import Vsa.MemRepr
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

/-- `addr` is read by `ExprRepr m a e`. -/
inductive ExprFp (m : Mem) : Nat → Expr → Nat → Prop where
  | tag {a : Nat} {e : Expr} {k : Nat} : k < 4 → ExprFp m a e (a + k)
  -- payload / pointer / count windows (offset 8, plus 16/24/32 for children)
  | off8 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 8 + k)
  | off16 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 16 + k)
  | off24 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 24 + k)
  | off32 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 32 + k)
  -- string bytes for a `char*` at offset 8 (str/var/assign-name/fn-name)
  | str8 {a : Nat} {e : Expr} {p k : Nat} :
    read64 m (a + 8) = some p → ExprFp m a e (p + k)
  -- child expr at offset 8 (call fn), 16 (assign/binary/logical/unary l), 24 (binary/logical r)
  | child8 {a : Nat} {e ec : Expr} {p addr : Nat} :
    read64 m (a + 8) = some p → ExprFp m p ec addr → ExprFp m a e addr
  | child16 {a : Nat} {e ec : Expr} {p addr : Nat} :
    read64 m (a + 16) = some p → ExprFp m p ec addr → ExprFp m a e addr
  | child24 {a : Nat} {e ec : Expr} {p addr : Nat} :
    read64 m (a + 24) = some p → ExprFp m p ec addr → ExprFp m a e addr
  -- call arg array at offset 16
  | argArr {a : Nat} {e : Expr} {args argc addr : Nat} {es : List Expr} :
    read64 m (a + 16) = some args → ExprArrayFp m args argc es addr → ExprFp m a e addr
  -- fn params array at offset 16, body block at offset 32
  | paramsArr {a : Nat} {e : Expr} {params paramc addr : Nat} {ps : List String} :
    read64 m (a + 16) = some params → ParamsFp m params paramc ps addr → ExprFp m a e addr
  | body32 {a : Nat} {e : Expr} {body addr : Nat} {ss : List Stmt} :
    read64 m (a + 32) = some body → StmtFp m body (.block ss) addr → ExprFp m a e addr

/-- `addr` is read by `ExprArrayRepr m a n es`. -/
inductive ExprArrayFp (m : Mem) : Nat → Nat → List Expr → Nat → Prop where
  | slot {a n : Nat} {es : List Expr} {k : Nat} : k < 8 → ExprArrayFp m a n es (a + k)
  | elem {a p n addr : Nat} {e : Expr} {es : List Expr} :
    read64 m a = some p → ExprFp m p e addr → ExprArrayFp m a n es addr
  | tail {a n addr : Nat} {e : Expr} {es : List Expr} :
    ExprArrayFp m (a + 8) n es addr → ExprArrayFp m a (n + 1) (e :: es) addr

/-- `addr` is read by `ParamsRepr m a n xs`. -/
inductive ParamsFp (m : Mem) : Nat → Nat → List String → Nat → Prop where
  | slot {a n : Nat} {xs : List String} {k : Nat} : k < 8 → ParamsFp m a n xs (a + k)
  | str {a p n addr : Nat} {xs : List String} :
    read64 m a = some p → ParamsFp m a n xs (p + addr)
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
  | str8 {a : Nat} {s : Stmt} {p k : Nat} :
    read64 m (a + 8) = some p → StmtFp m a s (p + k)
  -- expr children at offsets 8 (if/while cond, expr stmt), 16 (var-init value)
  | expr8 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    read64 m (a + 8) = some p → ExprFp m p e addr → StmtFp m a s addr
  | expr16 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    read64 m (a + 16) = some p → ExprFp m p e addr → StmtFp m a s addr
  -- stmt children at offsets 8 (block array via count@16), 16 (if-then, while body),
  -- 24 (if-else), 32 (for body)
  | stmt16 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    read64 m (a + 16) = some p → StmtFp m p t addr → StmtFp m a s addr
  | stmt24 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    read64 m (a + 24) = some p → StmtFp m p t addr → StmtFp m a s addr
  | stmt32 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    read64 m (a + 32) = some p → StmtFp m p t addr → StmtFp m a s addr
  -- block: stmt array at offset 8, count at offset 16
  | blockArr {a : Nat} {s : Stmt} {stmts count addr : Nat} {ss : List Stmt} :
    read64 m (a + 8) = some stmts → StmtArrayFp m stmts count ss addr → StmtFp m a s addr
  -- for-loop optional init (stmt) at offset 8, optional cond/step (expr) at 16/24
  | optStmt8 {a : Nat} {s : Stmt} {os : Option Stmt} {addr : Nat} :
    OptStmtFp m (a + 8) os addr → StmtFp m a s addr
  | optExpr16 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    OptExprFp m (a + 16) oe addr → StmtFp m a s addr
  | optExpr24 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    OptExprFp m (a + 24) oe addr → StmtFp m a s addr

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
  | slot {a n : Nat} {ss : List Stmt} {k : Nat} : k < 8 → StmtArrayFp m a n ss (a + k)
  | elem {a p n addr : Nat} {s : Stmt} {ss : List Stmt} :
    read64 m a = some p → StmtFp m p s addr → StmtArrayFp m a n ss addr
  | tail {a n addr : Nat} {s : Stmt} {ss : List Stmt} :
    StmtArrayFp m (a + 8) n ss addr → StmtArrayFp m a (n + 1) (s :: ss) addr

end

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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
    case exprAssign =>
      intro a p q x ee hk hp hcs hq hee ih
      intro hfp
      exact ExprRepr.assign
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
        (ih (fun addr ha => hfp _ (.child16 hq ha)))
    case exprBinary =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.binary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 hr ha)))
    case exprLogical =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.logical
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 hr ha)))
    case exprUnary =>
      intro a p op ee hk hop hp hee ih
      intro hfp
      exact ExprRepr.unary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.child16 hp ha)))
    case exprCall =>
      intro a f args argc ef es hk hf hef hargs hargc harr ihf iharr
      intro hfp
      exact ExprRepr.call
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hf)
        (ihf (fun addr ha => hfp _ (.child8 hf ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hargs)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hargc)
        (iharr (fun addr ha => hfp _ (.argArr hargs ha)))
    case exprFnNamed =>
      intro a p params paramc body x ps ss hk hp hpne hcs hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnNamed
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 hbody ha)))
    case exprFnAnon =>
      intro a params paramc body ps ss hk hp hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnAnon
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 hbody ha)))
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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str hp)))
        (ih (fun addr ha => hfp _ (.tail ha)))
    -- ===== StmtRepr =====
    case stExpr =>
      intro a p ee hk hp hee ih
      intro hfp
      exact StmtRepr.expr
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.expr8 hp ha)))
    case stVarInit =>
      intro a p q x ee hk hp hcs hq hqne hee ih
      intro hfp
      exact StmtRepr.varInit
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq) hqne
        (ih (fun addr ha => hfp _ (.expr16 hq ha)))
    case stVarNull =>
      intro a p x hk hp hcs hq
      intro hfp
      exact StmtRepr.varNull
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
    case stBlock =>
      intro a stmts count ss hk hstmts hcount harr ih
      intro hfp
      exact StmtRepr.block
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hstmts)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off16 (by omega)))]; exact hcount)
        (ih (fun addr ha => hfp _ (.blockArr hstmts ha)))
    case stIfElse =>
      intro a c t e ec st se hk hc hec ht hst he hene hse ihc iht ihe
      intro hfp
      exact StmtRepr.ifElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he) hene
        (ihe (fun addr ha => hfp _ (.stmt24 he ha)))
    case stIfNoElse =>
      intro a c t ec st hk hc hec ht hst he ihc iht
      intro hfp
      exact StmtRepr.ifNoElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he)
    case stWhile =>
      intro a c b ec sb hk hc hec hb hsb ihc ihb
      intro hfp
      exact StmtRepr.whileS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt16 hb ha)))
    case stFor =>
      intro a b oinit ocond ostep sb hk hinit hcond hstep hb hsb ihinit ihcond ihstep ihb
      intro hfp
      exact StmtRepr.forS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (ihinit (fun addr ha => hfp _ (.optStmt8 ha)))
        (ihcond (fun addr ha => hfp _ (.optExpr16 ha)))
        (ihstep (fun addr ha => hfp _ (.optExpr24 ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt32 hb ha)))
    case stRetSome =>
      intro a p ee hk hp hpne hee ih
      intro hfp
      exact StmtRepr.retSome
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.expr8 hp ha)))
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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
    case exprAssign =>
      intro a p q x ee hk hp hcs hq hee ih
      intro hfp
      exact ExprRepr.assign
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
        (ih (fun addr ha => hfp _ (.child16 hq ha)))
    case exprBinary =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.binary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 hr ha)))
    case exprLogical =>
      intro a l r op el er hk hop hl hel hr her ihl ihr
      intro hfp
      exact ExprRepr.logical
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hl)
        (ihl (fun addr ha => hfp _ (.child16 hl ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact hr)
        (ihr (fun addr ha => hfp _ (.child24 hr ha)))
    case exprUnary =>
      intro a p op ee hk hop hp hee ih
      intro hfp
      exact ExprRepr.unary
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off8 (by omega)))]; exact hop)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.child16 hp ha)))
    case exprCall =>
      intro a f args argc ef es hk hf hef hargs hargc harr ihf iharr
      intro hfp
      exact ExprRepr.call
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hf)
        (ihf (fun addr ha => hfp _ (.child8 hf ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hargs)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hargc)
        (iharr (fun addr ha => hfp _ (.argArr hargs ha)))
    case exprFnNamed =>
      intro a p params paramc body x ps ss hk hp hpne hcs hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnNamed
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 hbody ha)))
    case exprFnAnon =>
      intro a params paramc body ps ss hk hp hpar hparc hpr hbody hblk ihpr ihblk
      intro hfp
      exact ExprRepr.fnAnon
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hpar)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off24 (by omega)))]; exact hparc)
        (ihpr (fun addr ha => hfp _ (.paramsArr hpar ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hbody)
        (ihblk (fun addr ha => hfp _ (.body32 hbody ha)))
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
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str hp)))
        (ih (fun addr ha => hfp _ (.tail ha)))
    -- ===== StmtRepr =====
    case stExpr =>
      intro a p ee hk hp hee ih
      intro hfp
      exact StmtRepr.expr
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (ih (fun addr ha => hfp _ (.expr8 hp ha)))
    case stVarInit =>
      intro a p q x ee hk hp hcs hq hqne hee ih
      intro hfp
      exact StmtRepr.varInit
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq) hqne
        (ih (fun addr ha => hfp _ (.expr16 hq ha)))
    case stVarNull =>
      intro a p x hk hp hcs hq
      intro hfp
      exact StmtRepr.varNull
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp)
        (cstring_agreeP h hcs (fun k _ => hfp _ (.str8 hp)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hq)
    case stBlock =>
      intro a stmts count ss hk hstmts hcount harr ih
      intro hfp
      exact StmtRepr.block
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hstmts)
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.off16 (by omega)))]; exact hcount)
        (ih (fun addr ha => hfp _ (.blockArr hstmts ha)))
    case stIfElse =>
      intro a c t e ec st se hk hc hec ht hst he hene hse ihc iht ihe
      intro hfp
      exact StmtRepr.ifElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he) hene
        (ihe (fun addr ha => hfp _ (.stmt24 he ha)))
    case stIfNoElse =>
      intro a c t ec st hk hc hec ht hst he ihc iht
      intro hfp
      exact StmtRepr.ifNoElse
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact ht)
        (iht (fun addr ha => hfp _ (.stmt16 ht ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off24 hk))]; exact he)
    case stWhile =>
      intro a c b ec sb hk hc hec hb hsb ihc ihb
      intro hfp
      exact StmtRepr.whileS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hc)
        (ihc (fun addr ha => hfp _ (.expr8 hc ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off16 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt16 hb ha)))
    case stFor =>
      intro a b oinit ocond ostep sb hk hinit hcond hstep hb hsb ihinit ihcond ihstep ihb
      intro hfp
      exact StmtRepr.forS
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (ihinit (fun addr ha => hfp _ (.optStmt8 ha)))
        (ihcond (fun addr ha => hfp _ (.optExpr16 ha)))
        (ihstep (fun addr ha => hfp _ (.optExpr24 ha)))
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off32 hk))]; exact hb)
        (ihb (fun addr ha => hfp _ (.stmt32 hb ha)))
    case stRetSome =>
      intro a p ee hk hp hpne hee ih
      intro hfp
      exact StmtRepr.retSome
        (by rw [← read32_agreeP h (fun k hk => hfp _ (.tag hk))]; exact hk)
        (by rw [← read64_agreeP h (fun k hk => hfp _ (.off8 hk))]; exact hp) hpne
        (ih (fun addr ha => hfp _ (.expr8 hp ha)))
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

end Vsa.Sim
