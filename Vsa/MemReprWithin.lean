import Vsa.MemRepr

/-!
# Hereditary ownership of represented AST reads

The seven mutual relations retain every premise of `MemRepr` and require
ownership of precisely each represented read. String ownership includes the
terminating NUL. Empty arrays read no cells. No pairwise separation is imposed,
so immutable nodes, names, literals, and string suffixes may share storage.

Erasure and transport recurse over the representation derivation. The allowed
byte predicate is fixed throughout transport; no execution assumption occurs.
-/

namespace Vsa.MemRepr

open Vsa.While

/-- Every byte in a read window is allowed. -/
def Covers (P : Nat → Prop) (a width : Nat) : Prop :=
  ∀ i, i < width → P (a + i)

/-- An ASCII C string whose content and terminating NUL are allowed. -/
def CStringWithin (m : Mem) (P : Nat → Prop) (a : Nat) (s : String) : Prop :=
  CString m a s ∧ ∀ i, i ≤ s.length → P (a + i)

/-- Widening the allowed byte set preserves coverage. -/
theorem Covers.mono {P Q : Nat → Prop} {a width : Nat}
    (h : Covers P a width) (hPQ : ∀ k, P k → Q k) : Covers Q a width :=
  fun i hi => hPQ _ (h i hi)

/-- Byte agreement transports an exactly covered little-endian read. -/
theorem Covers.readLE_eq {m m' : Mem} {P : Nat → Prop} {a width : Nat}
    (h : Covers P a width) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    readLE m a width = readLE m' a width := by
  induction width generalizing a with
  | zero => rfl
  | succ width ih =>
    have hhead : m[a]? = m'[a]? := hagree a (by simpa using h 0 (Nat.succ_pos _))
    have htail : Covers P (a + 1) width := by
      intro i hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        h (i + 1) (Nat.succ_lt_succ hi)
    simp only [readLE, hhead, ih htail]

/-- Byte agreement transports a covered four-byte read. -/
theorem Covers.read32_eq {m m' : Mem} {P : Nat → Prop} {a : Nat}
    (h : Covers P a 4) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    read32 m a = read32 m' a := h.readLE_eq hagree

/-- Byte agreement transports a covered eight-byte read. -/
theorem Covers.read64_eq {m m' : Mem} {P : Nat → Prop} {a : Nat}
    (h : Covers P a 8) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    read64 m a = read64 m' a := h.readLE_eq hagree

/-- Byte agreement also preserves the signed interpretation. -/
theorem Covers.readI64_eq {m m' : Mem} {P : Nat → Prop} {a : Nat}
    (h : Covers P a 8) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    readI64 m a = readI64 m' a := by
  simp only [readI64, h.read64_eq hagree]

private theorem cstr_transport_within {m m' : Mem} {P : Nat → Prop}
    (hagree : ∀ k, P k → m[k]? = m'[k]?) {a : Nat} {cs : List Char}
    (h : CStr m a cs) (hP : ∀ i, i ≤ cs.length → P (a + i)) : CStr m' a cs := by
  induction h with
  | nil hz =>
    exact .nil ((hagree _ (by simpa using hP 0 (Nat.zero_le _))).symm.trans hz)
  | cons hb hne hascii ht ih =>
    apply CStr.cons ((hagree _ (by simpa using hP 0 (Nat.zero_le _))).symm.trans hb) hne hascii
    apply ih
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hP (i + 1) (Nat.succ_le_succ hi)

/-- Forget string ownership without changing the represented string. -/
theorem CStringWithin.erase {m : Mem} {P : Nat → Prop} {a : Nat} {s : String}
    (h : CStringWithin m P a s) : CString m a s := h.1

/-- Transport string bytes and widen their allowed set, including the NUL. -/
theorem CStringWithin.map {m m' : Mem} {P Q : Nat → Prop} {a : Nat} {s : String}
    (h : CStringWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) : CStringWithin m' Q a s := by
  obtain ⟨⟨cs, hc, hs⟩, hP⟩ := h
  have hlen : cs.length = s.length := by rw [hs, String.length_ofList]
  exact ⟨⟨cs, cstr_transport_within hagree hc (fun i hi => hP i (hlen ▸ hi)), hs⟩,
    fun i hi => hPQ _ (hP i hi)⟩

/-- Preserve string representation under agreement on its fixed owned bytes. -/
theorem CStringWithin.transport {m m' : Mem} {P : Nat → Prop} {a : Nat} {s : String}
    (h : CStringWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    CStringWithin m' P a s := h.map hagree (fun _ hp => hp)

/-- Widen the allowed string bytes without changing memory. -/
theorem CStringWithin.mono {m : Mem} {P Q : Nat → Prop} {a : Nat} {s : String}
    (h : CStringWithin m P a s) (hPQ : ∀ k, P k → Q k) : CStringWithin m Q a s :=
  h.map (fun _ _ => rfl) hPQ

mutual

/-- `Expr` struct at address `a` represents the deep-embedded expression.
Constructor per `ExprKind` (`EX_INT = 0 … EX_FN = 10`). -/
inductive ExprReprWithin (m : Mem) (P : Nat → Prop) : Nat → Expr → Prop where
  | int {a : Nat} {n : Int} :
    read32 m a = some 0 → Covers P a 4 → readI64 m (a + 8) = some n → Covers P (a + 8) 8 →
    ExprReprWithin m P a (.int n)
  | str {a p : Nat} {s : String} :
    read32 m a = some 1 → Covers P a 4 → read64 m (a + 8) = some p → Covers P (a + 8) 8 → CStringWithin m P p s →
    ExprReprWithin m P a (.str s)
  | boolTrue {a : Nat} {b : Nat} :
    read32 m a = some 2 → Covers P a 4 → read32 m (a + 8) = some b → Covers P (a + 8) 4 → b ≠ 0 →
    ExprReprWithin m P a (.bool true)
  | boolFalse {a : Nat} :
    read32 m a = some 2 → Covers P a 4 → read32 m (a + 8) = some 0 → Covers P (a + 8) 4 →
    ExprReprWithin m P a (.bool false)
  | null {a : Nat} :
    read32 m a = some 3 → Covers P a 4 →
    ExprReprWithin m P a .null
  | var {a p : Nat} {x : String} :
    read32 m a = some 4 → Covers P a 4 → read64 m (a + 8) = some p → Covers P (a + 8) 8 → CStringWithin m P p x →
    ExprReprWithin m P a (.var x)
  | assign {a p q : Nat} {x : String} {e : Expr} :
    read32 m a = some 5 → Covers P a 4 →
    read64 m (a + 8) = some p → Covers P (a + 8) 8 → CStringWithin m P p x →
    read64 m (a + 16) = some q → Covers P (a + 16) 8 → ExprReprWithin m P q e →
    ExprReprWithin m P a (.assign x e)
  | binary {a l r : Nat} {op : BinOp} {el er : Expr} :
    read32 m a = some 6 → Covers P a 4 →
    read32 m (a + 8) = some (binOpTok op) → Covers P (a + 8) 4 →
    read64 m (a + 16) = some l → Covers P (a + 16) 8 → ExprReprWithin m P l el →
    read64 m (a + 24) = some r → Covers P (a + 24) 8 → ExprReprWithin m P r er →
    ExprReprWithin m P a (.binary op el er)
  | logical {a l r : Nat} {op : LogOp} {el er : Expr} :
    read32 m a = some 7 → Covers P a 4 →
    read32 m (a + 8) = some (logOpTok op) → Covers P (a + 8) 4 →
    read64 m (a + 16) = some l → Covers P (a + 16) 8 → ExprReprWithin m P l el →
    read64 m (a + 24) = some r → Covers P (a + 24) 8 → ExprReprWithin m P r er →
    ExprReprWithin m P a (.logical op el er)
  | unary {a p : Nat} {op : UnOp} {e : Expr} :
    read32 m a = some 8 → Covers P a 4 →
    read32 m (a + 8) = some (unOpTok op) → Covers P (a + 8) 4 →
    read64 m (a + 16) = some p → Covers P (a + 16) 8 → ExprReprWithin m P p e →
    ExprReprWithin m P a (.unary op e)
  | call {a f args argc : Nat} {ef : Expr} {es : List Expr} :
    read32 m a = some 9 → Covers P a 4 →
    read64 m (a + 8) = some f → Covers P (a + 8) 8 → ExprReprWithin m P f ef →
    read64 m (a + 16) = some args → Covers P (a + 16) 8 →
    read32 m (a + 24) = some argc → Covers P (a + 24) 4 →
    -- `argc` is a C `int`.  The evaluator loads it with `lw` and compares it
    -- with signed `blt`, so represented call nodes exclude negative i32 words.
    argc < 2 ^ 31 →
    ExprArrayReprWithin m P args argc es →
    ExprReprWithin m P a (.call ef es)
  | fnNamed {a p params paramc body : Nat} {x : String} {ps : List String}
      {ss : List Stmt} :
    read32 m a = some 10 → Covers P a 4 →
    read64 m (a + 8) = some p → Covers P (a + 8) 8 → p ≠ 0 → CStringWithin m P p x →
    read64 m (a + 16) = some params → Covers P (a + 16) 8 →
    read32 m (a + 24) = some paramc → Covers P (a + 24) 4 →
    ParamsReprWithin m P params paramc ps →
    read64 m (a + 32) = some body → Covers P (a + 32) 8 → StmtReprWithin m P body (.block ss) →
    ExprReprWithin m P a (.fn (some x) ps ss)
  | fnAnon {a params paramc body : Nat} {ps : List String} {ss : List Stmt} :
    read32 m a = some 10 → Covers P a 4 →
    read64 m (a + 8) = some 0 → Covers P (a + 8) 8 →
    read64 m (a + 16) = some params → Covers P (a + 16) 8 →
    read32 m (a + 24) = some paramc → Covers P (a + 24) 4 →
    ParamsReprWithin m P params paramc ps →
    read64 m (a + 32) = some body → Covers P (a + 32) 8 → StmtReprWithin m P body (.block ss) →
    ExprReprWithin m P a (.fn none ps ss)

/-- `Expr **` array of `n` expression pointers. -/
inductive ExprArrayReprWithin (m : Mem) (P : Nat → Prop) : Nat → Nat → List Expr → Prop where
  | nil {a : Nat} : ExprArrayReprWithin m P a 0 []
  | cons {a p n : Nat} {e : Expr} {es : List Expr} :
    read64 m a = some p → Covers P a 8 → ExprReprWithin m P p e →
    ExprArrayReprWithin m P (a + 8) n es →
    ExprArrayReprWithin m P a (n + 1) (e :: es)

/-- `char **` array of `n` parameter names. -/
inductive ParamsReprWithin (m : Mem) (P : Nat → Prop) : Nat → Nat → List String → Prop where
  | nil {a : Nat} : ParamsReprWithin m P a 0 []
  | cons {a p n : Nat} {x : String} {xs : List String} :
    read64 m a = some p → Covers P a 8 → CStringWithin m P p x →
    ParamsReprWithin m P (a + 8) n xs →
    ParamsReprWithin m P a (n + 1) (x :: xs)

/-- `Stmt` struct at address `a` (`ST_EXPR = 0 … ST_CONTINUE = 8`). -/
inductive StmtReprWithin (m : Mem) (P : Nat → Prop) : Nat → Stmt → Prop where
  | expr {a p : Nat} {e : Expr} :
    read32 m a = some 0 → Covers P a 4 → read64 m (a + 8) = some p → Covers P (a + 8) 8 → ExprReprWithin m P p e →
    StmtReprWithin m P a (.expr e)
  | varInit {a p q : Nat} {x : String} {e : Expr} :
    read32 m a = some 1 → Covers P a 4 →
    read64 m (a + 8) = some p → Covers P (a + 8) 8 → CStringWithin m P p x →
    read64 m (a + 16) = some q → Covers P (a + 16) 8 → q ≠ 0 → ExprReprWithin m P q e →
    StmtReprWithin m P a (.varDecl x (some e))
  | varNull {a p : Nat} {x : String} :
    read32 m a = some 1 → Covers P a 4 →
    read64 m (a + 8) = some p → Covers P (a + 8) 8 → CStringWithin m P p x →
    read64 m (a + 16) = some 0 → Covers P (a + 16) 8 →
    StmtReprWithin m P a (.varDecl x none)
  | block {a stmts count : Nat} {ss : List Stmt} :
    read32 m a = some 2 → Covers P a 4 →
    read64 m (a + 8) = some stmts → Covers P (a + 8) 8 →
    read32 m (a + 16) = some count → Covers P (a + 16) 4 →
    StmtArrayReprWithin m P stmts count ss →
    StmtReprWithin m P a (.block ss)
  | ifElse {a c t e : Nat} {ec : Expr} {st se : Stmt} :
    read32 m a = some 3 → Covers P a 4 →
    read64 m (a + 8) = some c → Covers P (a + 8) 8 → ExprReprWithin m P c ec →
    read64 m (a + 16) = some t → Covers P (a + 16) 8 → StmtReprWithin m P t st →
    read64 m (a + 24) = some e → Covers P (a + 24) 8 → e ≠ 0 → StmtReprWithin m P e se →
    StmtReprWithin m P a (.ifStmt ec st (some se))
  | ifNoElse {a c t : Nat} {ec : Expr} {st : Stmt} :
    read32 m a = some 3 → Covers P a 4 →
    read64 m (a + 8) = some c → Covers P (a + 8) 8 → ExprReprWithin m P c ec →
    read64 m (a + 16) = some t → Covers P (a + 16) 8 → StmtReprWithin m P t st →
    read64 m (a + 24) = some 0 → Covers P (a + 24) 8 →
    StmtReprWithin m P a (.ifStmt ec st none)
  | whileS {a c b : Nat} {ec : Expr} {sb : Stmt} :
    read32 m a = some 4 → Covers P a 4 →
    read64 m (a + 8) = some c → Covers P (a + 8) 8 → ExprReprWithin m P c ec →
    read64 m (a + 16) = some b → Covers P (a + 16) 8 → StmtReprWithin m P b sb →
    StmtReprWithin m P a (.whileStmt ec sb)
  | forS {a b : Nat} {oinit : Option Stmt} {ocond ostep : Option Expr}
      {sb : Stmt} :
    read32 m a = some 5 → Covers P a 4 →
    OptStmtReprWithin m P (a + 8) oinit →
    OptExprReprWithin m P (a + 16) ocond →
    OptExprReprWithin m P (a + 24) ostep →
    read64 m (a + 32) = some b → Covers P (a + 32) 8 → StmtReprWithin m P b sb →
    StmtReprWithin m P a (.forStmt oinit ocond ostep sb)
  | retSome {a p : Nat} {e : Expr} :
    read32 m a = some 6 → Covers P a 4 → read64 m (a + 8) = some p → Covers P (a + 8) 8 → p ≠ 0 →
    ExprReprWithin m P p e →
    StmtReprWithin m P a (.ret (some e))
  | retNone {a : Nat} :
    read32 m a = some 6 → Covers P a 4 → read64 m (a + 8) = some 0 → Covers P (a + 8) 8 →
    StmtReprWithin m P a (.ret none)
  | brk {a : Nat} : read32 m a = some 7 → Covers P a 4 → StmtReprWithin m P a .brk
  | cont {a : Nat} : read32 m a = some 8 → Covers P a 4 → StmtReprWithin m P a .cont

/-- An optional statement pointer field (NULL ↔ `none`). -/
inductive OptStmtReprWithin (m : Mem) (P : Nat → Prop) : Nat → Option Stmt → Prop where
  | none {a : Nat} : read64 m a = some 0 → Covers P a 8 → OptStmtReprWithin m P a none
  | some {a p : Nat} {s : Stmt} :
    read64 m a = some p → Covers P a 8 → p ≠ 0 → StmtReprWithin m P p s →
    OptStmtReprWithin m P a (some s)

/-- An optional expression pointer field (NULL ↔ `none`). -/
inductive OptExprReprWithin (m : Mem) (P : Nat → Prop) : Nat → Option Expr → Prop where
  | none {a : Nat} : read64 m a = some 0 → Covers P a 8 → OptExprReprWithin m P a none
  | some {a p : Nat} {e : Expr} :
    read64 m a = some p → Covers P a 8 → p ≠ 0 → ExprReprWithin m P p e →
    OptExprReprWithin m P a (some e)

/-- `Stmt **` array of `n` statement pointers (the shape `parse_program`
returns and `interp_run` consumes). -/
inductive StmtArrayReprWithin (m : Mem) (P : Nat → Prop) : Nat → Nat → List Stmt → Prop where
  | nil {a : Nat} : StmtArrayReprWithin m P a 0 []
  | cons {a p n : Nat} {s : Stmt} {ss : List Stmt} :
    read64 m a = some p → Covers P a 8 → StmtReprWithin m P p s →
    StmtArrayReprWithin m P (a + 8) n ss →
    StmtArrayReprWithin m P a (n + 1) (s :: ss)

end

/-- Forget hereditary ownership. -/
theorem ExprReprWithin.erase {m : Mem} {P : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) :
    ExprRepr m a e := by
  apply ExprReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem ExprArrayReprWithin.erase {m : Mem} {P : Nat → Prop} {a n : Nat} {es : List Expr}
    (h : ExprArrayReprWithin m P a n es) :
    ExprArrayRepr m a n es := by
  apply ExprArrayReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem ParamsReprWithin.erase {m : Mem} {P : Nat → Prop} {a n : Nat} {xs : List String}
    (h : ParamsReprWithin m P a n xs) :
    ParamsRepr m a n xs := by
  apply ParamsReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem StmtReprWithin.erase {m : Mem} {P : Nat → Prop} {a : Nat} {s : Stmt}
    (h : StmtReprWithin m P a s) :
    StmtRepr m a s := by
  apply StmtReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem OptStmtReprWithin.erase {m : Mem} {P : Nat → Prop} {a : Nat} {s : Option Stmt}
    (h : OptStmtReprWithin m P a s) :
    OptStmtRepr m a s := by
  apply OptStmtReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem OptExprReprWithin.erase {m : Mem} {P : Nat → Prop} {a : Nat} {e : Option Expr}
    (h : OptExprReprWithin m P a e) :
    OptExprRepr m a e := by
  apply OptExprReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Forget hereditary ownership. -/
theorem StmtArrayReprWithin.erase {m : Mem} {P : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m P a n ss) :
    StmtArrayRepr m a n ss := by
  apply StmtArrayReprWithin.rec
    (motive_1 := fun a e _ => ExprRepr m a e)
    (motive_2 := fun a n es _ => ExprArrayRepr m a n es)
    (motive_3 := fun a n xs _ => ParamsRepr m a n xs)
    (motive_4 := fun a s _ => StmtRepr m a s)
    (motive_5 := fun a s _ => OptStmtRepr m a s)
    (motive_6 := fun a e _ => OptExprRepr m a e)
    (motive_7 := fun a n ss _ => StmtArrayRepr m a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.erase ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem ExprReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    ExprReprWithin m' Q a e := by
  apply ExprReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem ExprArrayReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a n : Nat} {es : List Expr}
    (h : ExprArrayReprWithin m P a n es) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    ExprArrayReprWithin m' Q a n es := by
  apply ExprArrayReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem ParamsReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a n : Nat} {xs : List String}
    (h : ParamsReprWithin m P a n xs) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    ParamsReprWithin m' Q a n xs := by
  apply ParamsReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem StmtReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a : Nat} {s : Stmt}
    (h : StmtReprWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    StmtReprWithin m' Q a s := by
  apply StmtReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem OptStmtReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a : Nat} {s : Option Stmt}
    (h : OptStmtReprWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    OptStmtReprWithin m' Q a s := by
  apply OptStmtReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem OptExprReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a : Nat} {e : Option Expr}
    (h : OptExprReprWithin m P a e) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    OptExprReprWithin m' Q a e := by
  apply OptExprReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Transport all recursive reads and widen the allowed set. -/
theorem StmtArrayReprWithin.map {m m' : Mem} {P Q : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m P a n ss) (hagree : ∀ k, P k → m[k]? = m'[k]?)
    (hPQ : ∀ k, P k → Q k) :
    StmtArrayReprWithin m' Q a n ss := by
  apply StmtArrayReprWithin.rec
    (motive_1 := fun a e _ => ExprReprWithin m' Q a e)
    (motive_2 := fun a n es _ => ExprArrayReprWithin m' Q a n es)
    (motive_3 := fun a n xs _ => ParamsReprWithin m' Q a n xs)
    (motive_4 := fun a s _ => StmtReprWithin m' Q a s)
    (motive_5 := fun a s _ => OptStmtReprWithin m' Q a s)
    (motive_6 := fun a e _ => OptExprReprWithin m' Q a e)
    (motive_7 := fun a n ss _ => StmtArrayReprWithin m' Q a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros
    constructor
    all_goals first
      | assumption
      | exact CStringWithin.map ‹_› hagree hPQ
      | exact Covers.mono ‹_› hPQ
      | exact (Covers.read32_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.read64_eq ‹_› hagree).symm.trans ‹_›
      | exact (Covers.readI64_eq ‹_› hagree).symm.trans ‹_›

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem ExprReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    ExprReprWithin m' P a e := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem ExprReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) (hPQ : ∀ k, P k → Q k) :
    ExprReprWithin m Q a e := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem ExprArrayReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a n : Nat} {es : List Expr}
    (h : ExprArrayReprWithin m P a n es) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    ExprArrayReprWithin m' P a n es := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem ExprArrayReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a n : Nat} {es : List Expr}
    (h : ExprArrayReprWithin m P a n es) (hPQ : ∀ k, P k → Q k) :
    ExprArrayReprWithin m Q a n es := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem ParamsReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a n : Nat} {xs : List String}
    (h : ParamsReprWithin m P a n xs) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    ParamsReprWithin m' P a n xs := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem ParamsReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a n : Nat} {xs : List String}
    (h : ParamsReprWithin m P a n xs) (hPQ : ∀ k, P k → Q k) :
    ParamsReprWithin m Q a n xs := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem StmtReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a : Nat} {s : Stmt}
    (h : StmtReprWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    StmtReprWithin m' P a s := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem StmtReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a : Nat} {s : Stmt}
    (h : StmtReprWithin m P a s) (hPQ : ∀ k, P k → Q k) :
    StmtReprWithin m Q a s := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem OptStmtReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a : Nat} {s : Option Stmt}
    (h : OptStmtReprWithin m P a s) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    OptStmtReprWithin m' P a s := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem OptStmtReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a : Nat} {s : Option Stmt}
    (h : OptStmtReprWithin m P a s) (hPQ : ∀ k, P k → Q k) :
    OptStmtReprWithin m Q a s := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem OptExprReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a : Nat} {e : Option Expr}
    (h : OptExprReprWithin m P a e) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    OptExprReprWithin m' P a e := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem OptExprReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a : Nat} {e : Option Expr}
    (h : OptExprReprWithin m P a e) (hPQ : ∀ k, P k → Q k) :
    OptExprReprWithin m Q a e := h.map (fun _ _ => rfl) hPQ

/-- Preserve the entire represented graph under agreement on owned bytes. -/
theorem StmtArrayReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m P a n ss) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    StmtArrayReprWithin m' P a n ss := h.map hagree (fun _ hp => hp)

/-- Widen the allowed set; immutable sharing remains unrestricted. -/
theorem StmtArrayReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m P a n ss) (hPQ : ∀ k, P k → Q k) :
    StmtArrayReprWithin m Q a n ss := h.map (fun _ _ => rfl) hPQ

/-- A program array with hereditary ownership and the original count premise. -/
def ProgramReprWithin (m : Mem) (P : Nat → Prop) (a n : Nat) (p : Program) : Prop :=
  StmtArrayReprWithin m P a n p ∧ n = p.length

/-- Ownership strengthens the original program representation. -/
theorem ProgramReprWithin.erase {m : Mem} {P : Nat → Prop} {a n : Nat} {p : Program}
    (h : ProgramReprWithin m P a n p) : ProgramRepr m a n p :=
  ⟨h.1.erase, h.2⟩

/-- Agreement on the fixed owned set preserves the complete program. -/
theorem ProgramReprWithin.transport {m m' : Mem} {P : Nat → Prop} {a n : Nat} {p : Program}
    (h : ProgramReprWithin m P a n p) (hagree : ∀ k, P k → m[k]? = m'[k]?) :
    ProgramReprWithin m' P a n p := ⟨h.1.transport hagree, h.2⟩

/-- Widen the program's allowed byte set. -/
theorem ProgramReprWithin.mono {m : Mem} {P Q : Nat → Prop} {a n : Nat} {p : Program}
    (h : ProgramReprWithin m P a n p) (hPQ : ∀ k, P k → Q k) :
    ProgramReprWithin m Q a n p := ⟨h.1.mono hPQ, h.2⟩

#print axioms ExprReprWithin.erase
#print axioms ExprReprWithin.transport
#print axioms ExprReprWithin.mono
#print axioms ExprArrayReprWithin.erase
#print axioms ExprArrayReprWithin.transport
#print axioms ExprArrayReprWithin.mono
#print axioms ParamsReprWithin.erase
#print axioms ParamsReprWithin.transport
#print axioms ParamsReprWithin.mono
#print axioms StmtReprWithin.erase
#print axioms StmtReprWithin.transport
#print axioms StmtReprWithin.mono
#print axioms OptStmtReprWithin.erase
#print axioms OptStmtReprWithin.transport
#print axioms OptStmtReprWithin.mono
#print axioms OptExprReprWithin.erase
#print axioms OptExprReprWithin.transport
#print axioms OptExprReprWithin.mono
#print axioms StmtArrayReprWithin.erase
#print axioms StmtArrayReprWithin.transport
#print axioms StmtArrayReprWithin.mono
#print axioms CStringWithin.erase
#print axioms CStringWithin.transport
#print axioms CStringWithin.mono
#print axioms ProgramReprWithin.erase
#print axioms ProgramReprWithin.transport
#print axioms ProgramReprWithin.mono

end Vsa.MemRepr
