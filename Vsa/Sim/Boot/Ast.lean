import Vsa.Sim.Boot.Store
import Vsa.MemReprWithin

/-!
# The represented AST: uniqueness and a covered decoder

* Uniqueness: a memory represents at most one AST at an address
  (`ExprRepr.unique`, …, `ProgramRepr.unique`). Constructors are told apart by
  the tag word and by zero/nonzero pointer or word fields; strings by
  `CString.unique`.
* Decoder: `decodeExpr v P fuel a`, …, `decodeProgram v P fuel a n` read the
  nodes through the byte view `v`, check that every read window (every byte of
  a field, every byte of a string including its NUL) satisfies `P`, and return
  the AST. `fuel` bounds the recursion depth plus the array lengths along a
  path and every string's length. Soundness (`decodeProgram_sound`): over a
  partial view of `m` the decoded program is `ProgramReprWithin m (P · = true)`.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.While

/-! ## Uniqueness -/

theorem _root_.Vsa.MemRepr.CStr.unique {m : Mem} {a : Nat} {cs cs' : List Char}
    (h : CStr m a cs) (h' : CStr m a cs') : cs = cs' := by
  induction h generalizing cs' with
  | nil hz =>
    cases h' with
    | nil _ => rfl
    | cons hb hne _ _ => rw [hz] at hb; cases hb; exact absurd rfl hne
  | cons hb hne _ _ ih =>
    cases h' with
    | nil hz => rw [hz] at hb; cases hb; exact absurd rfl hne
    | cons hb' _ _ ht' =>
      rw [hb] at hb'
      cases hb'
      rw [ih ht']

theorem _root_.Vsa.MemRepr.CString.unique {m : Mem} {a : Nat} {s s' : String}
    (h : CString m a s) (h' : CString m a s') : s = s' := by
  obtain ⟨cs, hc, rfl⟩ := h
  obtain ⟨cs', hc', rfl⟩ := h'
  rw [CStr.unique hc hc']

theorem binOpTok_inj {o o' : BinOp} : binOpTok o = binOpTok o' ↔ o = o' := by
  cases o <;> cases o' <;> decide

theorem logOpTok_inj {o o' : LogOp} : logOpTok o = logOpTok o' ↔ o = o' := by
  cases o <;> cases o' <;> decide

theorem unOpTok_inj {o o' : UnOp} : unOpTok o = unOpTok o' ↔ o = o' := by
  cases o <;> cases o' <;> decide

/-- Every expression represented at `a` is `e`. -/
def UniqE (m : Mem) (a : Nat) (e : Expr) : Prop := ∀ e', ExprRepr m a e' → e' = e
/-- Every expression array represented at `a` with count `n` is `es`. -/
def UniqEA (m : Mem) (a n : Nat) (es : List Expr) : Prop :=
  ∀ es', ExprArrayRepr m a n es' → es' = es
/-- Every parameter array represented at `a` with count `n` is `xs`. -/
def UniqP (m : Mem) (a n : Nat) (xs : List String) : Prop :=
  ∀ xs', ParamsRepr m a n xs' → xs' = xs
/-- Every statement represented at `a` is `s`. -/
def UniqS (m : Mem) (a : Nat) (s : Stmt) : Prop := ∀ s', StmtRepr m a s' → s' = s
/-- Every optional statement field represented at `a` is `s`. -/
def UniqOS (m : Mem) (a : Nat) (s : Option Stmt) : Prop :=
  ∀ s', OptStmtRepr m a s' → s' = s
/-- Every optional expression field represented at `a` is `e`. -/
def UniqOE (m : Mem) (a : Nat) (e : Option Expr) : Prop :=
  ∀ e', OptExprRepr m a e' → e' = e
/-- Every statement array represented at `a` with count `n` is `ss`. -/
def UniqSA (m : Mem) (a n : Nat) (ss : List Stmt) : Prop :=
  ∀ ss', StmtArrayRepr m a n ss' → ss' = ss

theorem UniqE.use {m : Mem} {a : Nat} {e e' : Expr} (h : UniqE m a e) (h' : ExprRepr m a e') :
    e' = e := h e' h'
theorem UniqEA.use {m : Mem} {a n : Nat} {es es' : List Expr} (h : UniqEA m a n es)
    (h' : ExprArrayRepr m a n es') : es' = es := h es' h'
theorem UniqP.use {m : Mem} {a n : Nat} {xs xs' : List String} (h : UniqP m a n xs)
    (h' : ParamsRepr m a n xs') : xs' = xs := h xs' h'
theorem UniqS.use {m : Mem} {a : Nat} {s s' : Stmt} (h : UniqS m a s) (h' : StmtRepr m a s') :
    s' = s := h s' h'
theorem UniqOS.use {m : Mem} {a : Nat} {s s' : Option Stmt} (h : UniqOS m a s)
    (h' : OptStmtRepr m a s') : s' = s := h s' h'
theorem UniqOE.use {m : Mem} {a : Nat} {e e' : Option Expr} (h : UniqOE m a e)
    (h' : OptExprRepr m a e') : e' = e := h e' h'
theorem UniqSA.use {m : Mem} {a n : Nat} {ss ss' : List Stmt} (h : UniqSA m a n ss)
    (h' : StmtArrayRepr m a n ss') : ss' = ss := h ss' h'

/-- Close an equation between two decoded children from the child's
uniqueness hypothesis or C-string uniqueness (either orientation). -/
macro "uniq_close" : tactic =>
  `(tactic| first
    | rfl
    | (apply UniqE.use <;> assumption)
    | (apply Eq.symm; apply UniqE.use <;> assumption)
    | (apply UniqEA.use <;> assumption)
    | (apply Eq.symm; apply UniqEA.use <;> assumption)
    | (apply UniqP.use <;> assumption)
    | (apply Eq.symm; apply UniqP.use <;> assumption)
    | (apply UniqS.use <;> assumption)
    | (apply Eq.symm; apply UniqS.use <;> assumption)
    | (apply UniqOS.use <;> assumption)
    | (apply Eq.symm; apply UniqOS.use <;> assumption)
    | (apply UniqOE.use <;> assumption)
    | (apply Eq.symm; apply UniqOE.use <;> assumption)
    | (apply UniqSA.use <;> assumption)
    | (apply Eq.symm; apply UniqSA.use <;> assumption)
    | (apply Stmt.block.inj; apply UniqS.use <;> assumption)
    | (apply Eq.symm; apply Stmt.block.inj; apply UniqS.use <;> assumption)
    | (apply CString.unique <;> assumption))

/-- Case step of the uniqueness recursion: the second derivation is either a
different constructor (its field reads contradict the first) or the same one
(its fields agree, and so do its children). -/
macro "uniq_step" : tactic =>
  `(tactic| (
    intro _ h'
    cases h'
    all_goals
      simp_all only [Option.some.injEq, binOpTok_inj, logOpTok_inj, unOpTok_inj,
        reduceCtorEq, Nat.reduceEqDiff, Expr.assign.injEq, Expr.binary.injEq, Expr.logical.injEq,
        Expr.unary.injEq, Expr.call.injEq, Expr.fn.injEq, Expr.str.injEq, Expr.var.injEq,
        Expr.int.injEq, Stmt.expr.injEq, Stmt.varDecl.injEq, Stmt.block.injEq,
        Stmt.ifStmt.injEq, Stmt.whileStmt.injEq, Stmt.forStmt.injEq, Stmt.ret.injEq,
        List.cons.injEq, Option.some.injEq, true_and, and_true, ne_eq,
        not_false_eq_true, not_true_eq_false]
    all_goals (try subst_vars)
    all_goals (repeat' constructor) <;> uniq_close))

/-- Uniqueness for all seven relations at once (the recursor's conclusion). -/
structure UniqueAll (m : Mem) : Prop where
  expr : ∀ a e, ExprRepr m a e → UniqE m a e
  exprArray : ∀ a n es, ExprArrayRepr m a n es → UniqEA m a n es
  params : ∀ a n xs, ParamsRepr m a n xs → UniqP m a n xs
  stmt : ∀ a s, StmtRepr m a s → UniqS m a s
  optStmt : ∀ a s, OptStmtRepr m a s → UniqOS m a s
  optExpr : ∀ a e, OptExprRepr m a e → UniqOE m a e
  stmtArray : ∀ a n ss, StmtArrayRepr m a n ss → UniqSA m a n ss

theorem unique_all {m : Mem} : UniqueAll m := by
  -- The seven recursors share their 35 minor premises (`?c1 … ?c35`).
  refine ⟨@ExprRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @ExprArrayRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @ParamsRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @StmtRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @OptStmtRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @OptExprRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @StmtArrayRepr.rec m
      (fun a e _ => UniqE m a e) (fun a n es _ => UniqEA m a n es)
      (fun a n xs _ => UniqP m a n xs) (fun a s _ => UniqS m a s) (fun a s _ => UniqOS m a s)
      (fun a e _ => UniqOE m a e) (fun a n ss _ => UniqSA m a n ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
      ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35⟩
  all_goals intros
  all_goals uniq_step

theorem _root_.Vsa.MemRepr.ExprRepr.unique {m : Mem} {a : Nat} {e e' : Expr}
    (h : ExprRepr m a e) (h' : ExprRepr m a e') : e = e' :=
  (unique_all.expr _ _ h e' h').symm

theorem _root_.Vsa.MemRepr.ExprArrayRepr.unique {m : Mem} {a n : Nat} {es es' : List Expr}
    (h : ExprArrayRepr m a n es) (h' : ExprArrayRepr m a n es') : es = es' :=
  (unique_all.exprArray _ _ _ h es' h').symm

theorem _root_.Vsa.MemRepr.ParamsRepr.unique {m : Mem} {a n : Nat} {xs xs' : List String}
    (h : ParamsRepr m a n xs) (h' : ParamsRepr m a n xs') : xs = xs' :=
  (unique_all.params _ _ _ h xs' h').symm

theorem _root_.Vsa.MemRepr.StmtRepr.unique {m : Mem} {a : Nat} {s s' : Stmt}
    (h : StmtRepr m a s) (h' : StmtRepr m a s') : s = s' :=
  (unique_all.stmt _ _ h s' h').symm

theorem _root_.Vsa.MemRepr.OptStmtRepr.unique {m : Mem} {a : Nat} {s s' : Option Stmt}
    (h : OptStmtRepr m a s) (h' : OptStmtRepr m a s') : s = s' :=
  (unique_all.optStmt _ _ h s' h').symm

theorem _root_.Vsa.MemRepr.OptExprRepr.unique {m : Mem} {a : Nat} {e e' : Option Expr}
    (h : OptExprRepr m a e) (h' : OptExprRepr m a e') : e = e' :=
  (unique_all.optExpr _ _ h e' h').symm

theorem _root_.Vsa.MemRepr.StmtArrayRepr.unique {m : Mem} {a n : Nat} {ss ss' : List Stmt}
    (h : StmtArrayRepr m a n ss) (h' : StmtArrayRepr m a n ss') : ss = ss' :=
  (unique_all.stmtArray _ _ _ h ss' h').symm

/-- A memory represents at most one program at `a` with count `n`. -/
theorem _root_.Vsa.MemRepr.ProgramRepr.unique {m : Mem} {a n : Nat} {p p' : Program}
    (h : ProgramRepr m a n p) (h' : ProgramRepr m a n p') : p = p' :=
  StmtArrayRepr.unique h.1 h'.1

/-! ## Covered reads through a view -/

/-- Little-endian read of `w` bytes at `a` through `v`, requiring `P` on every
byte of the window. -/
def rdc (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | w + 1 =>
    if P a then
      match v a, rdc v P (a + 1) w with
      | some b, some r => some (b.toNat + 256 * r)
      | _, _ => none
    else none

/-- A covered read: the memory read and the window's coverage. -/
structure RdOk (m : Mem) (P : Nat → Prop) (a w x : Nat) : Prop where
  read : readLE m a w = some x
  covers : Covers P a w

theorem rdc_sound {m : Mem} {v : Nat → Option (BitVec 8)} {P : Nat → Bool}
    (hv : PartialView m v) : ∀ {w a x}, rdc v P a w = some x → RdOk m (P · = true) a w x := by
  intro w
  induction w with
  | zero => intro a x h; cases h; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ w ih =>
    intro a x h
    simp only [rdc] at h
    split at h
    · rename_i hP
      split at h
      · rename_i b r hb hr
        cases h
        have ht := ih hr
        refine ⟨?_, ?_⟩
        · simp only [readLE, hv a b hb, ht.read]; rfl
        · intro i hi
          cases i with
          | zero => simpa using hP
          | succ i =>
            have := ht.covers i (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      · cases h
    · cases h

/-- The NUL-terminated ASCII string at `a` through `v`, within `fuel` bytes,
requiring `P` on every byte including the NUL. -/
def cstrc (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (a : Nat) : Nat → Option (List Char)
  | 0 => none
  | fuel + 1 =>
    if P a then
      match v a with
      | some b =>
        if b = 0 then some []
        else if b.toNat < 128 then (cstrc v P (a + 1) fuel).map (Char.ofNat b.toNat :: ·)
        else none
      | none => none
    else none

/-- The covered string at `a` as a `String`. -/
def strc (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (fuel a : Nat) : Option String :=
  (cstrc v P a fuel).map String.ofList

/-- A covered string: its characters and the coverage of every byte and the NUL. -/
structure CstrOk (m : Mem) (P : Nat → Prop) (a : Nat) (cs : List Char) : Prop where
  str : CStr m a cs
  covers : ∀ i, i ≤ cs.length → P (a + i)

theorem cstrc_sound {m : Mem} {v : Nat → Option (BitVec 8)} {P : Nat → Bool}
    (hv : PartialView m v) :
    ∀ {fuel a cs}, cstrc v P a fuel = some cs → CstrOk m (P · = true) a cs := by
  intro fuel
  induction fuel with
  | zero => intro a cs h; cases h
  | succ fuel ih =>
    intro a cs h
    simp only [cstrc] at h
    split at h
    · rename_i hP
      split at h
      · rename_i b hb
        split at h
        · rename_i h0
          cases h
          refine ⟨.nil (by rw [hv a b hb, h0]), fun i hi => ?_⟩
          have : i = 0 := by simpa using hi
          subst this; simpa using hP
        · rename_i h0
          split at h
          · rename_i h128
            cases hr : cstrc v P (a + 1) fuel with
            | none => rw [hr] at h; cases h
            | some rest =>
              rw [hr] at h
              cases h
              have ht := ih hr
              refine ⟨.cons (hv a b hb) h0 h128 ht.str, fun i hi => ?_⟩
              cases i with
              | zero => simpa using hP
              | succ i =>
                have := ht.covers i (by simpa using hi)
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
          · cases h
      · cases h
    · cases h

theorem strc_sound {m : Mem} {v : Nat → Option (BitVec 8)} {P : Nat → Bool}
    (hv : PartialView m v) {fuel a : Nat} {s : String} (h : strc v P fuel a = some s) :
    CStringWithin m (P · = true) a s := by
  unfold strc at h
  cases hc : cstrc v P a fuel with
  | none => rw [hc] at h; cases h
  | some cs =>
    rw [hc] at h
    cases h
    have ht := cstrc_sound hv hc
    exact ⟨⟨cs, ht.str, rfl⟩, fun i hi => ht.covers i (by simpa [String.length_ofList] using hi)⟩

/-! ## Operator tokens -/

def binOps : List BinOp := [.add, .sub, .mul, .div, .mod, .ne, .eq, .lt, .le, .gt, .ge]
def logOps : List LogOp := [.and, .or]
def unOps : List UnOp := [.neg, .not]

/-- The operator stored as token `t`. -/
def binOpOfTok (t : Nat) : Option BinOp := binOps.find? (binOpTok · == t)
def logOpOfTok (t : Nat) : Option LogOp := logOps.find? (logOpTok · == t)
def unOpOfTok (t : Nat) : Option UnOp := unOps.find? (unOpTok · == t)

theorem binOpOfTok_sound {t : Nat} {o : BinOp} (h : binOpOfTok t = some o) :
    binOpTok o = t := by
  simpa using List.find?_some h
theorem logOpOfTok_sound {t : Nat} {o : LogOp} (h : logOpOfTok t = some o) :
    logOpTok o = t := by
  simpa using List.find?_some h
theorem unOpOfTok_sound {t : Nat} {o : UnOp} (h : unOpOfTok t = some o) :
    unOpTok o = t := by
  simpa using List.find?_some h

/-! ## The decoder -/

/-- `n` parameter names from the `char **` array at `a`. -/
def decodeParams (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (fuel : Nat) :
    Nat → Nat → Option (List String)
  | _, 0 => some []
  | a, n + 1 => do
    let p ← rdc v P a 8
    let x ← strc v P fuel p
    let xs ← decodeParams v P fuel (a + 8) n
    pure (x :: xs)

mutual

/-- The expression at `a`. -/
def decodeExpr (v : Nat → Option (BitVec 8)) (P : Nat → Bool) : Nat → Nat → Option Expr
  | 0, _ => none
  | fuel + 1, a => do
    let tag ← rdc v P a 4
    match tag with
    | 0 => do
      let w ← rdc v P (a + 8) 8
      pure (.int (BitVec.ofNat 64 w).toInt)
    | 1 => do
      let p ← rdc v P (a + 8) 8
      let s ← strc v P fuel p
      pure (.str s)
    | 2 => do
      let b ← rdc v P (a + 8) 4
      pure (.bool (b != 0))
    | 3 => pure .null
    | 4 => do
      let p ← rdc v P (a + 8) 8
      let x ← strc v P fuel p
      pure (.var x)
    | 5 => do
      let p ← rdc v P (a + 8) 8
      let x ← strc v P fuel p
      let q ← rdc v P (a + 16) 8
      let e ← decodeExpr v P fuel q
      pure (.assign x e)
    | 6 => do
      let t ← rdc v P (a + 8) 4
      let op ← binOpOfTok t
      let l ← rdc v P (a + 16) 8
      let el ← decodeExpr v P fuel l
      let r ← rdc v P (a + 24) 8
      let er ← decodeExpr v P fuel r
      pure (.binary op el er)
    | 7 => do
      let t ← rdc v P (a + 8) 4
      let op ← logOpOfTok t
      let l ← rdc v P (a + 16) 8
      let el ← decodeExpr v P fuel l
      let r ← rdc v P (a + 24) 8
      let er ← decodeExpr v P fuel r
      pure (.logical op el er)
    | 8 => do
      let t ← rdc v P (a + 8) 4
      let op ← unOpOfTok t
      let p ← rdc v P (a + 16) 8
      let e ← decodeExpr v P fuel p
      pure (.unary op e)
    | 9 => do
      let f ← rdc v P (a + 8) 8
      let ef ← decodeExpr v P fuel f
      let args ← rdc v P (a + 16) 8
      let argc ← rdc v P (a + 24) 4
      if argc < 2 ^ 31 then do
        let es ← decodeExprArray v P fuel args argc
        pure (.call ef es)
      else none
    | 10 => do
      let p ← rdc v P (a + 8) 8
      let name ← if p = 0 then some none else (strc v P fuel p).map some
      let params ← rdc v P (a + 16) 8
      let paramc ← rdc v P (a + 24) 4
      let ps ← decodeParams v P fuel params paramc
      let body ← rdc v P (a + 32) 8
      let sb ← decodeStmt v P fuel body
      match sb with
      | .block ss => pure (.fn name ps ss)
      | _ => none
    | _ => none

/-- `n` expressions from the `Expr **` array at `a`. -/
def decodeExprArray (v : Nat → Option (BitVec 8)) (P : Nat → Bool) :
    Nat → Nat → Nat → Option (List Expr)
  | _, _, 0 => some []
  | 0, _, _ + 1 => none
  | fuel + 1, a, n + 1 => do
    let p ← rdc v P a 8
    let e ← decodeExpr v P fuel p
    let es ← decodeExprArray v P fuel (a + 8) n
    pure (e :: es)

/-- The statement at `a`. -/
def decodeStmt (v : Nat → Option (BitVec 8)) (P : Nat → Bool) : Nat → Nat → Option Stmt
  | 0, _ => none
  | fuel + 1, a => do
    let tag ← rdc v P a 4
    match tag with
    | 0 => do
      let p ← rdc v P (a + 8) 8
      let e ← decodeExpr v P fuel p
      pure (.expr e)
    | 1 => do
      let p ← rdc v P (a + 8) 8
      let x ← strc v P fuel p
      let q ← rdc v P (a + 16) 8
      if q = 0 then pure (.varDecl x none)
      else do
        let e ← decodeExpr v P fuel q
        pure (.varDecl x (some e))
    | 2 => do
      let stmts ← rdc v P (a + 8) 8
      let count ← rdc v P (a + 16) 4
      let ss ← decodeStmtArray v P fuel stmts count
      pure (.block ss)
    | 3 => do
      let c ← rdc v P (a + 8) 8
      let ec ← decodeExpr v P fuel c
      let t ← rdc v P (a + 16) 8
      let st ← decodeStmt v P fuel t
      let e ← rdc v P (a + 24) 8
      if e = 0 then pure (.ifStmt ec st none)
      else do
        let se ← decodeStmt v P fuel e
        pure (.ifStmt ec st (some se))
    | 4 => do
      let c ← rdc v P (a + 8) 8
      let ec ← decodeExpr v P fuel c
      let b ← rdc v P (a + 16) 8
      let sb ← decodeStmt v P fuel b
      pure (.whileStmt ec sb)
    | 5 => do
      let oi ← decodeOptStmt v P fuel (a + 8)
      let oc ← decodeOptExpr v P fuel (a + 16)
      let os ← decodeOptExpr v P fuel (a + 24)
      let b ← rdc v P (a + 32) 8
      let sb ← decodeStmt v P fuel b
      pure (.forStmt oi oc os sb)
    | 6 => do
      let p ← rdc v P (a + 8) 8
      if p = 0 then pure (.ret none)
      else do
        let e ← decodeExpr v P fuel p
        pure (.ret (some e))
    | 7 => pure .brk
    | 8 => pure .cont
    | _ => none

/-- The optional statement pointer field at `a`. -/
def decodeOptStmt (v : Nat → Option (BitVec 8)) (P : Nat → Bool) :
    Nat → Nat → Option (Option Stmt)
  | 0, _ => none
  | fuel + 1, a => do
    let p ← rdc v P a 8
    if p = 0 then pure none
    else (decodeStmt v P fuel p).map some

/-- The optional expression pointer field at `a`. -/
def decodeOptExpr (v : Nat → Option (BitVec 8)) (P : Nat → Bool) :
    Nat → Nat → Option (Option Expr)
  | 0, _ => none
  | fuel + 1, a => do
    let p ← rdc v P a 8
    if p = 0 then pure none
    else (decodeExpr v P fuel p).map some

/-- `n` statements from the `Stmt **` array at `a`. -/
def decodeStmtArray (v : Nat → Option (BitVec 8)) (P : Nat → Bool) :
    Nat → Nat → Nat → Option (List Stmt)
  | _, _, 0 => some []
  | 0, _, _ + 1 => none
  | fuel + 1, a, n + 1 => do
    let p ← rdc v P a 8
    let s ← decodeStmt v P fuel p
    let ss ← decodeStmtArray v P fuel (a + 8) n
    pure (s :: ss)

end

/-- The program: `n` statements from the `Stmt **` array at `a`. -/
def decodeProgram (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (fuel a n : Nat) :
    Option Program :=
  decodeStmtArray v P fuel a n

/-! ## Soundness -/

section Sound

variable {m : Mem} {v : Nat → Option (BitVec 8)} {P : Nat → Bool}

/-- Open the monadic binds of a decoder step hypothesis. -/
macro "dec_open " h:ident : tactic =>
  `(tactic| try simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at $h:ident)

theorem decodeParams_sound (hv : PartialView m v) {fuel : Nat} :
    ∀ {n a xs}, decodeParams v P fuel a n = some xs → ParamsReprWithin m (P · = true) a n xs := by
  intro n
  induction n with
  | zero => intro a xs h; cases h; exact .nil
  | succ n ih =>
    intro a xs h
    simp only [decodeParams] at h
    dec_open h
    obtain ⟨p, hp, x, hx, xs', hxs, rfl⟩ := h
    exact .cons (rdc_sound hv hp).read (rdc_sound hv hp).covers (strc_sound hv hx) (ih hxs)

/-- Soundness of the six mutually recursive decoders at one fuel. -/
structure DecodeSound (m : Mem) (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (fuel : Nat) :
    Prop where
  expr : ∀ a e, decodeExpr v P fuel a = some e → ExprReprWithin m (P · = true) a e
  exprArray : ∀ a n es, decodeExprArray v P fuel a n = some es →
    ExprArrayReprWithin m (P · = true) a n es
  stmt : ∀ a s, decodeStmt v P fuel a = some s → StmtReprWithin m (P · = true) a s
  optStmt : ∀ a s, decodeOptStmt v P fuel a = some s → OptStmtReprWithin m (P · = true) a s
  optExpr : ∀ a e, decodeOptExpr v P fuel a = some e → OptExprReprWithin m (P · = true) a e
  stmtArray : ∀ a n ss, decodeStmtArray v P fuel a n = some ss →
    StmtArrayReprWithin m (P · = true) a n ss

/-- Close a field obligation of a Within constructor from the decoder's
hypotheses: a covered read, a string, a decoded child, or a side condition. -/
macro "dec_close " hv:ident ih:ident : tactic =>
  `(tactic| first
    | exact (rdc_sound $hv (by assumption)).read
    | exact (rdc_sound $hv (by assumption)).covers
    | exact strc_sound $hv (by assumption)
    | exact DecodeSound.expr $ih _ _ (by assumption)
    | exact DecodeSound.exprArray $ih _ _ _ (by assumption)
    | exact DecodeSound.stmt $ih _ _ (by assumption)
    | exact DecodeSound.optStmt $ih _ _ (by assumption)
    | exact DecodeSound.optExpr $ih _ _ (by assumption)
    | exact DecodeSound.stmtArray $ih _ _ _ (by assumption)
    | exact decodeParams_sound $hv (by assumption)
    | assumption)

theorem decodeSound_zero : DecodeSound m v P 0 where
  expr _ _ h := by simp [decodeExpr] at h
  exprArray _ n _ h := by
    cases n with
    | zero => simp only [decodeExprArray, Option.some.injEq] at h; subst h; exact .nil
    | succ n => simp [decodeExprArray] at h
  stmt _ _ h := by simp [decodeStmt] at h
  optStmt _ _ h := by simp [decodeOptStmt] at h
  optExpr _ _ h := by simp [decodeOptExpr] at h
  stmtArray _ n _ h := by
    cases n with
    | zero => simp only [decodeStmtArray, Option.some.injEq] at h; subst h; exact .nil
    | succ n => simp [decodeStmtArray] at h

theorem decodeSound_succ (hv : PartialView m v) {fuel : Nat} (ih : DecodeSound m v P fuel) :
    DecodeSound m v P (fuel + 1) where
  expr a e h := by
    simp only [decodeExpr] at h
    dec_open h
    obtain ⟨tag, htag, h⟩ := h
    split at h <;> dec_open h
    · obtain ⟨w, hw, rfl⟩ := h
      refine .int (rdc_sound hv htag).read (rdc_sound hv htag).covers ?_ (rdc_sound hv hw).covers
      simp only [readI64, read64, (rdc_sound hv hw).read, Option.map_some]
    · obtain ⟨p, hp, s, hs, rfl⟩ := h
      apply ExprReprWithin.str <;> dec_close hv ih
    · obtain ⟨b, hb, rfl⟩ := h
      by_cases hb0 : b = 0
      · subst hb0
        apply ExprReprWithin.boolFalse <;> dec_close hv ih
      · have hne : (b != 0) = true := by simpa using hb0
        rw [hne]
        apply ExprReprWithin.boolTrue <;> dec_close hv ih
    · cases h
      apply ExprReprWithin.null <;> dec_close hv ih
    · obtain ⟨p, hp, s, hs, rfl⟩ := h
      apply ExprReprWithin.var <;> dec_close hv ih
    · obtain ⟨p, hp, x, hx, q, hq, e', he, rfl⟩ := h
      apply ExprReprWithin.assign <;> dec_close hv ih
    · obtain ⟨t, ht, op, hop, l, hl, el, hel, r, hr, er, her, rfl⟩ := h
      obtain rfl := binOpOfTok_sound hop
      apply ExprReprWithin.binary <;> dec_close hv ih
    · obtain ⟨t, ht, op, hop, l, hl, el, hel, r, hr, er, her, rfl⟩ := h
      obtain rfl := logOpOfTok_sound hop
      apply ExprReprWithin.logical <;> dec_close hv ih
    · obtain ⟨t, ht, op, hop, p, hp, e', he, rfl⟩ := h
      obtain rfl := unOpOfTok_sound hop
      apply ExprReprWithin.unary <;> dec_close hv ih
    · obtain ⟨f, hf, ef, hef, args, hargs, argc, hargc, h⟩ := h
      split at h <;> dec_open h
      · obtain ⟨es, hes, rfl⟩ := h
        apply ExprReprWithin.call <;> dec_close hv ih
      · cases h
    · obtain ⟨p, hp, h⟩ := h
      by_cases hp0 : p = 0
      · subst hp0
        simp only [ite_true] at h
        dec_open h
        obtain ⟨_, rfl, params, hparams, paramc, hparamc, ps, hps, body, hbody, sb, hsb, h⟩ := h
        split at h <;> dec_open h
        · subst h
          apply ExprReprWithin.fnAnon <;> dec_close hv ih
        · cases h
      · simp only [hp0, ite_false] at h
        dec_open h
        obtain ⟨_, ⟨x, hx, rfl⟩, params, hparams, paramc, hparamc, ps, hps, body, hbody, sb, hsb,
          h⟩ := h
        split at h <;> dec_open h
        · subst h
          apply ExprReprWithin.fnNamed <;> dec_close hv ih
        · cases h
    · cases h
  exprArray a n es h := by
    cases n with
    | zero => simp only [decodeExprArray, Option.some.injEq] at h; subst h; exact .nil
    | succ n =>
      simp only [decodeExprArray] at h
      dec_open h
      obtain ⟨p, hp, e, he, es', hes, rfl⟩ := h
      apply ExprArrayReprWithin.cons <;> dec_close hv ih
  stmt a s h := by
    simp only [decodeStmt] at h
    dec_open h
    obtain ⟨tag, htag, h⟩ := h
    split at h <;> dec_open h
    · obtain ⟨p, hp, e, he, rfl⟩ := h
      apply StmtReprWithin.expr <;> dec_close hv ih
    · obtain ⟨p, hp, x, hx, q, hq, h⟩ := h
      split at h <;> dec_open h
      · rename_i hq0
        subst hq0
        cases h
        apply StmtReprWithin.varNull <;> dec_close hv ih
      · rename_i hq0
        obtain ⟨e, he, rfl⟩ := h
        apply StmtReprWithin.varInit <;> dec_close hv ih
    · obtain ⟨stmts, hstmts, count, hcount, ss, hss, rfl⟩ := h
      apply StmtReprWithin.block <;> dec_close hv ih
    · obtain ⟨c, hc, ec, hec, t, ht, st, hst, e, he, h⟩ := h
      split at h <;> dec_open h
      · rename_i he0
        subst he0
        cases h
        apply StmtReprWithin.ifNoElse <;> dec_close hv ih
      · rename_i he0
        obtain ⟨se, hse, rfl⟩ := h
        apply StmtReprWithin.ifElse <;> dec_close hv ih
    · obtain ⟨c, hc, ec, hec, b, hb, sb, hsb, rfl⟩ := h
      apply StmtReprWithin.whileS <;> dec_close hv ih
    · obtain ⟨oi, hoi, oc, hoc, os, hos, b, hb, sb, hsb, rfl⟩ := h
      apply StmtReprWithin.forS <;> dec_close hv ih
    · obtain ⟨p, hp, h⟩ := h
      split at h <;> dec_open h
      · rename_i hp0
        subst hp0
        cases h
        apply StmtReprWithin.retNone <;> dec_close hv ih
      · rename_i hp0
        obtain ⟨e, he, rfl⟩ := h
        apply StmtReprWithin.retSome <;> dec_close hv ih
    · cases h
      apply StmtReprWithin.brk <;> dec_close hv ih
    · cases h
      apply StmtReprWithin.cont <;> dec_close hv ih
    · cases h
  optStmt a s h := by
    simp only [decodeOptStmt] at h
    dec_open h
    obtain ⟨p, hp, h⟩ := h
    split at h <;> dec_open h
    · rename_i hp0
      subst hp0
      cases h
      apply OptStmtReprWithin.none <;> dec_close hv ih
    · rename_i hp0
      obtain ⟨s', hs, rfl⟩ := h
      apply OptStmtReprWithin.some <;> dec_close hv ih
  optExpr a e h := by
    simp only [decodeOptExpr] at h
    dec_open h
    obtain ⟨p, hp, h⟩ := h
    split at h <;> dec_open h
    · rename_i hp0
      subst hp0
      cases h
      apply OptExprReprWithin.none <;> dec_close hv ih
    · rename_i hp0
      obtain ⟨e', he, rfl⟩ := h
      apply OptExprReprWithin.some <;> dec_close hv ih
  stmtArray a n ss h := by
    cases n with
    | zero => simp only [decodeStmtArray, Option.some.injEq] at h; subst h; exact .nil
    | succ n =>
      simp only [decodeStmtArray] at h
      dec_open h
      obtain ⟨p, hp, s, hs, ss', hss, rfl⟩ := h
      apply StmtArrayReprWithin.cons <;> dec_close hv ih

/-- The decoders are sound at every fuel. -/
theorem decodeSound (hv : PartialView m v) : ∀ fuel, DecodeSound m v P fuel
  | 0 => decodeSound_zero
  | fuel + 1 => decodeSound_succ hv (decodeSound hv fuel)

theorem decodeExpr_sound (hv : PartialView m v) {fuel a : Nat} {e : Expr}
    (h : decodeExpr v P fuel a = some e) : ExprReprWithin m (P · = true) a e :=
  (decodeSound hv fuel).expr a e h

theorem decodeExprArray_sound (hv : PartialView m v) {fuel a n : Nat} {es : List Expr}
    (h : decodeExprArray v P fuel a n = some es) : ExprArrayReprWithin m (P · = true) a n es :=
  (decodeSound hv fuel).exprArray a n es h

theorem decodeStmt_sound (hv : PartialView m v) {fuel a : Nat} {s : Stmt}
    (h : decodeStmt v P fuel a = some s) : StmtReprWithin m (P · = true) a s :=
  (decodeSound hv fuel).stmt a s h

theorem decodeOptStmt_sound (hv : PartialView m v) {fuel a : Nat} {s : Option Stmt}
    (h : decodeOptStmt v P fuel a = some s) : OptStmtReprWithin m (P · = true) a s :=
  (decodeSound hv fuel).optStmt a s h

theorem decodeOptExpr_sound (hv : PartialView m v) {fuel a : Nat} {e : Option Expr}
    (h : decodeOptExpr v P fuel a = some e) : OptExprReprWithin m (P · = true) a e :=
  (decodeSound hv fuel).optExpr a e h

theorem decodeStmtArray_sound (hv : PartialView m v) {fuel a n : Nat} {ss : List Stmt}
    (h : decodeStmtArray v P fuel a n = some ss) : StmtArrayReprWithin m (P · = true) a n ss :=
  (decodeSound hv fuel).stmtArray a n ss h

theorem StmtArrayReprWithin.count_eq_length {Q : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m Q a n ss) : n = ss.length := by
  induction ss generalizing a n with
  | nil => cases h; rfl
  | cons s ss ih => cases h with | cons _ _ _ ht => simp [ih ht]

/-- **Decoder soundness**: over a partial view of `m`, a decoded program is
represented at `a` with count `n`, every read covered by `P`. -/
theorem decodeProgram_sound (hv : PartialView m v) {fuel a n : Nat} {p : Program}
    (h : decodeProgram v P fuel a n = some p) : ProgramReprWithin m (P · = true) a n p :=
  have hs := decodeStmtArray_sound hv h
  ⟨hs, StmtArrayReprWithin.count_eq_length hs⟩

theorem decodeProgram_repr (hv : PartialView m v) {fuel a n : Nat} {p : Program}
    (h : decodeProgram v P fuel a n = some p) : ProgramRepr m a n p :=
  (decodeProgram_sound hv h).erase

end Sound

/-! ## Checking a decoded program against an expected one

`Expr`/`Stmt` derive no `DecidableEq` (nested mutual inductives), so the
kernel check compares with the structural `Bool` equality `stmtsBeq`:
`decodesTo v P fuel a n p = true` is decided by `decide +kernel`. -/

mutual

def exprBeq : Expr → Expr → Bool
  | .int n, .int n' => n == n'
  | .str s, .str s' => s == s'
  | .bool b, .bool b' => b == b'
  | .null, .null => true
  | .var x, .var x' => x == x'
  | .assign x e, .assign x' e' => x == x' && exprBeq e e'
  | .binary o l r, .binary o' l' r' => o == o' && exprBeq l l' && exprBeq r r'
  | .logical o l r, .logical o' l' r' => o == o' && exprBeq l l' && exprBeq r r'
  | .unary o e, .unary o' e' => o == o' && exprBeq e e'
  | .call f es, .call f' es' => exprBeq f f' && exprsBeq es es'
  | .fn x ps b, .fn x' ps' b' => x == x' && ps == ps' && stmtsBeq b b'
  | _, _ => false

def exprsBeq : List Expr → List Expr → Bool
  | [], [] => true
  | e :: es, e' :: es' => exprBeq e e' && exprsBeq es es'
  | _, _ => false

def optExprBeq : Option Expr → Option Expr → Bool
  | none, none => true
  | some e, some e' => exprBeq e e'
  | _, _ => false

def stmtBeq : Stmt → Stmt → Bool
  | .expr e, .expr e' => exprBeq e e'
  | .varDecl x e, .varDecl x' e' => x == x' && optExprBeq e e'
  | .block ss, .block ss' => stmtsBeq ss ss'
  | .ifStmt c t e, .ifStmt c' t' e' => exprBeq c c' && stmtBeq t t' && optStmtBeq e e'
  | .whileStmt c b, .whileStmt c' b' => exprBeq c c' && stmtBeq b b'
  | .forStmt i c s b, .forStmt i' c' s' b' =>
    optStmtBeq i i' && optExprBeq c c' && optExprBeq s s' && stmtBeq b b'
  | .ret e, .ret e' => optExprBeq e e'
  | .brk, .brk => true
  | .cont, .cont => true
  | _, _ => false

def optStmtBeq : Option Stmt → Option Stmt → Bool
  | none, none => true
  | some s, some s' => stmtBeq s s'
  | _, _ => false

def stmtsBeq : List Stmt → List Stmt → Bool
  | [], [] => true
  | s :: ss, s' :: ss' => stmtBeq s s' && stmtsBeq ss ss'
  | _, _ => false

end

/-- Bool equality on operands of `exprBeq`: the nested cases open the `&&`
chain and the `==` of lawful types. -/
macro "beq_open " h:ident : tactic =>
  `(tactic| simp only [exprBeq, exprsBeq, optExprBeq, stmtBeq, optStmtBeq, stmtsBeq,
    Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at $h:ident)

mutual

theorem exprBeq_sound : ∀ {e e' : Expr}, exprBeq e e' = true → e = e'
  | .int _, .int _, h | .str _, .str _, h | .bool _, .bool _, h | .var _, .var _, h => by
    beq_open h; rw [h]
  | .null, .null, _ => rfl
  | .assign _ e, .assign _ e', h => by
    beq_open h; rw [h.1, exprBeq_sound (e := e) (e' := e') h.2]
  | .binary _ l r, .binary _ l' r', h | .logical _ l r, .logical _ l' r', h => by
    beq_open h
    obtain ⟨⟨ho, hl⟩, hr⟩ := h
    rw [ho, exprBeq_sound (e := l) (e' := l') hl, exprBeq_sound (e := r) (e' := r') hr]
  | .unary _ e, .unary _ e', h => by
    beq_open h; rw [h.1, exprBeq_sound (e := e) (e' := e') h.2]
  | .call f es, .call f' es', h => by
    beq_open h
    rw [exprBeq_sound (e := f) (e' := f') h.1, exprsBeq_sound (es := es) (es' := es') h.2]
  | .fn _ _ b, .fn _ _ b', h => by
    beq_open h
    obtain ⟨⟨hx, hps⟩, hb⟩ := h
    rw [hx, hps, stmtsBeq_sound (ss := b) (ss' := b') hb]
  | .int _, .str _, h | .int _, .bool _, h | .int _, .null, h | .int _, .var _, h
  | .int _, .assign .., h | .int _, .binary .., h | .int _, .logical .., h | .int _, .unary .., h
  | .int _, .call .., h | .int _, .fn .., h => by beq_open h
  | .str _, .int _, h | .str _, .bool _, h | .str _, .null, h | .str _, .var _, h
  | .str _, .assign .., h | .str _, .binary .., h | .str _, .logical .., h | .str _, .unary .., h
  | .str _, .call .., h | .str _, .fn .., h => by beq_open h
  | .bool _, .int _, h | .bool _, .str _, h | .bool _, .null, h | .bool _, .var _, h
  | .bool _, .assign .., h | .bool _, .binary .., h | .bool _, .logical .., h
  | .bool _, .unary .., h | .bool _, .call .., h | .bool _, .fn .., h => by beq_open h
  | .null, .int _, h | .null, .str _, h | .null, .bool _, h | .null, .var _, h
  | .null, .assign .., h | .null, .binary .., h | .null, .logical .., h | .null, .unary .., h
  | .null, .call .., h | .null, .fn .., h => by beq_open h
  | .var _, .int _, h | .var _, .str _, h | .var _, .bool _, h | .var _, .null, h
  | .var _, .assign .., h | .var _, .binary .., h | .var _, .logical .., h | .var _, .unary .., h
  | .var _, .call .., h | .var _, .fn .., h => by beq_open h
  | .assign .., .int _, h | .assign .., .str _, h | .assign .., .bool _, h
  | .assign .., .null, h | .assign .., .var _, h | .assign .., .binary .., h
  | .assign .., .logical .., h | .assign .., .unary .., h | .assign .., .call .., h
  | .assign .., .fn .., h => by beq_open h
  | .binary .., .int _, h | .binary .., .str _, h | .binary .., .bool _, h
  | .binary .., .null, h | .binary .., .var _, h | .binary .., .assign .., h
  | .binary .., .logical .., h | .binary .., .unary .., h | .binary .., .call .., h
  | .binary .., .fn .., h => by beq_open h
  | .logical .., .int _, h | .logical .., .str _, h | .logical .., .bool _, h
  | .logical .., .null, h | .logical .., .var _, h | .logical .., .assign .., h
  | .logical .., .binary .., h | .logical .., .unary .., h | .logical .., .call .., h
  | .logical .., .fn .., h => by beq_open h
  | .unary .., .int _, h | .unary .., .str _, h | .unary .., .bool _, h
  | .unary .., .null, h | .unary .., .var _, h | .unary .., .assign .., h
  | .unary .., .binary .., h | .unary .., .logical .., h | .unary .., .call .., h
  | .unary .., .fn .., h => by beq_open h
  | .call .., .int _, h | .call .., .str _, h | .call .., .bool _, h
  | .call .., .null, h | .call .., .var _, h | .call .., .assign .., h
  | .call .., .binary .., h | .call .., .logical .., h | .call .., .unary .., h
  | .call .., .fn .., h => by beq_open h
  | .fn .., .int _, h | .fn .., .str _, h | .fn .., .bool _, h
  | .fn .., .null, h | .fn .., .var _, h | .fn .., .assign .., h
  | .fn .., .binary .., h | .fn .., .logical .., h | .fn .., .unary .., h
  | .fn .., .call .., h => by beq_open h

theorem exprsBeq_sound : ∀ {es es' : List Expr}, exprsBeq es es' = true → es = es'
  | [], [], _ => rfl
  | e :: es, e' :: es', h => by
    beq_open h
    rw [exprBeq_sound (e := e) (e' := e') h.1, exprsBeq_sound (es := es) (es' := es') h.2]
  | [], _ :: _, h | _ :: _, [], h => by beq_open h

theorem optExprBeq_sound : ∀ {e e' : Option Expr}, optExprBeq e e' = true → e = e'
  | none, none, _ => rfl
  | some e, some e', h => by beq_open h; rw [exprBeq_sound (e := e) (e' := e') h]
  | none, some _, h | some _, none, h => by beq_open h

theorem stmtBeq_sound : ∀ {s s' : Stmt}, stmtBeq s s' = true → s = s'
  | .expr e, .expr e', h => by beq_open h; rw [exprBeq_sound (e := e) (e' := e') h]
  | .varDecl _ e, .varDecl _ e', h => by
    beq_open h; rw [h.1, optExprBeq_sound (e := e) (e' := e') h.2]
  | .block ss, .block ss', h => by beq_open h; rw [stmtsBeq_sound (ss := ss) (ss' := ss') h]
  | .ifStmt c t e, .ifStmt c' t' e', h => by
    beq_open h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    rw [exprBeq_sound (e := c) (e' := c') hc, stmtBeq_sound (s := t) (s' := t') ht,
      optStmtBeq_sound (s := e) (s' := e') he]
  | .whileStmt c b, .whileStmt c' b', h => by
    beq_open h
    rw [exprBeq_sound (e := c) (e' := c') h.1, stmtBeq_sound (s := b) (s' := b') h.2]
  | .forStmt i c s b, .forStmt i' c' s' b', h => by
    beq_open h
    obtain ⟨⟨⟨hi, hc⟩, hs⟩, hb⟩ := h
    rw [optStmtBeq_sound (s := i) (s' := i') hi, optExprBeq_sound (e := c) (e' := c') hc,
      optExprBeq_sound (e := s) (e' := s') hs, stmtBeq_sound (s := b) (s' := b') hb]
  | .ret e, .ret e', h => by beq_open h; rw [optExprBeq_sound (e := e) (e' := e') h]
  | .brk, .brk, _ | .cont, .cont, _ => rfl
  | .expr _, .varDecl .., h | .expr _, .block _, h | .expr _, .ifStmt .., h
  | .expr _, .whileStmt .., h | .expr _, .forStmt .., h | .expr _, .ret _, h
  | .expr _, .brk, h | .expr _, .cont, h => by beq_open h
  | .varDecl .., .expr _, h | .varDecl .., .block _, h | .varDecl .., .ifStmt .., h
  | .varDecl .., .whileStmt .., h | .varDecl .., .forStmt .., h | .varDecl .., .ret _, h
  | .varDecl .., .brk, h | .varDecl .., .cont, h => by beq_open h
  | .block _, .expr _, h | .block _, .varDecl .., h | .block _, .ifStmt .., h
  | .block _, .whileStmt .., h | .block _, .forStmt .., h | .block _, .ret _, h
  | .block _, .brk, h | .block _, .cont, h => by beq_open h
  | .ifStmt .., .expr _, h | .ifStmt .., .varDecl .., h | .ifStmt .., .block _, h
  | .ifStmt .., .whileStmt .., h | .ifStmt .., .forStmt .., h | .ifStmt .., .ret _, h
  | .ifStmt .., .brk, h | .ifStmt .., .cont, h => by beq_open h
  | .whileStmt .., .expr _, h | .whileStmt .., .varDecl .., h | .whileStmt .., .block _, h
  | .whileStmt .., .ifStmt .., h | .whileStmt .., .forStmt .., h | .whileStmt .., .ret _, h
  | .whileStmt .., .brk, h | .whileStmt .., .cont, h => by beq_open h
  | .forStmt .., .expr _, h | .forStmt .., .varDecl .., h | .forStmt .., .block _, h
  | .forStmt .., .ifStmt .., h | .forStmt .., .whileStmt .., h | .forStmt .., .ret _, h
  | .forStmt .., .brk, h | .forStmt .., .cont, h => by beq_open h
  | .ret _, .expr _, h | .ret _, .varDecl .., h | .ret _, .block _, h
  | .ret _, .ifStmt .., h | .ret _, .whileStmt .., h | .ret _, .forStmt .., h
  | .ret _, .brk, h | .ret _, .cont, h => by beq_open h
  | .brk, .expr _, h | .brk, .varDecl .., h | .brk, .block _, h
  | .brk, .ifStmt .., h | .brk, .whileStmt .., h | .brk, .forStmt .., h
  | .brk, .ret _, h | .brk, .cont, h => by beq_open h
  | .cont, .expr _, h | .cont, .varDecl .., h | .cont, .block _, h
  | .cont, .ifStmt .., h | .cont, .whileStmt .., h | .cont, .forStmt .., h
  | .cont, .ret _, h | .cont, .brk, h => by beq_open h

theorem optStmtBeq_sound : ∀ {s s' : Option Stmt}, optStmtBeq s s' = true → s = s'
  | none, none, _ => rfl
  | some s, some s', h => by beq_open h; rw [stmtBeq_sound (s := s) (s' := s') h]
  | none, some _, h | some _, none, h => by beq_open h

theorem stmtsBeq_sound : ∀ {ss ss' : List Stmt}, stmtsBeq ss ss' = true → ss = ss'
  | [], [], _ => rfl
  | s :: ss, s' :: ss', h => by
    beq_open h
    rw [stmtBeq_sound (s := s) (s' := s') h.1, stmtsBeq_sound (ss := ss) (ss' := ss') h.2]
  | [], _ :: _, h | _ :: _, [], h => by beq_open h

end

/-- The program decoded at `a` with count `n` is `p` (a kernel-decidable check). -/
def decodesTo (v : Nat → Option (BitVec 8)) (P : Nat → Bool) (fuel a n : Nat) (p : Program) :
    Bool :=
  match decodeProgram v P fuel a n with
  | some q => stmtsBeq q p
  | none => false

theorem decodesTo_eq {v : Nat → Option (BitVec 8)} {P : Nat → Bool} {fuel a n : Nat}
    {p : Program} (h : decodesTo v P fuel a n p = true) : decodeProgram v P fuel a n = some p := by
  unfold decodesTo at h
  split at h
  · rename_i q hq
    rw [hq, stmtsBeq_sound h]
  · cases h

/-- A successful check represents `p` at `a` with count `n`, reads covered by `P`. -/
theorem decodesTo_sound {m : Mem} {v : Nat → Option (BitVec 8)} {P : Nat → Bool}
    (hv : PartialView m v) {fuel a n : Nat} {p : Program} (h : decodesTo v P fuel a n p = true) :
    ProgramReprWithin m (P · = true) a n p :=
  decodeProgram_sound hv (decodesTo_eq h)

/-! ## Regression: one expression statement `print("hi");` -/

private def smokeLE (a w n : Nat) : List (Nat × BitVec 8) :=
  (List.range w).map fun i => (a + i, BitVec.ofNat 8 (n / 256 ^ i))

/-- Array at `0x100`; `Stmt` at `0x110`; call at `0x120`, callee `var` at
`0x140`, argument array at `0x150`, `str` at `0x160`; names at `0x180`/`0x188`. -/
private def smokeCells : List (Nat × BitVec 8) :=
  smokeLE 0x100 8 0x110 ++
  smokeLE 0x110 4 0 ++ smokeLE 0x118 8 0x120 ++
  smokeLE 0x120 4 9 ++ smokeLE 0x128 8 0x140 ++ smokeLE 0x130 8 0x150 ++ smokeLE 0x138 4 1 ++
  smokeLE 0x140 4 4 ++ smokeLE 0x148 8 0x180 ++
  smokeLE 0x150 8 0x160 ++
  smokeLE 0x160 4 1 ++ smokeLE 0x168 8 0x188 ++
  [(0x180, 0x70), (0x181, 0x72), (0x182, 0x69), (0x183, 0x6e), (0x184, 0x74), (0x185, 0),
   (0x188, 0x68), (0x189, 0x69), (0x18a, 0)]

private def smokeView (k : Nat) : Option (BitVec 8) := (smokeCells.find? (·.1 == k)).map (·.2)

example : decodesTo smokeView (fun k => 0x100 ≤ k && k < 0x18b) 16 0x100 1
    [.expr (.call (.var "print") [.str "hi"])] = true := by
  decide +kernel

/-- Leaving the argument string's NUL uncovered fails the check. -/
example : decodesTo smokeView (fun k => 0x100 ≤ k && k < 0x18a) 16 0x100 1
    [.expr (.call (.var "print") [.str "hi"])] = false := by
  decide +kernel

end Vsa.Sim.Boot
