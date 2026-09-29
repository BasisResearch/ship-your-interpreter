import Vsa.While.Types

/-!
# A verified type checker

`typeCheck Δ p` decides `WellTyped Δ p` (`typeCheck_iff`). The checker follows
the typing rules syntactically. A function literal's return type is read off
its first `return` statement (`retTySeq`), or is `null` when its body has
none; `retTy_sound`/`retTy_found` show this is the only type the rules allow.
-/

namespace Vsa.While.Types

open Vsa.While

/-- Operator result types (`BinTy` as a function). -/
def binTy : BinOp → Ty → Ty → Option Ty
  | .add, .int, .int => some .int
  | .add, .str, _ => some .str
  | .add, _, .str => some .str
  | .sub, .int, .int => some .int
  | .mul, .int, .int => some .int
  | .div, .int, .int => some .int
  | .mod, .int, .int => some .int
  | .eq, _, _ => some .bool
  | .ne, _, _ => some .bool
  | .lt, .int, .int => some .bool
  | .le, .int, .int => some .bool
  | .gt, .int, .int => some .bool
  | .ge, .int, .int => some .bool
  | .lt, .str, .str => some .bool
  | .le, .str, .str => some .bool
  | .gt, .str, .str => some .bool
  | .ge, .str, .str => some .bool
  | _, _, _ => none

/-- Call result types (`CallTy` as a function). -/
def callTy : Ty → List Ty → Option Ty
  | .fn ps r, ts => if ps = ts then some r else none
  | .native .print, _ => some .null
  | .native .println, _ => some .null
  | .native .assert, [_] => some .null
  | .native .assert, [_, _] => some .null
  | _, _ => none

/-- First available result. -/
def orO {α : Type} : Option α → Option α → Option α
  | some a, _ => some a
  | none, b => b

/-- The defined names after a statement. -/
def declOut (S : List String) : Stmt → List String
  | .varDecl x _ => x :: S
  | _ => S

/-- The defined names after a `for` initializer. -/
def initOut (S : List String) : Option Stmt → List String
  | some i => declOut S i
  | none => S

mutual

/-- Boolean decision procedure for `MustExit`. -/
def mustExitB : Stmt → Bool
  | .ret _ => true
  | .brk => true
  | .cont => true
  | .block ss => mustExitSeqB ss
  | .ifStmt _ t (some e) => mustExitB t && mustExitB e
  | _ => false

/-- Boolean decision procedure for `MustExitSeq`. -/
def mustExitSeqB : List Stmt → Bool
  | [] => false
  | s :: ss => mustExitB s || mustExitSeqB ss

end

mutual

/-- Expression type, if any. -/
def checkE (Δ : TyEnv) (S : List String) : Expr → Option Ty
  | .int _ => some .int
  | .str _ => some .str
  | .bool _ => some .bool
  | .null => some .null
  | .var x => if x ∈ S then some (Δ x) else none
  | .assign x e =>
    if x ∈ S ∧ checkE Δ S e = some (Δ x) then some (Δ x) else none
  | .binary op l r =>
    match checkE Δ S l, checkE Δ S r with
    | some tl, some tr => binTy op tl tr
    | _, _ => none
  | .logical _ l r =>
    match checkE Δ S l, checkE Δ S r with
    | some _, some _ => some .bool
    | _, _ => none
  | .unary .neg e => if checkE Δ S e = some .int then some .int else none
  | .unary .not e =>
    match checkE Δ S e with
    | some _ => some .bool
    | none => none
  | .call f args =>
    if args.length ≤ maxArgs then
      match checkE Δ S f, checkArgs Δ S args with
      | some tf, some ts => callTy tf ts
      | _, _ => none
    else none
  | .fn _ params body =>
    let r := (retTySeq Δ (params ++ S) body).getD .null
    if (checkSeq Δ (params ++ S) (some r) false body).isSome ∧
        (r = .null ∨ mustExitSeqB body = true) then
      some (.fn (params.map Δ) r)
    else none

/-- Argument types, if any. -/
def checkArgs (Δ : TyEnv) (S : List String) : List Expr → Option (List Ty)
  | [] => some []
  | e :: es =>
    match checkE Δ S e, checkArgs Δ S es with
    | some t, some ts => some (t :: ts)
    | _, _ => none

/-- Defined names after a statement, if it is well-typed. -/
def checkS (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) :
    Stmt → Option (List String)
  | .expr e => if (checkE Δ S e).isSome then some S else none
  | .varDecl x none => if Δ x = .null then some (x :: S) else none
  | .varDecl x (some e) =>
    if checkE Δ S e = some (Δ x) ∨ checkRec Δ S x e = true then some (x :: S) else none
  | .block ss => if (checkSeq Δ S R L ss).isSome then some S else none
  | .ifStmt c t (some e) =>
    if (checkE Δ S c).isSome ∧ (checkS Δ S R L t).isSome ∧ (checkS Δ S R L e).isSome then
      some S
    else none
  | .ifStmt c t none =>
    if (checkE Δ S c).isSome ∧ (checkS Δ S R L t).isSome then some S else none
  | .whileStmt c b =>
    if (checkE Δ S c).isSome ∧ (checkS Δ S R true b).isSome then some S else none
  | .forStmt init cnd step b =>
    match checkInit Δ S R L init with
    | some S₁ =>
      if checkEO Δ S₁ cnd = true ∧ checkEO Δ S₁ step = true ∧
          (checkS Δ S₁ R true b).isSome then some S
      else none
    | none => none
  | .ret (some e) =>
    match R with
    | some t => if checkE Δ S e = some t then some S else none
    | none => none
  | .ret none => if R = some .null then some S else none
  | .brk => if L = true then some S else none
  | .cont => if L = true then some S else none

/-- `var x = fn (…) {…}` with `x` bound in the body (`WtS.varRec`). -/
def checkRec (Δ : TyEnv) (S : List String) (x : String) : Expr → Bool
  | .fn _ params body =>
    match Δ x with
    | .fn ps r => decide (ps = params.map Δ) &&
        (checkSeq Δ (params ++ x :: S) (some r) false body).isSome &&
        (decide (r = .null) || mustExitSeqB body)
    | _ => false
  | _ => false

/-- The optional `for` initializer. -/
def checkInit (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) :
    Option Stmt → Option (List String)
  | none => some S
  | some s => checkS Δ S R L s

/-- An optional expression. -/
def checkEO (Δ : TyEnv) (S : List String) : Option Expr → Bool
  | none => true
  | some e => (checkE Δ S e).isSome

/-- Defined names after a sequence, if it is well-typed. -/
def checkSeq (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) :
    List Stmt → Option (List String)
  | [] => some S
  | s :: ss =>
    match checkS Δ S R L s with
    | some S₁ => checkSeq Δ S₁ R L ss
    | none => none

/-- The type of the first `return` in a statement (outside nested function
literals). -/
def retTy (Δ : TyEnv) (S : List String) : Stmt → Option Ty
  | .ret (some e) => checkE Δ S e
  | .ret none => some .null
  | .block ss => retTySeq Δ S ss
  | .ifStmt _ t (some e) => orO (retTy Δ S t) (retTy Δ S e)
  | .ifStmt _ t none => retTy Δ S t
  | .whileStmt _ b => retTy Δ S b
  | .forStmt init _ _ b => orO (retTyInit Δ S init) (retTy Δ (initOut S init) b)
  | _ => none

/-- The type of the first `return` in a `for` initializer. -/
def retTyInit (Δ : TyEnv) (S : List String) : Option Stmt → Option Ty
  | some i => retTy Δ S i
  | none => none

/-- The type of the first `return` in a sequence. -/
def retTySeq (Δ : TyEnv) (S : List String) : List Stmt → Option Ty
  | [] => none
  | s :: ss => orO (retTy Δ S s) (retTySeq Δ (declOut S s) ss)

end

/-- **The type checker.** -/
def typeCheck (Δ : TyEnv) (p : Program) : Bool :=
  decide (Δ "print" = .native .print) && decide (Δ "println" = .native .println) &&
    decide (Δ "assert" = .native .assert) &&
    (checkSeq Δ builtinNames none false p).isSome

/-! ## Operator and call tables -/

theorem binTy_sound {op : BinOp} {a b t : Ty} (h : binTy op a b = some t) : BinTy op a b t := by
  cases op <;> cases a <;> cases b <;> simp [binTy] at h <;> subst h <;>
    first
    | exact .cmpInt _ (by decide)
    | exact .cmpStr _ (by decide)
    | constructor

theorem binTy_complete {op : BinOp} {a b t : Ty} (h : BinTy op a b t) : binTy op a b = some t := by
  cases op <;> cases a <;> cases b <;> cases h <;> first | rfl | (exfalso; simp_all)

theorem callTy_sound {tf : Ty} {ts : List Ty} {t : Ty} (h : callTy tf ts = some t) :
    CallTy tf ts t := by
  match tf, ts, h with
  | .fn ps r, ts, h =>
    simp only [callTy] at h
    split at h
    · cases h; subst ps; exact .fn _ _
    · cases h
  | .native .print, _, h => cases h; exact .print _
  | .native .println, _, h => cases h; exact .println _
  | .native .assert, [_], h => cases h; exact .assert1 _
  | .native .assert, [_, _], h => cases h; exact .assert2 _ _
  | .native .assert, [], h => cases h
  | .native .assert, _ :: _ :: _ :: _, h => cases h
  | .int, _, h => cases h
  | .bool, _, h => cases h
  | .str, _, h => cases h
  | .null, _, h => cases h

theorem callTy_complete {tf : Ty} {ts : List Ty} {t : Ty} (h : CallTy tf ts t) :
    callTy tf ts = some t := by
  cases h <;> simp [callTy]

/-! ## `MustExit` decisions -/

mutual

theorem mustExit_of_b : ∀ {s : Stmt}, mustExitB s = true → MustExit s
  | .ret _, _ => .ret _
  | .brk, _ => .brk
  | .cont, _ => .cont
  | .block ss, h => .block ss (mustExitSeq_of_b (by simpa [mustExitB] using h))
  | .ifStmt c t (some e), h => by
    simp only [mustExitB, Bool.and_eq_true] at h
    exact .ite c t e (mustExit_of_b h.1) (mustExit_of_b h.2)
  | .ifStmt _ _ none, h => by simp [mustExitB] at h
  | .expr _, h => by simp [mustExitB] at h
  | .varDecl _ _, h => by simp [mustExitB] at h
  | .whileStmt _ _, h => by simp [mustExitB] at h
  | .forStmt _ _ _ _, h => by simp [mustExitB] at h

theorem mustExitSeq_of_b : ∀ {ss : List Stmt}, mustExitSeqB ss = true → MustExitSeq ss
  | [], h => by simp [mustExitSeqB] at h
  | s :: ss, h => by
    simp only [mustExitSeqB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .head s ss (mustExit_of_b h)
    · exact .tail s ss (mustExitSeq_of_b h)

end

theorem mustExitB_complete :
    (∀ s, MustExit s → mustExitB s = true) ∧ (∀ ss, MustExitSeq ss → mustExitSeqB ss = true) := by
  refine ⟨@MustExit.rec (fun s _ => mustExitB s = true) (fun ss _ => mustExitSeqB ss = true)
      ?ret ?brk ?cont ?block ?ite ?head ?tail,
    @MustExitSeq.rec (fun s _ => mustExitB s = true) (fun ss _ => mustExitSeqB ss = true)
      ?ret ?brk ?cont ?block ?ite ?head ?tail⟩
  case ret => intro; rfl
  case brk => rfl
  case cont => rfl
  case block => intro _ _ ih; simpa [mustExitB] using ih
  case ite => intro _ _ _ _ _ ih₁ ih₂; simp [mustExitB, ih₁, ih₂]
  case head => intro _ _ _ ih; simp [mustExitSeqB, ih]
  case tail => intro _ _ _ ih; simp [mustExitSeqB, ih]

/-! ## Soundness -/

section Sound

variable {Δ : TyEnv}

theorem isSome_iff {α : Type} {o : Option α} : o.isSome = true ↔ ∃ a, o = some a := by
  cases o <;> simp

mutual

theorem checkE_sound : (e : Expr) → ∀ {S T}, checkE Δ S e = some T → WtE Δ S e T
  | .int _, _, _, h => by cases h; exact .int _ _
  | .str _, _, _, h => by cases h; exact .str _ _
  | .bool _, _, _, h => by cases h; exact .bool _ _
  | .null, _, _, h => by cases h; exact .null _
  | .var x, S, T, h => by
    simp only [checkE] at h
    split at h
    · cases h; exact .var _ _ ‹_›
    · cases h
  | .assign x e, S, T, h => by
    simp only [checkE] at h
    split at h
    · rename_i hc; cases h; exact .assign _ _ _ hc.1 (checkE_sound e hc.2)
    · cases h
  | .binary op l r, S, T, h => by
    simp only [checkE] at h
    cases hl : checkE Δ S l <;> cases hr : checkE Δ S r <;> simp only [hl, hr, reduceCtorEq] at h
    exact .binary _ _ _ _ _ _ _ (checkE_sound l hl) (checkE_sound r hr) (binTy_sound h)
  | .logical op l r, S, T, h => by
    simp only [checkE] at h
    cases hl : checkE Δ S l <;> cases hr : checkE Δ S r <;> simp only [hl, hr, reduceCtorEq] at h
    cases h
    exact .logical _ _ _ _ _ _ (checkE_sound l hl) (checkE_sound r hr)
  | .unary .neg e, S, T, h => by
    simp only [checkE] at h
    split at h
    · rename_i hc; cases h; exact .neg _ _ (checkE_sound e hc)
    · cases h
  | .unary .not e, S, T, h => by
    simp only [checkE] at h
    cases he : checkE Δ S e <;> simp only [he, reduceCtorEq] at h
    cases h
    exact .not _ _ _ (checkE_sound e he)
  | .call f args, S, T, h => by
    simp only [checkE] at h
    split at h
    · rename_i hlen
      cases hf : checkE Δ S f <;> cases ha : checkArgs Δ S args <;> simp only [hf, ha, reduceCtorEq] at h
      exact .call _ _ _ _ _ _ (checkE_sound f hf) hlen (checkArgs_sound args ha) (callTy_sound h)
    · cases h
  | .fn name params body, S, T, h => by
    simp only [checkE] at h
    split at h
    · rename_i hc
      cases h
      obtain ⟨S', hS'⟩ := isSome_iff.mp hc.1
      refine .fn _ _ _ _ _ _ (checkSeq_sound body hS') ?_
      rcases hc.2 with h | h
      · exact .inl h
      · exact .inr (mustExitSeq_of_b h)
    · cases h

theorem checkArgs_sound : (es : List Expr) → ∀ {S ts}, checkArgs Δ S es = some ts →
    WtArgs Δ S es ts
  | [], _, _, h => by cases h; exact .nil _
  | e :: es, S, ts, h => by
    simp only [checkArgs] at h
    cases he : checkE Δ S e <;> cases hes : checkArgs Δ S es <;> simp only [he, hes, reduceCtorEq] at h
    cases h
    exact .cons _ _ _ _ _ (checkE_sound e he) (checkArgs_sound es hes)

theorem checkS_sound : (s : Stmt) → ∀ {S R L S'}, checkS Δ S R L s = some S' →
    WtS Δ S R L s S'
  | .expr e, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨t, ht⟩ := isSome_iff.mp hc
      exact .expr _ _ _ _ _ (checkE_sound e ht)
    · cases h
  | .varDecl x none, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · cases h; exact .varNull _ _ _ _ ‹_›
    · cases h
  | .varDecl x (some e), S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      rcases hc with hc | hc
      · exact .varInit _ _ _ _ _ (checkE_sound e hc)
      · exact checkRec_sound e hc
    · cases h
  | .block ss, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨S₁, h₁⟩ := isSome_iff.mp hc
      exact .block _ _ _ _ _ (checkSeq_sound ss h₁)
    · cases h
  | .ifStmt c t (some e), S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨_, h₁⟩ := isSome_iff.mp hc.1
      obtain ⟨_, h₂⟩ := isSome_iff.mp hc.2.1
      obtain ⟨_, h₃⟩ := isSome_iff.mp hc.2.2
      exact .ifSome _ _ _ _ _ _ _ _ _ (checkE_sound c h₁) (checkS_sound t h₂) (checkS_sound e h₃)
    · cases h
  | .ifStmt c t none, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨_, h₁⟩ := isSome_iff.mp hc.1
      obtain ⟨_, h₂⟩ := isSome_iff.mp hc.2
      exact .ifNone _ _ _ _ _ _ _ (checkE_sound c h₁) (checkS_sound t h₂)
    · cases h
  | .whileStmt c b, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨_, h₁⟩ := isSome_iff.mp hc.1
      obtain ⟨_, h₂⟩ := isSome_iff.mp hc.2
      exact .whileS _ _ _ _ _ _ _ (checkE_sound c h₁) (checkS_sound b h₂)
    · cases h
  | .forStmt init cnd step b, S, R, L, S', h => by
    simp only [checkS] at h
    cases hi : checkInit Δ S R L init <;> simp only [hi, reduceCtorEq] at h
    split at h
    · rename_i hc; cases h
      obtain ⟨_, hb⟩ := isSome_iff.mp hc.2.2
      exact .forS _ _ _ _ _ _ _ _ _ (checkInit_sound init hi) (checkEO_sound cnd hc.1)
        (checkEO_sound step hc.2.1) (checkS_sound b hb)
    · cases h
  | .ret (some e), S, R, L, S', h => by
    simp only [checkS] at h
    cases R with
    | none => cases h
    | some t =>
      simp only at h
      split at h
      · rename_i hc; cases h; exact .ret _ _ _ _ (checkE_sound e hc)
      · cases h
  | .ret none, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h; subst hc; exact .retNull _ _
    · cases h
  | .brk, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h; subst hc; exact .brk _ _
    · cases h
  | .cont, S, R, L, S', h => by
    simp only [checkS] at h
    split at h
    · rename_i hc; cases h; subst hc; exact .cont _ _
    · cases h

theorem checkRec_sound : (e : Expr) → ∀ {S R L x}, checkRec Δ S x e = true →
    WtS Δ S R L (.varDecl x (some e)) (x :: S)
  | .fn name params body, S, R, L, x, h => by
    simp only [checkRec] at h
    split at h
    · rename_i ps r hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨⟨hps, hb⟩, hr⟩ := h
      obtain ⟨_, hb⟩ := isSome_iff.mp hb
      subst hps
      refine .varRec _ _ _ _ _ _ _ _ _ (checkSeq_sound body hb) ?_ hx
      rcases hr with hr | hr
      · exact .inl hr
      · exact .inr (mustExitSeq_of_b hr)
    · cases h
  | .int _, _, _, _, _, h => by cases h
  | .str _, _, _, _, _, h => by cases h
  | .bool _, _, _, _, _, h => by cases h
  | .null, _, _, _, _, h => by cases h
  | .var _, _, _, _, _, h => by cases h
  | .assign _ _, _, _, _, _, h => by cases h
  | .binary _ _ _, _, _, _, _, h => by cases h
  | .logical _ _ _, _, _, _, _, h => by cases h
  | .unary _ _, _, _, _, _, h => by cases h
  | .call _ _, _, _, _, _, h => by cases h

theorem checkInit_sound : (o : Option Stmt) → ∀ {S R L S'}, checkInit Δ S R L o = some S' →
    WtInit Δ S R L o S'
  | none, _, _, _, _, h => by cases h; exact .none _ _ _
  | some s, _, _, _, _, h => .some _ _ _ _ _ (checkS_sound s h)

theorem checkEO_sound : (o : Option Expr) → ∀ {S}, checkEO Δ S o = true → WtEO Δ S o
  | none, _, _ => .none _
  | some e, _, h => by
    obtain ⟨_, he⟩ := isSome_iff.mp h
    exact .some _ _ _ (checkE_sound e he)

theorem checkSeq_sound : (ss : List Stmt) → ∀ {S R L S'}, checkSeq Δ S R L ss = some S' →
    WtSeq Δ S R L ss S'
  | [], _, _, _, _, h => by cases h; exact .nil _ _ _
  | s :: ss, S, R, L, S', h => by
    simp only [checkSeq] at h
    cases hs : checkS Δ S R L s <;> simp only [hs, reduceCtorEq] at h
    exact .cons _ _ _ _ _ _ _ (checkS_sound s hs) (checkSeq_sound ss h)

end

end Sound

/-! ## Completeness -/

section Complete

variable {Δ : TyEnv}

theorem declOut_of_wt {S : List String} {R : Option Ty} {L : Bool} {s : Stmt}
    {S' : List String} (h : WtS Δ S R L s S') : S' = declOut S s := by
  cases h <;> rfl

theorem initOut_of_wt {S : List String} {R : Option Ty} {L : Bool} {o : Option Stmt}
    {S' : List String} (h : WtInit Δ S R L o S') : S' = initOut S o := by
  cases h with
  | none => rfl
  | some _ _ _ _ _ h => exact declOut_of_wt h

theorem orO_eq_some {α : Type} {a b : Option α} {x : α} (h : orO a b = some x) :
    a = some x ∨ b = some x := by
  cases a with
  | some y => exact .inl h
  | none => exact .inr h

theorem orO_isSome_left {α : Type} {a : Option α} (b : Option α) (h : a.isSome = true) :
    (orO a b).isSome = true := by
  cases a with
  | some _ => rfl
  | none => cases h

theorem orO_isSome_right {α : Type} (a : Option α) {b : Option α} (h : b.isSome = true) :
    (orO a b).isSome = true := by
  cases a with
  | some _ => rfl
  | none => exact h

/-- What the checker computes for a well-typed statement. -/
structure StmtCheck (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) (s : Stmt)
    (S' : List String) : Prop where
  check : checkS Δ S R L s = some S'
  ret : ∀ r t, R = some r → retTy Δ S s = some t → t = r
  found : L = false → MustExit s → (retTy Δ S s).isSome = true

/-- What the checker computes for a well-typed sequence. -/
structure SeqCheck (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) (ss : List Stmt)
    (S' : List String) : Prop where
  check : checkSeq Δ S R L ss = some S'
  ret : ∀ r t, R = some r → retTySeq Δ S ss = some t → t = r
  found : L = false → MustExitSeq ss → (retTySeq Δ S ss).isSome = true

/-- What the checker computes for a well-typed `for` initializer. -/
structure InitCheck (Δ : TyEnv) (S : List String) (R : Option Ty) (L : Bool) (o : Option Stmt)
    (S' : List String) : Prop where
  check : checkInit Δ S R L o = some S'
  ret : ∀ r t, R = some r → retTyInit Δ S o = some t → t = r

mutual

theorem checkE_complete : (e : Expr) → ∀ {S T}, WtE Δ S e T → checkE Δ S e = some T
  | .int _, _, _, h => by cases h; rfl
  | .str _, _, _, h => by cases h; rfl
  | .bool _, _, _, h => by cases h; rfl
  | .null, _, _, h => by cases h; rfl
  | .var x, S, T, h => by
    cases h with
    | var _ _ hx => simp [checkE, hx]
  | .assign x e, S, T, h => by
    cases h with
    | assign _ _ _ hx he => simp [checkE, hx, checkE_complete e he]
  | .binary op l r, S, T, h => by
    cases h with
    | binary _ _ _ _ _ _ _ hl hr hbt =>
      simp only [checkE, checkE_complete l hl, checkE_complete r hr]
      exact binTy_complete hbt
  | .logical op l r, S, T, h => by
    cases h with
    | logical _ _ _ _ _ _ hl hr =>
      simp only [checkE, checkE_complete l hl, checkE_complete r hr]
  | .unary .neg e, S, T, h => by
    cases h with
    | neg _ _ he => simp [checkE, checkE_complete e he]
  | .unary .not e, S, T, h => by
    cases h with
    | not _ _ _ he => simp [checkE, checkE_complete e he]
  | .call f args, S, T, h => by
    cases h with
    | call _ _ _ _ _ _ hf hlen ha hct =>
      simp only [checkE, hlen, ↓reduceIte, checkE_complete f hf, checkArgs_complete args ha]
      exact callTy_complete hct
  | .fn name params body, S, T, h => by
    cases h with
    | fn _ _ _ _ r S' hb hr =>
      have C := checkSeq_complete body hb
      have hcand : (retTySeq Δ (params ++ S) body).getD .null = r := by
        cases hc : retTySeq Δ (params ++ S) body with
        | some t => exact C.ret r t rfl hc
        | none =>
          rcases hr with hr | hr
          · exact hr.symm
          · have := C.found rfl hr
            rw [hc] at this; cases this
      have hr' : r = .null ∨ mustExitSeqB body = true := by
        rcases hr with hr | hr
        · exact .inl hr
        · exact .inr (mustExitB_complete.2 _ hr)
      simp only [checkE, hcand, C.check, Option.isSome_some, true_and, hr', ↓reduceIte]

theorem checkArgs_complete : (es : List Expr) → ∀ {S ts}, WtArgs Δ S es ts →
    checkArgs Δ S es = some ts
  | [], _, _, h => by cases h; rfl
  | e :: es, S, ts, h => by
    cases h with
    | cons _ _ _ _ _ he hes =>
      simp only [checkArgs, checkE_complete e he, checkArgs_complete es hes]

theorem checkS_complete : (s : Stmt) → ∀ {S R L S'}, WtS Δ S R L s S' → StmtCheck Δ S R L s S'
  | .expr e, S, R, L, S', h => by
    cases h with
    | expr _ _ _ _ _ he =>
      refine ⟨by simp [checkS, checkE_complete e he], ?_, ?_⟩
      · intro r t _ ht; cases ht
      · intro _ hm; cases hm
  | .varDecl x none, S, R, L, S', h => by
    cases h with
    | varNull _ _ _ _ hx =>
      refine ⟨by simp [checkS, hx], ?_, ?_⟩
      · intro r t _ ht; cases ht
      · intro _ hm; cases hm
  | .varDecl x (some e), S, R, L, S', h => by
    have hno : ∀ r t, R = some r → retTy Δ S (.varDecl x (some e)) = some t → t = r := by
      intro r t _ ht; cases ht
    have hnf : L = false → MustExit (.varDecl x (some e)) →
        (retTy Δ S (.varDecl x (some e))).isSome = true := by
      intro _ hm; cases hm
    cases h with
    | varInit _ _ _ _ _ he => exact ⟨by simp [checkS, checkE_complete e he], hno, hnf⟩
    | varRec _ _ _ _ name params body r S'' hb hr hx =>
      refine ⟨?_, hno, hnf⟩
      have hrec : checkRec Δ S x (.fn name params body) = true := by
        have hr' : (decide (r = .null) || mustExitSeqB body) = true := by
          rcases hr with hr | hr
          · simp [hr]
          · simp [mustExitB_complete.2 _ hr]
        simp only [checkRec, hx, decide_true, Bool.true_and,
          (checkSeq_complete body hb).check, Option.isSome_some]
        exact hr'
      simp [checkS, hrec]
  | .block ss, S, R, L, S', h => by
    cases h with
    | block _ _ _ _ _ hs =>
      have C := checkSeq_complete ss hs
      refine ⟨by simp [checkS, C.check], fun r t hR ht => C.ret r t hR ht, ?_⟩
      intro hL hm
      cases hm with
      | block _ hm => exact C.found hL hm
  | .ifStmt c t (some e), S, R, L, S', h => by
    cases h with
    | ifSome _ _ _ _ _ _ _ _ _ hc ht he =>
      have Ct := checkS_complete t ht
      have Ce := checkS_complete e he
      refine ⟨by simp [checkS, checkE_complete c hc, Ct.check, Ce.check], ?_, ?_⟩
      · intro r x hR hx
        rcases orO_eq_some hx with hx | hx
        · exact Ct.ret r x hR hx
        · exact Ce.ret r x hR hx
      · intro hL hm
        cases hm with
        | ite _ _ _ hmt _ => exact orO_isSome_left _ (Ct.found hL hmt)
  | .ifStmt c t none, S, R, L, S', h => by
    cases h with
    | ifNone _ _ _ _ _ _ _ hc ht =>
      have Ct := checkS_complete t ht
      refine ⟨by simp [checkS, checkE_complete c hc, Ct.check], ?_, ?_⟩
      · intro r x hR hx; exact Ct.ret r x hR hx
      · intro _ hm; cases hm
  | .whileStmt c b, S, R, L, S', h => by
    cases h with
    | whileS _ _ _ _ _ _ _ hc hb =>
      have Cb := checkS_complete b hb
      refine ⟨by simp [checkS, checkE_complete c hc, Cb.check], ?_, ?_⟩
      · intro r x hR hx; exact Cb.ret r x hR hx
      · intro _ hm; cases hm
  | .forStmt init cnd step b, S, R, L, S', h => by
    cases h with
    | forS _ _ _ _ _ _ _ S₁ _ hi hc hs hb =>
      have Ci := checkInit_complete init hi
      have Cb := checkS_complete b hb
      have hS₁ := initOut_of_wt hi
      refine ⟨by simp [checkS, Ci.check, checkEO_complete cnd hc, checkEO_complete step hs,
        Cb.check], ?_, ?_⟩
      · intro r x hR hx
        rcases orO_eq_some hx with hx | hx
        · exact Ci.ret r x hR hx
        · rw [← hS₁] at hx; exact Cb.ret r x hR hx
      · intro _ hm; cases hm
  | .ret (some e), S, R, L, S', h => by
    cases h with
    | ret _ _ _ t he =>
      have he' := checkE_complete e he
      refine ⟨by simp [checkS, he'], ?_, ?_⟩
      · intro r x hR hx
        simp only [retTy, he', Option.some.injEq] at hx
        cases hR; exact hx.symm
      · intro _ _; simp [retTy, he']
  | .ret none, S, R, L, S', h => by
    cases h with
    | retNull =>
      refine ⟨by simp [checkS], ?_, ?_⟩
      · intro r x hR hx
        simp only [retTy, Option.some.injEq] at hx
        cases hR; exact hx.symm
      · intro _ _; rfl
  | .brk, S, R, L, S', h => by
    cases h with
    | brk =>
      refine ⟨by simp [checkS], ?_, ?_⟩
      · intro r t _ ht; cases ht
      · intro hL _; cases hL
  | .cont, S, R, L, S', h => by
    cases h with
    | cont =>
      refine ⟨by simp [checkS], ?_, ?_⟩
      · intro r t _ ht; cases ht
      · intro hL _; cases hL

theorem checkInit_complete : (o : Option Stmt) → ∀ {S R L S'}, WtInit Δ S R L o S' →
    InitCheck Δ S R L o S'
  | none, _, _, _, _, h => by
    cases h
    exact ⟨rfl, fun _ _ _ ht => by cases ht⟩
  | some s, _, _, _, _, h => by
    cases h with
    | some _ _ _ _ _ hs =>
      have C := checkS_complete s hs
      exact ⟨C.check, fun r t hR ht => C.ret r t hR ht⟩

theorem checkEO_complete : (o : Option Expr) → ∀ {S}, WtEO Δ S o → checkEO Δ S o = true
  | none, _, _ => rfl
  | some e, _, h => by
    cases h with
    | some _ _ _ he => simp [checkEO, checkE_complete e he]

theorem checkSeq_complete : (ss : List Stmt) → ∀ {S R L S'}, WtSeq Δ S R L ss S' →
    SeqCheck Δ S R L ss S'
  | [], _, _, _, _, h => by
    cases h
    exact ⟨rfl, fun _ _ _ ht => (by cases ht), fun _ hm => (by cases hm)⟩
  | s :: ss, S, R, L, S', h => by
    cases h with
    | cons _ _ _ _ _ S₁ _ hs hss =>
      have Cs := checkS_complete s hs
      have Css := checkSeq_complete ss hss
      have hS₁ := declOut_of_wt hs
      refine ⟨by simp [checkSeq, Cs.check, Css.check], ?_, ?_⟩
      · intro r t hR ht
        rcases orO_eq_some ht with ht | ht
        · exact Cs.ret r t hR ht
        · rw [← hS₁] at ht; exact Css.ret r t hR ht
      · intro hL hm
        cases hm with
        | head _ _ hm => exact orO_isSome_left _ (Cs.found hL hm)
        | tail _ _ hm =>
          show (orO _ (retTySeq Δ (declOut S s) ss)).isSome = true
          rw [← hS₁]; exact orO_isSome_right _ (Css.found hL hm)

end

end Complete

/-- **The checker decides typing.** -/
theorem typeCheck_iff {Δ : TyEnv} {p : Program} : typeCheck Δ p = true ↔ WellTyped Δ p := by
  constructor
  · intro h
    simp only [typeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
    obtain ⟨S', hS'⟩ := isSome_iff.mp h₄
    exact ⟨⟨h₁, h₂, h₃⟩, S', checkSeq_sound p hS'⟩
  · rintro ⟨hB, S', hp⟩
    simp [typeCheck, hB.print, hB.println, hB.assert, (checkSeq_complete p hp).check]

/-- `WellTyped Δ p` is decidable. -/
instance (Δ : TyEnv) (p : Program) : Decidable (WellTyped Δ p) :=
  decidable_of_iff _ typeCheck_iff

end Vsa.While.Types
