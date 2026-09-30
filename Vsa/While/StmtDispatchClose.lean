import Vsa.While.Trichotomy

namespace Vsa.While

theorem topLevelAbruptErrs (p : Program) (st' : St) (status : Status)
    (hne : status ≠ .normal) (h : ExecSeq initSt 0 0 p st' status) : BigStepErr p :=
  Or.inr ⟨st', status, hne, h⟩

def ProgressE (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (e : Expr),
    ¬ (∃ st' v, EvalE st d env e st' v) → ¬ EvalErr st d env e →
    EApprox n st d env e

def ProgressArgs (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (es : List Expr),
    ¬ (∃ st' vs, EvalArgs st d env es st' vs) → ¬ EvalArgsErr st d env es →
    ArgsApprox n st d env es

def ProgressC (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (fv : Value) (vs : List Value),
    ¬ (∃ st' v, Call st d fv vs st' v) → ¬ CallErr st d fv vs →
    CApprox n st d fv vs

def ProgressS (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (s : Stmt),
    ¬ (∃ st' status, ExecS st d env s st' status) → ¬ ExecErr st d env s →
    SApprox n st d env s

def ProgressFl (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (step : Option Expr)
    (b : Stmt),
    ¬ (∃ st' status, ForLoop st d env cnd step b st' status) →
    ¬ ForLoopErr st d env cnd step b →
    FlApprox n st d env cnd step b

def ProgressSeq (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
    ¬ (∃ st' status, ExecSeq st d env ss st' status) → ¬ ExecSeqErr st d env ss →
    Approx n st d env ss

def Progress (n : Nat) : Prop :=
  ProgressE n ∧ ProgressArgs n ∧ ProgressC n ∧ ProgressS n ∧ ProgressFl n ∧
    ProgressSeq n

theorem evalTri (hE : ProgressE n) (st : St) (d : Nat) (env : Addr) (e : Expr) :
    (∃ st' v, EvalE st d env e st' v) ∨ EvalErr st d env e ∨
      EApprox n st d env e := by
  by_cases hc : ∃ st' v, EvalE st d env e st' v
  · exact Or.inl hc
  by_cases he : EvalErr st d env e
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hE st d env e hc he))

theorem argsTri (hA : ProgressArgs n) (st : St) (d : Nat) (env : Addr)
    (es : List Expr) :
    (∃ st' vs, EvalArgs st d env es st' vs) ∨ EvalArgsErr st d env es ∨
      ArgsApprox n st d env es := by
  by_cases hc : ∃ st' vs, EvalArgs st d env es st' vs
  · exact Or.inl hc
  by_cases he : EvalArgsErr st d env es
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hA st d env es hc he))

theorem callTri (hC : ProgressC n) (st : St) (d : Nat) (fv : Value)
    (vs : List Value) :
    (∃ st' v, Call st d fv vs st' v) ∨ CallErr st d fv vs ∨
      CApprox n st d fv vs := by
  by_cases hc : ∃ st' v, Call st d fv vs st' v
  · exact Or.inl hc
  by_cases he : CallErr st d fv vs
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hC st d fv vs hc he))

theorem stmtTri (hS : ProgressS n) (st : St) (d : Nat) (env : Addr) (s : Stmt) :
    (∃ st' status, ExecS st d env s st' status) ∨ ExecErr st d env s ∨
      SApprox n st d env s := by
  by_cases hc : ∃ st' status, ExecS st d env s st' status
  · exact Or.inl hc
  by_cases he : ExecErr st d env s
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hS st d env s hc he))

theorem flTri (hFl : ProgressFl n) (st : St) (d : Nat) (env : Addr)
    (cnd : Option Expr) (step : Option Expr) (b : Stmt) :
    (∃ st' status, ForLoop st d env cnd step b st' status) ∨
      ForLoopErr st d env cnd step b ∨ FlApprox n st d env cnd step b := by
  by_cases hc : ∃ st' status, ForLoop st d env cnd step b st' status
  · exact Or.inl hc
  by_cases he : ForLoopErr st d env cnd step b
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hFl st d env cnd step b hc he))

theorem progressE_succ (hE : ProgressE n) (hA : ProgressArgs n) (hC : ProgressC n)
    (st : St) (d : Nat) (env : Addr) (e : Expr)
    (hnc : ¬ (∃ st' v, EvalE st d env e st' v)) (hne : ¬ EvalErr st d env e) :
    EApprox (n + 1) st d env e := by
  cases e with
  | int m => exact absurd ⟨st, .int m, .int st d env m⟩ hnc
  | str s => exact absurd ⟨st, .str s, .str st d env s⟩ hnc
  | bool b => exact absurd ⟨st, .bool b, .bool st d env b⟩ hnc
  | null => exact absurd ⟨st, .null, .null st d env⟩ hnc
  | var x =>
    cases hget : st.store.get? env x with
    | none => exact absurd (.varUndef st d env x hget) hne
    | some v => exact absurd ⟨st, v, .var st d env x v hget⟩ hnc
  | assign x e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · cases hset : st'.store.set? env x v with
      | none => exact absurd (.assignUnbound st d env x e st' v hrun hset) hne
      | some store'' =>
        exact absurd ⟨⟨store'', st'.out⟩, v, .assign st d env x e st' v store'' hrun hset⟩ hnc
    · exact absurd (.assignE st d env x e herr) hne
    · exact .assignE n st d env x e hdiv
  | binary op l r =>
    rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
    · rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
      · cases hbo : binOpSem st''.store op lv rv with
        | none => exact absurd (.binaryOp st d env op l r st' st'' lv rv hl hr hbo) hne
        | some v => exact absurd ⟨st'', v, .binary st d env op l r st' st'' lv rv v hl hr hbo⟩ hnc
      · exact absurd (.binaryR st d env op l r st' lv hl herr) hne
      · exact .binaryR n st d env op l r st' lv hl hdiv
    · exact absurd (.binaryL st d env op l r herr) hne
    · exact .binaryL n st d env op l r hdiv
  | logical op l r =>
    cases op with
    | or =>
      rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
      · by_cases htr : lv.truthy = true
        · exact absurd ⟨st', .bool true, .orTrue st d env l r st' lv hl htr⟩ hnc
        · have hf : lv.truthy = false := by
            cases h : lv.truthy with
            | true => exact absurd h htr
            | false => rfl
          rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
          · exact absurd ⟨st'', .bool rv.truthy,
              .orFalse st d env l r st' st'' lv rv hl hf hr⟩ hnc
          · exact absurd (.orR st d env l r st' lv hl hf herr) hne
          · exact .orR n st d env l r st' lv hl hf hdiv
      · exact absurd (.orL st d env l r herr) hne
      · exact .orL n st d env l r hdiv
    | and =>
      rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
      · by_cases htr : lv.truthy = true
        · rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
          · exact absurd ⟨st'', .bool rv.truthy,
              .andTrue st d env l r st' st'' lv rv hl htr hr⟩ hnc
          · exact absurd (.andR st d env l r st' lv hl htr herr) hne
          · exact .andR n st d env l r st' lv hl htr hdiv
        · have hf : lv.truthy = false := by
            cases h : lv.truthy with
            | true => exact absurd h htr
            | false => rfl
          exact absurd ⟨st', .bool false, .andFalse st d env l r st' lv hl hf⟩ hnc
      · exact absurd (.andL st d env l r herr) hne
      · exact .andL n st d env l r hdiv
  | unary op e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · cases op with
      | not => exact absurd ⟨st', .bool (!v.truthy), .not st d env e st' v hrun⟩ hnc
      | neg =>
        cases v with
        | int m => exact absurd ⟨st', .int (wrap64 (-m)), .neg st d env e st' m hrun⟩ hnc
        | null => exact absurd (.negType st d env e st' .null hrun (by intro n h; cases h)) hne
        | bool b => exact absurd (.negType st d env e st' (.bool b) hrun (by intro n h; cases h)) hne
        | str s => exact absurd (.negType st d env e st' (.str s) hrun (by intro n h; cases h)) hne
        | closure a => exact absurd (.negType st d env e st' (.closure a) hrun (by intro n h; cases h)) hne
        | native f => exact absurd (.negType st d env e st' (.native f) hrun (by intro n h; cases h)) hne
    · exact absurd (.unaryE st d env op e herr) hne
    · exact .unaryE n st d env op e hdiv
  | call f args =>
    rcases evalTri hE st d env f with ⟨st', fv, hf⟩ | herr | hdiv
    · by_cases hbound : args.length ≤ maxArgs
      · rcases argsTri hA st' d env args with ⟨st'', vs, hargs⟩ | herr | hdiv
        · rcases callTri hC st'' d fv vs with ⟨st''', v, hcall⟩ | herr | hdiv
          · exact absurd
              ⟨st''', v, .call st d env f args st' st'' st''' fv vs v
                hf hbound hargs hcall⟩ hnc
          · exact absurd
              (.callC st d env f args st' st'' fv vs hf hbound hargs herr) hne
          · exact .callC n st d env f args st' st'' fv vs hf hbound hargs hdiv
        · exact absurd (.callArgs st d env f args st' fv hf hbound herr) hne
        · exact .callArgs n st d env f args st' fv hf hbound hdiv
      · exact absurd (.callTooMany st d env f args st' fv hf (by omega)) hne
    · exact absurd (.callF st d env f args herr) hne
    · exact .callF n st d env f args hdiv
  | fn name params body =>
    exact absurd
      ⟨⟨(st.store.allocClosure ⟨env, name, params, body⟩).1, st.out⟩,
        .closure (st.store.allocClosure ⟨env, name, params, body⟩).2,
        .fn st d env name params body _ _ rfl⟩ hnc

theorem seqTri (hSeq : ProgressSeq n) (st : St) (d : Nat) (env : Addr)
    (ss : List Stmt) :
    (∃ st' status, ExecSeq st d env ss st' status) ∨ ExecSeqErr st d env ss ∨
      Approx n st d env ss := by
  by_cases hc : ∃ st' status, ExecSeq st d env ss st' status
  · exact Or.inl hc
  by_cases he : ExecSeqErr st d env ss
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hSeq st d env ss hc he))

theorem progressArgs_succ (hE : ProgressE n) (hA : ProgressArgs n)
    (st : St) (d : Nat) (env : Addr) (es : List Expr)
    (hnc : ¬ (∃ st' vs, EvalArgs st d env es st' vs))
    (hne : ¬ EvalArgsErr st d env es) :
    ArgsApprox (n + 1) st d env es := by
  cases es with
  | nil => exact absurd ⟨st, [], .nil st d env⟩ hnc
  | cons e es' =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · rcases argsTri hA st' d env es' with ⟨st'', vs, hargs⟩ | herr | hdiv
      · exact absurd ⟨st'', v :: vs, .cons st d env e es' st' st'' v vs hrun hargs⟩ hnc
      · exact absurd (.tail st d env e es' st' v hrun herr) hne
      · exact .tail n st d env e es' st' v hrun hdiv
    · exact absurd (.head st d env e es' herr) hne
    · exact .head n st d env e es' hdiv

theorem progressC_succ (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (fv : Value) (vs : List Value)
    (hnc : ¬ (∃ st' v, Call st d fv vs st' v)) (hne : ¬ CallErr st d fv vs) :
    CApprox (n + 1) st d fv vs := by
  cases fv with
  | null => exact absurd (.notCallable st d .null vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | bool b => exact absurd (.notCallable st d (.bool b) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | int m => exact absurd (.notCallable st d (.int m) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | str s => exact absurd (.notCallable st d (.str s) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | native f =>
    cases f with
    | print => exact absurd ⟨_, _, .print st d vs⟩ hnc
    | println => exact absurd ⟨_, _, .println st d vs⟩ hnc
    | assert =>

      by_cases harity1 : ∃ v, vs = [v]
      · obtain ⟨v, hv⟩ := harity1; subst hv
        by_cases htr : v.truthy = true
        · exact absurd ⟨st, .null, .assertOk st d [v] v v (Or.inl rfl) htr⟩ hnc
        · have hf : v.truthy = false := by
            cases h : v.truthy with
            | true => exact absurd h htr
            | false => rfl
          exact absurd (.assertFail st d [v] v v (Or.inl rfl) hf) hne
      · by_cases harity2 : ∃ v m, vs = [v, m]
        · obtain ⟨v, m, hv⟩ := harity2; subst hv
          by_cases htr : v.truthy = true
          · exact absurd ⟨st, .null, .assertOk st d [v, m] v m (Or.inr rfl) htr⟩ hnc
          · have hf : v.truthy = false := by
              cases h : v.truthy with
              | true => exact absurd h htr
              | false => rfl
            exact absurd (.assertFail st d [v, m] v m (Or.inr rfl) hf) hne
        · exact absurd (.assertArity st d vs
            (by intro v h; exact harity1 ⟨v, h⟩)
            (by intro v m h; exact harity2 ⟨v, m, h⟩)) hne
  | closure a =>
    cases hcl : st.store.closures[a]? with
    | none => exact absurd (.badClosure st d a vs hcl) hne
    | some cd =>
      by_cases harity : vs.length = cd.params.length
      · by_cases hdepth : d < maxCallDepth
        ·

          cases halloc : st.store.allocFrame (some cd.env) with
          | mk store' frame =>
          rcases seqTri hSeq
              ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
                st.out⟩ (d + 1) frame cd.body with
            ⟨st'', status, hseq⟩ | herr | hdiv
          ·
            cases status with
            | normal =>
              exact absurd ⟨st'', .null,
                .closure st d a cd vs store' frame st'' .normal .null hcl harity hdepth
                  halloc hseq (Or.inl ⟨rfl, rfl⟩)⟩ hnc
            | ret rv =>
              exact absurd ⟨st'', rv,
                .closure st d a cd vs store' frame st'' (.ret rv) rv hcl harity hdepth
                  halloc hseq (Or.inr rfl)⟩ hnc
            | brk =>
              exact absurd (.escape st d a cd vs store' frame st'' .brk hcl harity
                hdepth halloc hseq (Or.inl rfl)) hne
            | cont =>
              exact absurd (.escape st d a cd vs store' frame st'' .cont hcl harity
                hdepth halloc hseq (Or.inr rfl)) hne
          · exact absurd (.body st d a cd vs store' frame hcl harity hdepth halloc herr) hne
          · exact .body n st d a cd vs store' frame hcl harity hdepth halloc hdiv
        · exact absurd (.depth st d a cd vs hcl harity hdepth) hne
      · exact absurd (.arity st d a cd vs hcl harity) hne

theorem progressSeq_succ (hS : ProgressS n) (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (hnc : ¬ (∃ st' status, ExecSeq st d env ss st' status))
    (hne : ¬ ExecSeqErr st d env ss) :
    Approx (n + 1) st d env ss := by
  cases ss with
  | nil => exact absurd ⟨st, .normal, .nil st d env⟩ hnc
  | cons s ss' =>
    rcases stmtTri hS st d env s with ⟨st', status, hrun⟩ | herr | hdiv
    · cases status with
      | normal =>

        rcases (by
          by_cases hc : ∃ st'' status, ExecSeq st' d env ss' st'' status
          · exact Or.inl hc
          by_cases herr : ExecSeqErr st' d env ss'
          · exact Or.inr (Or.inl herr)
          · exact Or.inr (Or.inr (hSeq st' d env ss' hc herr))
          : (∃ st'' status, ExecSeq st' d env ss' st'' status) ∨
              ExecSeqErr st' d env ss' ∨ Approx n st' d env ss') with
          ⟨st'', status, hseq⟩ | herr | hdiv
        · exact absurd ⟨st'', status, .consNormal st d env s ss' st' st'' status hrun hseq⟩ hnc
        · exact absurd (.tail st d env s ss' st' hrun herr) hne
        · exact .step n st d env s ss' st' hrun hdiv
      | brk =>
        exact absurd ⟨st', .brk, .consAbrupt st d env s ss' st' .brk hrun (by intro h; cases h)⟩ hnc
      | cont =>
        exact absurd ⟨st', .cont, .consAbrupt st d env s ss' st' .cont hrun (by intro h; cases h)⟩ hnc
      | ret rv =>
        exact absurd ⟨st', .ret rv, .consAbrupt st d env s ss' st' (.ret rv) hrun (by intro h; cases h)⟩ hnc
    · exact absurd (.head st d env s ss' herr) hne
    · exact .head n st d env s ss' hdiv

theorem progressS_succ (hE : ProgressE n)
    (hS : ProgressS n) (hFl : ProgressFl n) (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (env : Addr) (s : Stmt)
    (hnc : ¬ (∃ st' status, ExecS st d env s st' status)) (hne : ¬ ExecErr st d env s) :
    SApprox (n + 1) st d env s := by
  cases s with
  | expr e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · exact absurd ⟨st', .normal, .expr st d env e st' v hrun⟩ hnc
    · exact absurd (.expr st d env e herr) hne
    · exact .expr n st d env e hdiv
  | varDecl x init =>
    cases init with
    | none => exact absurd ⟨⟨st.store.define env x .null, st.out⟩, .normal, .varNull st d env x⟩ hnc
    | some e =>
      rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
      · exact absurd ⟨⟨st'.store.define env x v, st'.out⟩, .normal,
          .varInit st d env x e st' v hrun⟩ hnc
      · exact absurd (.varInit st d env x e herr) hne
      · exact .varInit n st d env x e hdiv
  | block ss =>
    cases halloc : st.store.allocFrame (some env) with
    | mk store' inner =>
      rcases seqTri hSeq ⟨store', st.out⟩ d inner ss with
        ⟨st', status, hseq⟩ | herr | hdiv
      · exact absurd ⟨st', status, .block st d env ss store' inner st' status halloc hseq⟩ hnc
      · exact absurd (.block st d env ss store' inner halloc herr) hne
      · exact .block n st d env ss store' inner halloc hdiv
  | ifStmt c t e =>
    rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
    · by_cases htr : v.truthy = true
      · rcases stmtTri hS st' d env t with ⟨st'', status, ht⟩ | herr | hdiv
        · exact absurd ⟨st'', status, .ifTrue st d env c t e st' st'' v status hc htr ht⟩ hnc
        · exact absurd (.ifThen st d env c t e st' v hc htr herr) hne
        · exact .ifThen n st d env c t e st' v hc htr hdiv
      · have hf : v.truthy = false := by
          cases h : v.truthy with | true => exact absurd h htr | false => rfl
        cases e with
        | none => exact absurd ⟨st', .normal, .ifNone st d env c t st' v hc hf⟩ hnc
        | some e' =>
          rcases stmtTri hS st' d env e' with ⟨st'', status, he'⟩ | herr | hdiv
          · exact absurd ⟨st'', status, .ifFalse st d env c t e' st' st'' v status hc hf he'⟩ hnc
          · exact absurd (.ifElse st d env c t e' st' v hc hf herr) hne
          · exact .ifElse n st d env c t e' st' v hc hf hdiv
    · exact absurd (.ifCond st d env c t e herr) hne
    · exact .ifCond n st d env c t e hdiv
  | whileStmt c b =>
    rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
    · by_cases htr : v.truthy = true
      · rcases stmtTri hS st' d env b with ⟨st'', status, hb⟩ | herr | hdiv
        · cases status with
          | brk => exact absurd ⟨st'', .normal, .whileBreak st d env c b st' st'' v hc htr hb⟩ hnc
          | ret rv => exact absurd ⟨st'', .ret rv, .whileRet st d env c b st' st'' v rv hc htr hb⟩ hnc
          | normal =>
            rcases stmtTri hS st'' d env (.whileStmt c b) with
              ⟨st''', status', hloop⟩ | herr | hdiv
            · exact absurd ⟨st''', status', .whileLoop st d env c b st' st'' st''' v .normal status' hc htr hb (Or.inl rfl) hloop⟩ hnc
            · exact absurd (.whileLoop st d env c b st' st'' v .normal hc htr hb (Or.inl rfl) herr) hne
            · exact .whileLoop n st d env c b st' st'' v .normal hc htr hb (Or.inl rfl) hdiv
          | cont =>
            rcases stmtTri hS st'' d env (.whileStmt c b) with
              ⟨st''', status', hloop⟩ | herr | hdiv
            · exact absurd ⟨st''', status', .whileLoop st d env c b st' st'' st''' v .cont status' hc htr hb (Or.inr rfl) hloop⟩ hnc
            · exact absurd (.whileLoop st d env c b st' st'' v .cont hc htr hb (Or.inr rfl) herr) hne
            · exact .whileLoop n st d env c b st' st'' v .cont hc htr hb (Or.inr rfl) hdiv
        · exact absurd (.whileBody st d env c b st' v hc htr herr) hne
        · exact .whileBody n st d env c b st' v hc htr hdiv
      · have hf : v.truthy = false := by
          cases h : v.truthy with | true => exact absurd h htr | false => rfl
        exact absurd ⟨st', .normal, .whileFalse st d env c b st' v hc hf⟩ hnc
    · exact absurd (.whileCond st d env c b herr) hne
    · exact .whileCond n st d env c b hdiv
  | forStmt init cnd step b =>
    cases halloc : st.store.allocFrame (some env) with
    | mk store' outer =>
      cases init with
      | none =>

        rcases flTri hFl ⟨store', st.out⟩ d outer cnd step b with
          ⟨st', status, hfl⟩ | herr | hdiv
        · exact absurd ⟨st', status,
            .forStart st d env none cnd step b store' outer ⟨store', st.out⟩ st' status
              halloc (.none ⟨store', st.out⟩ d outer) hfl⟩ hnc
        · exact absurd (.forLoop st d env none cnd step b store' outer ⟨store', st.out⟩
            halloc (.none ⟨store', st.out⟩ d outer) herr) hne
        · exact .forLoop n st d env none cnd step b store' outer ⟨store', st.out⟩
            halloc (.none ⟨store', st.out⟩ d outer) hdiv
      | some si =>

        rcases stmtTri hS ⟨store', st.out⟩ d outer si with ⟨st', status, hsi⟩ | herr | hdiv
        · rcases flTri hFl st' d outer cnd step b with ⟨st'', status', hfl⟩ | herr | hdiv
          · exact absurd ⟨st'', status',
              .forStart st d env (some si) cnd step b store' outer st' st'' status'
                halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) hfl⟩ hnc
          · exact absurd (.forLoop st d env (some si) cnd step b store' outer st'
              halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) herr) hne
          · exact .forLoop n st d env (some si) cnd step b store' outer st'
              halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) hdiv
        · exact absurd (.forInit st d env si cnd step b store' outer halloc herr) hne
        · exact .forInit n st d env si cnd step b store' outer halloc hdiv
  | ret e =>
    cases e with
    | none => exact absurd ⟨st, .ret .null, .retNull st d env⟩ hnc
    | some e' =>
      rcases evalTri hE st d env e' with ⟨st', v, hrun⟩ | herr | hdiv
      · exact absurd ⟨st', .ret v, .ret st d env e' st' v hrun⟩ hnc
      · exact absurd (.ret st d env e' herr) hne
      · exact .ret n st d env e' hdiv
  | brk => exact absurd ⟨st, .brk, .brk st d env⟩ hnc
  | cont => exact absurd ⟨st, .cont, .cont st d env⟩ hnc

theorem progressFl_succ (hE : ProgressE n) (hS : ProgressS n) (hFl : ProgressFl n)
    (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (step : Option Expr)
    (b : Stmt)
    (hnc : ¬ (∃ st' status, ForLoop st d env cnd step b st' status))
    (hne : ¬ ForLoopErr st d env cnd step b) :
    FlApprox (n + 1) st d env cnd step b := by

  have hcond : (FlApprox (n + 1) st d env cnd step b) ∨
      (∃ st', ForCond st d env cnd st') := by
    cases cnd with
    | none => exact Or.inr ⟨st, .none st d env⟩
    | some c =>
      rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
      · by_cases htr : v.truthy = true
        · exact Or.inr ⟨st', .some st d env c st' v hc htr⟩
        · have hf : v.truthy = false := by
            cases h : v.truthy with | true => exact absurd h htr | false => rfl
          exact absurd ⟨st', .normal, .condFalse st d env c step b st' v hc hf⟩ hnc
      · exact absurd (.cond st d env c step b herr) hne
      · exact Or.inl (.cond n st d env c step b hdiv)
  rcases hcond with hdone | ⟨st', hfc⟩
  · exact hdone

  rcases stmtTri hS st' d env b with ⟨st'', status, hb⟩ | herr | hdiv
  · cases status with
    | brk => exact absurd ⟨st'', .normal, .bodyBreak st d env cnd step b st' st'' hfc hb⟩ hnc
    | ret rv => exact absurd ⟨st'', .ret rv, .bodyRet st d env cnd step b st' st'' rv hfc hb⟩ hnc
    | normal =>

      cases step with
      | none =>
        rcases flTri hFl st'' d env cnd none b with ⟨st''', status', hloop⟩ | herr | hdiv
        · exact absurd ⟨st''', status', .loop st d env cnd none b st' st'' st'' st''' .normal status' hfc hb (Or.inl rfl) (.none st'' d env) hloop⟩ hnc
        · exact absurd (.loop st d env cnd none b st' st'' st'' .normal hfc hb (Or.inl rfl) (.none st'' d env) herr) hne
        · exact .loop n st d env cnd none b st' st'' st'' .normal hfc hb (Or.inl rfl) (.none st'' d env) hdiv
      | some e =>
        rcases evalTri hE st'' d env e with ⟨st''', ev, hstep⟩ | herr | hdiv
        · rcases flTri hFl st''' d env cnd (some e) b with ⟨st4, status', hloop⟩ | herr | hdiv
          · exact absurd ⟨st4, status', .loop st d env cnd (some e) b st' st'' st''' st4 .normal status' hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) hloop⟩ hnc
          · exact absurd (.loop st d env cnd (some e) b st' st'' st''' .normal hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) herr) hne
          · exact .loop n st d env cnd (some e) b st' st'' st''' .normal hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) hdiv
        · exact absurd (.step st d env cnd e b st' st'' .normal hfc hb (Or.inl rfl) herr) hne
        · exact .step n st d env cnd e b st' st'' .normal hfc hb (Or.inl rfl) hdiv
    | cont =>
      cases step with
      | none =>
        rcases flTri hFl st'' d env cnd none b with ⟨st''', status', hloop⟩ | herr | hdiv
        · exact absurd ⟨st''', status', .loop st d env cnd none b st' st'' st'' st''' .cont status' hfc hb (Or.inr rfl) (.none st'' d env) hloop⟩ hnc
        · exact absurd (.loop st d env cnd none b st' st'' st'' .cont hfc hb (Or.inr rfl) (.none st'' d env) herr) hne
        · exact .loop n st d env cnd none b st' st'' st'' .cont hfc hb (Or.inr rfl) (.none st'' d env) hdiv
      | some e =>
        rcases evalTri hE st'' d env e with ⟨st''', ev, hstep⟩ | herr | hdiv
        · rcases flTri hFl st''' d env cnd (some e) b with ⟨st4, status', hloop⟩ | herr | hdiv
          · exact absurd ⟨st4, status', .loop st d env cnd (some e) b st' st'' st''' st4 .cont status' hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) hloop⟩ hnc
          · exact absurd (.loop st d env cnd (some e) b st' st'' st''' .cont hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) herr) hne
          · exact .loop n st d env cnd (some e) b st' st'' st''' .cont hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) hdiv
        · exact absurd (.step st d env cnd e b st' st'' .cont hfc hb (Or.inr rfl) herr) hne
        · exact .step n st d env cnd e b st' st'' .cont hfc hb (Or.inr rfl) hdiv
  · exact absurd (.body st d env cnd step b st' hfc herr) hne
  · exact .body n st d env cnd step b st' hfc hdiv

theorem progress :
    ∀ n, Progress n := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun st d env e _ _ => .zero st d env e,
           fun st d env es _ _ => .zero st d env es,
           fun st d fv vs _ _ => .zero st d fv vs,
           fun st d env s _ _ => .zero st d env s,
           fun st d env cnd step b _ _ => .zero st d env cnd step b,
           fun st d env ss _ _ => .zero st d env ss⟩
  | succ n ih =>
    obtain ⟨ihE, ihA, ihC, ihS, ihFl, ihSeq⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro st d env e hnc hne
      exact progressE_succ ihE ihA ihC st d env e hnc hne
    ·
      intro st d env es hnc hne
      exact progressArgs_succ ihE ihA st d env es hnc hne
    ·
      intro st d fv vs hnc hne
      exact progressC_succ ihSeq st d fv vs hnc hne
    ·
      intro st d env s hnc hne
      exact progressS_succ ihE ihS ihFl ihSeq st d env s hnc hne
    ·
      intro st d env cnd step b hnc hne
      exact progressFl_succ ihE ihS ihFl st d env cnd step b hnc hne
    ·
      intro st d env ss hnc hne
      exact progressSeq_succ ihS ihSeq st d env ss hnc hne

theorem stmtDispatchD_holds : StmtDispatchD := by
  intro st d env s
  by_cases hc : ∃ st' status, ExecS st d env s st' status
  · exact Or.inl hc
  by_cases he : ExecErr st d env s
  · exact Or.inr (Or.inl he)
  · refine Or.inr (Or.inr ?_)
    intro n
    exact (progress n).2.2.2.1 st d env s hc he

theorem bigStep_or_err_of_execSeq (p : Program)
    {st' : St} {status : Status} (h : ExecSeq initSt 0 0 p st' status) :
    (∃ out, BigStep p out) ∨ BigStepErr p := by
  cases status with
  | normal => exact Or.inl ⟨st'.out, st', h, rfl⟩
  | brk => exact Or.inr (topLevelAbruptErrs p st' .brk (by intro h; cases h) h)
  | cont => exact Or.inr (topLevelAbruptErrs p st' .cont (by intro h; cases h) h)
  | ret v => exact Or.inr (topLevelAbruptErrs p st' (.ret v) (by intro h; cases h) h)

theorem trichotomy_unconditional : Trichotomy := by
  have hnode : NodeDispatch4 :=
    nodeDispatch4_of_stmtDispatchD stmtDispatchD_holds
  intro p
  by_cases hterm : ∃ st' status, ExecSeq initSt 0 0 p st' status
  · obtain ⟨st', status, hexec⟩ := hterm
    rcases bigStep_or_err_of_execSeq p hexec with hbs | herr
    · exact Or.inl hbs
    · exact Or.inr (Or.inl herr)
  by_cases herr : BigStepErr p
  · exact Or.inr (Or.inl herr)
  · exact Or.inr (Or.inr (fun n =>
      approx_of_nodeDispatch4 hnode n initSt 0 0 p hterm
        (fun hseqerr => herr (Or.inl hseqerr))))

end Vsa.While
