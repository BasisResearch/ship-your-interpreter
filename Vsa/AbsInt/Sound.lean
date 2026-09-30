import Vsa.AbsInt.SoundLemmas

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

variable {A : Type} [AbsDom A]

def WhileM (cfg : Cfg) (as : List Addr) (s₀ : Store) (st : Status) (s₁ : Store) :
    Stmt → Prop
  | .whileStmt c b => LoopOK cfg (whileF (A := A) cfg c b) as s₀ st s₁
  | _ => True

section Motives

variable (A)

def MEval (st : St) (_ : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    SGam as st'.store (aeval σ e).st ∧ Gam (aeval σ e).val v

def MArgs (st : St) (_ : Nat) (env : Addr) (es : List Expr) (st' : St)
    (vs : List Value) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    SGam as st'.store (aevalArgs σ es).1 ∧ Pw Gam (aevalArgs σ es).2.1 vs

def MExec (cfg : Cfg) (st : St) (_ : Nat) (env : Addr) (s : Stmt) (st' : St)
    (status : Status) : Prop :=
  ∀ (as : List Addr), as.head? = some env →
    (∀ σ : AState A, SGam as st.store σ → SOK as (aexec cfg σ s) status st'.store) ∧
      WhileM (A := A) cfg as st.store status st'.store s

def MInit (cfg : Cfg) (st : St) (_ : Nat) (env : Addr) (init : Option Stmt)
    (st' : St) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    SGam as st'.store (aexecOpt cfg σ init).any

def MFor (cfg : Cfg) (st : St) (_ : Nat) (env : Addr) (cnd step : Option Expr)
    (b : Stmt) (st' : St) (status : Status) : Prop :=
  ∀ (as : List Addr), as.head? = some env →
    LoopOK cfg (forF (A := A) cfg cnd step b) as st.store status st'.store

def MCond (st : St) (_ : Nat) (env : Addr) (cnd : Option Expr) (st' : St) : Prop :=
  ∀ (as : List Addr) (I : AState A), as.head? = some env → SGam as st.store I →
    SGam as st'.store (match cnd with
      | none => I
      | some c => branch true c (optEval cnd I))

def MStep (st : St) (_ : Nat) (env : Addr) (step : Option Expr) (st' : St) : Prop :=
  ∀ (as : List Addr) (I : AState A), as.head? = some env → SGam as st.store I →
    SGam as st'.store (match step with
      | none => I
      | some _ => (optEval step I).st)

def MSeq (cfg : Cfg) (st : St) (_ : Nat) (env : Addr) (ss : List Stmt) (st' : St)
    (status : Status) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    SOK as (aexecSeq cfg σ ss) status st'.store

end Motives

macro "unfold_aeval" h:term : tactic =>
  `(tactic| simp only [aeval, SGam.isBot_false $h, Bool.false_eq_true, ↓reduceIte])

set_option hygiene false in

local macro "absint_rec" r:ident h:term : tactic => `(tactic| (
  refine $r
    (motive_1 := fun st d env e st' v _ => MEval A st d env e st' v)
    (motive_2 := fun st d env es st' vs _ => MArgs A st d env es st' vs)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun st d env s st' status _ => MExec A cfg st d env s st' status)
    (motive_5 := fun st d env init st' _ => MInit A cfg st d env init st')
    (motive_6 := fun st d env cnd step b st' status _ =>
      MFor A cfg st d env cnd step b st' status)
    (motive_7 := fun st d env cnd st' _ => MCond A st d env cnd st')
    (motive_8 := fun st d env step st' _ => MStep A st d env step st')
    (motive_9 := fun st d env ss st' status _ => MSeq A cfg st d env ss st' status)
    ?int ?str ?bool ?null ?var ?assign ?binary ?orTrue ?orFalse ?andFalse ?andTrue
    ?neg ?not ?call ?fn ?argsNil ?argsCons ?cClosure ?cPrint ?cPrintln ?cAssert
    ?sExpr ?sVarInit ?sVarNull ?sBlock ?sIfTrue ?sIfFalse ?sIfNone ?sWhileFalse
    ?sWhileBreak ?sWhileRet ?sWhileLoop ?sFor ?sRet ?sRetNull ?sBrk ?sCont
    ?initNone ?initSome ?flCondFalse ?flBreak ?flRet ?flLoop ?condNone ?condSome
    ?stepNone ?stepSome ?seqNil ?seqNormal ?seqAbrupt $h
  case int =>
    intro st d env n as σ hd hσ
    unfold_aeval hσ
    exact ⟨hσ, ofValue_sound _⟩
  case str =>
    intro st d env x as σ hd hσ
    unfold_aeval hσ
    exact ⟨hσ, ofValue_sound _⟩
  case bool =>
    intro st d env b as σ hd hσ
    unfold_aeval hσ
    exact ⟨hσ, ofValue_sound _⟩
  case null =>
    intro st d env as σ hd hσ
    unfold_aeval hσ
    exact ⟨hσ, ofValue_sound _⟩
  case var =>
    intro st d env x v hget as σ hd hσ
    unfold_aeval hσ
    exact ⟨hσ, (SGam.lookup hd hσ).1 _ hget⟩
  case assign =>
    intro st d env x e st' v store'' _ hset ih as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ih as σ hd hσ
    exact ⟨(SGam.assign hd h1 h2).1 _ hset, h2⟩
  case binary =>
    intro st d env op l r st' st'' lv rv v _ _ hop ihl ihr as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihl as σ hd hσ
    obtain ⟨h3, h4⟩ := ihr as _ hd h1
    exact ⟨h3, binop_sound hop h2 h4⟩
  case orTrue =>
    intro st d env l r st' lv hl hlt ihl as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihl as σ hd hσ
    exact ⟨SGam.join_l _ (branch_sound hd hl hlt h1 h2),
      boolOf_sound (fun _ => by simp [mayT_sound h2 hlt]) (fun h => by cases h)⟩
  case orFalse =>
    intro st d env l r st' st'' lv rv hl hlf _ ihl ihr as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihl as σ hd hσ
    obtain ⟨h3, h4⟩ := ihr as _ hd (branch_sound hd hl hlf h1 h2)
    exact ⟨SGam.join_r _ h3,
      boolOf_sound (fun h => by simp [mayF_sound h2 hlf, mayT_sound h4 h])
        (fun h => by simp [mayF_sound h2 hlf, mayF_sound h4 h])⟩
  case andFalse =>
    intro st d env l r st' lv hl hlf ihl as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihl as σ hd hσ
    exact ⟨SGam.join_l _ (branch_sound hd hl hlf h1 h2),
      boolOf_sound (fun h => by cases h) (fun _ => by simp [mayF_sound h2 hlf])⟩
  case andTrue =>
    intro st d env l r st' st'' lv rv hl hlt _ ihl ihr as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihl as σ hd hσ
    obtain ⟨h3, h4⟩ := ihr as _ hd (branch_sound hd hl hlt h1 h2)
    exact ⟨SGam.join_r _ h3,
      boolOf_sound (fun h => by simp [mayT_sound h2 hlt, mayT_sound h4 h])
        (fun h => by simp [mayT_sound h2 hlt, mayF_sound h4 h])⟩
  case neg =>
    intro st d env e st' n _ ih as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ih as σ hd hσ
    exact ⟨h1, neg_sound h2⟩
  case not =>
    intro st d env e st' v _ ih as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ih as σ hd hσ
    exact ⟨h1, notOf_sound h2⟩
  case call =>
    intro st d env f args st' st'' st''' fv vs v _ _ _ hcall ihf iha _ as σ hd hσ
    unfold_aeval hσ
    obtain ⟨h1, h2⟩ := ihf as σ hd hσ
    obtain ⟨h3, _⟩ := iha as _ hd h1
    refine ⟨?_, ?_⟩ <;> simp only [callSt, callVal] <;>
      cases hn : asNative (aeval σ f).val
    · simp only [SGam.isBot_false h3, Bool.false_eq_true, ↓reduceIte]
      trivial
    · rename_i g
      have hfv := asNative_sound h2 hn
      subst hfv
      cases g <;> cases hcall <;> exact h3
    · exact top_sound
    · rename_i g
      have hfv := asNative_sound h2 hn
      subst hfv
      cases g <;> cases hcall <;> exact ofValue_sound _
  case fn =>
    intro st d env name params body store' a halloc as σ hd hσ
    unfold_aeval hσ
    simp only [Store.allocClosure, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    exact ⟨SGam.frames_eq (s := st.store) rfl hσ, closure_sound _⟩
  case argsNil =>
    intro st d env as σ hd hσ
    exact ⟨hσ, trivial⟩
  case argsCons =>
    intro st d env e es st' st'' v vs _ _ ihe ihes as σ hd hσ
    obtain ⟨h1, h2⟩ := ihe as σ hd hσ
    obtain ⟨h3, h4⟩ := ihes as _ hd h1
    exact ⟨h3, h2, h4⟩
  case cClosure => intros; trivial
  case cPrint => intros; trivial
  case cPrintln => intros; trivial
  case cAssert => intros; trivial
  case sExpr =>
    intro st d env e st' v _ ih as hd
    exact ⟨fun σ hσ => (ih as σ hd hσ).1, trivial⟩
  case sVarInit =>
    intro st d env x e st' v _ ih as hd
    refine ⟨fun σ hσ => ?_, trivial⟩
    obtain ⟨h1, h2⟩ := ih as σ hd hσ
    exact SGam.define hd h1 h2
  case sVarNull =>
    intro st d env x as hd
    exact ⟨fun σ hσ => SGam.define hd hσ (ofValue_sound _), trivial⟩
  case sBlock =>
    intro st d env ss store' inner st' status halloc _ ih as hd
    exact ⟨fun σ hσ => SOK.pop (ih (inner :: as) σ.push rfl (SGam.push hd hσ halloc)),
      trivial⟩
  case sIfTrue =>
    intro st d env c t e st' st'' v status hc htr _ ihc iht as hd
    refine ⟨fun σ hσ => ?_, trivial⟩
    obtain ⟨h1, h2⟩ := ihc as σ hd hσ
    exact SOK.withAl _ (SOK.join_l _ ((iht as hd).1 _ (branch_sound hd hc htr h1 h2)))
  case sIfFalse =>
    intro st d env c t e st' st'' v status hc hf _ ihc ihe as hd
    refine ⟨fun σ hσ => ?_, trivial⟩
    obtain ⟨h1, h2⟩ := ihc as σ hd hσ
    exact SOK.withAl _ (SOK.join_r _ ((ihe as hd).1 _ (branch_sound hd hc hf h1 h2)))
  case sIfNone =>
    intro st d env c t st' v hc hf ihc as hd
    refine ⟨fun σ hσ => ?_, trivial⟩
    obtain ⟨h1, h2⟩ := ihc as σ hd hσ
    exact SOK.withAl _ (SOK.join_r _ (st := .normal) (branch_sound hd hc hf h1 h2))
  case sWhileFalse =>
    intro st d env c b st' v hc hf ihc as hd
    have hl : LoopOK cfg (whileF (A := A) cfg c b) as st.store .normal st'.store :=
      LoopOK.exit fun I hI => by
        obtain ⟨h1, h2⟩ := ihc as I hd hI
        exact SGam.join_l _ (branch_sound hd hc hf h1 h2)
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sWhileBreak =>
    intro st d env c b st' st'' v hc ht _ ihc ihb as hd
    have hl : LoopOK cfg (whileF (A := A) cfg c b) as st.store .normal st''.store :=
      LoopOK.exit fun I hI => by
        obtain ⟨h1, h2⟩ := ihc as I hd hI
        exact SGam.join_r _ ((ihb as hd).1 _ (branch_sound hd hc ht h1 h2))
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sWhileRet =>
    intro st d env c b st' st'' v rv hc ht _ ihc ihb as hd
    have hl : LoopOK cfg (whileF (A := A) cfg c b) as st.store (.ret rv) st''.store :=
      LoopOK.exit fun I hI => by
        obtain ⟨h1, h2⟩ := ihc as I hd hI
        exact (ihb as hd).1 _ (branch_sound hd hc ht h1 h2)
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sWhileLoop =>
    intro st d env c b st' st'' st''' v status status' hc ht _ hst _ ihc ihb ihw as hd
    have hl : LoopOK cfg (whileF (A := A) cfg c b) as st.store status' st'''.store := by
      refine LoopOK.cont (fun I hI => ?_) (ihw as hd).2
      obtain ⟨h1, h2⟩ := ihc as I hd hI
      have hb := (ihb as hd).1 _ (branch_sound hd hc ht h1 h2)
      rcases hst with rfl | rfl
      · exact SGam.join_l _ hb
      · exact SGam.join_r _ hb
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sFor =>
    intro st d env init cnd step b store' outer st' st'' status halloc _ _ ihi ihf as hd
    refine ⟨fun σ hσ => ?_, trivial⟩
    have hi := ihi (outer :: as) σ.push rfl (SGam.push hd hσ halloc)
    exact SOK.withAl _ (SOK.pop ((ihf (outer :: as) rfl).unroll _ _ hi))
  case sRet =>
    intro st d env e st' v _ ih as hd
    exact ⟨fun σ hσ => ih as σ hd hσ, trivial⟩
  case sRetNull =>
    intro st d env as hd
    exact ⟨fun σ hσ => ⟨hσ, ofValue_sound _⟩, trivial⟩
  case sBrk =>
    intro st d env as hd
    exact ⟨fun σ hσ => hσ, trivial⟩
  case sCont =>
    intro st d env as hd
    exact ⟨fun σ hσ => hσ, trivial⟩
  case initNone =>
    intro st d env as σ hd hσ
    exact SOK.any (st := .normal) hσ
  case initSome =>
    intro st d env s st' status _ ih as σ hd hσ
    exact SOK.any ((ih as hd).1 σ hσ)
  case flCondFalse =>
    intro st d env c step b st' v hc hf ihc as hd
    exact LoopOK.exit fun I hI => by
      obtain ⟨h1, h2⟩ := ihc as I hd hI
      exact SGam.join_l _ (branch_sound hd hc hf h1 h2)
  case flBreak =>
    intro st d env cnd step b st' st'' _ _ ihc ihb as hd
    exact LoopOK.exit fun I hI => SGam.join_r _ ((ihb as hd).1 _ (ihc as I hd hI))
  case flRet =>
    intro st d env cnd step b st' st'' rv _ _ ihc ihb as hd
    exact LoopOK.exit fun I hI => (ihb as hd).1 _ (ihc as I hd hI)
  case flLoop =>
    intro st d env cnd step b st' st'' st''' st'''' status status' _ _ hst _ _ ihc ihb
      ihs ihl as hd
    refine LoopOK.cont (fun I hI => ?_) (ihl as hd)
    have hb := (ihb as hd).1 _ (ihc as I hd hI)
    have hm : SGam as st''.store
        ((aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).norm.join
         (aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).cont) := by
      rcases hst with rfl | rfl
      · exact SGam.join_l _ hb
      · exact SGam.join_r _ hb
    have := ihs as _ hd hm
    cases step with
    | none => exact this
    | some e => exact this
  case condNone =>
    intro st d env as I hd hI
    exact hI
  case condSome =>
    intro st d env c st' v hc ht ihc as I hd hI
    obtain ⟨h1, h2⟩ := ihc as I hd hI
    exact branch_sound hd hc ht h1 h2
  case stepNone =>
    intro st d env as I hd hI
    exact hI
  case stepSome =>
    intro st d env e st' v _ ihe as I hd hI
    exact (ihe as I hd hI).1
  case seqNil =>
    intro st d env as σ hd hσ
    exact hσ
  case seqNormal =>
    intro st d env s ss st' st'' status _ _ ihs ihss as σ hd hσ
    exact SOK.seq_r _ (ihss as _ hd ((ihs as hd).1 σ hσ))
  case seqAbrupt =>
    intro st d env s ss st' status _ hne ihs as σ hd hσ
    exact SOK.seq_l _ hne ((ihs as hd).1 σ hσ)))

theorem eval_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr} {e : Expr}
    {v : Value} (h : EvalE st d env e st' v) : MEval A st d env e st' v := by
  absint_rec EvalE.rec h

theorem args_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr} {es : List Expr}
    {vs : List Value} (h : EvalArgs st d env es st' vs) : MArgs A st d env es st' vs := by
  absint_rec EvalArgs.rec h

theorem exec_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr} {s : Stmt}
    {status : Status} (h : ExecS st d env s st' status) :
    MExec A cfg st d env s st' status := by
  absint_rec ExecS.rec h

theorem init_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr}
    {init : Option Stmt} (h : ExecInit st d env init st') :
    MInit A cfg st d env init st' := by
  absint_rec ExecInit.rec h

theorem for_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr}
    {cnd step : Option Expr} {b : Stmt} {status : Status}
    (h : ForLoop st d env cnd step b st' status) :
    MFor A cfg st d env cnd step b st' status := by
  absint_rec ForLoop.rec h

theorem cond_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr}
    {cnd : Option Expr} (h : ForCond st d env cnd st') : MCond A st d env cnd st' := by
  absint_rec ForCond.rec h

theorem step_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr}
    {step : Option Expr} (h : ExecStep st d env step st') : MStep A st d env step st' := by
  absint_rec ExecStep.rec h

theorem seq_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr} {ss : List Stmt}
    {status : Status} (h : ExecSeq st d env ss st' status) :
    MSeq A cfg st d env ss st' status := by
  absint_rec ExecSeq.rec h

end Vsa.AbsInt
