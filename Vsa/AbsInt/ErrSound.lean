import Vsa.AbsInt.Program
import Vsa.AbsInt.ErrK

/-!
# Soundness of the alarms

If a statement run from a store in `γ(σ)` reaches a runtime error of kind
`k` (`ExecErrK`), then `k` is among the alarms `aexec` raises from `σ`. So a
kind absent from `alarms cfg p` cannot occur in any run of `p`
(`kind_sound`), and a program without alarms has no runtime error at all
(`no_error_of_no_alarms`).

Every motive also records `k ≠ .abrupt`: a closure body cannot raise the
top-level `abrupt` error, so an unanalysed call covers any kind it raises by
`Kind.inCall`.
-/

namespace Vsa.AbsInt

open Vsa.While AbsDom

variable {A : Type} [AbsDom A]

theorem Kind.mem_inCall {k : Kind} (h : k ≠ .abrupt) : k ∈ Kind.inCall := by
  cases k <;> simp_all [Kind.inCall]

theorem binFailKind_ne_abrupt (op : BinOp) (l r : Value) : binFailKind op l r ≠ .abrupt := by
  unfold binFailKind
  split <;> decide

/-- A loop's alarms cover an error reached from `s₀`, both at every
post-fixpoint and in every unrolling. -/
structure LoopAl (cfg : Cfg) (F : AState A → LStep A) (k : Kind) (as : List Addr)
    (s₀ : Store) : Prop where
  fix : ∀ J, (∀ s, SGam as s (F J).next → SGam as s J) → SGam as s₀ J → k ∈ (F J).al
  unroll : ∀ n I, SGam as s₀ I → k ∈ (loopAbs cfg F n I).al

/-- The error occurs in the current iteration. -/
theorem LoopAl.here {cfg : Cfg} {F : AState A → LStep A} {k : Kind} {as : List Addr}
    {s₀ : Store} (h : ∀ I, SGam as s₀ I → k ∈ (F I).al) : LoopAl cfg F k as s₀ where
  fix J _ hJ := h J hJ
  unroll n I hI := by
    cases n with
    | zero => exact h _ (postFix_ge hI)
    | succ n =>
      simp only [loopAbs]
      split
      · exact h I hI
      · exact Kind.mem_union.2 (Or.inl (h I hI))

/-- The error occurs in a later iteration, entered from `s₀'`. -/
theorem LoopAl.later {cfg : Cfg} {F : AState A → LStep A} {k : Kind} {as : List Addr}
    {s₀ s₀' : Store} (hc : ∀ I, SGam as s₀ I → SGam as s₀' (F I).next)
    (ih : LoopAl cfg F k as s₀') : LoopAl cfg F k as s₀ where
  fix J hJ h := ih.fix J hJ (hJ _ (hc J h))
  unroll n I hI := by
    cases n with
    | zero =>
      exact ih.fix _ (fun _ hs => postFix_post hs) (postFix_post (hc _ (postFix_ge hI)))
    | succ n =>
      simp only [loopAbs]
      split
      · rename_i hcond
        simp only [Bool.or_eq_true] at hcond
        have hn := hc I hI
        rcases hcond with hb | hle
        · rw [SGam.isBot_false hn] at hb; cases hb
        · exact ih.fix I (fun _ hs => SGam.le hle hs) (SGam.le hle hn)
      · exact Kind.mem_union.2 (Or.inr (ih.unroll n _ (hc I hI)))

/-- The loop part of the statement error motive. -/
def WhileE (cfg : Cfg) (k : Kind) (as : List Addr) (s₀ : Store) : Stmt → Prop
  | .whileStmt c b => LoopAl cfg (whileF (A := A) cfg c b) k as s₀
  | _ => True

section Motives

variable (A)

/-- Expression error motive. -/
def EEval (k : Kind) (st : St) (env : Addr) (e : Expr) : Prop :=
  k ≠ .abrupt ∧ ∀ (as : List Addr) (σ : AState A), as.head? = some env →
    SGam as st.store σ → k ∈ (aeval σ e).al

/-- Argument-list error motive. -/
def EArgs (k : Kind) (st : St) (env : Addr) (es : List Expr) : Prop :=
  k ≠ .abrupt ∧ ∀ (as : List Addr) (σ : AState A), as.head? = some env →
    SGam as st.store σ → k ∈ (aevalArgs σ es).2.2

/-- Call error motive. -/
def ECall (k : Kind) (fv : Value) (vs : List Value) : Prop :=
  k ≠ .abrupt ∧ ∀ (a : A) (avs : List A), Gam a fv → Pw Gam avs vs → k ∈ callAl a avs

/-- Statement error motive. -/
def EExec (cfg : Cfg) (k : Kind) (st : St) (env : Addr) (s : Stmt) : Prop :=
  k ≠ .abrupt ∧ ∀ (as : List Addr), as.head? = some env →
    (∀ σ : AState A, SGam as st.store σ → k ∈ (aexec cfg σ s).al) ∧
      WhileE (A := A) cfg k as st.store s

/-- `for` loop error motive. -/
def EFor (cfg : Cfg) (k : Kind) (st : St) (env : Addr) (cnd step : Option Expr)
    (b : Stmt) : Prop :=
  k ≠ .abrupt ∧ ∀ (as : List Addr), as.head? = some env →
    LoopAl cfg (forF (A := A) cfg cnd step b) k as st.store

/-- Sequence error motive. -/
def ESeq (cfg : Cfg) (k : Kind) (st : St) (env : Addr) (ss : List Stmt) : Prop :=
  k ≠ .abrupt ∧ ∀ (as : List Addr) (σ : AState A), as.head? = some env →
    SGam as st.store σ → k ∈ (aexecSeq cfg σ ss).al

end Motives

/-- Close a membership goal in a union of alarm lists. -/
macro "mem_al" : tactic =>
  `(tactic| simp_all [Kind.mem_union, Kind.inCall])

/-- `assert` on arguments where the first may be falsy raises an alarm. -/
theorem assertOk_false_of_falsy {avs : List A} {vs : List Value} {v m : Value}
    (hvs : vs = [v] ∨ vs = [v, m]) (hf : v.truthy = false) (hp : Pw Gam avs vs) :
    assertOk avs = false := by
  rcases hvs with rfl | rfl
  · match avs, hp with
    | [a], hp => simp [assertOk, mayF_sound hp.1 hf]
  · match avs, hp with
    | [a, _], hp => simp [assertOk, mayF_sound hp.1 hf]

theorem assertOk_false_of_arity {avs : List A} {vs : List Value}
    (h1 : ∀ v, vs ≠ [v]) (h2 : ∀ v m, vs ≠ [v, m]) (hp : Pw Gam avs vs) :
    assertOk avs = false := by
  match avs, vs, hp with
  | [], _, _ => rfl
  | [_], [v], _ => exact absurd rfl (h1 v)
  | [_, _], [v, m], _ => exact absurd rfl (h2 v m)
  | _ :: _ :: _ :: _, _, _ => rfl

/-- Calling a closure value: no native is identified. -/
theorem callAl_closure {a : A} {avs : List A} {c : Addr} (ha : Gam a (.closure c)) :
    callAl a avs = Kind.inCall := by
  unfold callAl
  cases hn : asNative a with
  | none => rfl
  | some g => cases asNative_sound ha hn

set_option hygiene false in
/-- One application of an error recursor with the alarm motives. -/
local macro "absint_err_rec" r:ident h:term : tactic => `(tactic| (
  refine $r
    (motive_1 := fun k st _ env e _ => EEval A k st env e)
    (motive_2 := fun k st _ env es _ => EArgs A k st env es)
    (motive_3 := fun k _ _ fv vs _ => ECall A k fv vs)
    (motive_4 := fun k st _ env s _ => EExec A cfg k st env s)
    (motive_5 := fun k st _ env cnd step b _ => EFor A cfg k st env cnd step b)
    (motive_6 := fun k st _ env ss _ => ESeq A cfg k st env ss)
    ?varUndef ?assignE ?assignUnbound ?binaryL ?binaryR ?binaryOp ?orL ?orR ?andL ?andR
    ?unaryE ?negType ?callF ?callTooMany ?callArgs ?callC ?argsHead ?argsTail
    ?notCallable ?badClosure ?arity ?depth ?body ?escape ?assertFail ?assertArity
    ?sExpr ?sVarInit ?sBlock ?sIfCond ?sIfThen ?sIfElse ?sWhileCond ?sWhileBody
    ?sWhileLoop ?sForInit ?sForLoop ?sRet ?flCond ?flBody ?flStep ?flLoop
    ?seqHead ?seqTail $h
  case varUndef =>
    intro st d env x hnone
    refine ⟨by decide, fun as σ hd hσ => ?_⟩
    unfold_aeval hσ
    rw [(SGam.lookup hd hσ).2 hnone]
    simp
  case assignE =>
    intro k st d env x e _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    unfold_aeval hσ
    mem_al
  case assignUnbound =>
    intro st d env x e st' v he hset
    refine ⟨by decide, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg he as σ hd hσ
    have := (SGam.assign hd h1 h2).2 hset
    unfold_aeval hσ
    mem_al
  case binaryL =>
    intro k st d env op l r _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    unfold_aeval hσ
    mem_al
  case binaryR =>
    intro k st d env op l r st' lv hl _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, _⟩ := eval_sound cfg hl as σ hd hσ
    have := ih.2 as _ hd h1
    unfold_aeval hσ
    mem_al
  case binaryOp =>
    intro st d env op l r st' st'' lv rv hl hr hop
    refine ⟨binFailKind_ne_abrupt op lv rv, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hl as σ hd hσ
    obtain ⟨_, h4⟩ := eval_sound cfg hr as _ hd h1
    have := binErr_sound hop h2 h4
    unfold_aeval hσ
    mem_al
  case orL =>
    intro k st d env l r _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    unfold_aeval hσ
    mem_al
  case orR =>
    intro k st d env l r st' lv hl hlf _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hl as σ hd hσ
    have := ih.2 as _ hd (branch_sound hd hl hlf h1 h2)
    unfold_aeval hσ
    mem_al
  case andL =>
    intro k st d env l r _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    unfold_aeval hσ
    mem_al
  case andR =>
    intro k st d env l r st' lv hl hlt _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hl as σ hd hσ
    have := ih.2 as _ hd (branch_sound hd hl hlt h1 h2)
    unfold_aeval hσ
    mem_al
  case unaryE =>
    intro k st d env op e _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    cases op <;> unfold_aeval hσ <;> mem_al
  case negType =>
    intro st d env e st' v he hv
    refine ⟨by decide, fun as σ hd hσ => ?_⟩
    obtain ⟨_, h2⟩ := eval_sound cfg he as σ hd hσ
    have := negErr_sound h2 hv
    unfold_aeval hσ
    mem_al
  case callF =>
    intro k st d env f args _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    unfold_aeval hσ
    mem_al
  case callTooMany =>
    intro st d env f args st' fv _ hlt
    refine ⟨by decide, fun as σ hd hσ => ?_⟩
    have : ¬ args.length ≤ maxArgs := Nat.not_le.mpr hlt
    unfold_aeval hσ
    mem_al
  case callArgs =>
    intro k st d env f args st' fv hf _ _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, _⟩ := eval_sound cfg hf as σ hd hσ
    have := ih.2 as _ hd h1
    unfold_aeval hσ
    mem_al
  case callC =>
    intro k st d env f args st' st'' fv vs hf _ ha _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hf as σ hd hσ
    obtain ⟨_, h4⟩ := args_sound cfg ha as _ hd h1
    have := ih.2 _ _ h2 h4
    unfold_aeval hσ
    mem_al
  case argsHead =>
    intro k st d env e es _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as σ hd hσ
    simp only [aevalArgs]
    mem_al
  case argsTail =>
    intro k st d env e es st' v he _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    obtain ⟨h1, _⟩ := eval_sound cfg he as σ hd hσ
    have := ih.2 as _ hd h1
    simp only [aevalArgs]
    mem_al
  case notCallable =>
    intro st d fv vs _ hnn
    refine ⟨by decide, fun a avs ha _ => ?_⟩
    unfold callAl
    cases hn : asNative a with
    | none => simp [Kind.inCall]
    | some g => exact absurd (asNative_sound ha hn) (hnn g)
  case badClosure =>
    intro st d c vs _
    exact ⟨by decide, fun a avs ha _ => by rw [callAl_closure ha]; decide⟩
  case arity =>
    intro st d c cd vs _ _
    exact ⟨by decide, fun a avs ha _ => by rw [callAl_closure ha]; decide⟩
  case depth =>
    intro st d c cd vs _ _ _
    exact ⟨by decide, fun a avs ha _ => by rw [callAl_closure ha]; decide⟩
  case body =>
    intro k st d c cd vs store' frame _ _ _ _ _ ih
    exact ⟨ih.1, fun a avs ha _ => by rw [callAl_closure ha]; exact Kind.mem_inCall ih.1⟩
  case escape =>
    intro st d c cd vs store' frame st' status _ _ _ _ _ _
    exact ⟨by decide, fun a avs ha _ => by rw [callAl_closure ha]; decide⟩
  case assertFail =>
    intro st d vs v m hvs hf
    refine ⟨by decide, fun a avs ha hp => ?_⟩
    unfold callAl
    cases hn : asNative a with
    | none => simp [Kind.inCall]
    | some g =>
      cases asNative_sound ha hn
      simp [assertOk_false_of_falsy hvs hf hp]
  case assertArity =>
    intro st d vs h1 h2
    refine ⟨by decide, fun a avs ha hp => ?_⟩
    unfold callAl
    cases hn : asNative a with
    | none => simp [Kind.inCall]
    | some g =>
      cases asNative_sound ha hn
      simp [assertOk_false_of_arity h1 h2 hp]
  case sExpr =>
    intro k st d env e _ ih
    exact ⟨ih.1, fun as hd => ⟨fun σ hσ => ih.2 as σ hd hσ, trivial⟩⟩
  case sVarInit =>
    intro k st d env x e _ ih
    exact ⟨ih.1, fun as hd => ⟨fun σ hσ => ih.2 as σ hd hσ, trivial⟩⟩
  case sBlock =>
    intro k st d env ss store' inner halloc _ ih
    exact ⟨ih.1, fun as hd =>
      ⟨fun σ hσ => ih.2 (inner :: as) σ.push rfl (SGam.push hd hσ halloc), trivial⟩⟩
  case sIfCond =>
    intro k st d env c t e _ ih
    refine ⟨ih.1, fun as hd => ⟨fun σ hσ => ?_, trivial⟩⟩
    have := ih.2 as σ hd hσ
    simp only [aexec]
    mem_al
  case sIfThen =>
    intro k st d env c t e st' v hc ht _ ih
    refine ⟨ih.1, fun as hd => ⟨fun σ hσ => ?_, trivial⟩⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hc as σ hd hσ
    have := (ih.2 as hd).1 _ (branch_sound hd hc ht h1 h2)
    simp only [aexec, SRes.join]
    mem_al
  case sIfElse =>
    intro k st d env c t e st' v hc hf _ ih
    refine ⟨ih.1, fun as hd => ⟨fun σ hσ => ?_, trivial⟩⟩
    obtain ⟨h1, h2⟩ := eval_sound cfg hc as σ hd hσ
    have := (ih.2 as hd).1 _ (branch_sound hd hc hf h1 h2)
    simp only [aexec, aexecOpt, SRes.join]
    mem_al
  case sWhileCond =>
    intro k st d env c b _ ih
    refine ⟨ih.1, fun as hd => ?_⟩
    have hl : LoopAl cfg (whileF (A := A) cfg c b) k as st.store :=
      LoopAl.here fun I hI => by
        have := ih.2 as I hd hI
        simp only [whileF, whileStep]
        mem_al
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sWhileBody =>
    intro k st d env c b st' v hc ht _ ih
    refine ⟨ih.1, fun as hd => ?_⟩
    have hl : LoopAl cfg (whileF (A := A) cfg c b) k as st.store :=
      LoopAl.here fun I hI => by
        obtain ⟨h1, h2⟩ := eval_sound cfg hc as I hd hI
        have := (ih.2 as hd).1 _ (branch_sound hd hc ht h1 h2)
        simp only [whileF, whileStep]
        mem_al
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sWhileLoop =>
    intro k st d env c b st' st'' v status hc ht hb hst _ ih
    refine ⟨ih.1, fun as hd => ?_⟩
    have hl : LoopAl cfg (whileF (A := A) cfg c b) k as st.store := by
      refine LoopAl.later (fun I hI => ?_) (ih.2 as hd).2
      obtain ⟨h1, h2⟩ := eval_sound cfg hc as I hd hI
      have hb' := (exec_sound cfg hb as hd).1 _ (branch_sound hd hc ht h1 h2)
      rcases hst with rfl | rfl
      · exact SGam.join_l _ hb'
      · exact SGam.join_r _ hb'
    exact ⟨fun σ hσ => hl.unroll _ _ hσ, hl⟩
  case sForInit =>
    intro k st d env init cnd step b store' outer halloc _ ih
    refine ⟨ih.1, fun as hd => ⟨fun σ hσ => ?_, trivial⟩⟩
    have := (ih.2 (outer :: as) rfl).1 _ (SGam.push hd hσ halloc)
    simp only [aexec, aexecOpt]
    mem_al
  case sForLoop =>
    intro k st d env init cnd step b store' outer st' halloc hi _ ih
    refine ⟨ih.1, fun as hd => ⟨fun σ hσ => ?_, trivial⟩⟩
    have h1 := init_sound cfg hi (outer :: as) σ.push rfl (SGam.push hd hσ halloc)
    exact Kind.mem_union.2 (Or.inr ((ih.2 (outer :: as) rfl).unroll cfg.unroll _ h1))
  case sRet =>
    intro k st d env e _ ih
    exact ⟨ih.1, fun as hd => ⟨fun σ hσ => ih.2 as σ hd hσ, trivial⟩⟩
  case flCond =>
    intro k st d env c step b _ ih
    refine ⟨ih.1, fun as hd => LoopAl.here fun I hI => ?_⟩
    have := ih.2 as I hd hI
    simp only [forF, forStep, optEval]
    mem_al
  case flBody =>
    intro k st d env cnd step b st' hcond _ ih
    refine ⟨ih.1, fun as hd => LoopAl.here fun I hI => ?_⟩
    exact Kind.mem_union.2 (Or.inl (Kind.mem_union.2 (Or.inr
      ((ih.2 as hd).1 _ (cond_sound cfg hcond as I hd hI)))))
  case flStep =>
    intro k st d env cnd e b st' st'' status hcond hb hst _ ih
    refine ⟨ih.1, fun as hd => LoopAl.here fun I hI => ?_⟩
    have hb' := (exec_sound cfg hb as hd).1 _ (cond_sound cfg hcond as I hd hI)
    have hm : SGam as st''.store
        ((aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).norm.join
         (aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).cont) := by
      rcases hst with rfl | rfl
      · exact SGam.join_l _ hb'
      · exact SGam.join_r _ hb'
    exact Kind.mem_union.2 (Or.inr (ih.2 as _ hd hm))
  case flLoop =>
    intro k st d env cnd step b st' st'' st''' status hcond hb hst hs _ ih
    refine ⟨ih.1, fun as hd => LoopAl.later (fun I hI => ?_) (ih.2 as hd)⟩
    have hb' := (exec_sound cfg hb as hd).1 _ (cond_sound cfg hcond as I hd hI)
    have hm : SGam as st''.store
        ((aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).norm.join
         (aexec cfg (match cnd with
          | none => I
          | some c => branch true c (optEval cnd I)) b).cont) := by
      rcases hst with rfl | rfl
      · exact SGam.join_l _ hb'
      · exact SGam.join_r _ hb'
    have := step_sound cfg hs as _ hd hm
    cases step with
    | none => exact this
    | some e => exact this
  case seqHead =>
    intro k st d env s ss _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := (ih.2 as hd).1 σ hσ
    simp only [aexecSeq, SRes.seq]
    mem_al
  case seqTail =>
    intro k st d env s ss st' hs _ ih
    refine ⟨ih.1, fun as σ hd hσ => ?_⟩
    have := ih.2 as _ hd ((exec_sound cfg hs as hd).1 σ hσ)
    simp only [aexecSeq, SRes.seq]
    mem_al))

/-- Alarm soundness for statement sequences. -/
theorem seq_alarm_sound (cfg : Cfg) {k : Kind} {st : St} {d : Nat} {env : Addr}
    {ss : List Stmt} (h : ExecSeqErrK k st d env ss) : ESeq A cfg k st env ss := by
  absint_err_rec ExecSeqErrK.rec h

/-! ## Programs -/

/-- A run of `p` reaches a runtime error of kind `k`. -/
def KindErr (k : Kind) (p : Program) : Prop :=
  ExecSeqErrK k initSt 0 0 p ∨ (k = .abrupt ∧ TopAbrupt p)

/-- Every runtime error of a program has a kind. -/
theorem bigStepErr_hasKind {p : Program} (h : BigStepErr p) : HasKind fun k => KindErr k p := by
  rcases h with h | h
  · obtain ⟨k, hk⟩ := Vsa.AbsInt.ExecSeqErr.hasKind h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨.abrupt, Or.inr ⟨rfl, h⟩⟩

/-- **Alarm soundness**: every kind of runtime error a run of `p` can reach is
among the analysis's alarms. -/
theorem alarms_sound (cfg : Cfg) {p : Program} {k : Kind} (h : KindErr k p) :
    k ∈ alarms (A := A) cfg p := by
  unfold alarms
  rcases h with h | ⟨rfl, st', status, hne, hrun⟩
  · exact Kind.mem_union.2 (Or.inl ((seq_alarm_sound cfg h).2 [0] initState rfl
      initState_sound))
  · refine Kind.mem_union.2 (Or.inr ?_)
    have hs := analyze_sound (A := A) cfg hrun
    have hbot : ((analyze (A := A) cfg p).brk.isBot && (analyze (A := A) cfg p).cont.isBot &&
        (analyze (A := A) cfg p).ret.isBot) = false := by
      cases status with
      | normal => exact absurd rfl hne
      | brk => simp [SGam.isBot_false hs]
      | cont => simp [SGam.isBot_false hs]
      | ret v => simp [SGam.isBot_false hs.1]
    rw [hbot]
    simp

/-- **"No runtime error of kind `k`"**: a kind the analysis does not report
cannot occur in any run. -/
theorem kind_sound (cfg : Cfg) {p : Program} {k : Kind}
    (hk : k ∉ alarms (A := A) cfg p) : ¬ KindErr k p :=
  fun h => hk (alarms_sound cfg h)

/-- A program without alarms has no runtime error. -/
theorem no_error_of_no_alarms (cfg : Cfg) {p : Program}
    (h : alarms (A := A) cfg p = []) : ¬ BigStepErr p := by
  intro herr
  obtain ⟨k, hk⟩ := bigStepErr_hasKind herr
  have := alarms_sound (A := A) cfg hk
  rw [h] at this
  cases this

end Vsa.AbsInt
