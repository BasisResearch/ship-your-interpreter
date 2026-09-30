import Vsa.While.TypeStore

namespace Vsa.While.Types

open Vsa.While

variable {Δ : TyEnv}

theorem mustExit_both :
    (∀ s, MustExit s → ∀ st d env st', ¬ ExecS st d env s st' .normal) ∧
    (∀ ss, MustExitSeq ss → ∀ st d env st', ¬ ExecSeq st d env ss st' .normal) := by
  refine ⟨@MustExit.rec
      (fun s _ => ∀ st d env st', ¬ ExecS st d env s st' .normal)
      (fun ss _ => ∀ st d env st', ¬ ExecSeq st d env ss st' .normal)
      ?ret ?brk ?cont ?block ?ite ?head ?tail,
    @MustExitSeq.rec
      (fun s _ => ∀ st d env st', ¬ ExecS st d env s st' .normal)
      (fun ss _ => ∀ st d env st', ¬ ExecSeq st d env ss st' .normal)
      ?ret ?brk ?cont ?block ?ite ?head ?tail⟩
  case ret => intro e st d env st' hx; cases hx
  case brk => intro st d env st' hx; cases hx
  case cont => intro st d env st' hx; cases hx
  case block =>
    intro ss _ ih st d env st' hx
    cases hx with
    | block _ _ _ _ _ _ _ _ _ hseq => exact ih _ _ _ _ hseq
  case ite =>
    intro c t e _ _ iht ihe st d env st' hx
    cases hx with
    | ifTrue _ _ _ _ _ _ _ _ _ _ _ _ hb => exact iht _ _ _ _ hb
    | ifFalse _ _ _ _ _ _ _ _ _ _ _ _ hb => exact ihe _ _ _ _ hb
  case head =>
    intro s ss _ ih st d env st' hx
    cases hx with
    | consNormal _ _ _ _ _ _ _ _ h1 _ => exact ih _ _ _ _ h1
    | consAbrupt _ _ _ _ _ _ _ _ hne => exact hne rfl
  case tail =>
    intro s ss _ ih st d env st' hx
    cases hx with
    | consNormal _ _ _ _ _ _ _ _ _ h2 => exact ih _ _ _ _ h2
    | consAbrupt _ _ _ _ _ _ _ _ hne => exact hne rfl

theorem mustExitSeq_sound {ss : List Stmt} (h : MustExitSeq ss) {st st' : St} {d : Nat}
    {env : Addr} (hx : ExecSeq st d env ss st' .normal) : False :=
  mustExit_both.2 ss h st d env st' hx

theorem Ext.lt {s s' : Store} {a : Addr} (hE : Ext s s') (h : a < s.frames.size) :
    a < s'.frames.size :=
  Nat.lt_of_lt_of_le h hE.size_le

theorem binOp_typed {s : Store} {op : BinOp} {lv rv v : Value} {tl tr t : Ty}
    (hl : ValTy Δ s lv tl) (hr : ValTy Δ s rv tr) (hbt : BinTy op tl tr t)
    (hop : binOpSem s op lv rv = some v) : ValTy Δ s v t := by
  cases hbt with
  | cmpInt op' hop' =>
    rcases hop' with rfl | rfl | rfl | rfl <;> cases hl <;> cases hr <;>
      simp only [binOpSem, Option.some.injEq] at hop <;> subst hop <;> constructor
  | cmpStr op' hop' =>
    rcases hop' with rfl | rfl | rfl | rfl <;> cases hl <;> cases hr <;>
      simp only [binOpSem, Option.some.injEq] at hop <;> subst hop <;> constructor
  | _ =>
    cases hl <;> cases hr <;> simp [binOpSem] at hop <;>
      first
      | (subst hop; constructor)
      | (obtain ⟨_, rfl⟩ := hop; constructor)

theorem valTy_int {s : Store} {v : Value} (h : ValTy Δ s v .int) : ∃ n, v = .int n := by
  cases h; exact ⟨_, rfl⟩

theorem valTys_length {s : Store} {vs : List Value} {ts : List Ty}
    (h : ValTys Δ s vs ts) : vs.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simp [ih]

theorem defAll_append {s : Store} {a : Addr} {S₁ S₂ : List String}
    (h₁ : DefAll s a S₁) (h₂ : DefAll s a S₂) : DefAll s a (S₁ ++ S₂) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

theorem call_entry {st : St} {cd : ClosureData} {vs : List Value}
    {store' : Store} {frame : Addr} {S : List String}
    (hS : StoreOK Δ st.store) (halloc : st.store.allocFrame (some cd.env) = (store', frame))
    (hdef : DefAll st.store cd.env S) (hvs : ValTys Δ st.store vs (cd.params.map Δ)) :
    let s' := (cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store'
    Ext st.store s' ∧ StoreOK Δ s' ∧ frame < s'.frames.size ∧
      DefAll s' frame (cd.params ++ S) := by
  have hE1 := allocFrame_ext halloc
  have hfr := allocFrame_size halloc
  obtain ⟨hE2, hS2, hD2⟩ := foldDefine_spec (Δ := Δ) cd.params vs store' hfr
    (allocFrame_storeOK halloc hS) (hvs.ext hE1)
  exact ⟨hE1.trans hE2, hS2, hE2.lt hfr,
    defAll_append hD2 ((allocFrame_defAll halloc hdef).ext hE2)⟩

section Motives

variable (Δ : TyEnv)

abbrev PresE (st : St) (_d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) : Prop :=
  ∀ S T, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtE Δ S e T → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧ ValTy Δ st'.store v T

abbrev PresArgs (st : St) (_d : Nat) (env : Addr) (es : List Expr) (st' : St)
    (vs : List Value) : Prop :=
  ∀ S ts, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtArgs Δ S es ts → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧ ValTys Δ st'.store vs ts

abbrev PresCall (st : St) (_d : Nat) (fv : Value) (vs : List Value) (st' : St)
    (v : Value) : Prop :=
  ∀ tf ts t, StoreOK Δ st.store → ValTy Δ st.store fv tf → ValTys Δ st.store vs ts →
    CallTy tf ts t → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧ ValTy Δ st'.store v t

abbrev PresS (st : St) (_d : Nat) (env : Addr) (s : Stmt) (st' : St) (status : Status) :
    Prop :=
  ∀ S R L S', StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtS Δ S R L s S' → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧
      DefAll st'.store env S' ∧ StatusOK Δ st'.store R L status

abbrev PresInit (st : St) (_d : Nat) (env : Addr) (init : Option Stmt) (st' : St) : Prop :=
  ∀ S R L S', StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtInit Δ S R L init S' → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧
      DefAll st'.store env S'

abbrev PresLoop (st : St) (_d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
    (st' : St) (status : Status) : Prop :=
  ∀ S R L S₂, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtEO Δ S cnd → WtEO Δ S step → WtS Δ S R true b S₂ →
    Ext st.store st'.store ∧ StoreOK Δ st'.store ∧ StatusOK Δ st'.store R L status

abbrev PresOpt (st : St) (env : Addr) (o : Option Expr) (st' : St) : Prop :=
  ∀ S, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtEO Δ S o → Ext st.store st'.store ∧ StoreOK Δ st'.store

abbrev PresSeq (st : St) (_d : Nat) (env : Addr) (ss : List Stmt) (st' : St)
    (status : Status) : Prop :=
  ∀ S R L S', StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtSeq Δ S R L ss S' → Ext st.store st'.store ∧ StoreOK Δ st'.store ∧
      StatusOK Δ st'.store R L status

end Motives

structure Preservation (Δ : TyEnv) : Prop where
  evalE : ∀ st d env e st' v, EvalE st d env e st' v → PresE Δ st d env e st' v
  evalArgs : ∀ st d env es st' vs, EvalArgs st d env es st' vs → PresArgs Δ st d env es st' vs
  call : ∀ st d fv vs st' v, Call st d fv vs st' v → PresCall Δ st d fv vs st' v
  execS : ∀ st d env s st' status, ExecS st d env s st' status →
    PresS Δ st d env s st' status
  execInit : ∀ st d env init st', ExecInit st d env init st' → PresInit Δ st d env init st'
  forLoop : ∀ st d env cnd step b st' status, ForLoop st d env cnd step b st' status →
    PresLoop Δ st d env cnd step b st' status
  forCond : ∀ st d env cnd st', ForCond st d env cnd st' → PresOpt Δ st env cnd st'
  execStep : ∀ st d env step st', ExecStep st d env step st' → PresOpt Δ st env step st'
  execSeq : ∀ st d env ss st' status, ExecSeq st d env ss st' status →
    PresSeq Δ st d env ss st' status

theorem preservation (Δ : TyEnv) : Preservation Δ := by
  refine ⟨
    @EvalE.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @EvalArgs.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @Call.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ExecS.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ExecInit.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ForLoop.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ForCond.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ExecStep.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50,
    @ExecSeq.rec (fun st d env e st' v _ => PresE Δ st d env e st' v)
      (fun st d env es st' vs _ => PresArgs Δ st d env es st' vs)
      (fun st d fv vs st' v _ => PresCall Δ st d fv vs st' v)
      (fun st d env s st' status _ => PresS Δ st d env s st' status)
      (fun st d env init st' _ => PresInit Δ st d env init st')
      (fun st d env cnd step b st' status _ => PresLoop Δ st d env cnd step b st' status)
      (fun st _ env cnd st' _ => PresOpt Δ st env cnd st')
      (fun st _ env step st' _ => PresOpt Δ st env step st')
      (fun st d env ss st' status _ => PresSeq Δ st d env ss st' status)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44 ?c45 ?c46 ?c47 ?c48 ?c49 ?c50⟩

  case c1 => intro _ _ _ _ _ _ hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, .int _⟩
  case c2 => intro _ _ _ _ _ _ hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, .str _⟩
  case c3 => intro _ _ _ _ _ _ hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, .bool _⟩
  case c4 => intro _ _ _ _ _ hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, .null⟩
  case c5 =>
    intro _ _ _ _ _ hget _ _ hS _ _ hwt
    cases hwt; exact ⟨.refl _, hS, get?_typed hS hget⟩
  case c6 =>
    intro _ _ env x e st₁ v store'' _ hset ihe S T hS henv hD hwt
    cases hwt with
    | assign _ _ _ _ hwe =>
      obtain ⟨hE, hS₁, hv⟩ := ihe _ _ hS henv hD hwe
      obtain ⟨hE₂, hS₂⟩ := set_spec (Δ := Δ) _ _ _ _ hset
      exact ⟨hE.trans hE₂, hS₂ hS₁ (hv.ext hE₂), hv.ext hE₂⟩
  case c7 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hop ihl ihr S T hS henv hD hwt
    cases hwt with
    | binary _ _ _ _ tl tr _ hwl hwr hbt =>
      obtain ⟨hE₁, hS₁, hvl⟩ := ihl _ _ hS henv hD hwl
      obtain ⟨hE₂, hS₂, hvr⟩ := ihr _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwr
      exact ⟨hE₁.trans hE₂, hS₂, binOp_typed (hvl.ext hE₂) hvr hbt hop⟩
  case c8 =>
    intro _ _ _ _ _ _ _ _ _ ihl S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ tl tr hwl _ =>
      obtain ⟨hE₁, hS₁, _⟩ := ihl _ _ hS henv hD hwl
      exact ⟨hE₁, hS₁, .bool _⟩
  case c9 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ihl ihr S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ tl tr hwl hwr =>
      obtain ⟨hE₁, hS₁, _⟩ := ihl _ _ hS henv hD hwl
      obtain ⟨hE₂, hS₂, _⟩ := ihr _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwr
      exact ⟨hE₁.trans hE₂, hS₂, .bool _⟩
  case c10 =>
    intro _ _ _ _ _ _ _ _ _ ihl S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ tl tr hwl _ =>
      obtain ⟨hE₁, hS₁, _⟩ := ihl _ _ hS henv hD hwl
      exact ⟨hE₁, hS₁, .bool _⟩
  case c11 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ihl ihr S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ tl tr hwl hwr =>
      obtain ⟨hE₁, hS₁, _⟩ := ihl _ _ hS henv hD hwl
      obtain ⟨hE₂, hS₂, _⟩ := ihr _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwr
      exact ⟨hE₁.trans hE₂, hS₂, .bool _⟩
  case c12 =>
    intro _ _ _ _ _ _ _ ihe S T hS henv hD hwt
    cases hwt with
    | neg _ _ hwe =>
      obtain ⟨hE₁, hS₁, _⟩ := ihe _ _ hS henv hD hwe
      exact ⟨hE₁, hS₁, .int _⟩
  case c13 =>
    intro _ _ _ _ _ _ _ ihe S T hS henv hD hwt
    cases hwt with
    | not _ _ _ hwe =>
      obtain ⟨hE₁, hS₁, _⟩ := ihe _ _ hS henv hD hwe
      exact ⟨hE₁, hS₁, .bool _⟩
  case c14 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihf ihargs ihcall S T hS henv hD hwt
    cases hwt with
    | call _ _ _ tf ts _ hwf _ hwa hct =>
      obtain ⟨hE₁, hS₁, hvf⟩ := ihf _ _ hS henv hD hwf
      obtain ⟨hE₂, hS₂, hvs⟩ := ihargs _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwa
      obtain ⟨hE₃, hS₃, hv⟩ := ihcall _ _ _ hS₂ (hvf.ext hE₂) hvs hct
      exact ⟨hE₁.trans (hE₂.trans hE₃), hS₃, hv⟩
  case c15 =>
    intro _ _ env name params body _ a halloc S T hS _ hD hwt
    cases hwt with
    | fn _ _ _ _ r S' hb hr =>
      obtain ⟨hE, hcd⟩ := allocClosure_ext halloc
      exact ⟨hE, allocClosure_storeOK halloc hS,
        .closure a ⟨env, name, params, body⟩ S S' r hcd hb hr (hD.ext hE)⟩

  case c16 => intro _ _ _ _ _ hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, .nil⟩
  case c17 =>
    intro _ _ _ _ _ _ _ _ _ _ _ ihe ihes S ts hS henv hD hwt
    cases hwt with
    | cons _ _ _ t ts hwe hwes =>
      obtain ⟨hE₁, hS₁, hv⟩ := ihe _ _ hS henv hD hwe
      obtain ⟨hE₂, hS₂, hvs⟩ := ihes _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwes
      exact ⟨hE₁.trans hE₂, hS₂, .cons _ _ _ _ (hv.ext hE₂) hvs⟩

  case c18 =>
    intro _ _ a cd _ _ _ _ _ _ hcd _ _ halloc hbody hres ihbody tf ts t hS hf hvs hct
    cases hf with
    | closure _ cd' S S' r hcd' hb hr hdef =>
      rw [hcd] at hcd'
      cases hcd'
      cases hct
      obtain ⟨hE₁, hS₁, hfr, hD₁⟩ := call_entry hS halloc hdef hvs
      obtain ⟨hE₂, hS₂, hst⟩ := ihbody _ _ _ _ hS₁ hfr hD₁ hb
      refine ⟨hE₁.trans hE₂, hS₂, ?_⟩
      rcases hres with ⟨rfl, rfl⟩ | rfl
      · rcases hr with rfl | hm
        · exact .null
        · exact (mustExitSeq_sound hm hbody).elim
      · obtain ⟨t', ht', hv⟩ := hst
        cases ht'
        exact hv
  case c19 =>
    intro _ _ _ tf ts t hS hf _ hct
    cases hf; cases hct; exact ⟨.refl _, hS, .null⟩
  case c20 =>
    intro _ _ _ tf ts t hS hf _ hct
    cases hf; cases hct; exact ⟨.refl _, hS, .null⟩
  case c21 =>
    intro _ _ _ _ _ _ _ tf ts t hS hf _ hct
    cases hf; cases hct <;> exact ⟨.refl _, hS, .null⟩

  case c22 =>
    intro _ _ _ _ _ _ _ ihe S R L S' hS henv hD hwt
    cases hwt with
    | expr _ _ _ _ _ hwe =>
      obtain ⟨hE, hS₁, _⟩ := ihe _ _ hS henv hD hwe
      exact ⟨hE, hS₁, hD.ext hE, trivial⟩
  case c23 =>
    intro st _ env x _ st₁ v he ihe S R L S' hS henv hD hwt
    cases hwt with
    | varInit _ _ _ _ _ hwe =>
      obtain ⟨hE₁, hS₁, hv⟩ := ihe _ _ hS henv hD hwe
      have hE₂ := define_ext st₁.store env x v
      refine ⟨hE₁.trans hE₂, define_storeOK hS₁ (hv.ext hE₂), ?_, trivial⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact define_defined _ _ _ _ (hE₁.lt henv)
      · exact (hD y hy).ext (hE₁.trans hE₂)
    | varRec _ _ _ _ name params body r S'' hb hr hx =>
      cases he with
      | fn _ _ _ _ _ _ store' a halloc =>
        obtain ⟨hE₁, hcd⟩ := allocClosure_ext halloc
        have hE₂ := define_ext store' env x (.closure a)
        have hDS : DefAll (store'.define env x (.closure a)) env (x :: S) := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact define_defined _ _ _ _ (hE₁.lt henv)
          · exact (hD y hy).ext (hE₁.trans hE₂)
        have hv : ValTy Δ (store'.define env x (.closure a)) (.closure a) (Δ x) := by
          rw [hx]
          exact .closure a ⟨env, name, params, body⟩ (x :: S) S'' r
            (hE₂.closures a _ hcd) hb hr hDS
        exact ⟨hE₁.trans hE₂, define_storeOK (allocClosure_storeOK halloc hS) hv, hDS,
          trivial⟩
  case c24 =>
    intro st _ env x S R L S' hS henv hD hwt
    cases hwt with
    | varNull _ _ _ _ hx =>
      have hE := define_ext st.store env x .null
      refine ⟨hE, define_storeOK hS (by rw [hx]; exact .null), ?_, trivial⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact define_defined _ _ _ _ henv
      · exact (hD y hy).ext hE
  case c25 =>
    intro _ _ _ _ _ _ _ _ halloc _ ihseq S R L S' hS henv hD hwt
    cases hwt with
    | block _ _ _ _ S'' hws =>
      have hE₁ := allocFrame_ext halloc
      obtain ⟨hE₂, hS₂, hst⟩ := ihseq _ _ _ _ (allocFrame_storeOK halloc hS)
        (allocFrame_size halloc) (allocFrame_defAll halloc hD) hws
      exact ⟨hE₁.trans hE₂, hS₂, hD.ext (hE₁.trans hE₂), hst⟩
  case c26 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ ihc iht S R L S' hS henv hD hwt
    have go : ∀ {tc S₁}, WtE Δ S _ tc → WtS Δ S R L _ S₁ → _ := fun hwc hwtt => by
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, hst⟩ := iht _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwtt
      exact (⟨hE₁.trans hE₂, hS₂, hD.ext (hE₁.trans hE₂), hst⟩ :
        Ext _ _ ∧ StoreOK Δ _ ∧ DefAll _ _ S ∧ StatusOK Δ _ R L _)
    cases hwt with
    | ifSome _ _ _ _ _ _ _ _ _ hwc hwtt _ => exact go hwc hwtt
    | ifNone _ _ _ _ _ _ _ hwc hwtt => exact go hwc hwtt
  case c27 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe S R L S' hS henv hD hwt
    cases hwt with
    | ifSome _ _ _ _ _ _ _ _ _ hwc _ hwe =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, hst⟩ := ihe _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwe
      exact ⟨hE₁.trans hE₂, hS₂, hD.ext (hE₁.trans hE₂), hst⟩
  case c28 =>
    intro _ _ _ _ _ _ _ _ _ ihc S R L S' hS henv hD hwt
    cases hwt with
    | ifNone _ _ _ _ _ _ _ hwc _ =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      exact ⟨hE₁, hS₁, hD.ext hE₁, trivial⟩
  case c29 =>
    intro _ _ _ _ _ _ _ _ _ ihc S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ _ _ hwc _ =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      exact ⟨hE₁, hS₁, hD.ext hE₁, trivial⟩
  case c30 =>
    intro _ _ _ _ _ _ _ _ _ _ _ ihc ihb S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ _ _ hwc hwb =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, _⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
      exact ⟨hE₁.trans hE₂, hS₂, hD.ext (hE₁.trans hE₂), trivial⟩
  case c31 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ihc ihb S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ _ _ hwc hwb =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, hst⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
      exact ⟨hE₁.trans hE₂, hS₂, hD.ext (hE₁.trans hE₂), hst⟩
  case c32 =>
    intro _ _ _ c b _ _ _ _ _ _ _ _ _ _ _ ihc ihb ihw S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ tc S₁ hwc hwb =>
      obtain ⟨hE₁, hS₁, _⟩ := ihc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, _⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
      obtain ⟨hE₃, hS₃, hD₃, hst⟩ := ihw _ _ _ _ hS₂ (hE₂.lt (hE₁.lt henv))
        (hD.ext (hE₁.trans hE₂)) (.whileS S R L c b tc S₁ hwc hwb)
      exact ⟨hE₁.trans (hE₂.trans hE₃), hS₃, hD₃, hst⟩
  case c33 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ halloc _ _ ihinit ihloop S R L S' hS henv hD hwt
    cases hwt with
    | forS _ _ _ _ _ _ _ S₁ S₂ hwi hwc hws hwb =>
      have hE₁ := allocFrame_ext halloc
      have hout := allocFrame_size halloc
      obtain ⟨hE₂, hS₂, hD₂⟩ := ihinit _ _ _ _ (allocFrame_storeOK halloc hS) hout
        (allocFrame_defAll halloc hD) hwi
      obtain ⟨hE₃, hS₃, hst⟩ := ihloop _ _ _ _ hS₂ (hE₂.lt hout) hD₂ hwc hws hwb
      exact ⟨hE₁.trans (hE₂.trans hE₃), hS₃, hD.ext (hE₁.trans (hE₂.trans hE₃)), hst⟩
  case c34 =>
    intro _ _ _ _ _ _ _ ihe S R L S' hS henv hD hwt
    cases hwt with
    | ret _ _ _ t hwe =>
      obtain ⟨hE, hS₁, hv⟩ := ihe _ _ hS henv hD hwe
      exact ⟨hE, hS₁, hD.ext hE, ⟨t, rfl, hv⟩⟩
  case c35 =>
    intro _ _ _ S R L S' hS _ hD hwt
    cases hwt; exact ⟨.refl _, hS, hD, ⟨.null, rfl, .null⟩⟩
  case c36 => intro _ _ _ S R L S' hS _ hD hwt; cases hwt; exact ⟨.refl _, hS, hD, rfl⟩
  case c37 => intro _ _ _ S R L S' hS _ hD hwt; cases hwt; exact ⟨.refl _, hS, hD, rfl⟩

  case c38 => intro _ _ _ S R L S' hS _ hD hwt; cases hwt; exact ⟨.refl _, hS, hD⟩
  case c39 =>
    intro _ _ _ _ _ _ _ ihs S R L S' hS henv hD hwt
    cases hwt with
    | some _ _ _ _ _ hws =>
      obtain ⟨hE, hS₁, hD₁, _⟩ := ihs _ _ _ _ hS henv hD hws
      exact ⟨hE, hS₁, hD₁⟩

  case c40 =>
    intro _ _ _ _ _ _ _ _ _ _ ihc S R L S₂ hS henv hD hwc _ _
    cases hwc with
    | some _ _ _ hwe =>
      obtain ⟨hE, hS₁, _⟩ := ihc _ _ hS henv hD hwe
      exact ⟨hE, hS₁, trivial⟩
  case c41 =>
    intro _ _ _ _ _ _ _ _ _ _ ihcond ihb S R L S₂ hS henv hD hwc _ hwb
    obtain ⟨hE₁, hS₁⟩ := ihcond _ hS henv hD hwc
    obtain ⟨hE₂, hS₂, _, _⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
    exact ⟨hE₁.trans hE₂, hS₂, trivial⟩
  case c42 =>
    intro _ _ _ _ _ _ _ _ _ _ _ ihcond ihb S R L S₂ hS henv hD hwc _ hwb
    obtain ⟨hE₁, hS₁⟩ := ihcond _ hS henv hD hwc
    obtain ⟨hE₂, hS₂, _, hst⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
    exact ⟨hE₁.trans hE₂, hS₂, hst⟩
  case c43 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihcond ihb ihstep ihloop S R L S₂ hS henv hD
      hwc hws hwb
    obtain ⟨hE₁, hS₁⟩ := ihcond _ hS henv hD hwc
    obtain ⟨hE₂, hS₂, _, _⟩ := ihb _ _ _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwb
    have hE₁₂ := hE₁.trans hE₂
    obtain ⟨hE₃, hS₃⟩ := ihstep _ hS₂ (hE₁₂.lt henv) (hD.ext hE₁₂) hws
    have hE₁₃ := hE₁₂.trans hE₃
    obtain ⟨hE₄, hS₄, hst⟩ := ihloop _ _ _ _ hS₃ (hE₁₃.lt henv) (hD.ext hE₁₃) hwc hws hwb
    exact ⟨hE₁₃.trans hE₄, hS₄, hst⟩

  case c44 => intro _ _ _ S hS _ _ _; exact ⟨.refl _, hS⟩
  case c45 =>
    intro _ _ _ _ _ _ _ _ ihc S hS henv hD hwc
    cases hwc with
    | some _ _ _ hwe =>
      obtain ⟨hE, hS₁, _⟩ := ihc _ _ hS henv hD hwe
      exact ⟨hE, hS₁⟩

  case c46 => intro _ _ _ S hS _ _ _; exact ⟨.refl _, hS⟩
  case c47 =>
    intro _ _ _ _ _ _ _ ihe S hS henv hD hws
    cases hws with
    | some _ _ _ hwe =>
      obtain ⟨hE, hS₁, _⟩ := ihe _ _ hS henv hD hwe
      exact ⟨hE, hS₁⟩

  case c48 => intro _ _ _ S R L S' hS _ _ hwt; cases hwt; exact ⟨.refl _, hS, trivial⟩
  case c49 =>
    intro _ _ _ _ _ _ _ _ _ _ ihs ihss S R L S' hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ S₁ _ hws hwss =>
      obtain ⟨hE₁, hS₁, hD₁, _⟩ := ihs _ _ _ _ hS henv hD hws
      obtain ⟨hE₂, hS₂, hst⟩ := ihss _ _ _ _ hS₁ (hE₁.lt henv) hD₁ hwss
      exact ⟨hE₁.trans hE₂, hS₂, hst⟩
  case c50 =>
    intro _ _ _ _ _ _ _ _ _ ihs S R L S' hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ S₁ _ hws _ =>
      obtain ⟨hE, hS₁, _, hst⟩ := ihs _ _ _ _ hS henv hD hws
      exact ⟨hE, hS₁, hst⟩

theorem initSt_storeOK {Δ : TyEnv} (hB : BuiltinsTyped Δ) : StoreOK Δ initSt.store := by
  intro a f hf p hp
  match a, hf with
  | 0, hf =>
    rw [show initSt.store.frames[0]? = some ⟨none, [("print", .native .print),
      ("println", .native .println), ("assert", .native .assert)]⟩ from rfl] at hf
    cases hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [hB.print]; exact .native _
    · rw [hB.println]; exact .native _
    · rw [hB.assert]; exact .native _

theorem initSt_defAll : DefAll initSt.store 0 builtinNames := by
  intro x hx
  simp only [builtinNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨.native .print, rfl⟩
  · exact ⟨.native .println, rfl⟩
  · exact ⟨.native .assert, rfl⟩

theorem wellTyped_run {Δ : TyEnv} {p : Program} (hwt : WellTyped Δ p) {st' : St}
    {status : Status} (h : ExecSeq initSt 0 0 p st' status) :
    Ext initSt.store st'.store ∧ StoreOK Δ st'.store ∧ status = .normal := by
  obtain ⟨S', hws⟩ := hwt.body
  obtain ⟨hE, hS, hst⟩ := (preservation Δ).execSeq _ _ _ _ _ _ h _ _ _ _
    (initSt_storeOK hwt.builtins) (by decide) initSt_defAll hws
  refine ⟨hE, hS, ?_⟩
  cases status with
  | normal => rfl
  | brk => cases hst
  | cont => cases hst
  | ret v => obtain ⟨_, h, _⟩ := hst; cases h

theorem wellTyped_not_topAbrupt {Δ : TyEnv} {p : Program} (hwt : WellTyped Δ p) :
    ¬ TopAbrupt p := by
  rintro ⟨st', status, hne, h⟩
  exact hne (wellTyped_run hwt h).2.2

end Vsa.While.Types
