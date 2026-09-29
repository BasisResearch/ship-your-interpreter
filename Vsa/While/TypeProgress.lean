import Vsa.While.TypePreservation
import Vsa.While.StmtDispatchClose

/-!
# Progress: well-typed programs reach no type error

The error judgment of `Vsa/While/ErrorSem.lean` (`EvalErr` … `ExecSeqErr`)
derives every runtime error of the interpreter. From a typed configuration,
every error derivation is an `EvalErrN` … `ExecSeqErrN` derivation: its leaf is
division or remainder by zero, a failed `assert`, or the call-depth cap
(`progress`). Every other leaf of the error judgment contradicts typing.

With the classical trichotomy (`trichotomy_unconditional`), a well-typed
program terminates normally, reaches one of those three errors, or diverges
(`type_soundness`).
-/

namespace Vsa.While.Types

open Vsa.While

variable {Δ : TyEnv}

/-- A well-typed operator application fails only by division or remainder by
zero. -/
theorem binOp_none {s : Store} {op : BinOp} {lv rv : Value} {tl tr t : Ty}
    (hl : ValTy Δ s lv tl) (hr : ValTy Δ s rv tr) (hbt : BinTy op tl tr t)
    (hop : binOpSem s op lv rv = none) : (op = .div ∨ op = .mod) ∧ rv = .int 0 := by
  cases hbt with
  | cmpInt op' hop' =>
    rcases hop' with rfl | rfl | rfl | rfl <;> cases hl <;> cases hr <;> simp [binOpSem] at hop
  | cmpStr op' hop' =>
    rcases hop' with rfl | rfl | rfl | rfl <;> cases hl <;> cases hr <;> simp [binOpSem] at hop
  | div =>
    cases hl; cases hr; simp only [binOpSem] at hop
    split at hop
    · rename_i h; simp only [beq_iff_eq] at h; exact ⟨.inl rfl, by rw [h]⟩
    · cases hop
  | mod =>
    cases hl; cases hr; simp only [binOpSem] at hop
    split at hop
    · rename_i h; simp only [beq_iff_eq] at h; exact ⟨.inr rfl, by rw [h]⟩
    · cases hop
  | _ => cases hl <;> cases hr <;> simp [binOpSem] at hop

section Motives

variable (Δ : TyEnv)

abbrev ProgE (st : St) (d : Nat) (env : Addr) (e : Expr) : Prop :=
  ∀ S T, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtE Δ S e T → EvalErrN st d env e

abbrev ProgArgs (st : St) (d : Nat) (env : Addr) (es : List Expr) : Prop :=
  ∀ S ts, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtArgs Δ S es ts → EvalArgsErrN st d env es

abbrev ProgCall (st : St) (d : Nat) (fv : Value) (vs : List Value) : Prop :=
  ∀ tf ts t, StoreOK Δ st.store → ValTy Δ st.store fv tf → ValTys Δ st.store vs ts →
    CallTy tf ts t → CallErrN st d fv vs

abbrev ProgS (st : St) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ S R L S', StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtS Δ S R L s S' → ExecErrN st d env s

abbrev ProgLoop (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) :
    Prop :=
  ∀ S R S₂, StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtEO Δ S cnd → WtEO Δ S step → WtS Δ S R true b S₂ → ForLoopErrN st d env cnd step b

abbrev ProgSeq (st : St) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∀ S R L S', StoreOK Δ st.store → env < st.store.frames.size → DefAll st.store env S →
    WtSeq Δ S R L ss S' → ExecSeqErrN st d env ss

end Motives

/-- Progress for each of the six error relations. -/
structure Progress (Δ : TyEnv) : Prop where
  evalE : ∀ st d env e, EvalErr st d env e → ProgE Δ st d env e
  evalArgs : ∀ st d env es, EvalArgsErr st d env es → ProgArgs Δ st d env es
  call : ∀ st d fv vs, CallErr st d fv vs → ProgCall Δ st d fv vs
  execS : ∀ st d env s, ExecErr st d env s → ProgS Δ st d env s
  forLoop : ∀ st d env cnd step b, ForLoopErr st d env cnd step b →
    ProgLoop Δ st d env cnd step b
  execSeq : ∀ st d env ss, ExecSeqErr st d env ss → ProgSeq Δ st d env ss

/-- **Progress.** From a typed configuration, every runtime error is division
or remainder by zero, a failed `assert`, or the call-depth cap. -/
theorem progress (Δ : TyEnv) : Progress Δ := by
  have P := preservation Δ
  refine ⟨
    @EvalErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44,
    @EvalArgsErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44,
    @CallErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44,
    @ExecErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44,
    @ForLoopErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44,
    @ExecSeqErr.rec (fun st d env e _ => ProgE Δ st d env e)
      (fun st d env es _ => ProgArgs Δ st d env es)
      (fun st d fv vs _ => ProgCall Δ st d fv vs)
      (fun st d env s _ => ProgS Δ st d env s)
      (fun st d env cnd step b _ => ProgLoop Δ st d env cnd step b)
      (fun st d env ss _ => ProgSeq Δ st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35 ?c36 ?c37 ?c38
      ?c39 ?c40 ?c41 ?c42 ?c43 ?c44⟩
  -- EvalErr
  case c1 =>
    intro _ _ _ x hnone S T _ _ hD hwt
    cases hwt with
    | var _ _ hx =>
      obtain ⟨v, hv⟩ := hD x hx
      rw [hnone] at hv; cases hv
  case c2 =>
    intro _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | assign _ _ _ _ hwe => exact .assignE _ _ _ _ _ (ih _ _ hS henv hD hwe)
  case c3 =>
    intro _ _ env x _ st₁ v he hnone S T hS henv hD hwt
    cases hwt with
    | assign _ _ _ hx hwe =>
      obtain ⟨hE, _, _⟩ := P.evalE _ _ _ _ _ _ he _ _ hS henv hD hwe
      obtain ⟨s', hs'⟩ := set?_of_defined v ((hD x hx).ext hE)
      rw [hnone] at hs'; cases hs'
  case c4 =>
    intro _ _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | binary _ _ _ _ _ _ _ hwl _ _ => exact .binaryL _ _ _ _ _ _ (ih _ _ hS henv hD hwl)
  case c5 =>
    intro _ _ _ _ _ _ _ _ hl _ ih S T hS henv hD hwt
    cases hwt with
    | binary _ _ _ _ _ _ _ hwl hwr _ =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hl _ _ hS henv hD hwl
      exact .binaryR _ _ _ _ _ _ _ _ hl (ih _ _ hS₁ (hE.lt henv) (hD.ext hE) hwr)
  case c6 =>
    intro _ _ _ _ _ _ _ _ _ _ hl hr hnone S T hS henv hD hwt
    cases hwt with
    | binary _ _ _ _ _ _ _ hwl hwr hbt =>
      obtain ⟨hE₁, hS₁, hvl⟩ := P.evalE _ _ _ _ _ _ hl _ _ hS henv hD hwl
      obtain ⟨hE₂, _, hvr⟩ := P.evalE _ _ _ _ _ _ hr _ _ hS₁ (hE₁.lt henv) (hD.ext hE₁) hwr
      obtain ⟨hop, rfl⟩ := binOp_none (hvl.ext hE₂) hvr hbt hnone
      exact .divZero _ _ _ _ _ _ _ _ _ hop hl hr
  case c7 =>
    intro _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ _ _ hwl _ => exact .orL _ _ _ _ _ (ih _ _ hS henv hD hwl)
  case c8 =>
    intro _ _ _ _ _ _ _ hl hf _ ih S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ _ _ hwl hwr =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hl _ _ hS henv hD hwl
      exact .orR _ _ _ _ _ _ _ hl hf (ih _ _ hS₁ (hE.lt henv) (hD.ext hE) hwr)
  case c9 =>
    intro _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ _ _ hwl _ => exact .andL _ _ _ _ _ (ih _ _ hS henv hD hwl)
  case c10 =>
    intro _ _ _ _ _ _ _ hl ht _ ih S T hS henv hD hwt
    cases hwt with
    | logical _ _ _ _ _ _ hwl hwr =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hl _ _ hS henv hD hwl
      exact .andR _ _ _ _ _ _ _ hl ht (ih _ _ hS₁ (hE.lt henv) (hD.ext hE) hwr)
  case c11 =>
    intro _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | neg _ _ hwe => exact .unaryE _ _ _ _ _ (ih _ _ hS henv hD hwe)
    | not _ _ _ hwe => exact .unaryE _ _ _ _ _ (ih _ _ hS henv hD hwe)
  case c12 =>
    intro _ _ _ _ _ _ he hnot S T hS henv hD hwt
    cases hwt with
    | neg _ _ hwe =>
      obtain ⟨_, _, hv⟩ := P.evalE _ _ _ _ _ _ he _ _ hS henv hD hwe
      obtain ⟨n, rfl⟩ := valTy_int hv
      exact absurd rfl (hnot n)
  case c13 =>
    intro _ _ _ _ _ _ ih S T hS henv hD hwt
    cases hwt with
    | call _ _ _ _ _ _ hwf _ _ _ => exact .callF _ _ _ _ _ (ih _ _ hS henv hD hwf)
  case c14 =>
    intro _ _ _ _ _ _ _ _ hlt S T _ _ _ hwt
    cases hwt with
    | call _ _ _ _ _ _ _ hle _ _ => exact absurd hle (Nat.not_le.mpr hlt)
  case c15 =>
    intro _ _ _ _ _ _ _ hf hle _ ih S T hS henv hD hwt
    cases hwt with
    | call _ _ _ _ _ _ hwf _ hwa _ =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hf _ _ hS henv hD hwf
      exact .callArgs _ _ _ _ _ _ _ hf hle (ih _ _ hS₁ (hE.lt henv) (hD.ext hE) hwa)
  case c16 =>
    intro _ _ _ _ _ _ _ _ _ hf hle hargs _ ih S T hS henv hD hwt
    cases hwt with
    | call _ _ _ _ _ _ hwf _ hwa hct =>
      obtain ⟨hE₁, hS₁, hvf⟩ := P.evalE _ _ _ _ _ _ hf _ _ hS henv hD hwf
      obtain ⟨hE₂, hS₂, hvs⟩ := P.evalArgs _ _ _ _ _ _ hargs _ _ hS₁ (hE₁.lt henv)
        (hD.ext hE₁) hwa
      exact .callC _ _ _ _ _ _ _ _ _ hf hle hargs (ih _ _ _ hS₂ (hvf.ext hE₂) hvs hct)
  -- EvalArgsErr
  case c17 =>
    intro _ _ _ _ _ _ ih S ts hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ hwe _ => exact .head _ _ _ _ _ (ih _ _ hS henv hD hwe)
  case c18 =>
    intro _ _ _ _ _ _ _ he _ ih S ts hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ hwe hwes =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ he _ _ hS henv hD hwe
      exact .tail _ _ _ _ _ _ _ he (ih _ _ hS₁ (hE.lt henv) (hD.ext hE) hwes)
  -- CallErr
  case c19 =>
    intro _ _ _ _ hnc hnn tf ts t _ hf _ hct
    cases hct <;> cases hf
    · exact absurd rfl (hnc _)
    all_goals exact absurd rfl (hnn _)
  case c20 =>
    intro _ _ _ _ hnone tf ts t _ hf _ _
    cases hf with
    | closure _ _ _ _ _ hcd _ _ _ => rw [hnone] at hcd; cases hcd
  case c21 =>
    intro _ _ _ cd _ hcd hne tf ts t _ hf hvs hct
    cases hf with
    | closure _ cd' _ _ _ hcd' _ _ _ =>
      rw [hcd] at hcd'; cases hcd'; cases hct
      exact (hne (by rw [valTys_length hvs, List.length_map])).elim
  case c22 =>
    intro _ _ _ _ _ hcd hlen hnd _ _ _ _ _ _ _
    exact .depth _ _ _ _ _ hcd hlen hnd
  case c23 =>
    intro _ _ _ cd _ _ _ hcd hlen hd halloc _ ih tf ts t hS hf hvs hct
    cases hf with
    | closure _ cd' S S' r hcd' hb _ hdef =>
      rw [hcd] at hcd'; cases hcd'; cases hct
      obtain ⟨_, hS₁, hfr, hD₁⟩ := call_entry hS halloc hdef hvs
      exact .body _ _ _ _ _ _ _ hcd hlen hd halloc (ih _ _ _ _ hS₁ hfr hD₁ hb)
  case c24 =>
    intro _ _ _ cd _ _ _ _ status hcd _ _ halloc hbody hst tf ts t hS hf hvs hct
    cases hf with
    | closure _ cd' S S' r hcd' hb _ hdef =>
      rw [hcd] at hcd'; cases hcd'; cases hct
      obtain ⟨_, hS₁, hfr, hD₁⟩ := call_entry hS halloc hdef hvs
      obtain ⟨_, _, hok⟩ := P.execSeq _ _ _ _ _ _ hbody _ _ _ _ hS₁ hfr hD₁ hb
      rcases hst with rfl | rfl <;> cases hok
  case c25 =>
    intro _ _ _ _ _ hvs hf _ _ _ _ _ _ _
    exact .assertFail _ _ _ _ _ hvs hf
  case c26 =>
    intro _ _ _ h1 h2 tf ts t _ hf hvs hct
    cases hf
    cases hct with
    | assert1 =>
      cases hvs with
      | cons _ _ _ _ _ hr => cases hr; exact absurd rfl (h1 _)
    | assert2 =>
      cases hvs with
      | cons _ _ _ _ _ hr =>
        cases hr with
        | cons _ _ _ _ _ hr => cases hr; exact absurd rfl (h2 _ _)
  -- ExecErr
  case c27 =>
    intro _ _ _ _ _ ih S R L S' hS henv hD hwt
    cases hwt with
    | expr _ _ _ _ _ hwe => exact .expr _ _ _ _ (ih _ _ hS henv hD hwe)
  case c28 =>
    intro _ _ _ _ _ herr ih S R L S' hS henv hD hwt
    cases hwt with
    | varInit _ _ _ _ _ hwe => exact .varInit _ _ _ _ _ (ih _ _ hS henv hD hwe)
    | varRec => cases herr
  case c29 =>
    intro _ _ _ _ _ _ halloc _ ih S R L S' hS henv hD hwt
    cases hwt with
    | block _ _ _ _ _ hws =>
      exact .block _ _ _ _ _ _ halloc (ih _ _ _ _ (allocFrame_storeOK halloc hS)
        (allocFrame_size halloc) (allocFrame_defAll halloc hD) hws)
  case c30 =>
    intro _ _ _ _ _ _ _ ih S R L S' hS henv hD hwt
    cases hwt with
    | ifSome _ _ _ _ _ _ _ _ _ hwc _ _ => exact .ifCond _ _ _ _ _ _ (ih _ _ hS henv hD hwc)
    | ifNone _ _ _ _ _ _ _ hwc _ => exact .ifCond _ _ _ _ _ _ (ih _ _ hS henv hD hwc)
  case c31 =>
    intro _ _ _ _ _ _ _ _ hc ht _ ih S R L S' hS henv hD hwt
    cases hwt with
    | ifSome _ _ _ _ _ _ _ _ _ hwc hwt _ =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hc _ _ hS henv hD hwc
      exact .ifThen _ _ _ _ _ _ _ _ hc ht (ih _ _ _ _ hS₁ (hE.lt henv) (hD.ext hE) hwt)
    | ifNone _ _ _ _ _ _ _ hwc hwt =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hc _ _ hS henv hD hwc
      exact .ifThen _ _ _ _ _ _ _ _ hc ht (ih _ _ _ _ hS₁ (hE.lt henv) (hD.ext hE) hwt)
  case c32 =>
    intro _ _ _ _ _ _ _ _ hc hf _ ih S R L S' hS henv hD hwt
    cases hwt with
    | ifSome _ _ _ _ _ _ _ _ _ hwc _ hwe =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hc _ _ hS henv hD hwc
      exact .ifElse _ _ _ _ _ _ _ _ hc hf (ih _ _ _ _ hS₁ (hE.lt henv) (hD.ext hE) hwe)
  case c33 =>
    intro _ _ _ _ _ _ ih S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ _ _ hwc _ => exact .whileCond _ _ _ _ _ (ih _ _ hS henv hD hwc)
  case c34 =>
    intro _ _ _ _ _ _ _ hc ht _ ih S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ _ _ hwc hwb =>
      obtain ⟨hE, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hc _ _ hS henv hD hwc
      exact .whileBody _ _ _ _ _ _ _ hc ht (ih _ _ _ _ hS₁ (hE.lt henv) (hD.ext hE) hwb)
  case c35 =>
    intro _ _ _ c b _ _ _ _ hc ht hb hstat _ ih S R L S' hS henv hD hwt
    cases hwt with
    | whileS _ _ _ _ _ tc S₁ hwc hwb =>
      obtain ⟨hE₁, hS₁, _⟩ := P.evalE _ _ _ _ _ _ hc _ _ hS henv hD hwc
      obtain ⟨hE₂, hS₂, _, _⟩ := P.execS _ _ _ _ _ _ hb _ _ _ _ hS₁ (hE₁.lt henv)
        (hD.ext hE₁) hwb
      exact .whileLoop _ _ _ _ _ _ _ _ _ hc ht hb hstat
        (ih _ _ _ _ hS₂ (hE₂.lt (hE₁.lt henv)) (hD.ext (hE₁.trans hE₂))
          (.whileS S R L c b tc S₁ hwc hwb))
  case c36 =>
    intro _ _ _ _ _ _ _ _ _ halloc _ ih S R L S' hS henv hD hwt
    cases hwt with
    | forS _ _ _ _ _ _ _ S₁ S₂ hwi _ _ _ =>
      cases hwi with
      | some _ _ _ _ _ hws =>
        exact .forInit _ _ _ _ _ _ _ _ _ halloc (ih _ _ _ _ (allocFrame_storeOK halloc hS)
          (allocFrame_size halloc) (allocFrame_defAll halloc hD) hws)
  case c37 =>
    intro _ _ _ _ _ _ _ _ _ _ halloc hinit _ ih S R L S' hS henv hD hwt
    cases hwt with
    | forS _ _ _ _ _ _ _ S₁ S₂ hwi hwc hws hwb =>
      have hout := allocFrame_size halloc
      obtain ⟨hE₂, hS₂, hD₂⟩ := P.execInit _ _ _ _ _ hinit _ _ _ _
        (allocFrame_storeOK halloc hS) hout (allocFrame_defAll halloc hD) hwi
      exact .forLoop _ _ _ _ _ _ _ _ _ _ halloc hinit
        (ih _ _ _ hS₂ (hE₂.lt hout) hD₂ hwc hws hwb)
  case c38 =>
    intro _ _ _ _ _ ih S R L S' hS henv hD hwt
    cases hwt with
    | ret _ _ _ _ hwe => exact .ret _ _ _ _ (ih _ _ hS henv hD hwe)
  -- ForLoopErr
  case c39 =>
    intro _ _ _ _ _ _ _ ih S R S₂ hS henv hD hwc _ _
    cases hwc with
    | some _ _ _ hwe => exact .cond _ _ _ _ _ _ (ih _ _ hS henv hD hwe)
  case c40 =>
    intro _ _ _ _ _ _ _ hcond _ ih S R S₂ hS henv hD hwc _ hwb
    obtain ⟨hE, hS₁⟩ := P.forCond _ _ _ _ _ hcond _ hS henv hD hwc
    exact .body _ _ _ _ _ _ _ hcond (ih _ _ _ _ hS₁ (hE.lt henv) (hD.ext hE) hwb)
  case c41 =>
    intro _ _ _ _ _ _ _ _ _ hcond hb hstat _ ih S R S₂ hS henv hD hwc hws hwb
    obtain ⟨hE₁, hS₁⟩ := P.forCond _ _ _ _ _ hcond _ hS henv hD hwc
    obtain ⟨hE₂, hS₂, _, _⟩ := P.execS _ _ _ _ _ _ hb _ _ _ _ hS₁ (hE₁.lt henv)
      (hD.ext hE₁) hwb
    cases hws with
    | some _ _ _ hwe =>
      exact .step _ _ _ _ _ _ _ _ _ hcond hb hstat
        (ih _ _ hS₂ (hE₂.lt (hE₁.lt henv)) (hD.ext (hE₁.trans hE₂)) hwe)
  case c42 =>
    intro _ _ _ _ _ _ _ _ _ _ hcond hb hstat hstep _ ih S R S₂ hS henv hD hwc hws hwb
    obtain ⟨hE₁, hS₁⟩ := P.forCond _ _ _ _ _ hcond _ hS henv hD hwc
    obtain ⟨hE₂, hS₂, _, _⟩ := P.execS _ _ _ _ _ _ hb _ _ _ _ hS₁ (hE₁.lt henv)
      (hD.ext hE₁) hwb
    have hE₁₂ := hE₁.trans hE₂
    obtain ⟨hE₃, hS₃⟩ := P.execStep _ _ _ _ _ hstep _ hS₂ (hE₁₂.lt henv) (hD.ext hE₁₂) hws
    have hE₁₃ := hE₁₂.trans hE₃
    exact .loop _ _ _ _ _ _ _ _ _ _ hcond hb hstat hstep
      (ih _ _ _ hS₃ (hE₁₃.lt henv) (hD.ext hE₁₃) hwc hws hwb)
  -- ExecSeqErr
  case c43 =>
    intro _ _ _ _ _ _ ih S R L S' hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ _ _ hws _ => exact .head _ _ _ _ _ (ih _ _ _ _ hS henv hD hws)
  case c44 =>
    intro _ _ _ _ _ _ hs _ ih S R L S' hS henv hD hwt
    cases hwt with
    | cons _ _ _ _ _ S₁ _ hws hwss =>
      obtain ⟨hE, hS₁, hD₁, _⟩ := P.execS _ _ _ _ _ _ hs _ _ _ _ hS henv hD hws
      exact .tail _ _ _ _ _ _ hs (ih _ _ _ _ hS₁ (hE.lt henv) hD₁ hwss)

/-- **Progress for programs.** A runtime error of a well-typed program is
division or remainder by zero, a failed `assert`, or the call-depth cap. -/
theorem wellTyped_err {p : Program} (hwt : WellTyped Δ p) (h : BigStepErr p) :
    ExecSeqErrN initSt 0 0 p := by
  rcases h with h | h
  · obtain ⟨S', hws⟩ := hwt.body
    exact (progress Δ).execSeq _ _ _ _ h _ _ _ _ (initSt_storeOK hwt.builtins) (by decide)
      initSt_defAll hws
  · exact absurd h (wellTyped_not_topAbrupt hwt)

/-- **Type soundness.** A well-typed program terminates normally, reaches
division or remainder by zero, a failed `assert` or the call-depth cap, or
diverges. -/
theorem type_soundness {p : Program} (hwt : WellTyped Δ p) :
    (∃ out, BigStep p out) ∨ ExecSeqErrN initSt 0 0 p ∨ BigStepDiverges p := by
  rcases trichotomy_unconditional p with h | h | h
  · exact .inl h
  · exact .inr (.inl (wellTyped_err hwt h))
  · exact .inr (.inr h)

/-- The non-type errors are runtime errors: `ExecSeqErrN` … are sub-judgments of
the full error judgment. -/
structure ErrNSound : Prop where
  evalE : ∀ st d env e, EvalErrN st d env e → EvalErr st d env e
  evalArgs : ∀ st d env es, EvalArgsErrN st d env es → EvalArgsErr st d env es
  call : ∀ st d fv vs, CallErrN st d fv vs → CallErr st d fv vs
  execS : ∀ st d env s, ExecErrN st d env s → ExecErr st d env s
  forLoop : ∀ st d env cnd step b, ForLoopErrN st d env cnd step b →
    ForLoopErr st d env cnd step b
  execSeq : ∀ st d env ss, ExecSeqErrN st d env ss → ExecSeqErr st d env ss

theorem errN_sound : ErrNSound := by
  refine ⟨
    @EvalErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @EvalArgsErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @CallErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @ExecErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @ForLoopErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35,
    @ExecSeqErrN.rec (fun st d env e _ => EvalErr st d env e) (fun st d env es _ => EvalArgsErr st d env es)
      (fun st d fv vs _ => CallErr st d fv vs) (fun st d env s _ => ExecErr st d env s)
      (fun st d env cnd step b _ => ForLoopErr st d env cnd step b)
      (fun st d env ss _ => ExecSeqErr st d env ss)
      ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18 ?c19 ?c20
      ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31 ?c32 ?c33 ?c34 ?c35⟩
  case c1 => intro _ _ _ _ _ _ ih; exact .assignE _ _ _ _ _ ih
  case c2 => intro _ _ _ _ _ _ _ ih; exact .binaryL _ _ _ _ _ _ ih
  case c3 => intro _ _ _ _ _ _ _ _ hl _ ih; exact .binaryR _ _ _ _ _ _ _ _ hl ih
  case c4 =>
    intro _ _ _ _ _ _ _ _ _ hop hl hr
    refine .binaryOp _ _ _ _ _ _ _ _ _ _ hl hr ?_
    rcases hop with rfl | rfl <;> cases ‹Value› <;> simp [binOpSem]
  case c5 => intro _ _ _ _ _ _ ih; exact .orL _ _ _ _ _ ih
  case c6 => intro _ _ _ _ _ _ _ hl hf _ ih; exact .orR _ _ _ _ _ _ _ hl hf ih
  case c7 => intro _ _ _ _ _ _ ih; exact .andL _ _ _ _ _ ih
  case c8 => intro _ _ _ _ _ _ _ hl ht _ ih; exact .andR _ _ _ _ _ _ _ hl ht ih
  case c9 => intro _ _ _ _ _ _ ih; exact .unaryE _ _ _ _ _ ih
  case c10 => intro _ _ _ _ _ _ ih; exact .callF _ _ _ _ _ ih
  case c11 => intro _ _ _ _ _ _ _ hf hle _ ih; exact .callArgs _ _ _ _ _ _ _ hf hle ih
  case c12 =>
    intro _ _ _ _ _ _ _ _ _ hf hle hargs _ ih
    exact .callC _ _ _ _ _ _ _ _ _ hf hle hargs ih
  case c13 => intro _ _ _ _ _ _ ih; exact .head _ _ _ _ _ ih
  case c14 => intro _ _ _ _ _ _ _ he _ ih; exact .tail _ _ _ _ _ _ _ he ih
  case c15 => intro _ _ _ _ _ hcd hlen hnd; exact .depth _ _ _ _ _ hcd hlen hnd
  case c16 =>
    intro _ _ _ _ _ _ _ hcd hlen hd halloc _ ih
    exact .body _ _ _ _ _ _ _ hcd hlen hd halloc ih
  case c17 => intro _ _ _ _ _ hvs hf; exact .assertFail _ _ _ _ _ hvs hf
  case c18 => intro _ _ _ _ _ ih; exact .expr _ _ _ _ ih
  case c19 => intro _ _ _ _ _ _ ih; exact .varInit _ _ _ _ _ ih
  case c20 => intro _ _ _ _ _ _ halloc _ ih; exact .block _ _ _ _ _ _ halloc ih
  case c21 => intro _ _ _ _ _ _ _ ih; exact .ifCond _ _ _ _ _ _ ih
  case c22 => intro _ _ _ _ _ _ _ _ hc ht _ ih; exact .ifThen _ _ _ _ _ _ _ _ hc ht ih
  case c23 => intro _ _ _ _ _ _ _ _ hc hf _ ih; exact .ifElse _ _ _ _ _ _ _ _ hc hf ih
  case c24 => intro _ _ _ _ _ _ ih; exact .whileCond _ _ _ _ _ ih
  case c25 => intro _ _ _ _ _ _ _ hc ht _ ih; exact .whileBody _ _ _ _ _ _ _ hc ht ih
  case c26 =>
    intro _ _ _ _ _ _ _ _ _ hc ht hb hstat _ ih
    exact .whileLoop _ _ _ _ _ _ _ _ _ hc ht hb hstat ih
  case c27 =>
    intro _ _ _ _ _ _ _ _ _ halloc _ ih
    exact .forInit _ _ _ _ _ _ _ _ _ halloc ih
  case c28 =>
    intro _ _ _ _ _ _ _ _ _ _ halloc hinit _ ih
    exact .forLoop _ _ _ _ _ _ _ _ _ _ halloc hinit ih
  case c29 => intro _ _ _ _ _ ih; exact .ret _ _ _ _ ih
  case c30 => intro _ _ _ _ _ _ _ ih; exact .cond _ _ _ _ _ _ ih
  case c31 => intro _ _ _ _ _ _ _ hcond _ ih; exact .body _ _ _ _ _ _ _ hcond ih
  case c32 =>
    intro _ _ _ _ _ _ _ _ _ hcond hb hstat _ ih
    exact .step _ _ _ _ _ _ _ _ _ hcond hb hstat ih
  case c33 =>
    intro _ _ _ _ _ _ _ _ _ _ hcond hb hstat hstep _ ih
    exact .loop _ _ _ _ _ _ _ _ _ _ hcond hb hstat hstep ih
  case c34 => intro _ _ _ _ _ _ ih; exact .head _ _ _ _ _ ih
  case c35 => intro _ _ _ _ _ _ hs _ ih; exact .tail _ _ _ _ _ _ hs ih

/-- A program reaching a non-type error has a runtime error. -/
theorem bigStepErr_of_errN {p : Program} (h : ExecSeqErrN initSt 0 0 p) : BigStepErr p :=
  .inl (errN_sound.execSeq _ _ _ _ h)

end Vsa.While.Types
