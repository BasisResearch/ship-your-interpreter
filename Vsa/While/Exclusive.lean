import Vsa.While.ErrorSem

namespace Vsa.While

set_option linter.unusedVariables false

mutual

theorem EvalE.det : ∀ {st d a e s1 v1 s2 v2}, EvalE st d a e s1 v1 → EvalE st d a e s2 v2 →
    s1 = s2 ∧ v1 = v2
  | _, _, _, _, _, _, _, _, .int .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .str .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .bool .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .null .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .var _ _ _ x v hv, h2 => by
    cases h2 with
    | var _ _ _ _ v2 hv2 => rw [hv] at hv2; cases hv2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .assign _ _ _ x e st' v s'' he hs, h2 => by
    cases h2 with
    | assign _ _ _ _ _ st2 v2 s2'' he2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2
      rw [hs] at hs2; cases hs2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .binary _ _ _ op l r st' st'' lv rv v hl hr hop, h2 => by
    cases h2 with
    | binary _ _ _ _ _ _ st2' st2'' lv2 rv2 v2 hl2 hr2 hop2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2
      obtain ⟨rfl, rfl⟩ := EvalE.det hr hr2
      rw [hop] at hop2; cases hop2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .orTrue _ _ _ l r st' lv hl ht, h2 => by
    cases h2 with
    | orTrue _ _ _ _ _ st2 lv2 hl2 ht2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; exact ⟨rfl, rfl⟩
    | orFalse _ _ _ _ _ st2 st2' lv2 rv2 hl2 hf2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, _, _, .orFalse _ _ _ l r st' st'' lv rv hl hf hr, h2 => by
    cases h2 with
    | orTrue _ _ _ _ _ st2 lv2 hl2 ht2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [hf] at ht2; cases ht2
    | orFalse _ _ _ _ _ st2 st2' lv2 rv2 hl2 hf2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2
      obtain ⟨rfl, rfl⟩ := EvalE.det hr hr2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .andFalse _ _ _ l r st' lv hl hf, h2 => by
    cases h2 with
    | andFalse _ _ _ _ _ st2 lv2 hl2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; exact ⟨rfl, rfl⟩
    | andTrue _ _ _ _ _ st2 st2' lv2 rv2 hl2 ht2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, _, _, .andTrue _ _ _ l r st' st'' lv rv hl ht hr, h2 => by
    cases h2 with
    | andFalse _ _ _ _ _ st2 lv2 hl2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [ht] at hf2; cases hf2
    | andTrue _ _ _ _ _ st2 st2' lv2 rv2 hl2 ht2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2
      obtain ⟨rfl, rfl⟩ := EvalE.det hr hr2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .neg _ _ _ e st' n h, h2 => by
    cases h2 with
    | neg _ _ _ _ st2 n2 h' =>
      obtain ⟨rfl, hv⟩ := EvalE.det h h'; cases hv; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .not _ _ _ e st' v h, h2 => by
    cases h2 with
    | not _ _ _ _ st2 v2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det h h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .call _ _ _ f args st' st'' st''' fv vs v hf hlen ha hc, h2 => by
    cases h2 with
    | call _ _ _ _ _ s2' s2'' s2''' fv2 vs2 v2 hf2 hlen2 ha2 hc2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2
      obtain ⟨rfl, rfl⟩ := EvalArgs.det ha ha2
      exact Call.det hc hc2
  | _, _, _, _, _, _, _, _, .fn _ _ _ name params body store' a h, h2 => by
    cases h2 with
    | fn _ _ _ _ _ _ s2 a2 h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem EvalArgs.det : ∀ {st d a es s1 v1 s2 v2}, EvalArgs st d a es s1 v1 →
    EvalArgs st d a es s2 v2 → s1 = s2 ∧ v1 = v2
  | _, _, _, _, _, _, _, _, .nil .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .cons _ _ _ e es st' st'' v vs he hes, h2 => by
    cases h2 with
    | cons _ _ _ _ _ s2' s2'' v2 vs2 he2 hes2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2
      obtain ⟨rfl, rfl⟩ := EvalArgs.det hes hes2
      exact ⟨rfl, rfl⟩
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem Call.det : ∀ {st d fv vs s1 v1 s2 v2}, Call st d fv vs s1 v1 → Call st d fv vs s2 v2 →
    s1 = s2 ∧ v1 = v2
  | _, _, _, _, _, _, _, _,
      .closure _ _ a cd vs store' frame st' status v hcd hlen hd halloc hbody hst, h2 => by
    cases h2 with
    | closure _ _ _ cd2 _ store2 frame2 st2 status2 v2 hcd2 hlen2 hd2 halloc2 hbody2 hst2 =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      obtain ⟨rfl, rfl⟩ := ExecSeq.det hbody hbody2
      refine ⟨rfl, ?_⟩
      rcases hst with ⟨rfl, rfl⟩ | rfl
      · rcases hst2 with ⟨-, rfl⟩ | h
        · rfl
        · cases h
      · rcases hst2 with ⟨h, -⟩ | h
        · cases h
        · cases h; rfl
  | _, _, _, _, _, _, _, _, .print .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .println .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .assertOk .., h2 => by cases h2; exact ⟨rfl, rfl⟩
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem ExecS.det : ∀ {st d a s s1 t1 s2 t2}, ExecS st d a s s1 t1 → ExecS st d a s s2 t2 →
    s1 = s2 ∧ t1 = t2
  | _, _, _, _, _, _, _, _, .expr _ _ _ e st' v h, h2 => by
    cases h2 with
    | expr _ _ _ _ st2 v2 h' => obtain ⟨rfl, -⟩ := EvalE.det h h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .varInit _ _ _ x e st' v h, h2 => by
    cases h2 with
    | varInit _ _ _ _ _ st2 v2 h' => obtain ⟨rfl, rfl⟩ := EvalE.det h h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .varNull .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .block _ _ _ ss store' inner st' status halloc hs, h2 => by
    cases h2 with
    | block _ _ _ _ store2 inner2 st2 status2 halloc2 hs2 =>
      rw [halloc] at halloc2; cases halloc2; exact ExecSeq.det hs hs2
  | _, _, _, _, _, _, _, _, .ifTrue _ _ _ c t e st' st'' v status hc ht hs, h2 => by
    cases h2 with
    | ifTrue _ _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ExecS.det hs hs2
    | ifFalse _ _ _ _ _ _ st2 st2' v2 status2 hc2 hf2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
    | ifNone _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, _, _, .ifFalse _ _ _ c t e st' st'' v status hc hf hs, h2 => by
    cases h2 with
    | ifTrue _ _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | ifFalse _ _ _ _ _ _ st2 st2' v2 status2 hc2 hf2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ExecS.det hs hs2
  | _, _, _, _, _, _, _, _, .ifNone _ _ _ c t st' v hc hf, h2 => by
    cases h2 with
    | ifTrue _ _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | ifNone _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .whileFalse _ _ _ c b st' v hc hf, h2 => by
    cases h2 with
    | whileFalse _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ⟨rfl, rfl⟩
    | whileBreak _ _ _ _ _ st2 st2' v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | whileRet _ _ _ _ _ st2 st2' v2 rv2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | whileLoop _ _ _ _ _ st2 st2' st2'' v2 status2 status2' hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, _, _, .whileBreak _ _ _ c b st' st'' v hc ht hb, h2 => by
    cases h2 with
    | whileFalse _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
    | whileBreak _ _ _ _ _ st2 st2' v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, -⟩ := ExecS.det hb hb2; exact ⟨rfl, rfl⟩
    | whileRet _ _ _ _ _ st2 st2' v2 rv2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h
    | whileLoop _ _ _ _ _ st2 st2' st2'' v2 status2 status2' hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _, .whileRet _ _ _ c b st' st'' v rv hc ht hb, h2 => by
    cases h2 with
    | whileFalse _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
    | whileBreak _ _ _ _ _ st2 st2' v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h
    | whileRet _ _ _ _ _ st2 st2' v2 rv2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h; exact ⟨rfl, rfl⟩
    | whileLoop _ _ _ _ _ st2 st2' st2'' v2 status2 status2' hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _,
      .whileLoop _ _ _ c b st' st'' st''' v status status' hc ht hb hst hw, h2 => by
    cases h2 with
    | whileFalse _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
    | whileBreak _ _ _ _ _ st2 st2' v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst with h | h <;> cases h
    | whileRet _ _ _ _ _ st2 st2' v2 rv2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst with h | h <;> cases h
    | whileLoop _ _ _ _ _ st2 st2' st2'' v2 status2 status2' hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      exact ExecS.det hw hw2
  | _, _, _, _, _, _, _, _,
      .forStart _ _ _ init cnd step b store' outer st' st'' status halloc hi hl, h2 => by
    cases h2 with
    | forStart _ _ _ _ _ _ _ store2 outer2 st2 st2' status2 halloc2 hi2 hl2 =>
      rw [halloc] at halloc2; cases halloc2
      obtain rfl := ExecInit.det hi hi2
      exact ForLoop.det hl hl2
  | _, _, _, _, _, _, _, _, .ret _ _ _ e st' v h, h2 => by
    cases h2 with
    | ret _ _ _ _ st2 v2 h' => obtain ⟨rfl, rfl⟩ := EvalE.det h h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .retNull .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .brk .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .cont .., h2 => by cases h2; exact ⟨rfl, rfl⟩
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem ExecInit.det : ∀ {st d a init s1 s2}, ExecInit st d a init s1 →
    ExecInit st d a init s2 → s1 = s2
  | _, _, _, _, _, _, .none .., h2 => by cases h2; rfl
  | _, _, _, _, _, _, .some _ _ _ s st' status h, h2 => by
    cases h2 with
    | some _ _ _ _ st2 status2 h' => exact (ExecS.det h h').1
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ForLoop.det : ∀ {st d a cnd step b s1 t1 s2 t2}, ForLoop st d a cnd step b s1 t1 →
    ForLoop st d a cnd step b s2 t2 → s1 = s2 ∧ t1 = t2
  | _, _, _, _, _, _, _, _, _, _, .condFalse _ _ _ c step b st' v hc hf, h2 => by
    cases h2 with
    | condFalse _ _ _ _ _ _ st2 v2 hc2 hf2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ⟨rfl, rfl⟩
    | bodyBreak _ _ _ _ _ _ st2 st2' hc2 hb2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
    | bodyRet _ _ _ _ _ _ st2 st2' rv2 hc2 hb2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
    | loop _ _ _ _ _ _ st2 st2' st2'' st2''' status2 status2' hc2 hb2 hst2 hs2 hl2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, _, _, _, _, .bodyBreak _ _ _ cnd step b st' st'' hc hb, h2 => by
    have hnf : ∀ c s2 v, cnd = some c → EvalE _ _ _ c s2 v → v.truthy = false → False :=
      fun c s2 v e he hf => ForCond.not_false hc e he hf
    cases h2 with
    | condFalse _ _ _ _ _ _ st2 v2 hc2 hf2 =>
      exact (hnf _ _ _ rfl hc2 hf2).elim
    | bodyBreak _ _ _ _ _ _ st2 st2' hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, -⟩ := ExecS.det hb hb2; exact ⟨rfl, rfl⟩
    | bodyRet _ _ _ _ _ _ st2 st2' rv2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h
    | loop _ _ _ _ _ _ st2 st2' st2'' st2''' status2 status2' hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _, _, _, .bodyRet _ _ _ cnd step b st' st'' rv hc hb, h2 => by
    have hnf : ∀ c s2 v, cnd = some c → EvalE _ _ _ c s2 v → v.truthy = false → False :=
      fun c s2 v e he hf => ForCond.not_false hc e he hf
    cases h2 with
    | condFalse _ _ _ _ _ _ st2 v2 hc2 hf2 =>
      exact (hnf _ _ _ rfl hc2 hf2).elim
    | bodyBreak _ _ _ _ _ _ st2 st2' hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h
    | bodyRet _ _ _ _ _ _ st2 st2' rv2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, h⟩ := ExecS.det hb hb2; cases h; exact ⟨rfl, rfl⟩
    | loop _ _ _ _ _ _ st2 st2' st2'' st2''' status2 status2' hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _, _, _,
      .loop _ _ _ cnd step b st' st'' st''' st'''' status status' hc hb hst hs hl, h2 => by
    have hnf : ∀ c s2 v, cnd = some c → EvalE _ _ _ c s2 v → v.truthy = false → False :=
      fun c s2 v e he hf => ForCond.not_false hc e he hf
    cases h2 with
    | condFalse _ _ _ _ _ _ st2 v2 hc2 hf2 =>
      exact (hnf _ _ _ rfl hc2 hf2).elim
    | bodyBreak _ _ _ _ _ _ st2 st2' hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst with h | h <;> cases h
    | bodyRet _ _ _ _ _ _ st2 st2' rv2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst with h | h <;> cases h
    | loop _ _ _ _ _ _ st2 st2' st2'' st2''' status2 status2' hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      obtain rfl := ExecStep.det hs hs2
      exact ForLoop.det hl hl2
termination_by structural _ _ _ _ _ _ _ _ _ _ h1 => h1

theorem ForCond.det : ∀ {st d a cnd s1 s2}, ForCond st d a cnd s1 → ForCond st d a cnd s2 →
    s1 = s2
  | _, _, _, _, _, _, .none .., h2 => by cases h2; rfl
  | _, _, _, _, _, _, .some _ _ _ c st' v h ht, h2 => by
    cases h2 with
    | some _ _ _ _ st2 v2 h' ht2 => exact (EvalE.det h h').1
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ForCond.not_false : ∀ {st d a cnd s1 c s2 v}, ForCond st d a cnd s1 → cnd = some c →
    EvalE st d a c s2 v → v.truthy = false → False
  | _, _, _, _, _, _, _, _, .none .., hc, _, _ => by cases hc
  | _, _, _, _, _, _, _, _, .some _ _ _ c st' v h ht, hc, h2, hf => by
    have e := Option.some.inj hc
    subst e
    have := EvalE.det h h2
    obtain ⟨-, rfl⟩ := this; rw [ht] at hf; cases hf
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem ExecStep.det : ∀ {st d a step s1 s2}, ExecStep st d a step s1 →
    ExecStep st d a step s2 → s1 = s2
  | _, _, _, _, _, _, .none .., h2 => by cases h2; rfl
  | _, _, _, _, _, _, .some _ _ _ e st' v h, h2 => by
    cases h2 with
    | some _ _ _ _ st2 v2 h' => exact (EvalE.det h h').1
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecSeq.det : ∀ {st d a ss s1 t1 s2 t2}, ExecSeq st d a ss s1 t1 →
    ExecSeq st d a ss s2 t2 → s1 = s2 ∧ t1 = t2
  | _, _, _, _, _, _, _, _, .nil .., h2 => by cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, .consNormal _ _ _ s ss st' st'' status hs hss, h2 => by
    cases h2 with
    | consNormal _ _ _ _ _ st2 st2' status2 hs2 hss2 =>
      obtain ⟨rfl, -⟩ := ExecS.det hs hs2; exact ExecSeq.det hss hss2
    | consAbrupt _ _ _ _ _ st2 status2 hs2 hne2 =>
      obtain ⟨rfl, rfl⟩ := ExecS.det hs hs2; exact absurd rfl hne2
  | _, _, _, _, _, _, _, _, .consAbrupt _ _ _ s ss st' status hs hne, h2 => by
    cases h2 with
    | consNormal _ _ _ _ _ st2 st2' status2 hs2 hss2 =>
      obtain ⟨rfl, rfl⟩ := ExecS.det hs hs2; exact absurd rfl hne
    | consAbrupt _ _ _ _ _ st2 status2 hs2 hne2 => exact ExecS.det hs hs2
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

end

mutual

theorem EvalE.not_err : ∀ {st d a e s1 v1}, EvalE st d a e s1 v1 → EvalErr st d a e → False
  | _, _, _, _, _, _, .int .., herr => by cases herr
  | _, _, _, _, _, _, .str .., herr => by cases herr
  | _, _, _, _, _, _, .bool .., herr => by cases herr
  | _, _, _, _, _, _, .null .., herr => by cases herr
  | _, _, _, _, _, _, .var _ _ _ x v hv, herr => by
    cases herr with
    | varUndef _ _ _ _ hn => rw [hv] at hn; cases hn
  | _, _, _, _, _, _, .assign _ _ _ x e st' v s'' he hs, herr => by
    have ne := EvalE.not_err he
    cases herr with
    | assignE _ _ _ _ _ h' => exact ne h'
    | assignUnbound _ _ _ _ _ st2 v2 he2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2; rw [hs] at hs2; cases hs2
  | _, _, _, _, _, _, .binary _ _ _ op l r st' st'' lv rv v hl hr hop, herr => by
    have nl := EvalE.not_err hl
    have nr := EvalE.not_err hr
    cases herr with
    | binaryL _ _ _ _ _ _ h' => exact nl h'
    | binaryR _ _ _ _ _ _ st2 lv2 hl2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; exact nr hr2
    | binaryOp _ _ _ _ _ _ st2 st2' lv2 rv2 hl2 hr2 hop2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2
      obtain ⟨rfl, rfl⟩ := EvalE.det hr hr2
      rw [hop] at hop2; cases hop2
  | _, _, _, _, _, _, .orTrue _ _ _ l r st' lv hl ht, herr => by
    have nl := EvalE.not_err hl
    cases herr with
    | orL _ _ _ _ _ h' => exact nl h'
    | orR _ _ _ _ _ st2 lv2 hl2 hf2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, .orFalse _ _ _ l r st' st'' lv rv hl hf hr, herr => by
    have nl := EvalE.not_err hl
    have nr := EvalE.not_err hr
    cases herr with
    | orL _ _ _ _ _ h' => exact nl h'
    | orR _ _ _ _ _ st2 lv2 hl2 hf2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; exact nr hr2
  | _, _, _, _, _, _, .andFalse _ _ _ l r st' lv hl hf, herr => by
    have nl := EvalE.not_err hl
    cases herr with
    | andL _ _ _ _ _ h' => exact nl h'
    | andR _ _ _ _ _ st2 lv2 hl2 ht2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .andTrue _ _ _ l r st' st'' lv rv hl ht hr, herr => by
    have nl := EvalE.not_err hl
    have nr := EvalE.not_err hr
    cases herr with
    | andL _ _ _ _ _ h' => exact nl h'
    | andR _ _ _ _ _ st2 lv2 hl2 ht2 hr2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; exact nr hr2
  | _, _, _, _, _, _, .neg _ _ _ e st' n h, herr => by
    have ne := EvalE.not_err h
    cases herr with
    | unaryE _ _ _ _ _ h' => exact ne h'
    | negType _ _ _ _ st2 v2 h2 hn =>
      obtain ⟨rfl, rfl⟩ := EvalE.det h h2; exact hn n rfl
  | _, _, _, _, _, _, .not _ _ _ e st' v h, herr => by
    have ne := EvalE.not_err h
    cases herr with
    | unaryE _ _ _ _ _ h' => exact ne h'
  | _, _, _, _, _, _, .call _ _ _ f args st' st'' st''' fv vs v hf hlen ha hc, herr => by
    have nf := EvalE.not_err hf
    have na := EvalArgs.not_err ha
    have nc := Call.not_err hc
    cases herr with
    | callF _ _ _ _ _ h' => exact nf h'
    | callTooMany _ _ _ _ _ st2 fv2 hf2 hlt => omega
    | callArgs _ _ _ _ _ st2 fv2 hf2 hlen2 ha2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2; exact na ha2
    | callC _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 hc2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2
      obtain ⟨rfl, rfl⟩ := EvalArgs.det ha ha2
      exact nc hc2
  | _, _, _, _, _, _, .fn .., herr => by cases herr
termination_by structural _ _ _ _ _ _ h1 => h1

theorem EvalArgs.not_err : ∀ {st d a es s1 v1}, EvalArgs st d a es s1 v1 →
    EvalArgsErr st d a es → False
  | _, _, _, _, _, _, .nil .., herr => by cases herr
  | _, _, _, _, _, _, .cons _ _ _ e es st' st'' v vs he hes, herr => by
    have ne := EvalE.not_err he
    have nes := EvalArgs.not_err hes
    cases herr with
    | head _ _ _ _ _ h' => exact ne h'
    | tail _ _ _ _ _ st2 v2 he2 hes2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2; exact nes hes2
termination_by structural _ _ _ _ _ _ h1 => h1

theorem Call.not_err : ∀ {st d fv vs s1 v1}, Call st d fv vs s1 v1 → CallErr st d fv vs → False
  | _, _, _, _, _, _,
      .closure _ _ a cd vs store' frame st' status v hcd hlen hd halloc hbody hst, herr => by
    have nb := ExecSeq.not_err hbody
    cases herr with
    | notCallable _ _ _ _ hnc _ => exact hnc a rfl
    | badClosure _ _ _ _ hn => rw [hcd] at hn; cases hn
    | arity _ _ _ cd2 _ hcd2 hne =>
      rw [hcd] at hcd2; cases hcd2; exact hne hlen
    | depth _ _ _ cd2 _ hcd2 _ hnd =>
      rw [hcd] at hcd2; cases hcd2; exact hnd hd
    | body _ _ _ cd2 _ store2 frame2 hcd2 _ _ halloc2 hb2 =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      exact nb hb2
    | escape _ _ _ cd2 _ store2 frame2 st2 status2 hcd2 _ _ halloc2 hb2 hst2 =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      obtain ⟨rfl, rfl⟩ := ExecSeq.det hbody hb2
      rcases hst with ⟨rfl, -⟩ | rfl <;> rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, .print .., herr => by
    cases herr with
    | notCallable _ _ _ _ _ hnn => exact hnn _ rfl
  | _, _, _, _, _, _, .println .., herr => by
    cases herr with
    | notCallable _ _ _ _ _ hnn => exact hnn _ rfl
  | _, _, _, _, _, _, .assertOk _ _ vs v m hvs ht, herr => by
    cases herr with
    | notCallable _ _ _ _ _ hnn => exact hnn _ rfl
    | assertFail _ _ _ v2 m2 hvs2 hf2 =>
      have hv : v = v2 := by
        rcases hvs with rfl | rfl <;> rcases hvs2 with h | h <;> simp_all
      subst hv; rw [ht] at hf2; cases hf2
    | assertArity _ _ _ h1 h2 =>
      rcases hvs with rfl | rfl
      · exact h1 _ rfl
      · exact h2 _ _ rfl
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecS.not_err : ∀ {st d a s s1 t1}, ExecS st d a s s1 t1 → ExecErr st d a s → False
  | _, _, _, _, _, _, .expr _ _ _ e st' v h, herr => by
    have ne := EvalE.not_err h
    cases herr with
    | expr _ _ _ _ h' => exact ne h'
  | _, _, _, _, _, _, .varInit _ _ _ x e st' v h, herr => by
    have ne := EvalE.not_err h
    cases herr with
    | varInit _ _ _ _ _ h' => exact ne h'
  | _, _, _, _, _, _, .varNull .., herr => by cases herr
  | _, _, _, _, _, _, .block _ _ _ ss store' inner st' status halloc hs, herr => by
    have ns := ExecSeq.not_err hs
    cases herr with
    | block _ _ _ _ store2 inner2 halloc2 hs2 =>
      rw [halloc] at halloc2; cases halloc2; exact ns hs2
  | _, _, _, _, _, _, .ifTrue _ _ _ c t e st' st'' v status hc ht hs, herr => by
    have nc := EvalE.not_err hc
    have ns := ExecS.not_err hs
    cases herr with
    | ifCond _ _ _ _ _ _ h' => exact nc h'
    | ifThen _ _ _ _ _ _ st2 v2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ns hs2
    | ifElse _ _ _ _ _ _ st2 v2 hc2 hf2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, .ifFalse _ _ _ c t e st' st'' v status hc hf hs, herr => by
    have nc := EvalE.not_err hc
    have ns := ExecS.not_err hs
    cases herr with
    | ifCond _ _ _ _ _ _ h' => exact nc h'
    | ifThen _ _ _ _ _ _ st2 v2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | ifElse _ _ _ _ _ _ st2 v2 hc2 hf2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact ns hs2
  | _, _, _, _, _, _, .ifNone _ _ _ c t st' v hc hf, herr => by
    have nc := EvalE.not_err hc
    cases herr with
    | ifCond _ _ _ _ _ _ h' => exact nc h'
    | ifThen _ _ _ _ _ _ st2 v2 hc2 ht2 hs2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .whileFalse _ _ _ c b st' v hc hf, herr => by
    have nc := EvalE.not_err hc
    cases herr with
    | whileCond _ _ _ _ _ h' => exact nc h'
    | whileBody _ _ _ _ _ st2 v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | whileLoop _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .whileBreak _ _ _ c b st' st'' v hc ht hb, herr => by
    have nc := EvalE.not_err hc
    have nb := ExecS.not_err hb
    cases herr with
    | whileCond _ _ _ _ _ h' => exact nc h'
    | whileBody _ _ _ _ _ st2 v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact nb hb2
    | whileLoop _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, .whileRet _ _ _ c b st' st'' v rv hc ht hb, herr => by
    have nc := EvalE.not_err hc
    have nb := ExecS.not_err hb
    cases herr with
    | whileCond _ _ _ _ _ h' => exact nc h'
    | whileBody _ _ _ _ _ st2 v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact nb hb2
    | whileLoop _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _,
      .whileLoop _ _ _ c b st' st'' st''' v status status' hc ht hb hst hw, herr => by
    have nc := EvalE.not_err hc
    have nb := ExecS.not_err hb
    have nw := ExecS.not_err hw
    cases herr with
    | whileCond _ _ _ _ _ h' => exact nc h'
    | whileBody _ _ _ _ _ st2 v2 hc2 ht2 hb2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact nb hb2
    | whileLoop _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 hw2 =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      exact nw hw2
  | _, _, _, _, _, _,
      .forStart _ _ _ init cnd step b store' outer st' st'' status halloc hi hl, herr => by
    have ni := ExecInit.not_err hi
    have nl := ForLoop.not_err hl
    cases herr with
    | forInit _ _ _ init2 _ _ _ store2 outer2 halloc2 hi2 =>
      rw [halloc] at halloc2; cases halloc2; exact ni _ rfl hi2
    | forLoop _ _ _ _ _ _ _ store2 outer2 st2 halloc2 hi2 hl2 =>
      rw [halloc] at halloc2; cases halloc2
      obtain rfl := ExecInit.det hi hi2
      exact nl hl2
  | _, _, _, _, _, _, .ret _ _ _ e st' v h, herr => by
    have ne := EvalE.not_err h
    cases herr with
    | ret _ _ _ _ h' => exact ne h'
  | _, _, _, _, _, _, .retNull .., herr => by cases herr
  | _, _, _, _, _, _, .brk .., herr => by cases herr
  | _, _, _, _, _, _, .cont .., herr => by cases herr
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecInit.not_err : ∀ {st d a init s1}, ExecInit st d a init s1 →
    ∀ s, init = some s → ExecErr st d a s → False
  | _, _, _, _, _, .none .., _, he, _ => by cases he
  | _, _, _, _, _, .some _ _ _ s st' status h, s', he, herr => by
    have ns := ExecS.not_err h
    have e := Option.some.inj he
    subst e
    exact ns herr
termination_by structural _ _ _ _ _ h1 => h1

theorem ForLoop.not_err : ∀ {st d a cnd step b s1 t1}, ForLoop st d a cnd step b s1 t1 →
    ForLoopErr st d a cnd step b → False
  | _, _, _, _, _, _, _, _, .condFalse _ _ _ c step b st' v hc hf, herr => by
    have nc := EvalE.not_err hc
    cases herr with
    | cond _ _ _ _ _ _ h' => exact nc h'
    | body _ _ _ _ _ _ st2 hc2 hb2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
    | step _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 he2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2' ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2'; rw [hf] at ht2; cases ht2
    | loop _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 hl2 =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, _, _, .bodyBreak _ _ _ cnd step b st' st'' hc hb, herr => by
    have nc := ForCond.not_err hc
    have nb := ExecS.not_err hb
    cases herr with
    | cond _ _ _ _ _ _ h' => exact nc _ rfl h'
    | body _ _ _ _ _ _ st2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2; exact nb hb2
    | step _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 he2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
    | loop _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _, .bodyRet _ _ _ cnd step b st' st'' rv hc hb, herr => by
    have nc := ForCond.not_err hc
    have nb := ExecS.not_err hb
    cases herr with
    | cond _ _ _ _ _ _ h' => exact nc _ rfl h'
    | body _ _ _ _ _ _ st2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2; exact nb hb2
    | step _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 he2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
    | loop _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _,
      .loop _ _ _ cnd step b st' st'' st''' st'''' status status' hc hb hst hs hl, herr => by
    have nc := ForCond.not_err hc
    have nb := ExecS.not_err hb
    have ns := ExecStep.not_err hs
    have nl := ForLoop.not_err hl
    cases herr with
    | cond _ _ _ _ _ _ h' => exact nc _ rfl h'
    | body _ _ _ _ _ _ st2 hc2 hb2 =>
      obtain rfl := ForCond.det hc hc2; exact nb hb2
    | step _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 he2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      exact ns _ rfl he2
    | loop _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 hl2 =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      obtain rfl := ExecStep.det hs hs2
      exact nl hl2
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem ForCond.not_err : ∀ {st d a cnd s1}, ForCond st d a cnd s1 →
    ∀ c, cnd = some c → EvalErr st d a c → False
  | _, _, _, _, _, .none .., _, he, _ => by cases he
  | _, _, _, _, _, .some _ _ _ c st' v h ht, c', he, herr => by
    have ne := EvalE.not_err h
    have e := Option.some.inj he
    subst e
    exact ne herr
termination_by structural _ _ _ _ _ h1 => h1

theorem ExecStep.not_err : ∀ {st d a step s1}, ExecStep st d a step s1 →
    ∀ e, step = some e → EvalErr st d a e → False
  | _, _, _, _, _, .none .., _, he, _ => by cases he
  | _, _, _, _, _, .some _ _ _ e st' v h, e', he, herr => by
    have ne := EvalE.not_err h
    have e := Option.some.inj he
    subst e
    exact ne herr
termination_by structural _ _ _ _ _ h1 => h1

theorem ExecSeq.not_err : ∀ {st d a ss s1 t1}, ExecSeq st d a ss s1 t1 →
    ExecSeqErr st d a ss → False
  | _, _, _, _, _, _, .nil .., herr => by cases herr
  | _, _, _, _, _, _, .consNormal _ _ _ s ss st' st'' status hs hss, herr => by
    have ns := ExecS.not_err hs
    have nss := ExecSeq.not_err hss
    cases herr with
    | head _ _ _ _ _ h' => exact ns h'
    | tail _ _ _ _ _ st2 hs2 hss2 =>
      obtain ⟨rfl, -⟩ := ExecS.det hs hs2; exact nss hss2
  | _, _, _, _, _, _, .consAbrupt _ _ _ s ss st' status hs hne, herr => by
    have ns := ExecS.not_err hs
    cases herr with
    | head _ _ _ _ _ h' => exact ns h'
    | tail _ _ _ _ _ st2 hs2 hss2 =>
      obtain ⟨rfl, rfl⟩ := ExecS.det hs hs2; exact hne rfl
termination_by structural _ _ _ _ _ _ h1 => h1

end

def EBound (st : St) (d : Nat) (a : Addr) (e : Expr) : Prop :=
  ∃ N, ∀ n, EApprox n st d a e → n ≤ N

def ArgsBound (st : St) (d : Nat) (a : Addr) (es : List Expr) : Prop :=
  ∃ N, ∀ n, ArgsApprox n st d a es → n ≤ N

def CBound (st : St) (d : Nat) (fv : Value) (vs : List Value) : Prop :=
  ∃ N, ∀ n, CApprox n st d fv vs → n ≤ N

def SBound (st : St) (d : Nat) (a : Addr) (s : Stmt) : Prop :=
  ∃ N, ∀ n, SApprox n st d a s → n ≤ N

def FlBound (st : St) (d : Nat) (a : Addr) (cnd step : Option Expr) (b : Stmt) : Prop :=
  ∃ N, ∀ n, FlApprox n st d a cnd step b → n ≤ N

def SeqBound (st : St) (d : Nat) (a : Addr) (ss : List Stmt) : Prop :=
  ∃ N, ∀ n, Approx n st d a ss → n ≤ N

def OSBound (st : St) (d : Nat) (a : Addr) (o : Option Stmt) : Prop :=
  ∃ N, ∀ s n, o = some s → SApprox n st d a s → n ≤ N

def OEBound (st : St) (d : Nat) (a : Addr) (o : Option Expr) : Prop :=
  ∃ N, ∀ e n, o = some e → EApprox n st d a e → n ≤ N

theorem OEBound.none (st : St) (d : Nat) (a : Addr) : OEBound st d a none :=
  ⟨0, fun _ _ h _ => by cases h⟩
theorem OEBound.some {st : St} {d : Nat} {a : Addr} {e : Expr} (h : EBound st d a e) :
    OEBound st d a (some e) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun e' n he hn => by cases he; exact hN n hn⟩
theorem OSBound.none (st : St) (d : Nat) (a : Addr) : OSBound st d a none :=
  ⟨0, fun _ _ h _ => by cases h⟩
theorem OSBound.some {st : St} {d : Nat} {a : Addr} {s : Stmt} (h : SBound st d a s) :
    OSBound st d a (some s) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun s' n hs hn => by cases hs; exact hN n hn⟩

mutual

theorem EvalE.bound : ∀ {st d a e s1 v1}, EvalE st d a e s1 v1 → EBound st d a e
  | _, _, _, _, _, _, .int .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .str .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .bool .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .null .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .var .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .fn .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .assign _ _ _ x e st' v s'' he hs => by
    obtain ⟨N, hN⟩ := EvalE.bound he
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | assignE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .binary _ _ _ op l r st' st'' lv rv v hl hr hop => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalE.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | binaryL k _ _ _ _ _ _ h' => have := hNl k h'; omega
    | binaryR k _ _ _ _ _ _ st2 lv2 hl2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, _, _, .orTrue _ _ _ l r st' lv hl ht => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    refine ⟨Nl + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | orL k _ _ _ _ _ h' => have := hNl k h'; omega
    | orR k _ _ _ _ _ st2 lv2 hl2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, .orFalse _ _ _ l r st' st'' lv rv hl hf hr => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalE.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | orL k _ _ _ _ _ h' => have := hNl k h'; omega
    | orR k _ _ _ _ _ st2 lv2 hl2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, _, _, .andFalse _ _ _ l r st' lv hl hf => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    refine ⟨Nl + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | andL k _ _ _ _ _ h' => have := hNl k h'; omega
    | andR k _ _ _ _ _ st2 lv2 hl2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .andTrue _ _ _ l r st' st'' lv rv hl ht hr => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalE.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | andL k _ _ _ _ _ h' => have := hNl k h'; omega
    | andR k _ _ _ _ _ st2 lv2 hl2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, _, _, .neg _ _ _ e st' n h => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | unaryE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .not _ _ _ e st' v h => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | unaryE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .call _ _ _ f args st' st'' st''' fv vs v hf hlen ha hc => by
    obtain ⟨Nf, hNf⟩ := EvalE.bound hf
    obtain ⟨Na, hNa⟩ := EvalArgs.bound ha
    obtain ⟨Nc, hNc⟩ := Call.bound hc
    refine ⟨max Nf (max Na Nc) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | callF k _ _ _ _ _ h' => have := hNf k h'; omega
    | callArgs k _ _ _ _ _ st2 fv2 hf2 hlen2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2; have := hNa k h'; omega
    | callC k _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2
      obtain ⟨rfl, rfl⟩ := EvalArgs.det ha ha2
      have := hNc k h'; omega
termination_by structural _ _ _ _ _ _ h1 => h1

theorem EvalArgs.bound : ∀ {st d a es s1 v1}, EvalArgs st d a es s1 v1 → ArgsBound st d a es
  | _, _, _, _, _, _, .nil .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .cons _ _ _ e es st' st'' v vs he hes => by
    obtain ⟨Ne, hNe⟩ := EvalE.bound he
    obtain ⟨Ns, hNs⟩ := EvalArgs.bound hes
    refine ⟨max Ne Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | head k _ _ _ _ _ h' => have := hNe k h'; omega
    | tail k _ _ _ _ _ st2 v2 he2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2; have := hNs k h'; omega
termination_by structural _ _ _ _ _ _ h1 => h1

theorem Call.bound : ∀ {st d fv vs s1 v1}, Call st d fv vs s1 v1 → CBound st d fv vs
  | _, _, _, _, _, _,
      .closure _ _ a cd vs store' frame st' status v hcd hlen hd halloc hbody hst => by
    obtain ⟨N, hN⟩ := ExecSeq.bound hbody
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 _ _ halloc2 h' =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      have := hN k h'; omega
  | _, _, _, _, _, _, .print .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .println .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .assertOk .. => ⟨0, fun n hn => by cases hn; omega⟩
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecS.bound : ∀ {st d a s s1 t1}, ExecS st d a s s1 t1 → SBound st d a s
  | _, _, _, _, _, _, .expr _ _ _ e st' v h => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | expr k _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .varInit _ _ _ x e st' v h => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | varInit k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .varNull .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .block _ _ _ ss store' inner st' status halloc hs => by
    obtain ⟨N, hN⟩ := ExecSeq.bound hs
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | block k _ _ _ _ store2 inner2 halloc2 h' =>
      rw [halloc] at halloc2; cases halloc2; have := hN k h'; omega
  | _, _, _, _, _, _, .ifTrue _ _ _ c t e st' st'' v status hc ht hs => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Ns, hNs⟩ := ExecS.bound hs
    refine ⟨max Nc Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNs k h'; omega
    | ifElse k _ _ _ _ _ _ st2 v2 hc2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
  | _, _, _, _, _, _, .ifFalse _ _ _ c t e st' st'' v status hc hf hs => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Ns, hNs⟩ := ExecS.bound hs
    refine ⟨max Nc Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | ifElse k _ _ _ _ _ _ st2 v2 hc2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNs k h'; omega
  | _, _, _, _, _, _, .ifNone _ _ _ c t st' v hc hf => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    refine ⟨Nc + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .whileFalse _ _ _ c b st' v hc hf => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    refine ⟨Nc + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, .whileBreak _ _ _ c b st' st'' v hc ht hb => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNb k h'; omega
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, .whileRet _ _ _ c b st' st'' v rv hc ht hb => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNb k h'; omega
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, .whileLoop _ _ _ c b st' st'' st''' v status status' hc ht hb hst hw => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    obtain ⟨Nw, hNw⟩ := ExecS.bound hw
    refine ⟨max Nc (max Nb Nw) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNb k h'; omega
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      have := hNw k h'; omega
  | _, _, _, _, _, _,
      .forStart _ _ _ init cnd step b store' outer st' st'' status halloc hi hl => by
    obtain ⟨Ni, hNi⟩ := ExecInit.bound hi
    obtain ⟨Nl, hNl⟩ := ForLoop.bound hl
    refine ⟨max Ni Nl + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | forInit k _ _ _ init2 _ _ _ store2 outer2 halloc2 h' =>
      rw [halloc] at halloc2; cases halloc2; have := hNi _ k rfl h'; omega
    | forLoop k _ _ _ _ _ _ _ store2 outer2 st2 halloc2 hi2 h' =>
      rw [halloc] at halloc2; cases halloc2
      obtain rfl := ExecInit.det hi hi2
      have := hNl k h'; omega
  | _, _, _, _, _, _, .ret _ _ _ e st' v h => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ret k _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, _, _, .retNull .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .brk .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .cont .. => ⟨0, fun n hn => by cases hn; omega⟩
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecInit.bound : ∀ {st d a init s1}, ExecInit st d a init s1 → OSBound st d a init
  | _, _, _, _, _, .none .. => OSBound.none _ _ _
  | _, _, _, _, _, .some _ _ _ s st' status h => OSBound.some (ExecS.bound h)
termination_by structural _ _ _ _ _ h1 => h1

theorem ForLoop.bound : ∀ {st d a cnd step b s1 t1}, ForLoop st d a cnd step b s1 t1 →
    FlBound st d a cnd step b
  | _, _, _, _, _, _, _, _, .condFalse _ _ _ c step b st' v hc hf => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    refine ⟨Nc + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 =>
        obtain ⟨rfl, rfl⟩ := EvalE.det hc he2; rw [hf] at ht2; cases ht2
  | _, _, _, _, _, _, _, _, .bodyBreak _ _ _ cnd step b st' st'' hc hb => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _, .bodyRet _ _ _ cnd step b st' st'' rv hc hb => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      rcases hst2 with h | h <;> cases h
  | _, _, _, _, _, _, _, _,
      .loop _ _ _ cnd step b st' st'' st''' st'''' status status' hc hb hst hs hl => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    obtain ⟨Ns, hNs⟩ := ExecStep.bound hs
    obtain ⟨Nl, hNl⟩ := ForLoop.bound hl
    refine ⟨max (max Nc Nb) (max Ns Nl) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      have := hNs _ k rfl h'; omega
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      obtain rfl := ExecStep.det hs hs2
      have := hNl k h'; omega
termination_by structural _ _ _ _ _ _ _ _ h1 => h1

theorem ForCond.bound : ∀ {st d a cnd s1}, ForCond st d a cnd s1 → OEBound st d a cnd
  | _, _, _, _, _, .none .. => OEBound.none _ _ _
  | _, _, _, _, _, .some _ _ _ c st' v h ht => OEBound.some (EvalE.bound h)
termination_by structural _ _ _ _ _ h1 => h1

theorem ExecStep.bound : ∀ {st d a step s1}, ExecStep st d a step s1 → OEBound st d a step
  | _, _, _, _, _, .none .. => OEBound.none _ _ _
  | _, _, _, _, _, .some _ _ _ e st' v h => OEBound.some (EvalE.bound h)
termination_by structural _ _ _ _ _ h1 => h1

theorem ExecSeq.bound : ∀ {st d a ss s1 t1}, ExecSeq st d a ss s1 t1 → SeqBound st d a ss
  | _, _, _, _, _, _, .nil .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, _, _, .consNormal _ _ _ s ss st' st'' status hs hss => by
    obtain ⟨Ns, hNs⟩ := ExecS.bound hs
    obtain ⟨Nss, hNss⟩ := ExecSeq.bound hss
    refine ⟨max Ns Nss + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | step k _ _ _ _ _ st2 hs2 h' =>
      obtain ⟨rfl, -⟩ := ExecS.det hs hs2; have := hNss k h'; omega
    | head k _ _ _ _ _ h' => have := hNs k h'; omega
  | _, _, _, _, _, _, .consAbrupt _ _ _ s ss st' status hs hne => by
    obtain ⟨Ns, hNs⟩ := ExecS.bound hs
    refine ⟨Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | step k _ _ _ _ _ st2 hs2 h' =>
      obtain ⟨rfl, rfl⟩ := ExecS.det hs hs2; exact absurd rfl hne
    | head k _ _ _ _ _ h' => have := hNs k h'; omega
termination_by structural _ _ _ _ _ _ h1 => h1

end

mutual

theorem EvalErr.bound : ∀ {st d a e}, EvalErr st d a e → EBound st d a e
  | _, _, _, _, .varUndef .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, .assignE _ _ _ x e h => by
    obtain ⟨N, hN⟩ := EvalErr.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | assignE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .assignUnbound _ _ _ x e st' v he hs => by
    obtain ⟨N, hN⟩ := EvalE.bound he
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | assignE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .binaryL _ _ _ op l r hl => by
    have nl := fun st' lv (h : EvalE _ _ _ l st' lv) => EvalE.not_err h hl
    obtain ⟨N, hN⟩ := EvalErr.bound hl
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | binaryL k _ _ _ _ _ _ h' => have := hN k h'; omega
    | binaryR k _ _ _ _ _ _ st2 lv2 hl2 h' => exact (nl _ _ hl2).elim
  | _, _, _, _, .binaryR _ _ _ op l r st' lv hl hr => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalErr.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | binaryL k _ _ _ _ _ _ h' => have := hNl k h'; omega
    | binaryR k _ _ _ _ _ _ st2 lv2 hl2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, .binaryOp _ _ _ op l r st' st'' lv rv hl hr hop => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalE.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | binaryL k _ _ _ _ _ _ h' => have := hNl k h'; omega
    | binaryR k _ _ _ _ _ _ st2 lv2 hl2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, .orL _ _ _ l r hl => by
    obtain ⟨N, hN⟩ := EvalErr.bound hl
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | orL k _ _ _ _ _ h' => have := hN k h'; omega
    | orR k _ _ _ _ _ st2 lv2 hl2 hf2 h' => exact (EvalE.not_err hl2 hl).elim
  | _, _, _, _, .orR _ _ _ l r st' lv hl hf hr => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalErr.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | orL k _ _ _ _ _ h' => have := hNl k h'; omega
    | orR k _ _ _ _ _ st2 lv2 hl2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, .andL _ _ _ l r hl => by
    obtain ⟨N, hN⟩ := EvalErr.bound hl
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | andL k _ _ _ _ _ h' => have := hN k h'; omega
    | andR k _ _ _ _ _ st2 lv2 hl2 ht2 h' => exact (EvalE.not_err hl2 hl).elim
  | _, _, _, _, .andR _ _ _ l r st' lv hl ht hr => by
    obtain ⟨Nl, hNl⟩ := EvalE.bound hl
    obtain ⟨Nr, hNr⟩ := EvalErr.bound hr
    refine ⟨max Nl Nr + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | andL k _ _ _ _ _ h' => have := hNl k h'; omega
    | andR k _ _ _ _ _ st2 lv2 hl2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hl hl2; have := hNr k h'; omega
  | _, _, _, _, .unaryE _ _ _ op e h => by
    obtain ⟨N, hN⟩ := EvalErr.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | unaryE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .negType _ _ _ e st' v h hn => by
    obtain ⟨N, hN⟩ := EvalE.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | unaryE k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .callF _ _ _ f args hf => by
    obtain ⟨N, hN⟩ := EvalErr.bound hf
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | callF k _ _ _ _ _ h' => have := hN k h'; omega
    | callArgs k _ _ _ _ _ st2 fv2 hf2 hlen2 h' => exact (EvalE.not_err hf2 hf).elim
    | callC k _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 h' => exact (EvalE.not_err hf2 hf).elim
  | _, _, _, _, .callTooMany _ _ _ f args st' fv hf hlt => by
    obtain ⟨N, hN⟩ := EvalE.bound hf
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | callF k _ _ _ _ _ h' => have := hN k h'; omega
    | callArgs k _ _ _ _ _ st2 fv2 hf2 hlen2 h' => omega
    | callC k _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 h' => omega
  | _, _, _, _, .callArgs _ _ _ f args st' fv hf hlen ha => by
    obtain ⟨Nf, hNf⟩ := EvalE.bound hf
    obtain ⟨Na, hNa⟩ := EvalArgsErr.bound ha
    refine ⟨max Nf Na + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | callF k _ _ _ _ _ h' => have := hNf k h'; omega
    | callArgs k _ _ _ _ _ st2 fv2 hf2 hlen2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2; have := hNa k h'; omega
    | callC k _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2; exact (EvalArgs.not_err ha2 ha).elim
  | _, _, _, _, .callC _ _ _ f args st' st'' fv vs hf hlen ha hc => by
    obtain ⟨Nf, hNf⟩ := EvalE.bound hf
    obtain ⟨Na, hNa⟩ := EvalArgs.bound ha
    obtain ⟨Nc, hNc⟩ := CallErr.bound hc
    refine ⟨max Nf (max Na Nc) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | callF k _ _ _ _ _ h' => have := hNf k h'; omega
    | callArgs k _ _ _ _ _ st2 fv2 hf2 hlen2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2; have := hNa k h'; omega
    | callC k _ _ _ _ _ st2 st2' fv2 vs2 hf2 hlen2 ha2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hf hf2
      obtain ⟨rfl, rfl⟩ := EvalArgs.det ha ha2
      have := hNc k h'; omega
termination_by structural _ _ _ _ h1 => h1

theorem EvalArgsErr.bound : ∀ {st d a es}, EvalArgsErr st d a es → ArgsBound st d a es
  | _, _, _, _, .head _ _ _ e es he => by
    obtain ⟨N, hN⟩ := EvalErr.bound he
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | head k _ _ _ _ _ h' => have := hN k h'; omega
    | tail k _ _ _ _ _ st2 v2 he2 h' => exact (EvalE.not_err he2 he).elim
  | _, _, _, _, .tail _ _ _ e es st' v he hes => by
    obtain ⟨Ne, hNe⟩ := EvalE.bound he
    obtain ⟨Ns, hNs⟩ := EvalArgsErr.bound hes
    refine ⟨max Ne Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | head k _ _ _ _ _ h' => have := hNe k h'; omega
    | tail k _ _ _ _ _ st2 v2 he2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det he he2; have := hNs k h'; omega
termination_by structural _ _ _ _ h1 => h1

theorem CallErr.bound : ∀ {st d fv vs}, CallErr st d fv vs → CBound st d fv vs
  | _, _, _, _, .notCallable _ _ _ _ hnc _ => by
    refine ⟨0, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ a _ _ _ _ _ _ _ _ _ => exact (hnc a rfl).elim
  | _, _, _, _, .badClosure _ _ a _ hn0 => by
    refine ⟨0, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 _ _ _ _ => rw [hn0] at hcd2; cases hcd2
  | _, _, _, _, .arity _ _ a cd _ hcd hne => by
    refine ⟨0, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 hlen2 _ _ _ =>
      rw [hcd] at hcd2; cases hcd2; exact (hne hlen2).elim
  | _, _, _, _, .depth _ _ a cd _ hcd _ hnd => by
    refine ⟨0, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 hlen2 hd2 _ _ => exact (hnd hd2).elim
  | _, _, _, _, .body _ _ a cd vs store' frame hcd hlen hd halloc hb => by
    obtain ⟨N, hN⟩ := ExecSeqErr.bound hb
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 _ _ halloc2 h' =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      have := hN k h'; omega
  | _, _, _, _, .escape _ _ a cd vs store' frame st' status hcd hlen hd halloc hb hst => by
    obtain ⟨N, hN⟩ := ExecSeq.bound hb
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | body k _ _ _ cd2 _ store2 frame2 hcd2 _ _ halloc2 h' =>
      rw [hcd] at hcd2; cases hcd2
      rw [halloc] at halloc2; cases halloc2
      have := hN k h'; omega
  | _, _, _, _, .assertFail .. => ⟨0, fun n hn => by cases hn; omega⟩
  | _, _, _, _, .assertArity .. => ⟨0, fun n hn => by cases hn; omega⟩
termination_by structural _ _ _ _ h1 => h1

theorem ExecErr.bound : ∀ {st d a s}, ExecErr st d a s → SBound st d a s
  | _, _, _, _, .expr _ _ _ e h => by
    obtain ⟨N, hN⟩ := EvalErr.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | expr k _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .varInit _ _ _ x e h => by
    obtain ⟨N, hN⟩ := EvalErr.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | varInit k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .block _ _ _ ss store' inner halloc hs => by
    obtain ⟨N, hN⟩ := ExecSeqErr.bound hs
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | block k _ _ _ _ store2 inner2 halloc2 h' =>
      rw [halloc] at halloc2; cases halloc2; have := hN k h'; omega
  | _, _, _, _, .ifCond _ _ _ c t e hc => by
    obtain ⟨N, hN⟩ := EvalErr.bound hc
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hN k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' => exact (EvalE.not_err hc2 hc).elim
    | ifElse k _ _ _ _ _ _ st2 v2 hc2 hf2 h' => exact (EvalE.not_err hc2 hc).elim
  | _, _, _, _, .ifThen _ _ _ c t e st' v hc ht hs => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Ns, hNs⟩ := ExecErr.bound hs
    refine ⟨max Nc Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNs k h'; omega
    | ifElse k _ _ _ _ _ _ st2 v2 hc2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [ht] at hf2; cases hf2
  | _, _, _, _, .ifElse _ _ _ c t e st' v hc hf hs => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Ns, hNs⟩ := ExecErr.bound hs
    refine ⟨max Nc Ns + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ifCond k _ _ _ _ _ _ h' => have := hNc k h'; omega
    | ifThen k _ _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; rw [hf] at ht2; cases ht2
    | ifElse k _ _ _ _ _ _ st2 v2 hc2 hf2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNs k h'; omega
  | _, _, _, _, .whileCond _ _ _ c b hc => by
    obtain ⟨N, hN⟩ := EvalErr.bound hc
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hN k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' => exact (EvalE.not_err hc2 hc).elim
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      exact (EvalE.not_err hc2 hc).elim
  | _, _, _, _, .whileBody _ _ _ c b st' v hc ht hb => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Nb, hNb⟩ := ExecErr.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNb k h'; omega
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; exact (ExecS.not_err hb2 hb).elim
  | _, _, _, _, .whileLoop _ _ _ c b st' st'' v status hc ht hb hst hw => by
    obtain ⟨Nc, hNc⟩ := EvalE.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    obtain ⟨Nw, hNw⟩ := ExecErr.bound hw
    refine ⟨max Nc (max Nb Nw) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | whileCond k _ _ _ _ _ h' => have := hNc k h'; omega
    | whileBody k _ _ _ _ _ st2 v2 hc2 ht2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2; have := hNb k h'; omega
    | whileLoop k _ _ _ _ _ st2 st2' v2 status2 hc2 ht2 hb2 hst2 h' =>
      obtain ⟨rfl, rfl⟩ := EvalE.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      have := hNw k h'; omega
  | _, _, _, _, .forInit _ _ _ init cnd step b store' outer halloc hi => by
    obtain ⟨N, hN⟩ := ExecErr.bound hi
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | forInit k _ _ _ _ _ _ _ store2 outer2 halloc2 h' =>
      rw [halloc] at halloc2; cases halloc2; have := hN k h'; omega
    | forLoop k _ _ _ _ _ _ _ store2 outer2 st2 halloc2 hi2 h' =>
      rw [halloc] at halloc2; cases halloc2
      cases hi2 with
      | some _ _ _ _ st3 status3 hs3 => exact (ExecS.not_err hs3 hi).elim
  | _, _, _, _, .forLoop _ _ _ init cnd step b store' outer st' halloc hi hl => by
    obtain ⟨Ni, hNi⟩ := ExecInit.bound hi
    obtain ⟨Nl, hNl⟩ := ForLoopErr.bound hl
    refine ⟨max Ni Nl + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | forInit k _ _ _ _ _ _ _ store2 outer2 halloc2 h' =>
      rw [halloc] at halloc2; cases halloc2; have := hNi _ k rfl h'; omega
    | forLoop k _ _ _ _ _ _ _ store2 outer2 st2 halloc2 hi2 h' =>
      rw [halloc] at halloc2; cases halloc2
      obtain rfl := ExecInit.det hi hi2
      have := hNl k h'; omega
  | _, _, _, _, .ret _ _ _ e h => by
    obtain ⟨N, hN⟩ := EvalErr.bound h
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | ret k _ _ _ _ h' => have := hN k h'; omega
termination_by structural _ _ _ _ h1 => h1

theorem ForLoopErr.bound : ∀ {st d a cnd step b}, ForLoopErr st d a cnd step b →
    FlBound st d a cnd step b
  | _, _, _, _, _, _, .cond _ _ _ c stp b hc => by
    obtain ⟨N, hN⟩ := EvalErr.bound hc
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hN k h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 => exact (EvalE.not_err he2 hc).elim
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 => exact (EvalE.not_err he2 hc).elim
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      cases hc2 with
      | some _ _ _ _ _ v2 he2 ht2 => exact (EvalE.not_err he2 hc).elim
  | _, _, _, _, _, _, .body _ _ _ cnd stp b st' hc hb => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecErr.bound hb
    refine ⟨max Nc Nb + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2; exact (ExecS.not_err hb2 hb).elim
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2; exact (ExecS.not_err hb2 hb).elim
  | _, _, _, _, _, _, .step _ _ _ cnd e b st' st'' status hc hb hst he => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    obtain ⟨Ne, hNe⟩ := EvalErr.bound he
    refine ⟨max Nc (max Nb Ne) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      have := hNe k h'; omega
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      cases hs2 with
      | some _ _ _ _ st3 v3 he3 => exact (EvalE.not_err he3 he).elim
  | _, _, _, _, _, _, .loop _ _ _ cnd stp b st' st'' st''' status hc hb hst hs hl => by
    obtain ⟨Nc, hNc⟩ := ForCond.bound hc
    obtain ⟨Nb, hNb⟩ := ExecS.bound hb
    obtain ⟨Ns, hNs⟩ := ExecStep.bound hs
    obtain ⟨Nl, hNl⟩ := ForLoopErr.bound hl
    refine ⟨max (max Nc Nb) (max Ns Nl) + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | cond k _ _ _ _ _ _ h' => have := hNc _ k rfl h'; omega
    | body k _ _ _ _ _ _ st2 hc2 h' =>
      obtain rfl := ForCond.det hc hc2; have := hNb k h'; omega
    | step k _ _ _ _ _ _ st2 st2' status2 hc2 hb2 hst2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      have := hNs _ k rfl h'; omega
    | loop k _ _ _ _ _ _ st2 st2' st2'' status2 hc2 hb2 hst2 hs2 h' =>
      obtain rfl := ForCond.det hc hc2
      obtain ⟨rfl, rfl⟩ := ExecS.det hb hb2
      obtain rfl := ExecStep.det hs hs2
      have := hNl k h'; omega
termination_by structural _ _ _ _ _ _ h1 => h1

theorem ExecSeqErr.bound : ∀ {st d a ss}, ExecSeqErr st d a ss → SeqBound st d a ss
  | _, _, _, _, .head _ _ _ s ss hs => by
    obtain ⟨N, hN⟩ := ExecErr.bound hs
    refine ⟨N + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | step k _ _ _ _ _ st2 hs2 h' => exact (ExecS.not_err hs2 hs).elim
    | head k _ _ _ _ _ h' => have := hN k h'; omega
  | _, _, _, _, .tail _ _ _ s ss st' hs hss => by
    obtain ⟨Ns, hNs⟩ := ExecS.bound hs
    obtain ⟨Nss, hNss⟩ := ExecSeqErr.bound hss
    refine ⟨max Ns Nss + 1, fun n hn => ?_⟩
    cases hn with
    | zero => omega
    | step k _ _ _ _ _ st2 hs2 h' =>
      obtain ⟨rfl, -⟩ := ExecS.det hs hs2; have := hNss k h'; omega
    | head k _ _ _ _ _ h' => have := hNs k h'; omega
termination_by structural _ _ _ _ h1 => h1

end

theorem bigStep_not_err {p : Program} {out : String} (h : BigStep p out) :
    ¬ BigStepErr p := by
  obtain ⟨st', hs, -⟩ := h
  rintro (herr | ⟨st'', status, hne, hs'⟩)
  · exact ExecSeq.not_err hs herr
  · exact hne (ExecSeq.det hs hs').2.symm

theorem bigStep_not_diverges {p : Program} {out : String} (h : BigStep p out) :
    ¬ BigStepDiverges p := by
  obtain ⟨st', hs, -⟩ := h
  intro hdiv
  obtain ⟨N, hN⟩ := ExecSeq.bound hs
  have := hN (N + 1) (hdiv (N + 1))
  omega

theorem err_not_diverges {p : Program} (h : BigStepErr p) : ¬ BigStepDiverges p := by
  intro hdiv
  obtain ⟨N, hN⟩ : SeqBound initSt 0 0 p := by
    rcases h with herr | ⟨st', status, -, hs⟩
    · exact ExecSeqErr.bound herr
    · exact ExecSeq.bound hs
  have := hN (N + 1) (hdiv (N + 1))
  omega

structure ExactlyOne (p : Program) : Prop where
  some : (∃ out, BigStep p out) ∨ BigStepErr p ∨ BigStepDiverges p
  term_not_err : (∃ out, BigStep p out) → ¬ BigStepErr p
  term_not_div : (∃ out, BigStep p out) → ¬ BigStepDiverges p
  err_not_div : BigStepErr p → ¬ BigStepDiverges p

theorem err_or_div_of_not_bigStep {p : Program} (htri : Trichotomy)
    (h : ¬ ∃ out, BigStep p out) : BigStepErr p ∨ BigStepDiverges p :=
  stuck_of_trichotomy htri p h

end Vsa.While
