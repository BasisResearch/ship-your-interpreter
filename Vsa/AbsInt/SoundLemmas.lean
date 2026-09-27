import Vsa.AbsInt.Chain
import Vsa.AbsInt.Interp

/-!
# Soundness support: completions, loops and condition filters

`SOK as r status s` says the statement result `r` covers a concrete
completion with `status` in store `s`. The loop lemmas `LoopOK.exit` and
`LoopOK.cont` are the two cases of every concrete loop derivation; they
account for both the unrolled iterations and the checked post-fixpoint of
`loopAbs`. `branch_sound` is the soundness of condition refinement.
-/

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

variable {A : Type} [AbsDom A]

/-- A statement result covers a concrete completion. -/
def SOK (as : List Addr) (r : SRes A) : Status → Store → Prop
  | .normal, s => SGam as s r.norm
  | .brk, s => SGam as s r.brk
  | .cont, s => SGam as s r.cont
  | .ret v, s => SGam as s r.ret ∧ Gam r.retv v

theorem SGam.isBot_false {as : List Addr} {s : Store} {σ : AState A}
    (h : SGam as s σ) : σ.isBot = false := by
  cases σ with
  | bot => exact h.elim
  | top => rfl
  | sc _ => rfl

theorem SOK.join_l {as : List Addr} {r : SRes A} {st : Status} {s : Store}
    (r' : SRes A) (h : SOK as r st s) : SOK as (r.join r') st s := by
  cases st with
  | normal => exact SGam.join_l _ h
  | brk => exact SGam.join_l _ h
  | cont => exact SGam.join_l _ h
  | ret v =>
    refine ⟨SGam.join_l _ h.1, ?_⟩
    simp only [SRes.join, joinRet, SGam.isBot_false h.1, Bool.false_eq_true, ↓reduceIte]
    split
    · exact h.2
    · exact AbsDom.join_l h.2

theorem SOK.join_r {as : List Addr} {r' : SRes A} {st : Status} {s : Store}
    (r : SRes A) (h : SOK as r' st s) : SOK as (r.join r') st s := by
  cases st with
  | normal => exact SGam.join_r _ h
  | brk => exact SGam.join_r _ h
  | cont => exact SGam.join_r _ h
  | ret v =>
    refine ⟨SGam.join_r _ h.1, ?_⟩
    simp only [SRes.join, joinRet, SGam.isBot_false h.1, Bool.false_eq_true, ↓reduceIte]
    split
    · exact h.2
    · exact AbsDom.join_r h.2

theorem SOK.seq_r {as : List Addr} {r' : SRes A} {st : Status} {s : Store}
    (r : SRes A) (h : SOK as r' st s) : SOK as (r.seq r') st s := by
  cases st with
  | normal => exact h
  | brk => exact SGam.join_r _ h
  | cont => exact SGam.join_r _ h
  | ret v => exact SOK.join_r (r' := r') r (st := .ret v) h

theorem SOK.seq_l {as : List Addr} {r : SRes A} {st : Status} {s : Store}
    (r' : SRes A) (hne : st ≠ .normal) (h : SOK as r st s) : SOK as (r.seq r') st s := by
  cases st with
  | normal => exact absurd rfl hne
  | brk => exact SGam.join_l _ h
  | cont => exact SGam.join_l _ h
  | ret v => exact SOK.join_l (r := r) r' (st := .ret v) h

theorem SOK.pop {as : List Addr} {inner : Addr} {r : SRes A} {st : Status}
    {s : Store} (h : SOK (inner :: as) r st s) : SOK as r.pop st s := by
  cases st with
  | normal => exact SGam.pop h
  | brk => exact SGam.pop h
  | cont => exact SGam.pop h
  | ret v => exact ⟨SGam.pop h.1, h.2⟩

theorem SOK.withAl {as : List Addr} {r : SRes A} {st : Status} {s : Store}
    (al : List Kind) (h : SOK as r st s) : SOK as { r with al := al } st s := by
  cases st <;> exact h

theorem SOK.any {as : List Addr} {r : SRes A} {st : Status} {s : Store}
    (h : SOK as r st s) : SGam as s r.any := by
  unfold SRes.any
  cases st with
  | normal => exact SGam.join_l _ (SGam.join_l _ (SGam.join_l _ h))
  | brk => exact SGam.join_l _ (SGam.join_l _ (SGam.join_r _ h))
  | cont => exact SGam.join_l _ (SGam.join_r _ h)
  | ret v => exact SGam.join_r _ h.1

/-! ## Loops -/

theorem narrowIter_isPost {F : AState A → AState A} {I : AState A} :
    ∀ {n : Nat} {J : AState A}, isPost F I J = true → isPost F I (narrowIter F I n J) = true
  | 0, _, h => h
  | n + 1, J, h => by
    simp only [narrowIter]
    split
    · rename_i h'
      exact narrowIter_isPost h'
    · exact h

theorem postFix_cases (F : AState A → AState A) (n m : Nat) (I : AState A) :
    postFix F n m I = .top ∨ isPost F I (postFix F n m I) = true := by
  unfold postFix
  split
  · rename_i h
    exact Or.inr (narrowIter_isPost h)
  · exact Or.inl rfl

theorem postFix_ge {F : AState A → AState A} {n m : Nat} {I : AState A}
    {as : List Addr} {s : Store} (h : SGam as s I) : SGam as s (postFix F n m I) := by
  rcases postFix_cases F n m I with he | hp
  · rw [he]; trivial
  · simp only [isPost, Bool.and_eq_true] at hp
    exact SGam.le hp.1 h

theorem postFix_post {F : AState A → AState A} {n m : Nat} {I : AState A}
    {as : List Addr} {s : Store} (h : SGam as s (F (postFix F n m I))) :
    SGam as s (postFix F n m I) := by
  rcases postFix_cases F n m I with he | hp
  · rw [he]; trivial
  · simp only [isPost, Bool.and_eq_true] at hp
    exact SGam.le hp.2 h

/-- A loop run from `s₀` completing with `st` in `s₁` is covered by every
post-fixpoint and by every unrolling. -/
structure LoopOK (cfg : Cfg) (F : AState A → LStep A) (as : List Addr)
    (s₀ : Store) (st : Status) (s₁ : Store) : Prop where
  fix : ∀ J, (∀ s, SGam as s (F J).next → SGam as s J) → SGam as s₀ J →
    SOK as (F J).out st s₁
  unroll : ∀ k I, SGam as s₀ I → SOK as (loopAbs cfg F k I) st s₁

/-- The run leaves the loop in its first iteration. -/
theorem LoopOK.exit {cfg : Cfg} {F : AState A → LStep A} {as : List Addr}
    {s₀ s₁ : Store} {st : Status}
    (hex : ∀ I, SGam as s₀ I → SOK as (F I).out st s₁) : LoopOK cfg F as s₀ st s₁ where
  fix J _ h := hex J h
  unroll k I h := by
    cases k with
    | zero => exact hex _ (postFix_ge h)
    | succ k =>
      simp only [loopAbs]
      split
      · exact hex I h
      · exact SOK.join_l _ (hex I h)

/-- The run completes an iteration in `s₀'` and continues from there. -/
theorem LoopOK.cont {cfg : Cfg} {F : AState A → LStep A} {as : List Addr}
    {s₀ s₀' s₁ : Store} {st : Status}
    (hc : ∀ I, SGam as s₀ I → SGam as s₀' (F I).next)
    (ih : LoopOK cfg F as s₀' st s₁) : LoopOK cfg F as s₀ st s₁ where
  fix J hJ h := ih.fix J hJ (hJ _ (hc J h))
  unroll k I h := by
    cases k with
    | zero =>
      exact ih.fix _ (fun _ hs => postFix_post hs) (postFix_post (hc _ (postFix_ge h)))
    | succ k =>
      simp only [loopAbs]
      split
      · rename_i hcond
        simp only [Bool.or_eq_true] at hcond
        have hn := hc I h
        rcases hcond with hb | hle
        · rw [SGam.isBot_false hn] at hb; cases hb
        · exact ih.fix I (fun _ hs => SGam.le hle hs) (SGam.le hle hn)
      · exact SOK.join_r _ (ih.unroll k _ (hc I h))

/-! ## Pure conditions -/

/-- Pure expressions leave the state unchanged. -/
theorem isPure_eval {st st' : St} {d : Nat} {env : Addr} {e : Expr} {v : Value}
    (h : EvalE st d env e st' v) : isPure e = true → st' = st := by
  refine EvalE.rec
    (motive_1 := fun st _ _ e st' _ _ => isPure e = true → st' = st)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  all_goals first
    | trivial
    | simp_all [isPure]

theorem pureVal_isPure {σ : AState A} {r : Expr} {b : A} (h : pureVal σ r = some b) :
    isPure r = true := by
  cases r <;> simp_all [pureVal, isPure]

theorem pureVal_sound {as : List Addr} {env : Addr} {σ : AState A} {r : Expr}
    {b : A} {st st' : St} {d : Nat} {v : Value} (hd : as.head? = some env)
    (hp : pureVal σ r = some b) (hev : EvalE st d env r st' v)
    (hσ : SGam as st.store σ) : Gam b v := by
  cases hev <;> simp only [pureVal, Option.some.injEq, reduceCtorEq] at hp
  all_goals subst hp
  · exact ofValue_sound _
  · exact ofValue_sound _
  · exact ofValue_sound _
  · exact ofValue_sound _
  · rename_i hget
    exact (SGam.lookup hd hσ).1 _ hget

/-- Soundness of condition refinement. -/
theorem filterE_sound {as : List Addr} {env : Addr} :
    ∀ (c : Expr) (t : Bool) (σ : AState A) {st st' : St} {d : Nat} {v : Value},
      as.head? = some env → EvalE st d env c st' v → v.truthy = t →
      SGam as st'.store σ → SGam as st'.store (filterE t σ c)
  | .binary op (.var x) r, t, σ, st, st', d, v, hd, hev, ht, hσ => by
    simp only [filterE]
    cases hp : pureVal σ r with
    | none => exact hσ
    | some b =>
      simp only
      cases hev with
      | binary _ _ _ _ _ _ st1 _ lv rv _ hl hr hop =>
        cases hl with
        | var _ _ _ _ _ hget =>
          have hst := isPure_eval hr (pureVal_isPure hp)
          subst hst
          have hlv := (SGam.lookup hd hσ).1 _ hget
          have hrv := pureVal_sound hd hp hr hσ
          have href := refine_sound hlv hrv hop ht
          split
          · rename_i hbot
            exact (isBot_sound hbot href).elim
          · exact SGam.strengthen hd hσ hget href
  | .unary .not e, t, σ, st, st', d, v, hd, hev, ht, hσ => by
    simp only [filterE]
    cases hev with
    | not _ _ _ _ _ v' he =>
      have ht' : (!v'.truthy) = t := ht
      apply filterE_sound e (!t) σ hd he _ hσ
      rw [← ht', Bool.not_not]
  | .logical .and l r, t, σ, st, st', d, v, hd, hev, ht, hσ => by
    simp only [filterE]
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨rfl, hpl⟩, hpr⟩ := hc
      cases hev with
      | andFalse _ _ _ _ _ _ _ _ _ => simp [Value.truthy] at ht
      | andTrue _ _ _ _ _ st1 _ lv rv hl hlt hr =>
        have h1 := isPure_eval hl hpl
        have h2 := isPure_eval hr hpr
        subst h1 h2
        exact filterE_sound r true _ hd hr ht (filterE_sound l true σ hd hl hlt hσ)
    · exact hσ
  | .logical .or l r, t, σ, st, st', d, v, hd, hev, ht, hσ => by
    simp only [filterE]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      obtain ⟨⟨rfl, hpl⟩, hpr⟩ := hc
      cases hev with
      | orTrue _ _ _ _ _ _ _ _ _ => simp [Value.truthy] at ht
      | orFalse _ _ _ _ _ st1 _ lv rv hl hlt hr =>
        have h1 := isPure_eval hl hpl
        have h2 := isPure_eval hr hpr
        subst h1 h2
        exact filterE_sound r false _ hd hr ht (filterE_sound l false σ hd hl hlt hσ)
    · exact hσ
  | .int _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .str _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .bool _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .null, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .var _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .assign _ _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .call _ _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .fn _ _ _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .unary .neg _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.int _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.str _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.bool _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ .null _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.assign _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.binary _ _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.logical _ _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.unary _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.call _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ
  | .binary _ (.fn _ _ _) _, _, _, _, _, _, _, _, _, _, hσ => hσ

/-- Soundness of the branch states after a condition. -/
theorem branch_sound {as : List Addr} {env : Addr} {c : Expr} {t : Bool}
    {rc : ERes A} {st st' : St} {d : Nat} {v : Value} (hd : as.head? = some env)
    (hev : EvalE st d env c st' v) (ht : v.truthy = t)
    (hst : SGam as st'.store rc.st) (hv : Gam rc.val v) :
    SGam as st'.store (branch t c rc) := by
  unfold branch
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [if_pos (mayF_sound hv ht)]
    exact filterE_sound c false rc.st hd hev ht hst
  · rw [if_pos (mayT_sound hv ht)]
    exact filterE_sound c true rc.st hd hev ht hst

end Vsa.AbsInt
