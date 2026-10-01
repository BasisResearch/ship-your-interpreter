import Vsa.AbsInt.CostAnalysis
import Vsa.AbsInt.NoDup
import Vsa.AbsInt.Program
import Vsa.While.CostExists

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

set_option linter.unusedSectionVars false

theorem cle_add {a b : Nat} {x y : CB} (ha : CLe a x) (hb : CLe b y) :
    CLe (a + b) (cadd x y) := by
  cases x <;> cases y <;> simp only [CLe, cadd] at * <;> omega

theorem cle_add_l {a : Nat} {x : CB} (y : CB) (ha : CLe a x) : CLe a (cadd x y) := by
  cases x <;> cases y <;> simp only [CLe, cadd] at * <;> omega

theorem cle_max_l {a : Nat} {x : CB} (y : CB) (ha : CLe a x) : CLe a (cmax x y) := by
  cases x <;> cases y <;> simp only [CLe, cmax] at * <;> omega

theorem cle_max_r {a : Nat} {y : CB} (x : CB) (ha : CLe a y) : CLe a (cmax x y) := by
  cases x <;> cases y <;> simp only [CLe, cmax] at * <;> omega

theorem cle_zero (x : CB) (h : x = some 0) : CLe 0 x := by
  subst h; exact Nat.le_refl 0

theorem le_foldl_max (f : Nat → Nat) :
    ∀ (l : List Nat) (init : Nat), init ≤ l.foldl (fun m c => max m (f c)) init
  | [], _ => Nat.le_refl _
  | c :: l, init => Nat.le_trans (Nat.le_max_left init (f c)) (le_foldl_max f l _)

theorem mem_le_foldl_max (f : Nat → Nat) {c : Nat} :
    ∀ (l : List Nat) (init : Nat), c ∈ l → f c ≤ l.foldl (fun m c => max m (f c)) init
  | [], _, h => by cases h
  | d :: l, init, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right init (f c)) (le_foldl_max f l _)
    · exact mem_le_foldl_max f l _ h

theorem growthOf_le_growthMax {c k : Nat} (h : c ≤ k) : growthOf c ≤ growthMax k :=
  mem_le_foldl_max growthOf _ 0 (List.mem_range.mpr (by omega))

variable {A : Type} [AbsDom A] [ToItv A] [ToItvLaw A]

theorem any_of_vfind_isSome {vars : List (String × Value)} {x : String}
    (h : (vfind vars x).isSome = true) : vars.any (·.1 == x) = true := by
  cases hany : vars.any (·.1 == x)
  · rw [vfind_none_of_not_any hany] at h; cases h
  · rfl

theorem defineBound_sound {as : List Addr} {env : Addr} {s : Store} {σ : AState A}
    {x : String} (hd : as.head? = some env) (h : SGam as s σ) (hnd : FramesNoDup s) :
    CLe (defineCost s env x) (defineBound σ x) := by
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l =>
    cases l with
    | nil => trivial
    | cons S l =>
      cases as with
      | nil => exact h.elim
      | cons a as =>
        simp only [List.head?, Option.some.injEq] at hd
        subst hd
        obtain ⟨hf, -, -⟩ := h
        unfold FrameAt at hf
        cases hfr : s.frames[a]? with
        | none => rw [hfr] at hf; exact hf.elim
        | some f =>
          rw [hfr] at hf
          have hS := hf.2
          have hc := vars_length_le hS (hnd a f hfr)
          have hg := growthOf_le_growthMax hc
          unfold growthOf at hg
          have hgen : CLe (defineCost s a x)
              (some (nameCopyCost x + growthMax (dedup (keys S)).length)) := by
            simp only [defineCost, hfr, CLe]
            split
            · exact Nat.zero_le _
            · omega
          cases hgx : S.get x with
          | none => simp only [defineBound, hgx]; exact hgen
          | some bd =>
            obtain ⟨bv, bm⟩ := bd
            cases bm with
            | false => simp only [defineBound, hgx]; exact hgen
            | true =>
              have hx := hS x
              rw [hgx] at hx
              have hany := any_of_vfind_isSome (hx.1 rfl)
              simp only [defineBound, hgx, defineCost, hfr, hany, ↓reduceIte, CLe]
              exact Nat.le_refl 0

theorem noStr_sound {a : A} {v : Value} (hn : noStr a = true) (h : Gam a v) (t : String) :
    v ≠ .str t := by
  rintro rfl
  have hi := ToItvLaw.sound h
  unfold noStr at hn
  cases hia : ToItv.toItv a with
  | top => rw [hia] at hn; cases hn
  | bot => rw [hia] at hi; exact hi
  | range lo hi' => rw [hia] at hi; exact hi

theorem binCost_sound {s : Store} {op : BinOp} {l r : Value} {a b : A}
    (hl : Gam a l) (hr : Gam b r) : CLe (binOpCost s op l r) (binCost op a b) := by
  cases op
  case add =>
    unfold binCost
    by_cases hn : (noStr a && noStr b) = true
    · simp only [hn, ↓reduceIte]
      simp only [Bool.and_eq_true] at hn
      have h1 := noStr_sound hn.1 hl
      have h2 := noStr_sound hn.2 hr
      show binOpCost s .add l r ≤ 0
      cases l <;> cases r <;> first
        | exact absurd rfl (h1 _)
        | exact absurd rfl (h2 _)
        | simp [binOpCost]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]; trivial
  all_goals exact Nat.zero_le _

@[reducible] def liftDom (b : Int) : AbsDom (A × OffV) :=
  @prodDom A OffV _ (offDom b) (@Reduce.none A OffV _ (offDom b))

theorem liftScope_get (S : Scope A) (y : String) :
    (liftScope S).get y =
      (S.get y).map fun b => ⟨(b.val, (ToItv.toItv b.val, none)), b.must⟩ := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    obtain ⟨k, b⟩ := p
    simp only [liftScope, List.map_cons, Scope.get] at ih ⊢
    split
    · rfl
    · exact ih

theorem ScopeOK.lift {b : Int} {S : Scope A} {vars : List (String × Value)}
    (h : ScopeOK S vars) : @ScopeOK (A × OffV) (liftDom b) (liftScope S) vars := by
  intro y
  have hy := h y
  rw [liftScope_get]
  cases hg : S.get y with
  | none => rw [hg] at hy; exact hy
  | some bd =>
    rw [hg] at hy
    exact ⟨hy.1, fun v hv => ⟨hy.2 v hv, ToItvLaw.sound (hy.2 v hv), trivial⟩⟩

theorem Chain.lift {b : Int} {s : Store} :
    ∀ {as : List Addr} {l : List (Scope A)},
      Chain s as l → @Chain (A × OffV) (liftDom b) s as (l.map liftScope)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hf, hlt, hc⟩ =>
    ⟨FrameAt.mono (fun _ hp => ⟨hp.1, hp.2.lift⟩) hf, hlt, Chain.lift hc⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem SGam.lift_at {as : List Addr} {env : Addr} {s : Store} {J : AState A}
    {x : String} {n : Int} (hd : as.head? = some env) (h : SGam as s J)
    (hx : s.get? env x = some (.int n)) :
    @SGam (A × OffV) (liftDom n) as s (liftAt J x) := by
  have hv := (SGam.lookup hd h).1 _ hx
  unfold liftAt
  refine @SGam.strengthen (A × OffV) (liftDom n) _ _ _ _ _ _ _ hd ?_ hx
    ⟨hv, ToItvLaw.sound hv, by simp [Off.OK]⟩
  cases J with
  | bot => exact h.elim
  | top => trivial
  | sc l => exact Chain.lift h

theorem offset_rise {as : List Addr} {env : Addr} {s : Store} {x : String} {n : Int}
    {σ : AState (A × OffV)} (hd : as.head? = some env)
    (h : @SGam (A × OffV) (liftDom n) as s σ) {o : Int} (ho : offOf σ x = some o) :
    ∀ v, s.get? env x = some v → ∃ n', v = .int n' ∧ n + o ≤ n' := by
  intro v hv
  have hg := (@SGam.lookup (A × OffV) (liftDom n) _ _ _ _ _ hd h).1 v hv
  have hok : Off.OK n (σ.lookup x).1.2.2 v := hg.2.2
  unfold offOf at ho
  rw [ho] at hok
  cases v with
  | int n' => exact ⟨n', rfl, by simp only [Off.OK] at hok; omega⟩
  | _ => exact hok.elim

inductive LoopRun (P : Store → Store → Nat → Prop) (Q : Store → Nat → Prop) :
    Store → Nat → Prop
  | fin {s : Store} {n : Nat} : Q s n → LoopRun P Q s n
  | step {s s' : Store} {n m : Nat} : P s s' n → LoopRun P Q s' m → LoopRun P Q s (n + m)

def CountStep (cnt : Option (String × Expr × Nat))
    (nextL : AState (A × OffV) → AState (A × OffV)) (env : Addr) (I : AState A)
    (s s' : Store) : Prop :=
  ∀ x e k h, cnt = some (x, e, k) → hiOf I e = some h →
    ∃ n, s.get? env x = some (.int n) ∧ n < h + k ∧ (∀ l, loOf I x = some l → l ≤ n) ∧
      ∀ o, offOf (nextL (liftAt I x)) x = some o →
        ∀ v, s'.get? env x = some v → ∃ n', v = .int n' ∧ n + o ≤ n'

def IterStep (F : AState A → LStep A) (itc : AState A → CB)
    (cnt : Option (String × Expr × Nat)) (nextL : AState (A × OffV) → AState (A × OffV))
    (as : List Addr) (env : Addr) (s s' : Store) (n : Nat) : Prop :=
  ∀ I, SGam as s I → CLe n (itc I) ∧ SGam as s' (F I).next ∧ CountStep cnt nextL env I s s'

def IterFin (itc : AState A → CB) (as : List Addr) (s : Store) (n : Nat) : Prop :=
  ∀ I, SGam as s I → CLe n (itc I)

abbrev LRun (F : AState A → LStep A) (itc : AState A → CB)
    (cnt : Option (String × Expr × Nat)) (nextL : AState (A × OffV) → AState (A × OffV))
    (as : List Addr) (env : Addr) : Store → Nat → Prop :=
  LoopRun (IterStep F itc cnt nextL as env) (IterFin itc as)

theorem iterBound_spec {nextL : AState (A × OffV) → AState (A × OffV)} {c : Expr}
    {J : AState A} {K : Nat} (h : iterBound nextL c J = some K) :
    ∃ x e k l hh o, counted c = some (x, e, k) ∧ loOf J x = some l ∧ hiOf J e = some hh ∧
      offOf (nextL (liftAt J x)) x = some o ∧ 1 ≤ o ∧ K = (hh + k - l).toNat := by
  unfold iterBound at h
  split at h
  · rename_i x e k hc
    split at h
    · rename_i l hh o h1 h2 h3
      split at h
      · rename_i ho
        cases h
        exact ⟨x, e, k, l, hh, o, hc, h1, h2, h3, ho, rfl⟩
      · cases h
    · cases h
  · cases h

section Rank

variable {F : AState A → LStep A} {itc : AState A → CB}
  {cnt : Option (String × Expr × Nat)} {nextL : AState (A × OffV) → AState (A × OffV)}
  {as : List Addr} {env : Addr}

theorem LRun.rank {J : AState A} (hJ : ∀ s, SGam as s (F J).next → SGam as s J)
    {bnd : Option Nat}
    (hb : ∀ K, bnd = some K → ∃ x e k l hh o, cnt = some (x, e, k) ∧ loOf J x = some l ∧
      hiOf J e = some hh ∧ offOf (nextL (liftAt J x)) x = some o ∧ 1 ≤ o ∧
      K = (hh + k - l).toNat)
    {s₀ : Store} {N : Nat} (hr : LRun F itc cnt nextL as env s₀ N) (h0 : SGam as s₀ J) :
    CLe N (rankCost (itc J) bnd) := by
  unfold rankCost
  cases hc : itc J with
  | none => trivial
  | some C =>

    have hz : C = 0 → N = 0 := by
      intro hC
      subst hC
      induction hr with
      | fin hq =>
        have := hq J (by assumption)
        rw [hc] at this
        simp only [CLe] at this
        omega
      | step hp _ ih =>
        obtain ⟨h1, h2, -⟩ := hp J (by assumption)
        rw [hc] at h1
        simp only [CLe] at h1
        have := ih (hJ _ h2)
        omega
    rcases C with _ | C
    · show N ≤ 0
      rw [hz rfl]
      exact Nat.le_refl 0
    · cases hbd : bnd with
      | none => trivial
      | some K =>
        obtain ⟨x, e, k, l, hh, o, hcnt, hl, hhi, ho, ho1, rfl⟩ := hb K hbd
        show N ≤ (hh + k - l).toNat * (C + 1) + (C + 1)
        have claim : ∀ s N, LRun F itc cnt nextL as env s N → SGam as s J →
            N ≤ C + 1 ∨ ∃ n, s.get? env x = some (.int n) ∧ l ≤ n ∧
              N ≤ (hh + k - n).toNat * (C + 1) + (C + 1) := by
          intro s N hr hs
          induction hr with
          | fin hq =>
            have := hq J hs
            rw [hc] at this
            exact .inl this
          | @step s s' n m hp _ ih =>
            obtain ⟨h1, h2, h3⟩ := hp J hs
            rw [hc] at h1
            simp only [CLe] at h1
            obtain ⟨n0, hg0, hlt, hl0, hoff⟩ := h3 x e k hh hcnt hhi
            have hln := hl0 l hl
            have hT : 1 ≤ (hh + k - n0).toNat := by omega
            have hCT := Nat.mul_le_mul_right (C + 1) hT
            refine .inr ⟨n0, hg0, hln, ?_⟩
            rcases ih (hJ _ h2) with hm | ⟨n1, hg1, -, hm⟩
            · omega
            · obtain ⟨n', hv, hn'⟩ := hoff o ho _ hg1
              have hn1 : n1 = n' := by injection hv
              subst hn1
              have hT1 : (hh + k - n1).toNat + 1 ≤ (hh + k - n0).toNat := by omega
              have := Nat.mul_le_mul_right (C + 1) hT1
              rw [Nat.succ_mul] at this
              omega
        rcases claim s₀ N hr h0 with hN | ⟨n, -, hln, hN⟩
        · have := Nat.zero_le ((hh + k - l).toNat * (C + 1))
          omega
        · have hT : (hh + k - n).toNat ≤ (hh + k - l).toNat := by omega
          have := Nat.mul_le_mul_right (C + 1) hT
          omega

theorem LRun.unroll {cfg : Cfg} {rank : AState A → CB}
    (hrank : ∀ J s N, (∀ s, SGam as s (F J).next → SGam as s J) →
      LRun F itc cnt nextL as env s N → SGam as s J → CLe N (rank J)) :
    ∀ k I s N, LRun F itc cnt nextL as env s N → SGam as s I →
      CLe N (loopCost cfg F itc rank k I)
  | 0, I, s, N, hr, hs => hrank _ s N (fun _ h => postFix_post h) hr (postFix_ge hs)
  | k + 1, I, s, N, hr, hs => by
    simp only [loopCost]
    split
    · rename_i hbot
      cases hr with
      | fin hq => exact hq I hs
      | step hp _ =>
        have := SGam.isBot_false (hp I hs).2.1
        rw [hbot] at this
        cases this
    · split
      · rename_i _ hle
        exact hrank I s N (fun _ h => SGam.le hle h) hr hs
      · cases hr with
        | fin hq => exact cle_add_l _ (hq I hs)
        | step hp hrest =>
          obtain ⟨h1, h2, -⟩ := hp I hs
          exact cle_add h1 (LRun.unroll hrank k _ _ _ hrest h2)

end Rank

section Next

variable {B : Type} [AbsDom B]

theorem whileNext_sound (cfg : Cfg) {c : Expr} {b : Stmt} {st st' st'' : St} {d : Nat}
    {env : Addr} {v : Value} {status : Status} {as : List Addr}
    (hd : as.head? = some env) (hc : EvalE st d env c st' v) (ht : v.truthy = true)
    (hb : ExecS st' d env b st'' status) (hst : status = .normal ∨ status = .cont)
    {I : AState B} (hI : SGam as st.store I) : SGam as st''.store (whileF cfg c b I).next := by
  obtain ⟨h1, h2⟩ := eval_sound cfg hc as I hd hI
  have hb' := (exec_sound cfg hb as hd).1 _ (branch_sound hd hc ht h1 h2)
  rcases hst with rfl | rfl
  · exact SGam.join_l _ hb'
  · exact SGam.join_r _ hb'

theorem forMid_sound (cfg : Cfg) {cnd : Option Expr} {b : Stmt} {st st' st'' : St}
    {d : Nat} {env : Addr} {status : Status} {as : List Addr}
    (hd : as.head? = some env) (hc : ForCond st d env cnd st')
    (hb : ExecS st' d env b st'' status) (hst : status = .normal ∨ status = .cont)
    {I : AState B} (hI : SGam as st.store I) :
    SGam as st''.store
      ((aexec cfg (match cnd with
        | none => I
        | some c => branch true c (optEval cnd I)) b).norm.join
       (aexec cfg (match cnd with
        | none => I
        | some c => branch true c (optEval cnd I)) b).cont) := by
  have hb' := (exec_sound cfg hb as hd).1 _ (cond_sound cfg hc as I hd hI)
  rcases hst with rfl | rfl
  · exact SGam.join_l _ hb'
  · exact SGam.join_r _ hb'

theorem forNext_sound (cfg : Cfg) {cnd step : Option Expr} {b : Stmt}
    {st st' st'' st''' : St} {d : Nat} {env : Addr} {status : Status} {as : List Addr}
    (hd : as.head? = some env) (hc : ForCond st d env cnd st')
    (hb : ExecS st' d env b st'' status) (hst : status = .normal ∨ status = .cont)
    (hs : ExecStep st'' d env step st''')
    {I : AState B} (hI : SGam as st.store I) :
    SGam as st'''.store (forF cfg cnd step b I).next := by
  have := step_sound cfg hs as _ hd (forMid_sound cfg hd hc hb hst hI)
  cases step with
  | none => exact this
  | some e => exact this

end Next

theorem counted_true {c : Expr} {x : String} {e : Expr} {k : Nat}
    (hcnt : counted c = some (x, e, k)) {st st' : St} {d : Nat} {env : Addr} {v : Value}
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) {as : List Addr} {I : AState A}
    (hd : as.head? = some env) (hI : SGam as st.store I) {hh : Int}
    (hhi : hiOf I e = some hh) :
    st' = st ∧ ∃ n, st.store.get? env x = some (.int n) ∧ n < hh + k ∧
      ∀ l, loOf I x = some l → l ≤ n := by
  unfold hiOf at hhi
  split at hhi
  · rename_i a hpv
    split at hhi
    · rename_i lo hi' hia
      cases hhi
      unfold counted at hcnt
      split at hcnt <;> cases hcnt
      all_goals
        cases hc with
        | binary _ _ _ _ _ _ st1 _ lv rv _ hl hr hop =>
          cases hl with
          | var _ _ _ _ _ hget =>
            have hst := isPure_eval hr (pureVal_isPure hpv)
            subst hst
            refine ⟨rfl, ?_⟩
            have hrv := ToItvLaw.sound (pureVal_sound hd hpv hr hI)
            rw [hia] at hrv
            have hlv := (SGam.lookup hd hI).1 _ hget
            cases rv with
            | int m =>
              obtain ⟨-, hm⟩ := hrv
              simp only [Itv.InHi] at hm
              cases lv with
              | int n =>
                simp only [binOpSem, Option.some.injEq] at hop
                subst hop
                simp only [Value.truthy, decide_eq_true_eq] at ht
                refine ⟨n, hget, by omega, fun l hl => ?_⟩
                unfold loOf at hl
                have hi := ToItvLaw.sound hlv
                split at hl
                · rename_i hi'' hlo
                  cases hl
                  rw [hlo] at hi
                  exact hi.1
                · cases hl
              | _ => simp [binOpSem] at hop
            | _ => exact hrv.elim
    · cases hhi
  · cases hhi

section Eqns

variable (cfg : Cfg) (σ : AState A)

theorem scostOpt_none : scostOpt cfg σ none = some 0 := by rw [scostOpt]

theorem scostOpt_some (s : Stmt) : scostOpt cfg σ (some s) = scost cfg σ s := by
  rw [scostOpt]

theorem seqcost_nil : seqcost cfg σ [] = some 0 := by rw [seqcost]

theorem seqcost_cons (s : Stmt) (ss : List Stmt) :
    seqcost cfg σ (s :: ss) = cadd (scost cfg σ s) (seqcost cfg (aexec cfg σ s).norm ss) := by
  rw [seqcost]

theorem forItCost_eq (cnd step : Option Expr) (b : Stmt) :
    forItCost cfg cnd step b σ =
      cadd (cadd (optCost cnd σ)
          (scost cfg (match cnd with
            | none => σ
            | some c => branch true c (optEval cnd σ)) b))
        (optCost step
          ((aexec cfg (match cnd with
            | none => σ
            | some c => branch true c (optEval cnd σ)) b).norm.join
           (aexec cfg (match cnd with
            | none => σ
            | some c => branch true c (optEval cnd σ)) b).cont)) := rfl

end Eqns

section Motives

variable (A)

def itcW (cfg : Cfg) (c : Expr) (b : Stmt) (I : AState A) : CB :=
  cadd (ccost I c) (scost cfg (branch true c (aeval I c)) b)

abbrev WRun (cfg : Cfg) (c : Expr) (b : Stmt) (as : List Addr) (env : Addr) :
    Store → Nat → Prop :=
  LRun (whileF cfg c b) (itcW A cfg c b) (counted c)
    (fun I => (whileF cfg c b I).next) as env

abbrev FRun (cfg : Cfg) (cnd step : Option Expr) (b : Stmt) (as : List Addr)
    (env : Addr) : Store → Nat → Prop :=
  LRun (forF (A := A) cfg cnd step b) (forItCost (A := A) cfg cnd step b)
    (cnd.bind counted) (fun I => (forF cfg cnd step b I).next) as env

def WhileRunM (cfg : Cfg) (as : List Addr) (env : Addr) (s : Store) (n : Nat) :
    Stmt → Prop
  | .whileStmt c b => WRun A cfg c b as env s n
  | _ => True

def CEval (st : St) (env : Addr) (e : Expr) (n : Nat) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    FramesNoDup st.store → CLe n (ccost σ e)

def CArgs (st : St) (env : Addr) (es : List Expr) (n : Nat) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    FramesNoDup st.store → CLe n (cargs σ es)

def CExec (cfg : Cfg) (st : St) (env : Addr) (s : Stmt) (n : Nat) : Prop :=
  ∀ (as : List Addr), as.head? = some env → FramesNoDup st.store →
    (∀ σ : AState A, SGam as st.store σ → CLe n (scost cfg σ s)) ∧
      WhileRunM A cfg as env st.store n s

def CInit (cfg : Cfg) (st : St) (env : Addr) (init : Option Stmt) (n : Nat) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    FramesNoDup st.store → CLe n (scostOpt cfg σ init)

def CFor (cfg : Cfg) (st : St) (env : Addr) (cnd step : Option Expr) (b : Stmt)
    (n : Nat) : Prop :=
  ∀ (as : List Addr), as.head? = some env → FramesNoDup st.store →
    FRun A cfg cnd step b as env st.store n

def COpt (st : St) (env : Addr) (e : Option Expr) (n : Nat) : Prop :=
  ∀ (as : List Addr) (I : AState A), as.head? = some env → SGam as st.store I →
    FramesNoDup st.store → CLe n (optCost e I)

def CSeq (cfg : Cfg) (st : St) (env : Addr) (ss : List Stmt) (n : Nat) : Prop :=
  ∀ (as : List Addr) (σ : AState A), as.head? = some env → SGam as st.store σ →
    FramesNoDup st.store → CLe n (seqcost cfg σ ss)

end Motives

theorem whileRank {cfg : Cfg} {c : Expr} {b : Stmt} {as : List Addr} {env : Addr}
    (J : AState A) (s : Store) (N : Nat)
    (hJ : ∀ s, SGam as s (whileF cfg c b J).next → SGam as s J)
    (hr : WRun A cfg c b as env s N) (hs : SGam as s J) :
    CLe N (rankCost (cadd (ccost J c) (scost cfg (branch true c (aeval J c)) b))
      (iterBound (fun I => (whileF cfg c b I).next) c J)) :=
  LRun.rank (itc := itcW A cfg c b) hJ (fun _ h => iterBound_spec h) hr hs

theorem whileCost_of_run {cfg : Cfg} {c : Expr} {b : Stmt} {as : List Addr} {env : Addr}
    {s : Store} {N : Nat} (hr : WRun A cfg c b as env s N) {σ : AState A}
    (hσ : SGam as s σ) : CLe N (scost cfg σ (.whileStmt c b)) := by
  simp only [scost, SGam.isBot_false hσ, Bool.false_eq_true, ↓reduceIte]
  exact LRun.unroll (itc := itcW A cfg c b) (fun J s N hJ hr hs => whileRank J s N hJ hr hs)
    _ _ _ _ hr hσ

theorem forCost_of_run {cfg : Cfg} {cnd step : Option Expr} {b : Stmt} {as : List Addr}
    {env : Addr} {s : Store} {N : Nat} (hr : FRun A cfg cnd step b as env s N)
    {I : AState A} (hI : SGam as s I) :
    CLe N (loopCost cfg (forF cfg cnd step b)
        (fun I => forItCost cfg cnd step b I)
        (fun J => rankCost (forItCost cfg cnd step b J)
          (match cnd with
            | some c => iterBound (fun I => (forF cfg cnd step b I).next) c J
            | none => none))
        cfg.unroll I) := by
  refine LRun.unroll (fun J s N hJ hr hs => LRun.rank hJ ?_ hr hs) _ _ _ _ hr hI
  intro K hK
  cases cnd with
  | none => cases hK
  | some c =>
    obtain ⟨x, e, k, l, hh, o, h1, h2, h3, h4, h5, h6⟩ := iterBound_spec hK
    exact ⟨x, e, k, l, hh, o, by simp [h1], h2, h3, h4, h5, h6⟩

macro "unfold_ccost" h:term : tactic =>
  `(tactic| simp only [ccost, SGam.isBot_false $h, Bool.false_eq_true, ↓reduceIte])

macro "unfold_scost" h:term : tactic =>
  `(tactic| simp only [scost, SGam.isBot_false $h, Bool.false_eq_true, ↓reduceIte])

theorem whileCount {cfg : Cfg} {c : Expr} {b : Stmt} {st st' st'' : St} {d : Nat}
    {env : Addr} {v : Value} {status : Status} {as : List Addr}
    (hd : as.head? = some env) (hc : EvalE st d env c st' v) (ht : v.truthy = true)
    (hb : ExecS st' d env b st'' status) (hst : status = .normal ∨ status = .cont)
    {I : AState A} (hI : SGam as st.store I) :
    CountStep (counted c) (fun I => (whileF cfg c b I).next) env I st.store st''.store := by
  intro x e k hh hcnt hhi
  obtain ⟨-, n, hg, hlt, hlo⟩ := counted_true hcnt hc ht hd hI hhi
  refine ⟨n, hg, hlt, hlo, fun o ho => ?_⟩
  exact offset_rise hd
    (@whileNext_sound (A × OffV) (liftDom n) cfg c b st st' st'' d env v status as hd hc ht
      hb hst _ (SGam.lift_at hd hI hg)) ho

theorem forCount {cfg : Cfg} {cnd step : Option Expr} {b : Stmt}
    {st st' st'' st''' : St} {d : Nat} {env : Addr} {status : Status} {as : List Addr}
    (hd : as.head? = some env) (hc : ForCond st d env cnd st')
    (hb : ExecS st' d env b st'' status) (hst : status = .normal ∨ status = .cont)
    (hs : ExecStep st'' d env step st''')
    {I : AState A} (hI : SGam as st.store I) :
    CountStep (cnd.bind counted) (fun I => (forF cfg cnd step b I).next) env I
      st.store st'''.store := by
  intro x e k hh hcnt hhi
  cases cnd with
  | none => cases hcnt
  | some c =>
    cases hc with
    | some _ _ _ _ _ v hce hct =>
      obtain ⟨-, n, hg, hlt, hlo⟩ := counted_true hcnt hce hct hd hI hhi
      refine ⟨n, hg, hlt, hlo, fun o ho => ?_⟩
      exact offset_rise hd
        (@forNext_sound (A × OffV) (liftDom n) cfg (some c) step b st st' st'' st''' d env
          status as hd (.some _ _ _ _ _ v hce hct) hb hst hs _ (SGam.lift_at hd hI hg)) ho

set_option hygiene false in

local macro "cost_rec" r:ident h:term : tactic => `(tactic| (
  refine $r
    (motive_1 := fun st _ env e _ _ n _ => CEval A st env e n)
    (motive_2 := fun st _ env es _ _ n _ => CArgs A st env es n)
    (motive_3 := fun _ _ fv _ _ _ n _ => ∀ f, fv = .native f → n = 0)
    (motive_4 := fun st _ env s _ _ n _ => CExec A cfg st env s n)
    (motive_5 := fun st _ env init _ n _ => CInit A cfg st env init n)
    (motive_6 := fun st _ env cnd step b _ _ n _ => CFor A cfg st env cnd step b n)
    (motive_7 := fun st _ env cnd _ n _ => COpt A st env cnd n)
    (motive_8 := fun st _ env step _ n _ => COpt A st env step n)
    (motive_9 := fun st _ env ss _ _ n _ => CSeq A cfg st env ss n)
    ?int ?str ?bool ?null ?var ?assign ?binary ?orTrue ?orFalse ?andFalse ?andTrue
    ?neg ?not ?call ?fn ?argsNil ?argsCons ?cClosure ?cPrint ?cPrintln ?cAssert
    ?sExpr ?sVarInit ?sVarNull ?sBlock ?sIfTrue ?sIfFalse ?sIfNone ?sWhileFalse
    ?sWhileBreak ?sWhileRet ?sWhileLoop ?sFor ?sRet ?sRetNull ?sBrk ?sCont
    ?initNone ?initSome ?flCondFalse ?flBreak ?flRet ?flLoop ?condNone ?condSome
    ?stepNone ?stepSome ?seqNil ?seqNormal ?seqAbrupt $h
  case int =>
    intro st d env n as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl 0
  case str =>
    intro st d env x as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl 0
  case bool =>
    intro st d env x as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl 0
  case null =>
    intro st d env as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl 0
  case var =>
    intro st d env x v _ as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl 0
  case assign =>
    intro st d env x e st' v store'' n _ _ ih as σ hd hσ hnd
    unfold_ccost hσ
    exact ih as σ hd hσ hnd
  case binary =>
    intro st d env op l r st' st'' lv rv v nl nr hl hr _ ihl ihr as σ hd hσ hnd
    unfold_ccost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hl.sound as σ hd hσ
    obtain ⟨-, h4⟩ := eval_sound cfg hr.sound as _ hd h1
    exact cle_add (cle_add (ihl as σ hd hσ hnd)
      (ihr as _ hd h1 (nodup_eval hl.sound hnd))) (binCost_sound h2 h4)
  case orTrue =>
    intro st d env l r st' lv n hl hlt ihl as σ hd hσ hnd
    unfold_ccost hσ
    exact cle_add_l _ (ihl as σ hd hσ hnd)
  case orFalse =>
    intro st d env l r st' st'' lv rv nl nr hl hlf _ ihl ihr as σ hd hσ hnd
    unfold_ccost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hl.sound as σ hd hσ
    exact cle_add (ihl as σ hd hσ hnd)
      (ihr as _ hd (branch_sound hd hl.sound hlf h1 h2) (nodup_eval hl.sound hnd))
  case andFalse =>
    intro st d env l r st' lv n hl hlf ihl as σ hd hσ hnd
    unfold_ccost hσ
    exact cle_add_l _ (ihl as σ hd hσ hnd)
  case andTrue =>
    intro st d env l r st' st'' lv rv nl nr hl hlt _ ihl ihr as σ hd hσ hnd
    unfold_ccost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hl.sound as σ hd hσ
    exact cle_add (ihl as σ hd hσ hnd)
      (ihr as _ hd (branch_sound hd hl.sound hlt h1 h2) (nodup_eval hl.sound hnd))
  case neg =>
    intro st d env e st' n m _ ih as σ hd hσ hnd
    unfold_ccost hσ
    exact ih as σ hd hσ hnd
  case not =>
    intro st d env e st' v m _ ih as σ hd hσ hnd
    unfold_ccost hσ
    exact ih as σ hd hσ hnd
  case call =>
    intro st d env f args st' st'' st''' fv vs v nf na nc hf _ ha _ ihf iha ihc as σ hd hσ hnd
    unfold_ccost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hf.sound as σ hd hσ
    refine cle_add (cle_add (ihf as σ hd hσ hnd)
      (iha as _ hd h1 (nodup_eval hf.sound hnd))) ?_
    unfold callCost
    split
    · rename_i g hg
      rw [ihc g (asNative_sound h2 hg)]
      exact Nat.le_refl 0
    · trivial
  case fn =>
    intro st d env name params body store' a _ as σ hd hσ _
    unfold_ccost hσ
    exact Nat.le_refl _
  case argsNil =>
    intro st d env as σ hd hσ _
    exact Nat.le_refl 0
  case argsCons =>
    intro st d env e es st' st'' v vs ne nes he _ ihe ihes as σ hd hσ hnd
    obtain ⟨h1, -⟩ := eval_sound cfg he.sound as σ hd hσ
    exact cle_add (ihe as σ hd hσ hnd) (ihes as _ hd h1 (nodup_eval he.sound hnd))
  case cClosure =>
    intro st d a cd vs store' frame st' status v nb _ _ _ _ _ _ _ f hf
    cases hf
  case cPrint => intros; rfl
  case cPrintln => intros; rfl
  case cAssert => intros; rfl
  case sExpr =>
    intro st d env e st' v n _ ih as hd hnd
    exact ⟨fun σ hσ => by unfold_scost hσ; exact ih as σ hd hσ hnd, trivial⟩
  case sVarInit =>
    intro st d env x e st' v n he ih as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    obtain ⟨h1, -⟩ := eval_sound cfg he.sound as σ hd hσ
    exact cle_add (ih as σ hd hσ hnd) (defineBound_sound hd h1 (nodup_eval he.sound hnd))
  case sVarNull =>
    intro st d env x as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    exact defineBound_sound hd hσ hnd
  case sBlock =>
    intro st d env ss store' inner st' status n halloc _ ih as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    exact cle_add (Nat.le_refl _)
      (ih (inner :: as) σ.push rfl (SGam.push hd hσ halloc) (FramesNoDup.allocFrame halloc hnd))
  case sIfTrue =>
    intro st d env c t e st' st'' v status nc nt hc htr _ ihc iht as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hc.sound as σ hd hσ
    exact cle_add (ihc as σ hd hσ hnd) (cle_max_l _
      ((iht as hd (nodup_eval hc.sound hnd)).1 _ (branch_sound hd hc.sound htr h1 h2)))
  case sIfFalse =>
    intro st d env c t e st' st'' v status nc ne hc hf _ ihc ihe as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    obtain ⟨h1, h2⟩ := eval_sound cfg hc.sound as σ hd hσ
    rw [scostOpt_some]
    exact cle_add (ihc as σ hd hσ hnd) (cle_max_r _
      ((ihe as hd (nodup_eval hc.sound hnd)).1 _ (branch_sound hd hc.sound hf h1 h2)))
  case sIfNone =>
    intro st d env c t st' v nc _ _ ihc as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    exact cle_add_l _ (ihc as σ hd hσ hnd)
  case sWhileFalse =>
    intro st d env c b st' v nc _ _ ihc as hd hnd
    have hr : WRun A cfg c b as env st.store nc :=
      .fin fun I hI => cle_add_l _ (ihc as I hd hI hnd)
    exact ⟨fun σ hσ => whileCost_of_run hr hσ, hr⟩
  case sWhileBreak =>
    intro st d env c b st' st'' v nc nb hc ht _ ihc ihb as hd hnd
    have hr : WRun A cfg c b as env st.store (nc + nb) := .fin fun I hI => by
      obtain ⟨h1, h2⟩ := eval_sound cfg hc.sound as I hd hI
      exact cle_add (ihc as I hd hI hnd)
        ((ihb as hd (nodup_eval hc.sound hnd)).1 _ (branch_sound hd hc.sound ht h1 h2))
    exact ⟨fun σ hσ => whileCost_of_run hr hσ, hr⟩
  case sWhileRet =>
    intro st d env c b st' st'' v rv nc nb hc ht _ ihc ihb as hd hnd
    have hr : WRun A cfg c b as env st.store (nc + nb) := .fin fun I hI => by
      obtain ⟨h1, h2⟩ := eval_sound cfg hc.sound as I hd hI
      exact cle_add (ihc as I hd hI hnd)
        ((ihb as hd (nodup_eval hc.sound hnd)).1 _ (branch_sound hd hc.sound ht h1 h2))
    exact ⟨fun σ hσ => whileCost_of_run hr hσ, hr⟩
  case sWhileLoop =>
    intro st d env c b st' st'' st''' v status status' nc nb nr hc ht hb hst hw ihc ihb ihw
      as hd hnd
    have hnd' := nodup_eval hc.sound hnd
    have hnd'' := nodup_exec hb.sound hnd'
    have hr : WRun A cfg c b as env st.store (nc + nb + nr) := by
      refine .step (fun I hI => ⟨?_, ?_, ?_⟩) (ihw as hd hnd'').2
      · obtain ⟨h1, h2⟩ := eval_sound cfg hc.sound as I hd hI
        exact cle_add (ihc as I hd hI hnd)
          ((ihb as hd hnd').1 _ (branch_sound hd hc.sound ht h1 h2))
      · exact whileNext_sound cfg hd hc.sound ht hb.sound hst hI
      · exact whileCount hd hc.sound ht hb.sound hst hI
    exact ⟨fun σ hσ => whileCost_of_run hr hσ, hr⟩
  case sFor =>
    intro st d env init cnd step b store' outer st' st'' status ni nl halloc hi _ ihi ihl
      as hd hnd
    refine ⟨fun σ hσ => ?_, trivial⟩
    unfold_scost hσ
    have hp := SGam.push hd hσ halloc
    have hnd' := FramesNoDup.allocFrame halloc hnd
    have hs := init_sound cfg hi.sound (outer :: as) σ.push rfl hp
    exact cle_add (cle_add (Nat.le_refl _) (ihi (outer :: as) σ.push rfl hp hnd'))
      (forCost_of_run (ihl (outer :: as) rfl (nodup_init hi.sound hnd')) hs)
  case sRet =>
    intro st d env e st' v n _ ih as hd hnd
    exact ⟨fun σ hσ => by unfold_scost hσ; exact ih as σ hd hσ hnd, trivial⟩
  case sRetNull =>
    intro st d env as hd hnd
    exact ⟨fun σ hσ => by unfold_scost hσ; exact Nat.le_refl 0, trivial⟩
  case sBrk =>
    intro st d env as hd hnd
    exact ⟨fun σ hσ => by unfold_scost hσ; exact Nat.le_refl 0, trivial⟩
  case sCont =>
    intro st d env as hd hnd
    exact ⟨fun σ hσ => by unfold_scost hσ; exact Nat.le_refl 0, trivial⟩
  case initNone =>
    intro st d env as σ hd hσ _
    rw [scostOpt_none]
    exact Nat.le_refl 0
  case initSome =>
    intro st d env s st' status n _ ih as σ hd hσ hnd
    rw [scostOpt_some]
    exact (ih as hd hnd).1 σ hσ
  case flCondFalse =>
    intro st d env c step b st' v nc _ _ ihc as hd hnd
    exact .fin fun I hI => by
      rw [forItCost_eq]
      exact cle_add_l _ (cle_add_l _ (ihc as I hd hI hnd))
  case flBreak =>
    intro st d env cnd step b st' st'' nc nb hc _ ihc ihb as hd hnd
    exact .fin fun I hI => by
      rw [forItCost_eq]
      exact cle_add_l _ (cle_add (ihc as I hd hI hnd)
      ((ihb as hd (nodup_cond hc.sound hnd)).1 _ (cond_sound cfg hc.sound as I hd hI)))
  case flRet =>
    intro st d env cnd step b st' st'' rv nc nb hc _ ihc ihb as hd hnd
    exact .fin fun I hI => by
      rw [forItCost_eq]
      exact cle_add_l _ (cle_add (ihc as I hd hI hnd)
      ((ihb as hd (nodup_cond hc.sound hnd)).1 _ (cond_sound cfg hc.sound as I hd hI)))
  case flLoop =>
    intro st d env cnd step b st' st'' st''' st'''' status status' nc nb ns nr hc hb hst hs _
      ihc ihb ihs ihl as hd hnd
    have hnd' := nodup_cond hc.sound hnd
    have hnd'' := nodup_exec hb.sound hnd'
    refine .step (fun I hI => ⟨?_, ?_, ?_⟩) (ihl as hd (nodup_step hs.sound hnd''))
    · rw [forItCost_eq]
      exact cle_add (cle_add (ihc as I hd hI hnd)
        ((ihb as hd hnd').1 _ (cond_sound cfg hc.sound as I hd hI)))
        (ihs as _ hd (forMid_sound cfg hd hc.sound hb.sound hst hI) hnd'')
    · exact forNext_sound cfg hd hc.sound hb.sound hst hs.sound hI
    · exact forCount hd hc.sound hb.sound hst hs.sound hI
  case condNone =>
    intro st d env as I hd hI _
    exact Nat.le_refl 0
  case condSome =>
    intro st d env c st' v nc _ _ ihc as I hd hI hnd
    exact ihc as I hd hI hnd
  case stepNone =>
    intro st d env as I hd hI _
    exact Nat.le_refl 0
  case stepSome =>
    intro st d env e st' v n _ ihe as I hd hI hnd
    exact ihe as I hd hI hnd
  case seqNil =>
    intro st d env as σ hd hσ _
    rw [seqcost_nil]
    exact Nat.le_refl 0
  case seqNormal =>
    intro st d env s ss st' st'' status n1 n2 hs _ ihs ihss as σ hd hσ hnd
    rw [seqcost_cons]
    exact cle_add ((ihs as hd hnd).1 σ hσ)
      (ihss as _ hd ((exec_sound cfg hs.sound as hd).1 σ hσ) (nodup_exec hs.sound hnd))
  case seqAbrupt =>
    intro st d env s ss st' status n _ _ ihs as σ hd hσ hnd
    rw [seqcost_cons]
    exact cle_add_l _ ((ihs as hd hnd).1 σ hσ)))

theorem seqcost_sound (cfg : Cfg) {st st' : St} {d : Nat} {env : Addr} {ss : List Stmt}
    {status : Status} {n : Nat} (h : ExecSeqCost st d env ss st' status n) :
    CSeq A cfg st env ss n := by
  cost_rec ExecSeqCost.rec h

theorem progCost_sound (cfg : Cfg) {p : Program} {n : Nat}
    (h : progCost (A := A) cfg p = some n) :
    ∀ out, BigStep p out → BigStepBudget p out n := by
  rintro out ⟨st', hseq, hout⟩
  obtain ⟨m, hm⟩ := ExecSeqCost.exists hseq
  have := seqcost_sound cfg hm [0] (initState (A := A)) rfl initState_sound initSt_nodup
  unfold progCost at h
  rw [h] at this
  exact ⟨st', m, hm, hout, this⟩

end Vsa.AbsInt
