import Vsa.While.TypeCheck
import Vsa.While.Unify

namespace Vsa.While.Types

open Vsa.While Vsa.While.Unify

mutual

def enc : Ty → Tm
  | .int => .leaf 0
  | .bool => .leaf 1
  | .str => .leaf 2
  | .null => .leaf 3
  | .native .print => .leaf 4
  | .native .println => .leaf 5
  | .native .assert => .leaf 6
  | .fn ps r => .node 0 (encL ps) (enc r)

def encL : List Ty → Tm
  | [] => .leaf 7
  | t :: ts => .node 1 (enc t) (encL ts)

end

mutual

def dec : Tm → Ty
  | .leaf 1 => .bool
  | .leaf 2 => .str
  | .leaf 3 => .null
  | .leaf 4 => .native .print
  | .leaf 5 => .native .println
  | .leaf 6 => .native .assert
  | .node 0 a r => .fn (decL a) (dec r)
  | _ => .int

def decL : Tm → List Ty
  | .node 1 h t => dec h :: decL t
  | _ => []

end

def tList : List Tm → Tm
  | [] => .leaf 7
  | t :: ts => .node 1 t (tList ts)

def pvar (x : String) : Tm := .var (.name x)

def tINT : Tm := .leaf 0
def tBOOL : Tm := .leaf 1
def tSTR : Tm := .leaf 2
def tNULL : Tm := .leaf 3

abbrev Disj := List (List (Tm × Tm))

structure SS where
  σ : Subst
  n : Nat
  pend : List Disj

def unifyS (s : SS) (E : List (Tm × Tm)) : Option SS :=
  (unifyTop s.σ E).map fun σ => { s with σ := σ }

def firstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | a :: as =>
    match f a with
    | some r => some r
    | none => firstSome f as

def binAlts : BinOp → Tm → Tm → List (List (Tm × Tm) × Tm)
  | .add, a, b => [([(a, tINT), (b, tINT)], tINT), ([(a, tSTR)], tSTR), ([(b, tSTR)], tSTR)]
  | .sub, a, b => [([(a, tINT), (b, tINT)], tINT)]
  | .mul, a, b => [([(a, tINT), (b, tINT)], tINT)]
  | .div, a, b => [([(a, tINT), (b, tINT)], tINT)]
  | .mod, a, b => [([(a, tINT), (b, tINT)], tINT)]
  | .eq, _, _ => [([], tBOOL)]
  | .ne, _, _ => [([], tBOOL)]
  | .lt, a, b => [([(a, tINT), (b, tINT)], tBOOL), ([(a, tSTR), (b, tSTR)], tBOOL)]
  | .le, a, b => [([(a, tINT), (b, tINT)], tBOOL), ([(a, tSTR), (b, tSTR)], tBOOL)]
  | .gt, a, b => [([(a, tINT), (b, tINT)], tBOOL), ([(a, tSTR), (b, tSTR)], tBOOL)]
  | .ge, a, b => [([(a, tINT), (b, tINT)], tBOOL), ([(a, tSTR), (b, tSTR)], tBOOL)]

def callAlts (f : Tm) (ts : List Tm) (r : Tm) : List (List (Tm × Tm) × Tm) :=
  [([(f, .node 0 (tList ts) r)], r), ([(f, .leaf 4)], tNULL), ([(f, .leaf 5)], tNULL)] ++
    (if ts.length = 1 ∨ ts.length = 2 then [([(f, .leaf 6)], tNULL)] else [])

def viable (σ : Subst) (alts : List (List (Tm × Tm) × Tm)) : List (List (Tm × Tm) × Tm) :=
  alts.filter fun a => (unifyTop σ a.1).isSome

def branch (alts : List (List (Tm × Tm) × Tm)) (s : SS) (k : SS → Tm → Option SS) :
    Option SS :=
  match viable s.σ alts with
  | [] => none
  | [a] => (unifyS s a.1).bind fun s' => k s' a.2
  | a :: b :: rest =>
    k { s with n := s.n + 1,
               pend := ((a :: b :: rest).map fun c => (.var (.aux s.n), c.2) :: c.1) :: s.pend }
      (.var (.aux s.n))

def fnWrap (params : List String) (body : List Stmt)
    (bs : Option Tm → SS → (SS → Option SS) → Option SS) (s : SS)
    (k : SS → Tm → Option SS) : Option SS :=
  bs (some (.var (.aux s.n))) { s with n := s.n + 1 } fun s₂ =>
    (unifyS s₂ (if mustExitSeqB body then [] else [(.var (.aux s.n), tNULL)])).bind fun s₃ =>
      k s₃ (.node 0 (tList (params.map pvar)) (.var (.aux s.n)))

mutual

def srchE : Expr → SS → (SS → Tm → Option SS) → Option SS
  | .int _, s, k => k s tINT
  | .str _, s, k => k s tSTR
  | .bool _, s, k => k s tBOOL
  | .null, s, k => k s tNULL
  | .var x, s, k => k s (pvar x)
  | .assign x e, s, k =>
    srchE e s fun s₁ t => (unifyS s₁ [(t, pvar x)]).bind fun s₂ => k s₂ (pvar x)
  | .binary op l r, s, k =>
    srchE l s fun s₁ tl => srchE r s₁ fun s₂ tr =>
      branch (binAlts op tl tr) s₂ k
  | .logical _ l r, s, k => srchE l s fun s₁ _ => srchE r s₁ fun s₂ _ => k s₂ tBOOL
  | .unary .neg e, s, k =>
    srchE e s fun s₁ t => (unifyS s₁ [(t, tINT)]).bind fun s₂ => k s₂ tINT
  | .unary .not e, s, k => srchE e s fun s₁ _ => k s₁ tBOOL
  | .call f args, s, k =>
    srchE f s fun s₁ tf => srchArgs args s₁ fun s₂ ts =>
      branch (callAlts tf ts (.var (.aux s₂.n))) { s₂ with n := s₂.n + 1 } k
  | .fn _ params body, s, k => fnWrap params body (srchSeq body) s k

def srchArgs : List Expr → SS → (SS → List Tm → Option SS) → Option SS
  | [], s, k => k s []
  | e :: es, s, k => srchE e s fun s₁ t => srchArgs es s₁ fun s₂ ts => k s₂ (t :: ts)

def srchS : Stmt → Option Tm → SS → (SS → Option SS) → Option SS
  | .expr e, _, s, k => srchE e s fun s₁ _ => k s₁
  | .varDecl x none, _, s, k => (unifyS s [(pvar x, tNULL)]).bind k
  | .varDecl x (some e), _, s, k =>
    srchE e s fun s₁ t => (unifyS s₁ [(t, pvar x)]).bind k
  | .block ss, R, s, k => srchSeq ss R s k
  | .ifStmt c t e, R, s, k =>
    srchE c s fun s₁ _ => srchS t R s₁ fun s₂ => srchInit e R s₂ k
  | .whileStmt c b, R, s, k => srchE c s fun s₁ _ => srchS b R s₁ k
  | .forStmt init cnd step b, R, s, k =>
    srchInit init R s fun s₁ => srchOptE cnd s₁ fun s₂ => srchOptE step s₂ fun s₃ =>
      srchS b R s₃ k
  | .ret (some e), some r, s, k =>
    srchE e s fun s₁ t => (unifyS s₁ [(t, r)]).bind k
  | .ret none, some r, s, k => (unifyS s [(r, tNULL)]).bind k
  | .ret _, none, _, _ => none
  | .brk, _, s, k => k s
  | .cont, _, s, k => k s

def srchInit : Option Stmt → Option Tm → SS → (SS → Option SS) → Option SS
  | none, _, s, k => k s
  | some st, R, s, k => srchS st R s k

def srchOptE : Option Expr → SS → (SS → Option SS) → Option SS
  | none, s, k => k s
  | some e, s, k => srchE e s fun s₁ _ => k s₁

def srchSeq : List Stmt → Option Tm → SS → (SS → Option SS) → Option SS
  | [], _, s, k => k s
  | st :: ss, R, s, k => srchS st R s fun s₁ => srchSeq ss R s₁ k

end

def s₀ : SS :=
  ⟨[(.name "print", .leaf 4), (.name "println", .leaf 5), (.name "assert", .leaf 6)], 0, []⟩

def nViable (σ : Subst) (d : Disj) : Nat := (d.filter fun E => (unifyTop σ E).isSome).length

def pickMin {α : Type} (f : α → Nat) : List α → Option α
  | [] => none
  | a :: as =>
    match pickMin f as with
    | none => some a
    | some b => if f b < f a then some b else some a

theorem pickMin_mem {α : Type} {f : α → Nat} : ∀ {l : List α} {a : α}, pickMin f l = some a → a ∈ l
  | [], _, h => by cases h
  | b :: bs, a, h => by
    simp only [pickMin] at h
    split at h
    · cases h; exact List.mem_cons_self
    · rename_i c hc
      split at h
      · cases h; exact List.mem_cons_of_mem _ (pickMin_mem hc)
      · cases h; exact List.mem_cons_self

def resolve (σ : Subst) (ds : List Disj) : Option Subst :=
  if ds.any fun d => nViable σ d == 0 then none
  else
    match _h : pickMin (nViable σ) ds with
    | none => some σ
    | some d =>
      firstSome (fun E => (unifyTop σ E).bind fun σ' => resolve σ' (ds.erase d))
        (d.filter fun E => (unifyTop σ E).isSome)
termination_by ds.length
decreasing_by
  have hd := pickMin_mem _h
  rw [List.length_erase_of_mem hd]
  have := List.length_pos_of_mem hd
  omega

def searchProg (p : Program) : Option SS :=
  srchSeq p none s₀ fun s => (resolve s.σ s.pend).map fun σ => { s with σ := σ, pend := [] }

def envOfSubst (σ : Subst) : TyEnv := fun x => dec (canon σ (.name x))

def Δθ (θ : V → Tm) : TyEnv := fun x => dec (θ (.name x))

def dT (θ : V → Tm) (t : Tm) : Ty := dec (t.bind θ)

mutual

theorem dec_enc : (t : Ty) → dec (enc t) = t
  | .int => rfl
  | .bool => rfl
  | .str => rfl
  | .null => rfl
  | .native .print => rfl
  | .native .println => rfl
  | .native .assert => rfl
  | .fn ps r => by simp only [enc, dec, decL_encL ps, dec_enc r]

theorem decL_encL : (ts : List Ty) → decL (encL ts) = ts
  | [] => rfl
  | t :: ts => by simp only [encL, decL, dec_enc t, decL_encL ts]

end

theorem tList_bind (θ : V → Tm) : ∀ ts : List Tm, (tList ts).bind θ = tList (ts.map (·.bind θ))
  | [] => rfl
  | t :: ts => by simp [tList, Tm.bind, tList_bind θ ts]

theorem decL_tList : ∀ ts : List Tm, decL (tList ts) = ts.map dec
  | [] => rfl
  | t :: ts => by simp [tList, decL, decL_tList ts]

theorem encL_eq_tList : ∀ ts : List Ty, encL ts = tList (ts.map enc)
  | [] => rfl
  | t :: ts => by simp [encL, tList, encL_eq_tList ts]

theorem dT_fn (θ : V → Tm) (ts : List Tm) (r : Tm) :
    dT θ (.node 0 (tList ts) r) = .fn (ts.map (dT θ)) (dT θ r) := by
  simp [dT, Tm.bind, dec, tList_bind, decL_tList, Function.comp_def]

theorem unifyS_sound {s s' : SS} {E : List (Tm × Tm)} (h : unifyS s E = some s') :
    s'.n = s.n ∧ s'.pend = s.pend ∧ (Idem s.σ → Idem s'.σ) ∧
      ∀ θ, Sat θ s'.σ → Sat θ s.σ ∧ SatE θ E := by
  simp only [unifyS] at h
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl, fun hi => unifyTop_idem hi hσ, fun θ hs => unifyTop_sound hσ hs⟩

theorem satE_one {θ : V → Tm} {a b : Tm} (h : SatE θ [(a, b)]) : a.bind θ = b.bind θ :=
  h (a, b) (by simp)

theorem satE_two {θ : V → Tm} {a b c d : Tm} (h : SatE θ [(a, b), (c, d)]) :
    a.bind θ = b.bind θ ∧ c.bind θ = d.bind θ :=
  ⟨h (a, b) (by simp), h (c, d) (by simp)⟩

theorem binAlts_sound {θ : V → Tm} {op : BinOp} {a b : Tm} {alt : List (Tm × Tm) × Tm}
    (h : alt ∈ binAlts op a b) (hE : SatE θ alt.1) :
    BinTy op (dT θ a) (dT θ b) (dT θ alt.2) := by
  cases op <;> simp only [binAlts, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl <;>
    first
    | (obtain ⟨h1, h2⟩ := satE_two hE
       simp only [dT, h1, h2]
       first
       | exact .addInt | exact .sub | exact .mul | exact .div | exact .mod
       | exact .cmpInt _ (by decide) | exact .cmpStr _ (by decide))
    | (have h1 := satE_one hE
       simp only [dT, h1]
       first | exact .addStrL _ | exact .addStrR _)
    | exact .eq _ _
    | exact .ne _ _

theorem callAlts_sound {θ : V → Tm} {f r : Tm} {ts : List Tm} {alt : List (Tm × Tm) × Tm}
    (h : alt ∈ callAlts f ts r) (hE : SatE θ alt.1) :
    CallTy (dT θ f) (ts.map (dT θ)) (dT θ alt.2) := by
  simp only [callAlts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl) | h
  · have h1 := satE_one hE
    have : dT θ f = dT θ (.node 0 (tList ts) r) := by simp only [dT, h1]
    rw [this, dT_fn]; exact .fn _ _
  · have h1 := satE_one hE; simp only [dT, h1]; exact .print _
  · have h1 := satE_one hE; simp only [dT, h1]; exact .println _
  · split at h
    · rename_i hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      have h1 := satE_one hE
      simp only [dT, h1]
      rcases hl with hl | hl
      · match ts, hl with
        | [t], _ => exact .assert1 _
      · match ts, hl with
        | [t, u], _ => exact .assert2 _ _
    · cases h

def SatP (θ : V → Tm) (ds : List Disj) : Prop := ∀ d ∈ ds, ∃ E ∈ d, SatE θ E

structure Step (s s' : SS) (P : (V → Tm) → Prop) : Prop where
  idem : Idem s.σ → Idem s'.σ
  pend : ∀ d ∈ s.pend, d ∈ s'.pend
  sat : ∀ θ, Sat θ s'.σ → SatP θ s'.pend → Sat θ s.σ ∧ P θ

inductive Found {α : Type} (k : SS → α → Option SS) (res s : SS)
    (P : α → (V → Tm) → Prop) : Prop
  | intro (s' : SS) (a : α) (hk : k s' a = some res) (step : Step s s' (P a))

inductive FoundS (k : SS → Option SS) (res s : SS) (P : (V → Tm) → Prop) : Prop
  | intro (s' : SS) (hk : k s' = some res) (step : Step s s' P)

inductive Applies (θ : V → Tm) (τ : Tm) (alts : List (List (Tm × Tm) × Tm)) : Prop
  | intro (a : List (Tm × Tm) × Tm) (ha : a ∈ alts) (hE : SatE θ a.1)
      (hτ : τ.bind θ = a.2.bind θ)

theorem Step.trans {s₁ s₂ s₃ : SS} {P Q : (V → Tm) → Prop} (h₁ : Step s₁ s₂ P)
    (h₂ : Step s₂ s₃ Q) : Step s₁ s₃ fun θ => P θ ∧ Q θ :=
  ⟨fun h => h₂.idem (h₁.idem h), fun d hd => h₂.pend d (h₁.pend d hd), fun θ h hp => by
    obtain ⟨h, hq⟩ := h₂.sat θ h hp
    obtain ⟨h, hp'⟩ := h₁.sat θ h fun d hd => hp d (h₂.pend d hd)
    exact ⟨h, hp', hq⟩⟩

theorem Step.mono {s s' : SS} {P Q : (V → Tm) → Prop} (h : Step s s' P)
    (hPQ : ∀ θ, Sat θ s'.σ → P θ → Q θ) : Step s s' Q :=
  ⟨h.idem, h.pend, fun θ hs hp => ⟨(h.sat θ hs hp).1, hPQ θ hs (h.sat θ hs hp).2⟩⟩

theorem Step.unify {s s' : SS} {E : List (Tm × Tm)} (h : unifyS s E = some s') :
    Step s s' fun θ => SatE θ E := by
  obtain ⟨_, hp, hi, hs⟩ := unifyS_sound h
  exact ⟨hi, fun d hd => hp ▸ hd, fun θ h _ => hs θ h⟩

theorem Step.refl (s : SS) : Step s s fun _ => True :=
  ⟨id, fun _ h => h, fun _ h _ => ⟨h, trivial⟩⟩

theorem Step.fresh (s : SS) : Step s { s with n := s.n + 1 } fun _ => True :=
  ⟨id, fun _ h => h, fun _ h _ => ⟨h, trivial⟩⟩

theorem mem_viable {σ : Subst} {alts : List (List (Tm × Tm) × Tm)} {a : List (Tm × Tm) × Tm}
    (h : a ∈ viable σ alts) : a ∈ alts ∧ (unifyTop σ a.1).isSome = true := by
  simpa [viable] using h

theorem branch_sound {alts : List (List (Tm × Tm) × Tm)} {s : SS} {k : SS → Tm → Option SS}
    {res : SS} (h : branch alts s k = some res) :
    Found k res s fun τ θ => Applies θ τ alts := by
  unfold branch at h
  split at h
  · cases h
  · rename_i a hv
    obtain ⟨s', hu, hk⟩ := Option.bind_eq_some_iff.mp h
    have ha := (mem_viable (hv ▸ List.mem_singleton_self a : a ∈ viable s.σ alts)).1
    exact ⟨s', _, hk, (Step.unify hu).mono fun θ _ hE => ⟨a, ha, hE, rfl⟩⟩
  · rename_i a b rest hv
    refine ⟨_, _, h, ⟨id, fun d hd => List.mem_cons_of_mem _ hd, fun θ hs hp => ⟨hs, ?_⟩⟩⟩
    obtain ⟨E, hE, hsat⟩ := hp _ List.mem_cons_self
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hE
    have hc' := (mem_viable (hv ▸ hc : c ∈ viable s.σ alts)).1
    exact ⟨c, hc', fun e he => hsat e (List.mem_cons_of_mem _ he),
      hsat _ List.mem_cons_self⟩

inductive FnTyped (θ : V → Tm) (τ : Tm) (params : List String) (body : List Stmt)
    (Sb S'' : List String) : Prop
  | intro (r : Ty) (hτ : dT θ τ = .fn (params.map (Δθ θ)) r)
      (hb : WtSeq (Δθ θ) Sb (some r) false body S'') (hr : r = .null ∨ MustExitSeq body)

theorem fnWrap_sound {params : List String} {body : List Stmt} {Sb S'' : List String}
    (hb : ∀ R s k res, srchSeq body R s k = some res →
      FoundS k res s fun θ => WtSeq (Δθ θ) Sb (R.map (dT θ)) false body S'')
    {s : SS} {k : SS → Tm → Option SS} {res : SS}
    (h : fnWrap params body (srchSeq body) s k = some res) :
    Found k res s fun τ θ => FnTyped θ τ params body Sb S'' := by
  simp only [fnWrap] at h
  obtain ⟨s₂, h₂, st₂⟩ := hb _ _ _ _ h
  obtain ⟨s₃, hu, hk⟩ := Option.bind_eq_some_iff.mp h₂
  refine ⟨s₃, _, hk, ?_⟩
  have st := (Step.fresh s).trans (st₂.trans (Step.unify hu))
  refine st.mono fun θ _ ⟨_, hbody, hE⟩ => ⟨dT θ (.var (.aux s.n)), ?_, hbody, ?_⟩
  · rw [dT_fn, List.map_map]; rfl
  · cases hm : mustExitSeqB body
    · rw [hm] at hE
      exact .inl (by simp only [dT, satE_one hE]; rfl)
    · exact .inr (mustExitSeq_of_b hm)

mutual

theorem soundE : (e : Expr) → ∀ {Δ : TyEnv} {S : List String} {T : Ty}, WtE Δ S e T →
    ∀ (s : SS) (k : SS → Tm → Option SS) (res : SS), srchE e s k = some res →
    Found k res s fun τ θ => WtE (Δθ θ) S e (dT θ τ)
  | .int _, _, _, _, _, s, k, res, h => ⟨s, _, h, (Step.refl s).mono fun _ _ _ => .int _ _⟩
  | .str _, _, _, _, _, s, k, res, h => ⟨s, _, h, (Step.refl s).mono fun _ _ _ => .str _ _⟩
  | .bool _, _, _, _, _, s, k, res, h => ⟨s, _, h, (Step.refl s).mono fun _ _ _ => .bool _ _⟩
  | .null, _, _, _, _, s, k, res, h => ⟨s, _, h, (Step.refl s).mono fun _ _ _ => .null _⟩
  | .var x, _, _, _, D, s, k, res, h => by
    cases D with
    | var _ _ hx => exact ⟨s, _, h, (Step.refl s).mono fun _ _ _ => .var _ _ hx⟩
  | .assign x e, _, _, _, D, s, k, res, h => by
    cases D with
    | assign _ _ _ hx De =>
      simp only [srchE] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      obtain ⟨s₂, hu, hk⟩ := Option.bind_eq_some_iff.mp h₁
      refine ⟨s₂, _, hk, (st₁.trans (Step.unify hu)).mono fun θ _ ⟨he, hE⟩ => ?_⟩
      have := satE_one hE
      have ht : dT θ t = Δθ θ x := by simp only [dT, this]; rfl
      rw [ht] at he
      exact .assign _ _ _ hx he
  | .binary op l r, _, _, _, D, s, k, res, h => by
    cases D with
    | binary _ _ _ _ _ _ _ Dl Dr _ =>
      simp only [srchE] at h
      obtain ⟨s₁, tl, h₁, st₁⟩ := soundE l Dl s _ res h
      obtain ⟨s₂, tr, h₂, st₂⟩ := soundE r Dr s₁ _ res h₁
      obtain ⟨s₃, τ, hk, st₃⟩ := branch_sound h₂
      refine ⟨s₃, τ, hk, ((st₁.trans st₂).trans st₃).mono
        fun θ _ ⟨⟨hl, hr⟩, a, ha, hE, hτ⟩ => ?_⟩
      have : dT θ τ = dT θ a.2 := by simp only [dT, hτ]
      rw [this]
      exact .binary _ _ _ _ _ _ _ hl hr (binAlts_sound ha hE)
  | .logical op l r, _, _, _, D, s, k, res, h => by
    cases D with
    | logical _ _ _ _ _ _ Dl Dr =>
      simp only [srchE] at h
      obtain ⟨s₁, tl, h₁, st₁⟩ := soundE l Dl s _ res h
      obtain ⟨s₂, tr, h₂, st₂⟩ := soundE r Dr s₁ _ res h₁
      exact ⟨s₂, _, h₂, (st₁.trans st₂).mono fun θ _ ⟨hl, hr⟩ => .logical _ _ _ _ _ _ hl hr⟩
  | .unary .neg e, _, _, _, D, s, k, res, h => by
    cases D with
    | neg _ _ De =>
      simp only [srchE] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      obtain ⟨s₂, hu, hk⟩ := Option.bind_eq_some_iff.mp h₁
      refine ⟨s₂, _, hk, (st₁.trans (Step.unify hu)).mono fun θ _ ⟨he, hE⟩ => ?_⟩
      have ht : dT θ t = .int := by simp only [dT, satE_one hE]; rfl
      rw [ht] at he
      exact .neg _ _ he
  | .unary .not e, _, _, _, D, s, k, res, h => by
    cases D with
    | not _ _ _ De =>
      simp only [srchE] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      exact ⟨s₁, _, h₁, st₁.mono fun θ _ he => .not _ _ _ he⟩
  | .call f args, _, _, _, D, s, k, res, h => by
    cases D with
    | call _ _ _ _ _ _ Df hlen Da _ =>
      simp only [srchE] at h
      obtain ⟨s₁, tf, h₁, st₁⟩ := soundE f Df s _ res h
      obtain ⟨s₂, ts, h₂, st₂⟩ := soundArgs args Da s₁ _ res h₁
      obtain ⟨s₃, τ, hk, st₃⟩ := branch_sound h₂
      refine ⟨s₃, τ, hk, (((st₁.trans st₂).trans (Step.fresh s₂)).trans st₃).mono
        fun θ _ ⟨⟨⟨hf, ha'⟩, _⟩, a, ha, hE, hτ⟩ => ?_⟩
      have : dT θ τ = dT θ a.2 := by simp only [dT, hτ]
      rw [this]
      exact .call _ _ _ _ _ _ hf hlen ha' (callAlts_sound ha hE)
  | .fn name params body, _, _, _, D, s, k, res, h => by
    cases D with
    | fn _ _ _ _ r S' Db _ =>
      simp only [srchE] at h
      obtain ⟨s', τ, hk, st⟩ := fnWrap_sound (fun R s k res h => soundSeq body Db R s k res h) h
      refine ⟨s', τ, hk, st.mono fun θ _ ⟨r, hτ, hb, hr⟩ => ?_⟩
      rw [hτ]
      exact .fn _ _ _ _ _ _ hb hr

theorem soundArgs : (es : List Expr) → ∀ {Δ : TyEnv} {S : List String} {ts : List Ty},
    WtArgs Δ S es ts →
    ∀ (s : SS) (k : SS → List Tm → Option SS) (res : SS), srchArgs es s k = some res →
    Found k res s fun τs θ => WtArgs (Δθ θ) S es (τs.map (dT θ))
  | [], _, _, _, _, s, k, res, h => ⟨s, [], h, (Step.refl s).mono fun _ _ _ => .nil _⟩
  | e :: es, _, _, _, D, s, k, res, h => by
    cases D with
    | cons _ _ _ _ _ De Des =>
      simp only [srchArgs] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      obtain ⟨s₂, ts, h₂, st₂⟩ := soundArgs es Des s₁ _ res h₁
      exact ⟨s₂, t :: ts, h₂, (st₁.trans st₂).mono fun θ _ ⟨he, hes⟩ => .cons _ _ _ _ _ he hes⟩

theorem soundS : (st : Stmt) → ∀ {Δ : TyEnv} {S : List String} {R : Option Ty} {L : Bool}
    {S' : List String}, WtS Δ S R L st S' →
    ∀ (Rt : Option Tm) (s : SS) (k : SS → Option SS) (res : SS), srchS st Rt s k = some res →
    FoundS k res s fun θ => WtS (Δθ θ) S (Rt.map (dT θ)) L st S'
  | .expr e, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | expr _ _ _ _ _ De =>
      simp only [srchS] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      exact ⟨s₁, h₁, st₁.mono fun θ _ he => .expr _ _ _ _ _ he⟩
  | .varDecl x none, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | varNull =>
      simp only [srchS] at h
      obtain ⟨s₁, hu, hk⟩ := Option.bind_eq_some_iff.mp h
      refine ⟨s₁, hk, (Step.unify hu).mono fun θ _ hE => .varNull _ _ _ _ ?_⟩
      show dT θ (pvar x) = .null
      simp only [dT, satE_one hE]; rfl
  | .varDecl x (some e), _, _, _, _, _, D, Rt, s, k, res, h => by
    simp only [srchS] at h
    cases D with
    | varInit _ _ _ _ _ De =>
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      obtain ⟨s₂, hu, hk⟩ := Option.bind_eq_some_iff.mp h₁
      refine ⟨s₂, hk, (st₁.trans (Step.unify hu)).mono fun θ _ ⟨he, hE⟩ => ?_⟩
      have ht : dT θ t = Δθ θ x := by simp only [dT, satE_one hE]; rfl
      rw [ht] at he
      exact .varInit _ _ _ _ _ he
    | varRec _ _ _ _ name params body r S'' Db _ _ =>
      simp only [srchE] at h
      obtain ⟨s₁, τ, h₁, st₁⟩ := fnWrap_sound (fun R s k res h => soundSeq body Db R s k res h) h
      obtain ⟨s₂, hu, hk⟩ := Option.bind_eq_some_iff.mp h₁
      refine ⟨s₂, hk, (st₁.trans (Step.unify hu)).mono fun θ _ ⟨⟨r, hτ, hb, hr⟩, hE⟩ => ?_⟩
      have hx : Δθ θ x = .fn (params.map (Δθ θ)) r := by
        rw [← hτ]; simp only [dT, satE_one hE]; rfl
      exact .varRec _ _ _ _ _ _ _ _ _ hb hr hx
  | .block ss, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | block _ _ _ _ _ Ds =>
      simp only [srchS] at h
      obtain ⟨s₁, h₁, st₁⟩ := soundSeq ss Ds Rt s k res h
      exact ⟨s₁, h₁, st₁.mono fun θ _ hs => .block _ _ _ _ _ hs⟩
  | .ifStmt c t e, _, _, _, _, _, D, Rt, s, k, res, h => by
    simp only [srchS] at h
    cases D with
    | ifSome _ _ _ _ _ e' _ _ _ Dc Dt De =>
      obtain ⟨s₁, tc, h₁, st₁⟩ := soundE c Dc s _ res h
      obtain ⟨s₂, h₂, st₂⟩ := soundS t Dt Rt s₁ _ res h₁
      obtain ⟨s₃, h₃, st₃⟩ := soundInit (some e') (.some _ _ _ _ _ De) Rt s₂ k res h₂
      refine ⟨s₃, h₃, ((st₁.trans st₂).trans st₃).mono fun θ _ ⟨⟨hc, ht⟩, he⟩ => ?_⟩
      cases he with
      | some _ _ _ _ _ he => exact .ifSome _ _ _ _ _ _ _ _ _ hc ht he
    | ifNone _ _ _ _ _ _ _ Dc Dt =>
      obtain ⟨s₁, tc, h₁, st₁⟩ := soundE c Dc s _ res h
      obtain ⟨s₂, h₂, st₂⟩ := soundS t Dt Rt s₁ _ res h₁
      simp only [srchInit] at h₂
      exact ⟨s₂, h₂, (st₁.trans st₂).mono fun θ _ ⟨hc, ht⟩ => .ifNone _ _ _ _ _ _ _ hc ht⟩
  | .whileStmt c b, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | whileS _ _ _ _ _ _ _ Dc Db =>
      simp only [srchS] at h
      obtain ⟨s₁, tc, h₁, st₁⟩ := soundE c Dc s _ res h
      obtain ⟨s₂, h₂, st₂⟩ := soundS b Db Rt s₁ k res h₁
      exact ⟨s₂, h₂, (st₁.trans st₂).mono fun θ _ ⟨hc, hb⟩ => .whileS _ _ _ _ _ _ _ hc hb⟩
  | .forStmt init cnd step b, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | forS _ _ _ _ _ _ _ _ _ Di Dc Ds Db =>
      simp only [srchS] at h
      obtain ⟨s₁, h₁, st₁⟩ := soundInit init Di Rt s _ res h
      obtain ⟨s₂, h₂, st₂⟩ := soundOptE cnd Dc s₁ _ res h₁
      obtain ⟨s₃, h₃, st₃⟩ := soundOptE step Ds s₂ _ res h₂
      obtain ⟨s₄, h₄, st₄⟩ := soundS b Db Rt s₃ k res h₃
      exact ⟨s₄, h₄, (((st₁.trans st₂).trans st₃).trans st₄).mono
        fun θ _ ⟨⟨⟨hi, hc⟩, hs⟩, hb⟩ => .forS _ _ _ _ _ _ _ _ _ hi hc hs hb⟩
  | .ret (some e), _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | ret _ _ _ _ De =>
      cases Rt with
      | none => simp [srchS] at h
      | some r =>
        simp only [srchS] at h
        obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
        obtain ⟨s₂, hu, hk⟩ := Option.bind_eq_some_iff.mp h₁
        refine ⟨s₂, hk, (st₁.trans (Step.unify hu)).mono fun θ _ ⟨he, hE⟩ => ?_⟩
        have ht : dT θ t = dT θ r := by simp only [dT, satE_one hE]
        rw [ht] at he
        exact .ret _ _ _ _ he
  | .ret none, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | retNull =>
      cases Rt with
      | none => simp [srchS] at h
      | some r =>
        simp only [srchS] at h
        obtain ⟨s₁, hu, hk⟩ := Option.bind_eq_some_iff.mp h
        refine ⟨s₁, hk, (Step.unify hu).mono fun θ _ hE => ?_⟩
        have ht : dT θ r = .null := by simp only [dT, satE_one hE]; rfl
        simp only [Option.map_some, ht]
        exact .retNull _ _
  | .brk, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | brk => exact ⟨s, h, (Step.refl s).mono fun _ _ _ => .brk _ _⟩
  | .cont, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | cont => exact ⟨s, h, (Step.refl s).mono fun _ _ _ => .cont _ _⟩

theorem soundInit : (o : Option Stmt) → ∀ {Δ : TyEnv} {S : List String} {R : Option Ty}
    {L : Bool} {S' : List String}, WtInit Δ S R L o S' →
    ∀ (Rt : Option Tm) (s : SS) (k : SS → Option SS) (res : SS), srchInit o Rt s k = some res →
    FoundS k res s fun θ => WtInit (Δθ θ) S (Rt.map (dT θ)) L o S'
  | none, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D; exact ⟨s, h, (Step.refl s).mono fun _ _ _ => .none _ _ _⟩
  | some st, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | some _ _ _ _ _ Ds =>
      obtain ⟨s₁, h₁, st₁⟩ := soundS st Ds Rt s k res h
      exact ⟨s₁, h₁, st₁.mono fun θ _ hs => .some _ _ _ _ _ hs⟩

theorem soundOptE : (o : Option Expr) → ∀ {Δ : TyEnv} {S : List String}, WtEO Δ S o →
    ∀ (s : SS) (k : SS → Option SS) (res : SS), srchOptE o s k = some res →
    FoundS k res s fun θ => WtEO (Δθ θ) S o
  | none, _, _, _, s, k, res, h => ⟨s, h, (Step.refl s).mono fun _ _ _ => .none _⟩
  | some e, _, _, D, s, k, res, h => by
    cases D with
    | some _ _ _ De =>
      simp only [srchOptE] at h
      obtain ⟨s₁, t, h₁, st₁⟩ := soundE e De s _ res h
      exact ⟨s₁, h₁, st₁.mono fun θ _ he => .some _ _ _ he⟩

theorem soundSeq : (ss : List Stmt) → ∀ {Δ : TyEnv} {S : List String} {R : Option Ty}
    {L : Bool} {S' : List String}, WtSeq Δ S R L ss S' →
    ∀ (Rt : Option Tm) (s : SS) (k : SS → Option SS) (res : SS), srchSeq ss Rt s k = some res →
    FoundS k res s fun θ => WtSeq (Δθ θ) S (Rt.map (dT θ)) L ss S'
  | [], _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D; exact ⟨s, h, (Step.refl s).mono fun _ _ _ => .nil _ _ _⟩
  | st :: ss, _, _, _, _, _, D, Rt, s, k, res, h => by
    cases D with
    | cons _ _ _ _ _ _ _ Ds Dss =>
      simp only [srchSeq] at h
      obtain ⟨s₁, h₁, st₁⟩ := soundS st Ds Rt s _ res h
      obtain ⟨s₂, h₂, st₂⟩ := soundSeq ss Dss Rt s₁ k res h₁
      exact ⟨s₂, h₂, (st₁.trans st₂).mono fun θ _ ⟨hs, hss⟩ => .cons _ _ _ _ _ _ _ hs hss⟩

end

def BndT (n : Nat) (t : Tm) : Prop := ∀ m, V.aux m ∈ t.vars → m < n

def BndS (n : Nat) (σ : Subst) : Prop := ∀ m, V.aux m ∈ varsS σ → m < n

def Names (Δ : TyEnv) (θ : V → Tm) : Prop := ∀ x, θ (.name x) = enc (Δ x)

def BndP (n : Nat) (ds : List Disj) : Prop :=
  ∀ d ∈ ds, ∀ E ∈ d, ∀ e ∈ E, BndT n e.1 ∧ BndT n e.2

structure Inv (Δ : TyEnv) (θ : V → Tm) (s : SS) : Prop where
  sat : Sat θ s.σ
  idem : Idem s.σ
  bnd : BndS s.n s.σ
  names : Names Δ θ
  pend : SatP θ s.pend
  bndP : BndP s.n s.pend

def Agree (θ θ' : V → Tm) (n : Nat) : Prop := ∀ m < n, θ (.aux m) = θ' (.aux m)

theorem Agree.rfl' {θ : V → Tm} {n : Nat} : Agree θ θ n := fun _ _ => rfl

theorem Agree.trans {θ₁ θ₂ θ₃ : V → Tm} {n m : Nat} (h₁ : Agree θ₁ θ₂ n) (h₂ : Agree θ₂ θ₃ m)
    (hnm : n ≤ m) : Agree θ₁ θ₃ n :=
  fun k hk => (h₁ k hk).trans (h₂ k (by omega))

theorem BndT.mono {n m : Nat} {t : Tm} (h : BndT n t) (hnm : n ≤ m) : BndT m t :=
  fun k hk => by have := h k hk; omega

theorem BndT.leaf {n c : Nat} : BndT n (.leaf c) := fun _ h => by simp [Tm.vars] at h

theorem BndT.pvar {n : Nat} {x : String} : BndT n (pvar x) := fun _ h => by
  simp [Vsa.While.Types.pvar, Tm.vars] at h

theorem BndT.node {n c : Nat} {a b : Tm} : BndT n (.node c a b) ↔ BndT n a ∧ BndT n b := by
  simp only [BndT, Tm.vars, List.mem_append]
  exact ⟨fun h => ⟨fun m hm => h m (.inl hm), fun m hm => h m (.inr hm)⟩,
    fun h m hm => hm.elim (h.1 m) (h.2 m)⟩

theorem BndT.tList {n : Nat} : ∀ {ts : List Tm}, (∀ t ∈ ts, BndT n t) → BndT n (tList ts)
  | [], _ => BndT.leaf
  | t :: _, h => BndT.node.mpr ⟨h t List.mem_cons_self,
      BndT.tList fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem bind_agree {Δ : TyEnv} {θ θ' : V → Tm} {n : Nat} {t : Tm} (hθ : Names Δ θ)
    (hθ' : Names Δ θ') (ha : Agree θ θ' n) (hb : BndT n t) : t.bind θ = t.bind θ' := by
  apply Tm.bind_congr
  intro v hv
  cases v with
  | name x => rw [hθ, hθ']
  | aux m => exact ha m (hb m hv)

theorem unifyS_complete {Δ : TyEnv} {θ : V → Tm} {s : SS} {E : List (Tm × Tm)}
    (hI : Inv Δ θ s) (hE : SatE θ E) (hb : ∀ e ∈ E, BndT s.n e.1 ∧ BndT s.n e.2) :
    ∃ s', unifyS s E = some s' ∧ Inv Δ θ s' ∧ s'.n = s.n := by
  obtain ⟨σ, hσ, hs⟩ := unifyTop_complete hI.idem hI.sat hE
  refine ⟨{ s with σ := σ }, by simp [unifyS, hσ],
    ⟨hs, unifyTop_idem hI.idem hσ, ?_, hI.names, hI.pend, hI.bndP⟩, rfl⟩
  intro m hm
  rcases unifyTop_vars hσ hm with h | h
  · exact hI.bnd m h
  · simp only [varsE, List.mem_flatMap, List.mem_append] at h
    obtain ⟨e, he, h | h⟩ := h
    · exact (hb e he).1 m h
    · exact (hb e he).2 m h

theorem unifyS_one {Δ : TyEnv} {θ : V → Tm} {s : SS} {a b : Tm} (hI : Inv Δ θ s)
    (hab : a.bind θ = b.bind θ) (ha : BndT s.n a) (hb : BndT s.n b) :
    ∃ s', unifyS s [(a, b)] = some s' ∧ Inv Δ θ s' ∧ s'.n = s.n :=
  unifyS_complete hI (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact hab)
    (fun e he => by simp only [List.mem_singleton] at he; subst he; exact ⟨ha, hb⟩)

def upd (θ : V → Tm) (n : Nat) (t : Tm) : V → Tm := fun v => if v = .aux n then t else θ v

theorem upd_self (θ : V → Tm) (n : Nat) (t : Tm) : upd θ n t (.aux n) = t := by simp [upd]

theorem satE_agree {Δ : TyEnv} {θ θ' : V → Tm} {n : Nat} {E : List (Tm × Tm)}
    (hθ : Names Δ θ) (hθ' : Names Δ θ') (ha : Agree θ θ' n)
    (hb : ∀ e ∈ E, BndT n e.1 ∧ BndT n e.2) (h : SatE θ E) : SatE θ' E := by
  intro e he
  rw [← bind_agree hθ hθ' ha (hb e he).1, ← bind_agree hθ hθ' ha (hb e he).2]
  exact h e he

theorem BndP.mono {n m : Nat} {ds : List Disj} (h : BndP n ds) (hnm : n ≤ m) : BndP m ds :=
  fun d hd E hE e he => ⟨(h d hd E hE e he).1.mono hnm, (h d hd E hE e he).2.mono hnm⟩

theorem Inv.fresh {Δ : TyEnv} {θ : V → Tm} {s : SS} (hI : Inv Δ θ s) (t : Tm) :
    Inv Δ (upd θ s.n t) { s with n := s.n + 1 } ∧ Agree θ (upd θ s.n t) s.n := by
  have hagree : Agree θ (upd θ s.n t) s.n := fun m hm => by
    simp [upd]; omega
  have hnames : Names Δ (upd θ s.n t) := fun x => by simp [upd, hI.names x]
  refine ⟨⟨fun p hp => ?_, hI.idem, fun m hm => by have := hI.bnd m hm; show m < s.n + 1; omega,
    hnames, fun d hd => ?_, hI.bndP.mono (by simp)⟩, hagree⟩
  · have hp1 : p.1 ≠ .aux s.n := by
      intro h
      have := hI.bnd s.n (List.mem_flatMap.mpr ⟨p, hp, by simp [h]⟩)
      omega
    have hb : BndT s.n p.2 := fun m hm => hI.bnd m (List.mem_flatMap.mpr ⟨p, hp, by simp [hm]⟩)
    simp only [upd, hp1, ↓reduceIte]
    rw [← bind_agree hI.names hnames hagree hb]
    exact hI.sat p hp
  · obtain ⟨E, hE, hsat⟩ := hI.pend d hd
    exact ⟨E, hE, satE_agree hI.names hnames hagree (hI.bndP d hd E hE) hsat⟩

theorem branch_complete {Δ : TyEnv} {θ : V → Tm} {s : SS} {alts : List (List (Tm × Tm) × Tm)}
    {k : SS → Tm → Option SS} {a : List (Tm × Tm) × Tm} (hI : Inv Δ θ s) (ha : a ∈ alts)
    (hE : SatE θ a.1) (hb : ∀ c ∈ alts, (∀ e ∈ c.1, BndT s.n e.1 ∧ BndT s.n e.2) ∧ BndT s.n c.2)
    (hK : ∀ s' τ θ', Inv Δ θ' s' → Agree θ θ' s.n → s.n ≤ s'.n → BndT s'.n τ →
      τ.bind θ' = a.2.bind θ → k s' τ ≠ none) :
    branch alts s k ≠ none := by
  have hav : a ∈ viable s.σ alts := by
    obtain ⟨σ', hσ', _⟩ := unifyTop_complete hI.idem hI.sat hE
    simp [viable, ha, hσ']
  unfold branch
  split
  · rename_i hv; rw [hv] at hav; cases hav
  · rename_i c hv
    rw [hv, List.mem_singleton] at hav
    subst hav
    obtain ⟨s', hu, hI', hn'⟩ := unifyS_complete hI hE (hb a ha).1
    rw [hu]
    exact hK s' _ θ hI' Agree.rfl' (by omega) (by rw [hn']; exact (hb a ha).2) rfl
  · rename_i c d rest hv
    obtain ⟨hF, hagree⟩ := hI.fresh (a.2.bind θ)
    have hmem : ∀ x ∈ c :: d :: rest, x ∈ alts := fun x hx => (mem_viable (hv ▸ hx)).1
    refine hK _ _ _ ⟨hF.sat, hF.idem, hF.bnd, hF.names, ?_, ?_⟩ hagree (by simp) ?_ (upd_self _ _ _)
    · intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · refine ⟨(.var (.aux s.n), a.2) :: a.1, List.mem_map.mpr ⟨a, hv ▸ hav, rfl⟩, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simp only [Tm.bind, upd_self]
          exact bind_agree hI.names hF.names hagree (hb a ha).2
        · exact satE_agree hI.names hF.names hagree (hb a ha).1 hE e he
      · exact hF.pend D hD
    · intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · intro E hE e he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hE
        have hbx := hb x (hmem x hx)
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨fun m hm => by simp [Tm.vars] at hm; show m < s.n + 1; omega,
            hbx.2.mono (by simp)⟩
        · exact ⟨(hbx.1 e he).1.mono (by simp), (hbx.1 e he).2.mono (by simp)⟩
      · exact hF.bndP D hD
    · intro m hm; simp [Tm.vars] at hm; show m < s.n + 1; omega

def KE (Δ : TyEnv) (θ : V → Tm) (s : SS) (T : Ty) (k : SS → Tm → Option SS) : Prop :=
  ∀ s' τ θ', Inv Δ θ' s' → Agree θ θ' s.n → s.n ≤ s'.n → BndT s'.n τ → τ.bind θ' = enc T →
    k s' τ ≠ none

def KA (Δ : TyEnv) (θ : V → Tm) (s : SS) (Ts : List Ty) (k : SS → List Tm → Option SS) : Prop :=
  ∀ s' τs θ', Inv Δ θ' s' → Agree θ θ' s.n → s.n ≤ s'.n → (∀ τ ∈ τs, BndT s'.n τ) →
    τs.map (·.bind θ') = Ts.map enc → k s' τs ≠ none

def KS (Δ : TyEnv) (θ : V → Tm) (s : SS) (k : SS → Option SS) : Prop :=
  ∀ s' θ', Inv Δ θ' s' → Agree θ θ' s.n → s.n ≤ s'.n → k s' ≠ none

def RelR (θ : V → Tm) (n : Nat) (Rt : Option Tm) (R : Option Ty) : Prop :=
  Rt.map (·.bind θ) = R.map enc ∧ ∀ r, Rt = some r → BndT n r

theorem RelR.transport {Δ : TyEnv} {θ θ' : V → Tm} {n m : Nat} {Rt : Option Tm} {R : Option Ty}
    (h : RelR θ n Rt R) (hθ : Names Δ θ) (hθ' : Names Δ θ') (ha : Agree θ θ' n) (hnm : n ≤ m) :
    RelR θ' m Rt R := by
  refine ⟨?_, fun r hr => (h.2 r hr).mono hnm⟩
  cases Rt with
  | none => exact h.1
  | some r =>
    rw [← h.1]
    simp only [Option.map_some, bind_agree hθ hθ' ha (h.2 r rfl)]

theorem binAlts_bnd {op : BinOp} {a b : Tm} {n : Nat} (ha : BndT n a) (hb : BndT n b) :
    ∀ alt ∈ binAlts op a b, (∀ e ∈ alt.1, BndT n e.1 ∧ BndT n e.2) ∧ BndT n alt.2 := by
  intro alt h
  cases op <;> simp only [binAlts, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl <;>
    refine ⟨fun e he => ?_, BndT.leaf⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he <;>
    first
    | (rcases he with rfl | rfl <;> exact ⟨by assumption, BndT.leaf⟩)
    | (subst he; exact ⟨by assumption, BndT.leaf⟩)
    | cases he

theorem binAlts_complete {θ : V → Tm} {op : BinOp} {a b : Tm} {tl tr t : Ty}
    (hbt : BinTy op tl tr t) (ha : a.bind θ = enc tl) (hb : b.bind θ = enc tr) :
    ∃ alt ∈ binAlts op a b, SatE θ alt.1 ∧ alt.2.bind θ = enc t := by
  have two : ∀ {c d : Tm}, a.bind θ = c.bind θ → b.bind θ = d.bind θ → SatE θ [(a, c), (b, d)] := by
    intro c d h1 h2 e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption
  have one : ∀ {x c : Tm}, x.bind θ = c.bind θ → SatE θ [(x, c)] := by
    intro x c h e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact h
  cases hbt with
  | addInt => exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | addStrL _ => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, one ha, rfl⟩
  | addStrR _ =>
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), one hb, rfl⟩
  | sub => exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | mul => exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | div => exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | mod => exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | eq => exact ⟨_, List.mem_cons_self, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | ne => exact ⟨_, List.mem_cons_self, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | cmpInt op hop =>
    rcases hop with rfl | rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self, two ha hb, rfl⟩
  | cmpStr op hop =>
    rcases hop with rfl | rfl | rfl | rfl <;>
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, two ha hb, rfl⟩

theorem callAlts_bnd {f r : Tm} {ts : List Tm} {n : Nat} (hf : BndT n f)
    (hts : ∀ t ∈ ts, BndT n t) (hr : BndT n r) :
    ∀ alt ∈ callAlts f ts r, (∀ e ∈ alt.1, BndT n e.1 ∧ BndT n e.2) ∧ BndT n alt.2 := by
  intro alt h
  simp only [callAlts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl) | h
  · refine ⟨?_, hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro e rfl
    exact ⟨hf, BndT.node.mpr ⟨BndT.tList hts, hr⟩⟩
  · exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro e rfl; exact ⟨hf, BndT.leaf⟩,
      BndT.leaf⟩
  · exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro e rfl; exact ⟨hf, BndT.leaf⟩,
      BndT.leaf⟩
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro e rfl; exact ⟨hf, BndT.leaf⟩,
        BndT.leaf⟩
    · cases h

theorem callAlts_complete {θ : V → Tm} {f r : Tm} {ts : List Tm} {tf : Ty} {Ts : List Ty} {t : Ty}
    (hct : CallTy tf Ts t) (hf : f.bind θ = enc tf) (hts : ts.map (·.bind θ) = Ts.map enc)
    (hr : r.bind θ = enc t) :
    ∃ alt ∈ callAlts f ts r, SatE θ alt.1 ∧ alt.2.bind θ = enc t := by
  have one : ∀ {c : Tm}, f.bind θ = c.bind θ → SatE θ [(f, c)] := by
    intro c h e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact h
  have hlen : ts.length = Ts.length := by
    have := congrArg List.length hts; simpa using this
  cases hct with
  | fn ps _ =>
    refine ⟨_, List.mem_cons_self, one ?_, hr⟩
    rw [hf]
    simp only [enc, Tm.bind, tList_bind, hts, hr, encL_eq_tList]
  | print => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, one (by rw [hf]; rfl), rfl⟩
  | println =>
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      one (by rw [hf]; rfl), rfl⟩
  | assert1 u =>
    refine ⟨([(f, .leaf 6)], tNULL), ?_, one (by rw [hf]; rfl), rfl⟩
    simp only [callAlts, List.length_cons, List.length_nil] at hlen ⊢
    simp [hlen]
  | assert2 u w =>
    refine ⟨([(f, .leaf 6)], tNULL), ?_, one (by rw [hf]; rfl), rfl⟩
    simp only [callAlts, List.length_cons, List.length_nil] at hlen ⊢
    simp [hlen]

theorem fnWrap_complete {Δ : TyEnv} {params : List String} {body : List Stmt} {r : Ty}
    (hb : ∀ Rt s θ k, Inv Δ θ s → RelR θ s.n Rt (some r) → KS Δ θ s k →
      srchSeq body Rt s k ≠ none)
    (hr : r = .null ∨ MustExitSeq body) {s : SS} {θ : V → Tm} {k : SS → Tm → Option SS}
    (hI : Inv Δ θ s) (hK : KE Δ θ s (.fn (params.map Δ) r) k) :
    fnWrap params body (srchSeq body) s k ≠ none := by
  obtain ⟨hI₁, ha₁⟩ := hI.fresh (enc r)
  simp only [fnWrap]
  refine hb _ _ _ _ hI₁ ⟨by simp [Tm.bind, upd_self], fun r' h => ?_⟩ ?_
  · cases h; intro m hm; simp [Tm.vars] at hm; show m < s.n + 1; omega
  · intro s₂ θ₂ hI₂ ha₂ hn₂
    have hr₂ : θ₂ (.aux s.n) = enc r := by rw [← ha₂ s.n (by simp)]; exact upd_self _ _ _
    have hE : SatE θ₂ (if mustExitSeqB body then [] else [(.var (.aux s.n), tNULL)]) := by
      split
      · intro _ h; cases h
      · rename_i hm
        have hnull : r = .null := by
          rcases hr with hr | hr
          · exact hr
          · exact absurd (mustExitB_complete.2 _ hr) hm
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        simp [Tm.bind, hr₂, hnull, enc, tNULL]
    obtain ⟨s₃, hu, hI₃, hn₃⟩ := unifyS_complete hI₂ hE (by
      split
      · intro _ h; cases h
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact ⟨fun m hm => by simp [Tm.vars] at hm; simp at hn₂; omega, BndT.leaf⟩)
    dsimp only
    rw [hu]
    simp only [Option.bind_some]
    refine hK s₃ _ θ₂ hI₃ (ha₁.trans ha₂ (by simp)) (by simp at hn₂; omega) ?_ ?_
    · refine BndT.node.mpr ⟨BndT.tList fun t ht => ?_, fun m hm => ?_⟩
      · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact BndT.pvar
      · simp [Tm.vars] at hm; simp at hn₂; omega
    · simp only [Tm.bind, tList_bind, List.map_map, hr₂, enc, encL_eq_tList]
      congr 2
      apply List.map_congr_left
      intro x _
      exact hI₃.names x

abbrev CE (e : Expr) : Prop :=
  ∀ {Δ : TyEnv} {S : List String} {T : Ty}, WtE Δ S e T →
    ∀ (s : SS) (θ : V → Tm) (k : SS → Tm → Option SS), Inv Δ θ s → KE Δ θ s T k →
    srchE e s k ≠ none

abbrev CA (es : List Expr) : Prop :=
  ∀ {Δ : TyEnv} {S : List String} {Ts : List Ty}, WtArgs Δ S es Ts →
    ∀ (s : SS) (θ : V → Tm) (k : SS → List Tm → Option SS), Inv Δ θ s → KA Δ θ s Ts k →
    srchArgs es s k ≠ none

abbrev CS (st : Stmt) : Prop :=
  ∀ {Δ : TyEnv} {S : List String} {R : Option Ty} {L : Bool} {S' : List String},
    WtS Δ S R L st S' →
    ∀ (Rt : Option Tm) (s : SS) (θ : V → Tm) (k : SS → Option SS), Inv Δ θ s →
    RelR θ s.n Rt R → KS Δ θ s k → srchS st Rt s k ≠ none

abbrev CI (o : Option Stmt) : Prop :=
  ∀ {Δ : TyEnv} {S : List String} {R : Option Ty} {L : Bool} {S' : List String},
    WtInit Δ S R L o S' →
    ∀ (Rt : Option Tm) (s : SS) (θ : V → Tm) (k : SS → Option SS), Inv Δ θ s →
    RelR θ s.n Rt R → KS Δ θ s k → srchInit o Rt s k ≠ none

abbrev CO (o : Option Expr) : Prop :=
  ∀ {Δ : TyEnv} {S : List String}, WtEO Δ S o →
    ∀ (s : SS) (θ : V → Tm) (k : SS → Option SS), Inv Δ θ s → KS Δ θ s k →
    srchOptE o s k ≠ none

abbrev CQ (ss : List Stmt) : Prop :=
  ∀ {Δ : TyEnv} {S : List String} {R : Option Ty} {L : Bool} {S' : List String},
    WtSeq Δ S R L ss S' →
    ∀ (Rt : Option Tm) (s : SS) (θ : V → Tm) (k : SS → Option SS), Inv Δ θ s →
    RelR θ s.n Rt R → KS Δ θ s k → srchSeq ss Rt s k ≠ none

abbrev FnC (e : Expr) : Prop := ∀ n ps b, e = .fn n ps b → CQ b

theorem cE_int : ∀ n, CE (.int n) := by
  intro n
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s _ θ hI Agree.rfl' (Nat.le_refl _) BndT.leaf rfl

theorem cE_str : ∀ x, CE (.str x) := by
  intro x
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s _ θ hI Agree.rfl' (Nat.le_refl _) BndT.leaf rfl

theorem cE_bool : ∀ b, CE (.bool b) := by
  intro b
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s _ θ hI Agree.rfl' (Nat.le_refl _) BndT.leaf rfl

theorem cE_null : CE (.null) := by
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s _ θ hI Agree.rfl' (Nat.le_refl _) BndT.leaf rfl

theorem cE_var : ∀ x, CE (.var x) := by
  intro x
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s _ θ hI Agree.rfl' (Nat.le_refl _) BndT.pvar (hI.names x)

theorem cE_assign : ∀ x e, CE e → CE (.assign x e) := by
  intro x e ihE_e
  intro _ _ _ D s θ k hI hK
  cases D with
  | assign _ _ _ _ De =>
    simp only [srchE]
    refine ihE_e De s θ _ hI fun s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ ht => ?_
    obtain ⟨s₂, hu, hI₂, hn₂⟩ := unifyS_one (a := t) (b := pvar x) hI₁ (by simp only [ht, pvar, Tm.bind, hI₁.names x]) (hb₁) (BndT.pvar)
    rw [hu]
    exact hK s₂ _ θ₁ hI₂ ha₁ (by omega) BndT.pvar (hI₂.names x)

theorem cE_binary : ∀ op l r, CE l → CE r → CE (.binary op l r) := by
  intro op l r ihE_l ihE_r
  intro _ _ _ D s θ k hI hK
  cases D with
  | binary _ _ _ _ tl tr _ Dl Dr hbt =>
    simp only [srchE]
    refine ihE_l Dl s θ _ hI fun s₁ τl θ₁ hI₁ ha₁ hn₁ hb₁ hτl => ?_
    refine ihE_r Dr s₁ θ₁ _ hI₁ fun s₂ τr θ₂ hI₂ ha₂ hn₂ hb₂ hτr => ?_
    have hτl' : τl.bind θ₂ = enc tl := by rw [← bind_agree hI₁.names hI₂.names ha₂ hb₁]; exact hτl
    obtain ⟨a, ha, hE, hres⟩ := binAlts_complete hbt hτl' hτr
    refine branch_complete hI₂ ha hE (binAlts_bnd (hb₁.mono hn₂) hb₂)
      fun s₃ τ θ₃ hI₃ ha₃ hn₃ hb₃ hτ => ?_
    exact hK s₃ τ θ₃ hI₃ ((ha₁.trans ha₂ hn₁).trans ha₃ (by omega)) (by omega) hb₃
      (hτ.trans hres)

theorem cE_logical : ∀ op l r, CE l → CE r → CE (.logical op l r) := by
  intro op l r ihE_l ihE_r
  intro _ _ _ D s θ k hI hK
  cases D with
  | logical _ _ _ _ _ _ Dl Dr =>
    simp only [srchE]
    refine ihE_l Dl s θ _ hI fun s₁ τl θ₁ hI₁ ha₁ hn₁ _ _ => ?_
    refine ihE_r Dr s₁ θ₁ _ hI₁ fun s₂ τr θ₂ hI₂ ha₂ hn₂ _ _ => ?_
    exact hK s₂ _ θ₂ hI₂ (ha₁.trans ha₂ hn₁) (by omega) BndT.leaf rfl

theorem cE_neg : ∀ e, CE e → CE (.unary .neg e) := by
  intro e ihE_e
  intro _ _ _ D s θ k hI hK
  cases D with
  | neg _ _ De =>
    simp only [srchE]
    refine ihE_e De s θ _ hI fun s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ ht => ?_
    obtain ⟨s₂, hu, hI₂, hn₂⟩ := unifyS_one (a := t) (b := tINT) hI₁ (by simp only [ht]; rfl) (hb₁) (BndT.leaf)
    rw [hu]
    exact hK s₂ _ θ₁ hI₂ ha₁ (by omega) BndT.leaf rfl

theorem cE_not : ∀ e, CE e → CE (.unary .not e) := by
  intro e ihE_e
  intro _ _ _ D s θ k hI hK
  cases D with
  | not _ _ _ De =>
    simp only [srchE]
    refine ihE_e De s θ _ hI fun s₁ t θ₁ hI₁ ha₁ hn₁ _ _ => ?_
    exact hK s₁ _ θ₁ hI₁ ha₁ hn₁ BndT.leaf rfl

theorem cE_call : ∀ f args, CE f → CA args → CE (.call f args) := by
  intro f args ihE_f ihA_args
  intro _ _ T D s θ k hI hK
  cases D with
  | call _ _ _ tf Ts _ Df _ Da hct =>
    simp only [srchE]
    refine ihE_f Df s θ _ hI fun s₁ τf θ₁ hI₁ ha₁ hn₁ hbf hτf => ?_
    refine ihA_args Da s₁ θ₁ _ hI₁ fun s₂ τs θ₂ hI₂ ha₂ hn₂ hbs hτs => ?_
    obtain ⟨hI₃, ha₃⟩ := hI₂.fresh (enc T)
    have hτf' : τf.bind (upd θ₂ s₂.n (enc T)) = enc tf := by
      rw [← bind_agree hI₁.names hI₃.names (ha₂.trans ha₃ hn₂) hbf]; exact hτf
    have hτs' : τs.map (·.bind (upd θ₂ s₂.n (enc T))) = Ts.map enc := by
      rw [← hτs]
      apply List.map_congr_left
      intro t ht
      exact (bind_agree hI₂.names hI₃.names ha₃ (hbs t ht)).symm
    obtain ⟨a, ha, hE, hres⟩ := callAlts_complete (r := .var (.aux s₂.n)) hct hτf' hτs'
      (by simp [Tm.bind, upd_self])
    refine branch_complete hI₃ ha hE (callAlts_bnd (n := s₂.n + 1) (r := .var (.aux s₂.n))
      ((hbf.mono hn₂).mono (by omega)) (fun t ht => (hbs t ht).mono (by omega))
      (fun m hm => by simp [Tm.vars] at hm; omega)) fun s₄ τ θ₄ hI₄ ha₄ hn₄ hb₄ hτ => ?_
    simp only at hn₄
    exact hK s₄ τ θ₄ hI₄ (((ha₁.trans ha₂ hn₁).trans ha₃ (by omega)).trans ha₄
      (by show s.n ≤ s₂.n + 1; omega)) (by omega) hb₄ (hτ.trans hres)

theorem cE_fn : ∀ name params body, CQ body → CE (.fn name params body) := by
  intro name params body ihQ_body
  intro _ _ _ D s θ k hI hK
  cases D with
  | fn _ _ _ _ r S' Db hr =>
    simp only [srchE]
    exact fnWrap_complete (fun Rt s θ k hI hR hK => ihQ_body Db Rt s θ k hI hR hK)
      hr hI hK

theorem cA_nil : CA ([]) := by
  intro _ _ _ D s θ k hI hK
  cases D; exact hK s [] θ hI Agree.rfl' (Nat.le_refl _) (fun _ h => by cases h) rfl

theorem cA_cons : ∀ e es, CE e → CA es → CA (e :: es) := by
  intro e es ihE_e ihA_es
  intro _ _ _ D s θ k hI hK
  cases D with
  | cons _ _ _ t Ts De Des =>
    simp only [srchArgs]
    refine ihE_e De s θ _ hI fun s₁ τ θ₁ hI₁ ha₁ hn₁ hb₁ hτ => ?_
    refine ihA_es Des s₁ θ₁ _ hI₁ fun s₂ τs θ₂ hI₂ ha₂ hn₂ hbs hτs => ?_
    refine hK s₂ _ θ₂ hI₂ (ha₁.trans ha₂ hn₁) (by omega) ?_ ?_
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hb₁.mono hn₂
      · exact hbs u hu
    · rw [List.map_cons, List.map_cons, hτs, ← bind_agree hI₁.names hI₂.names ha₂ hb₁, hτ]

theorem cS_expr : ∀ e, CE e → CS (.expr e) := by
  intro e ihE_e
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | expr _ _ _ _ _ De =>
    simp only [srchS]
    exact ihE_e De s θ _ hI fun s₁ _ θ₁ hI₁ ha₁ hn₁ _ _ => hK s₁ θ₁ hI₁ ha₁ hn₁

theorem cS_varNull : ∀ x, CS (.varDecl x none) := by
  intro x
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | varNull _ _ _ _ hx =>
    simp only [srchS]
    obtain ⟨s₁, hu, hI₁, hn₁⟩ := unifyS_one (a := pvar x) (b := tNULL) hI (by simp only [pvar, Tm.bind, hI.names x, hx]; rfl) (BndT.pvar) (BndT.leaf)
    rw [hu]
    exact hK s₁ θ hI₁ Agree.rfl' (by omega)

theorem cS_varSome : ∀ x e, CE e → FnC e → CS (.varDecl x (some e)) := by
  intro x e ihE_e ihF_e
  intro Δ _ _ _ _ D Rt s θ k hI hR hK
  simp only [srchS]
  have finish : ∀ s₁ t θ₁, Inv Δ θ₁ s₁ → Agree θ θ₁ s.n → s.n ≤ s₁.n → BndT s₁.n t →
      t.bind θ₁ = (pvar x).bind θ₁ → (unifyS s₁ [(t, pvar x)]).bind k ≠ none := by
    intro s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ ht
    obtain ⟨s₂, hu, hI₂, hn₂⟩ := unifyS_one (a := t) (b := pvar x) hI₁ (by exact ht) (hb₁) (BndT.pvar)
    rw [hu]
    exact hK s₂ θ₁ hI₂ ha₁ (by omega)
  cases D with
  | varInit _ _ _ _ _ De =>
    refine ihE_e De s θ _ hI fun s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ ht => ?_
    exact finish s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ (by rw [ht]; simp [pvar, Tm.bind, hI₁.names x])
  | varRec _ _ _ _ name params body r S'' Db hr hx =>
    simp only [srchE]
    refine fnWrap_complete (fun Rt s θ k hI hR hK => (ihF_e name params body rfl) Db Rt s θ k hI hR hK)
      hr hI fun s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ ht => ?_
    exact finish s₁ t θ₁ hI₁ ha₁ hn₁ hb₁ (by rw [ht]; simp [pvar, Tm.bind, hI₁.names x, hx])

theorem cS_block : ∀ ss, CQ ss → CS (.block ss) := by
  intro ss ihQ_ss
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | block _ _ _ _ _ Ds =>
    simp only [srchS]
    exact ihQ_ss Ds Rt s θ k hI hR hK

theorem cS_if : ∀ c t e, CE c → CS t → CI e → CS (.ifStmt c t e) := by
  intro c t e ihE_c ihS_t ihI_e
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  simp only [srchS]
  cases D with
  | ifSome _ _ _ _ _ e' _ _ _ Dc Dt De =>
    refine ihE_c Dc s θ _ hI fun s₁ _ θ₁ hI₁ ha₁ hn₁ _ _ => ?_
    refine ihS_t Dt Rt s₁ θ₁ _ hI₁ (hR.transport hI.names hI₁.names ha₁ hn₁)
      fun s₂ θ₂ hI₂ ha₂ hn₂ => ?_
    refine ihI_e (.some _ _ _ _ _ De) Rt s₂ θ₂ k hI₂
      ((hR.transport hI.names hI₁.names ha₁ hn₁).transport hI₁.names hI₂.names ha₂ hn₂)
      fun s₃ θ₃ hI₃ ha₃ hn₃ => ?_
    exact hK s₃ θ₃ hI₃ ((ha₁.trans ha₂ hn₁).trans ha₃ (by omega)) (by omega)
  | ifNone _ _ _ _ _ _ _ Dc Dt =>
    refine ihE_c Dc s θ _ hI fun s₁ _ θ₁ hI₁ ha₁ hn₁ _ _ => ?_
    refine ihS_t Dt Rt s₁ θ₁ _ hI₁ (hR.transport hI.names hI₁.names ha₁ hn₁)
      fun s₂ θ₂ hI₂ ha₂ hn₂ => ?_
    simp only [srchInit]
    exact hK s₂ θ₂ hI₂ (ha₁.trans ha₂ hn₁) (by omega)

theorem cS_while : ∀ c b, CE c → CS b → CS (.whileStmt c b) := by
  intro c b ihE_c ihS_b
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | whileS _ _ _ _ _ _ _ Dc Db =>
    simp only [srchS]
    refine ihE_c Dc s θ _ hI fun s₁ _ θ₁ hI₁ ha₁ hn₁ _ _ => ?_
    refine ihS_b Db Rt s₁ θ₁ _ hI₁ (hR.transport hI.names hI₁.names ha₁ hn₁)
      fun s₂ θ₂ hI₂ ha₂ hn₂ => ?_
    exact hK s₂ θ₂ hI₂ (ha₁.trans ha₂ hn₁) (by omega)

theorem cS_for : ∀ init cnd step b, CI init → CO cnd → CO step → CS b → CS (.forStmt init cnd step b) := by
  intro init cnd step b ihI_init ihO_cnd ihO_step ihS_b
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | forS _ _ _ _ _ _ _ _ _ Di Dc Ds Db =>
    simp only [srchS]
    refine ihI_init Di Rt s θ _ hI hR fun s₁ θ₁ hI₁ ha₁ hn₁ => ?_
    refine ihO_cnd Dc s₁ θ₁ _ hI₁ fun s₂ θ₂ hI₂ ha₂ hn₂ => ?_
    refine ihO_step Ds s₂ θ₂ _ hI₂ fun s₃ θ₃ hI₃ ha₃ hn₃ => ?_
    have hR₃ := ((hR.transport hI.names hI₁.names ha₁ hn₁).transport hI₁.names hI₂.names ha₂
      hn₂).transport hI₂.names hI₃.names ha₃ hn₃
    refine ihS_b Db Rt s₃ θ₃ _ hI₃ hR₃ fun s₄ θ₄ hI₄ ha₄ hn₄ => ?_
    exact hK s₄ θ₄ hI₄ (((ha₁.trans ha₂ hn₁).trans ha₃ (by omega)).trans ha₄ (by omega))
      (by omega)

theorem cS_retSome : ∀ e, CE e → CS (.ret (some e)) := by
  intro e ihE_e
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | ret _ _ _ t De =>
    cases Rt with
    | none => exact absurd hR.1 (by simp)
    | some r =>
      have hr : r.bind θ = enc t := by simpa using hR.1
      have hbr := hR.2 r rfl
      simp only [srchS]
      refine ihE_e De s θ _ hI fun s₁ τ θ₁ hI₁ ha₁ hn₁ hb₁ hτ => ?_
      obtain ⟨s₂, hu, hI₂, hn₂⟩ := unifyS_one (a := τ) (b := r) hI₁
        (by rw [hτ, ← bind_agree hI.names hI₁.names ha₁ hbr, hr]) hb₁ (hbr.mono hn₁)
      rw [hu]
      exact hK s₂ θ₁ hI₂ ha₁ (by omega)

theorem cS_retNone : CS (.ret none) := by
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | retNull =>
    cases Rt with
    | none => exact absurd hR.1 (by simp)
    | some r =>
      have hr : r.bind θ = enc .null := by simpa using hR.1
      simp only [srchS]
      obtain ⟨s₁, hu, hI₁, hn₁⟩ := unifyS_one (a := r) (b := tNULL) hI (by simp only [hr]; rfl) (hR.2 r rfl) (BndT.leaf)
      rw [hu]
      exact hK s₁ θ hI₁ Agree.rfl' (by omega)

theorem cS_brk : CS (.brk) := by
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D; exact hK s θ hI Agree.rfl' (Nat.le_refl _)

theorem cS_cont : CS (.cont) := by
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D; exact hK s θ hI Agree.rfl' (Nat.le_refl _)

theorem cI_none : CI (none) := by
  intro _ _ _ _ _ _ Rt s θ k hI _ hK
  exact hK s θ hI Agree.rfl' (Nat.le_refl _)

theorem cI_some : ∀ st, CS st → CI (some st) := by
  intro st ihS_st
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | some _ _ _ _ _ Ds => exact ihS_st Ds Rt s θ k hI hR hK

theorem cO_none : CO (none) := by
  intro _ _ _ s θ k hI hK
  exact hK s θ hI Agree.rfl' (Nat.le_refl _)

theorem cO_some : ∀ e, CE e → CO (some e) := by
  intro e ihE_e
  intro _ _ D s θ k hI hK
  cases D with
  | some _ _ _ De =>
    simp only [srchOptE]
    exact ihE_e De s θ _ hI fun s₁ _ θ₁ hI₁ ha₁ hn₁ _ _ => hK s₁ θ₁ hI₁ ha₁ hn₁

theorem cQ_nil : CQ ([]) := by
  intro _ _ _ _ _ _ Rt s θ k hI _ hK
  exact hK s θ hI Agree.rfl' (Nat.le_refl _)

theorem cQ_cons : ∀ st ss, CS st → CQ ss → CQ (st :: ss) := by
  intro st ss ihS_st ihQ_ss
  intro _ _ _ _ _ D Rt s θ k hI hR hK
  cases D with
  | cons _ _ _ _ _ _ _ Ds Dss =>
    simp only [srchSeq]
    refine ihS_st Ds Rt s θ _ hI hR fun s₁ θ₁ hI₁ ha₁ hn₁ => ?_
    refine ihQ_ss Dss Rt s₁ θ₁ k hI₁ (hR.transport hI.names hI₁.names ha₁ hn₁)
      fun s₂ θ₂ hI₂ ha₂ hn₂ => ?_
    exact hK s₂ θ₂ hI₂ (ha₁.trans ha₂ hn₁) (by omega)

mutual

theorem completeE : (e : Expr) → CE e ∧ FnC e
  | .int n => ⟨cE_int n, fun _ _ _ h => by cases h⟩
  | .str x => ⟨cE_str x, fun _ _ _ h => by cases h⟩
  | .bool b => ⟨cE_bool b, fun _ _ _ h => by cases h⟩
  | .null => ⟨cE_null, fun _ _ _ h => by cases h⟩
  | .var x => ⟨cE_var x, fun _ _ _ h => by cases h⟩
  | .assign x e => ⟨cE_assign x e (completeE e).1, fun _ _ _ h => by cases h⟩
  | .binary op l r =>
    ⟨cE_binary op l r (completeE l).1 (completeE r).1, fun _ _ _ h => by cases h⟩
  | .logical op l r =>
    ⟨cE_logical op l r (completeE l).1 (completeE r).1, fun _ _ _ h => by cases h⟩
  | .unary .neg e => ⟨cE_neg e (completeE e).1, fun _ _ _ h => by cases h⟩
  | .unary .not e => ⟨cE_not e (completeE e).1, fun _ _ _ h => by cases h⟩
  | .call f args => ⟨cE_call f args (completeE f).1 (completeArgs args), fun _ _ _ h => by cases h⟩
  | .fn name params body =>
    ⟨cE_fn name params body (completeSeq body), fun _ _ _ h => by cases h; exact completeSeq body⟩

theorem completeArgs : (es : List Expr) → CA es
  | [] => cA_nil
  | e :: es => cA_cons e es (completeE e).1 (completeArgs es)

theorem completeS : (st : Stmt) → CS st
  | .expr e => cS_expr e (completeE e).1
  | .varDecl x none => cS_varNull x
  | .varDecl x (some e) => cS_varSome x e (completeE e).1 (completeE e).2
  | .block ss => cS_block ss (completeSeq ss)
  | .ifStmt c t e => cS_if c t e (completeE c).1 (completeS t) (completeInit e)
  | .whileStmt c b => cS_while c b (completeE c).1 (completeS b)
  | .forStmt init cnd step b =>
    cS_for init cnd step b (completeInit init) (completeOptE cnd) (completeOptE step) (completeS b)
  | .ret (some e) => cS_retSome e (completeE e).1
  | .ret none => cS_retNone
  | .brk => cS_brk
  | .cont => cS_cont

theorem completeInit : (o : Option Stmt) → CI o
  | none => cI_none
  | some st => cI_some st (completeS st)

theorem completeOptE : (o : Option Expr) → CO o
  | none => cO_none
  | some e => cO_some e (completeE e).1

theorem completeSeq : (ss : List Stmt) → CQ ss
  | [] => cQ_nil
  | st :: ss => cQ_cons st ss (completeS st) (completeSeq ss)

end

theorem inv_s₀ {Δ : TyEnv} (hB : BuiltinsTyped Δ) :
    Inv Δ (fun v => match v with | .name x => enc (Δ x) | .aux _ => .leaf 0) s₀ := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, fun _ => rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩
  · intro p hp
    simp only [s₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp [hB.print, enc, Tm.bind]
    · simp [hB.println, enc, Tm.bind]
    · simp [hB.assert, enc, Tm.bind]
  · simp [s₀, Distinct, dom]
  · intro p hp w hw
    simp only [s₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [Tm.vars] at hw
  · intro m hm
    simp [s₀, varsS, Tm.vars] at hm

theorem pickMin_none {α : Type} {f : α → Nat} : ∀ {l : List α}, pickMin f l = none → l = []
  | [], _ => rfl
  | a :: as, h => by
    simp only [pickMin] at h
    split at h
    · cases h
    · split at h <;> cases h

theorem firstSome_some {α β : Type} {f : α → Option β} {r : β} :
    ∀ {l : List α}, firstSome f l = some r → ∃ a ∈ l, f a = some r
  | [], h => by cases h
  | a :: as, h => by
    simp only [firstSome] at h
    split at h
    · rename_i r' hr; cases h; exact ⟨a, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, h⟩ := firstSome_some h
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem firstSome_ne_none {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {a : α}, a ∈ l → f a ≠ none → firstSome f l ≠ none
  | [], _, h, _ => by cases h
  | b :: bs, a, h, hf => by
    simp only [firstSome]
    split
    · simp
    · rename_i hb
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd hb hf
      · exact firstSome_ne_none h hf

theorem resolve_sound (ds : List Disj) (σ σ' : Subst) (h : resolve σ ds = some σ') :
    (Idem σ → Idem σ') ∧ ∀ θ, Sat θ σ' → Sat θ σ ∧ SatP θ ds := by
  rw [resolve] at h
  split at h
  · cases h
  · split at h
    · rename_i hp
      cases h
      rw [pickMin_none hp]
      exact ⟨id, fun θ hs => ⟨hs, fun _ h => by cases h⟩⟩
    · rename_i d hp
      have hd := pickMin_mem hp
      obtain ⟨E, hE, h₁⟩ := firstSome_some h
      obtain ⟨σ₁, hu, h₂⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨hi, hs⟩ := resolve_sound (ds.erase d) σ₁ σ' h₂
      refine ⟨fun h => hi (unifyTop_idem h hu), fun θ hθ => ?_⟩
      obtain ⟨hσ₁, hP⟩ := hs θ hθ
      obtain ⟨hσ, hEθ⟩ := unifyTop_sound hu hσ₁
      refine ⟨hσ, fun d' hd' => ?_⟩
      by_cases hdd : d' = d
      · subst hdd; exact ⟨E, (List.mem_filter.mp hE).1, hEθ⟩
      · exact hP d' ((List.mem_erase_of_ne hdd).mpr hd')
termination_by ds.length
decreasing_by
  rw [List.length_erase_of_mem hd]; have := List.length_pos_of_mem hd; omega

theorem resolve_complete (ds : List Disj) (σ : Subst) (θ : V → Tm) (hi : Idem σ)
    (hs : Sat θ σ) (hP : SatP θ ds) : resolve σ ds ≠ none := by
  have hviable : ∀ d ∈ ds, ∃ E ∈ d.filter (fun E => (unifyTop σ E).isSome), SatE θ E := by
    intro d hd
    obtain ⟨E, hE, hsat⟩ := hP d hd
    obtain ⟨σ', hσ', _⟩ := unifyTop_complete hi hs hsat
    exact ⟨E, List.mem_filter.mpr ⟨hE, by simp [hσ']⟩, hsat⟩
  rw [resolve]
  split
  · rename_i hany
    obtain ⟨d, hd, hz⟩ := List.any_eq_true.mp hany
    obtain ⟨E, hE, _⟩ := hviable d hd
    simp only [nViable, beq_iff_eq, List.length_eq_zero_iff] at hz
    rw [hz] at hE; cases hE
  · split
    · simp
    · rename_i d hp
      have hd := pickMin_mem hp
      obtain ⟨E, hE, hsat⟩ := hviable d hd
      obtain ⟨σ₁, hu, hs₁⟩ := unifyTop_complete hi hs hsat
      refine firstSome_ne_none hE ?_
      rw [hu]
      exact resolve_complete (ds.erase d) σ₁ θ (unifyTop_idem hi hu) hs₁
        fun d' hd' => hP d' (List.mem_of_mem_erase hd')
termination_by ds.length
decreasing_by
  rw [List.length_erase_of_mem hd]; have := List.length_pos_of_mem hd; omega

theorem search_complete {Δ : TyEnv} {p : Program} (h : WellTyped Δ p) :
    ∃ s, searchProg p = some s := by
  obtain ⟨S', D⟩ := h.body
  have := completeSeq p D none s₀ _
    (fun s => (resolve s.σ s.pend).map fun σ => { s with σ := σ, pend := [] })
    (inv_s₀ h.builtins) ⟨rfl, fun _ h => by cases h⟩
    (fun s' θ' hI' _ _ => by
      simpa using resolve_complete s'.pend s'.σ θ' hI'.idem hI'.sat hI'.pend)
  exact Option.ne_none_iff_exists'.mp this

theorem search_sound {Δ : TyEnv} {p : Program} (h : WellTyped Δ p) {s : SS}
    (hs : searchProg p = some s) : WellTyped (envOfSubst s.σ) p := by
  obtain ⟨S', D⟩ := h.body
  obtain ⟨s', hs', st⟩ := soundSeq p D none s₀ _ s hs
  obtain ⟨σ', hr, rfl⟩ := Option.map_eq_some_iff.mp hs'
  obtain ⟨hri, hrs⟩ := resolve_sound s'.pend s'.σ σ' hr
  have hidem : Idem σ' := hri (st.idem (inv_s₀ h.builtins).idem)
  obtain ⟨hσ, hP⟩ := hrs (canon σ') (canon_sat hidem)
  obtain ⟨hs₀, hp⟩ := st.sat (canon σ') hσ hP
  have hb : ∀ x c, (Unify.V.name x, Tm.leaf c) ∈ s₀.σ → envOfSubst σ' x = dec (.leaf c) := by
    intro x c hm
    have := hs₀ _ hm
    simp only [Tm.bind] at this
    simp only [envOfSubst, this]
  exact ⟨⟨hb "print" 4 (by simp [s₀]), hb "println" 5 (by simp [s₀]),
    hb "assert" 6 (by simp [s₀])⟩, S', hp⟩

end Vsa.While.Types
