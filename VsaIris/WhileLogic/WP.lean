import VsaIris.WhileLogic.WPGen

namespace Vsa.While.Logic

open Iris OFE CMRA BI Vsa.While

abbrev wpE (d env : Nat) (e : Expr) (Φ : Value → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' v => EvalE σ d env e σ' v) Φ

abbrev wpArgs (d env : Nat) (es : List Expr) (Φ : List Value → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' vs => EvalArgs σ d env es σ' vs) Φ

abbrev wpCall (d : Nat) (fv : Value) (vs : List Value) (Φ : Value → vProp) : vProp :=
  wpR 0 (fun σ σ' v => Call σ d fv vs σ' v) Φ

abbrev wpS (d env : Nat) (s : Stmt) (Φ : Status → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' st => ExecS σ d env s σ' st) Φ

abbrev wpSeq (d env : Nat) (ss : List Stmt) (Φ : Status → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' st => ExecSeq σ d env ss σ' st) Φ

abbrev wpGet (env : Nat) (x : String) (Φ : Value → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' v => σ' = σ ∧ σ.store.get? env x = some v) Φ

abbrev wpSet (env : Nat) (x : String) (v : Value) (Ψ : vProp) : vProp :=
  wpR (env + 1) (fun σ σ' (_ : Unit) => σ.store.set? env x v = some σ'.store ∧ σ'.out = σ.out)
    (fun _ => Ψ)

abbrev wpDef (env : Nat) (x : String) (v : Value) (Ψ : vProp) : vProp :=
  wpR (env + 1) (fun σ σ' (_ : Unit) => σ' = ⟨σ.store.define env x v, σ.out⟩) (fun _ => Ψ)

abbrev wpBin (op : BinOp) (lv rv : Value) (Φ : Value → vProp) : vProp :=
  wpR 0 (fun σ σ' v => σ' = σ ∧ binOpSem σ.store op lv rv = some v) Φ

section access

variable {env p : Nat} {x : String} {v v0 : Value} {F : Frame}

theorem wp_get_here {Φ : Value → vProp} (hx : F.find x = some v) :
    iprop(env ↦f F ∧ Φ v) ⊢ wpGet env x Φ :=
  wpR_read (m := singF env F) fun _ _ _ _ h =>
    ⟨rfl, Store.get?_here (rep_frame h (singF_at env F)).1 hx⟩

theorem wp_get_parent {Φ : Value → vProp} (hx : F.find x = none) (hp : F.parent = some p) :
    iprop(env ↦f F ∧ wpGet p x Φ) ⊢ wpGet env x Φ := by
  intro n y H σ rf hwf hlo hrep
  obtain ⟨hm, hW⟩ := and_holds.mp H
  obtain ⟨z, hz⟩ := ownM_holds.mp hm
  have hrep' : abs σ = singF env F • (z • rf) := by rw [hrep, hz, assoc']
  have hF := (rep_frame hrep' (singF_at env F)).1
  have hpe := hwf.parent_lt env F p hF hp
  obtain ⟨σ', a, r', ⟨hσ, hget⟩, hwf', hsz, hrep'', hΦ⟩ :=
    hW σ rf hwf (by have := Store.lt_size_of_getElem? hF; omega) hrep
  exact ⟨σ', a, r', ⟨hσ, by rw [Store.get?_parent hwf hF hx hp]; exact hget⟩,
    hwf', hsz, hrep'', hΦ⟩

theorem step_frame {σ σ' : St} {w : Res} {a : Nat} {F F' : Frame}
    (h : abs σ = singF a F • w)
    (hb : ∀ b, b ≠ a → σ'.store.frames[b]? = σ.store.frames[b]?)
    (ha : σ'.store.frames[a]? = some F')
    (hc : σ'.store.closures = σ.store.closures) (ho : σ'.out = σ.out) :
    abs σ' = singF a F' • w := by
  rw [← singF_setF a F F']
  exact rep_setF h (rep_frame h (singF_at a F)).2 hb ha hc ho

theorem wp_set_here_with {Rest Ψ : vProp} (hx : F.find x = some v0)
    (hK : iprop(env ↦f F.setVar x v ∗ Rest) ⊢ Ψ) :
    iprop(env ↦f F ∗ Rest) ⊢ wpSet env x v Ψ := by
  refine wpR_prim (m := singF env F) (Q := fun _ => env ↦f F.setVar x v) ?_ (fun _ => hK)
  intro σ w hwf _ h
  have hF := (rep_frame h (singF_at env F)).1
  let σ' : St := ⟨{ σ.store with frames := σ.store.frames.modify env (·.setVar x v) }, σ.out⟩
  refine ⟨σ', (), singF env (F.setVar x v), ⟨?_, rfl⟩, hwf.modify env _ (fun _ => rfl),
    by simp [σ'], ?_, fun n h => ownM_self _ n h⟩
  · exact Store.set?_here hF hx
  · refine step_frame h (fun b hb => ?_) ?_ rfl rfl
    · simp only [σ', Array.getElem?_modify]; simp [Ne.symm hb]
    · simp [σ', Array.getElem?_modify, hF]

theorem wp_set_here {Ψ : vProp} (hx : F.find x = some v0) :
    iprop(env ↦f F ∗ (env ↦f F.setVar x v -∗ Ψ)) ⊢ wpSet env x v Ψ :=
  wp_set_here_with hx (by iintro ⟨H1, H2⟩; iapply H2; iexact H1)

theorem wp_set_parent {Ψ : vProp} (hx : F.find x = none) (hp : F.parent = some p) :
    iprop(env ↦f F ∧ wpSet p x v Ψ) ⊢ wpSet env x v Ψ := by
  intro n y H σ rf hwf hlo hrep
  obtain ⟨hm, hW⟩ := and_holds.mp H
  obtain ⟨z, hz⟩ := ownM_holds.mp hm
  have hrep' : abs σ = singF env F • (z • rf) := by rw [hrep, hz, assoc']
  have hF := (rep_frame hrep' (singF_at env F)).1
  have hpe := hwf.parent_lt env F p hF hp
  obtain ⟨σ', a, r', ⟨hset, hout⟩, hwf', hsz, hrep'', hΦ⟩ :=
    hW σ rf hwf (by have := Store.lt_size_of_getElem? hF; omega) hrep
  exact ⟨σ', a, r', ⟨by rw [Store.set?_parent hwf hF hx hp]; exact hset, hout⟩,
    hwf', hsz, hrep'', hΦ⟩

theorem wp_def_with {Rest Ψ : vProp} (hK : iprop(env ↦f F.defVar x v ∗ Rest) ⊢ Ψ) :
    iprop(env ↦f F ∗ Rest) ⊢ wpDef env x v Ψ := by
  refine wpR_prim (m := singF env F) (Q := fun _ => env ↦f F.defVar x v) ?_ (fun _ => hK)
  intro σ w hwf _ h
  have hF := (rep_frame h (singF_at env F)).1
  refine ⟨⟨σ.store.define env x v, σ.out⟩, (), singF env (F.defVar x v), rfl,
    hwf.define env x v, by simp [Store.size_define], ?_, fun n h => ownM_self _ n h⟩
  refine step_frame h (fun b hb => ?_) ?_ rfl rfl
  · simp only [Store.frames_define]; simp [Ne.symm hb]
  · simp [Store.frames_define, hF]

theorem wp_def {Ψ : vProp} :
    iprop(env ↦f F ∗ (env ↦f F.defVar x v -∗ Ψ)) ⊢ wpDef env x v Ψ :=
  wp_def_with (by iintro ⟨H1, H2⟩; iapply H2; iexact H1)

end access

section expr

variable {d env : Nat}

theorem wp_int {Φ : Value → vProp} (n : Int) : Φ (.int n) ⊢ wpE d env (.int n) Φ :=
  wpR_ret fun σ => EvalE.int σ d env n

theorem wp_str {Φ : Value → vProp} (s : String) : Φ (.str s) ⊢ wpE d env (.str s) Φ :=
  wpR_ret fun σ => EvalE.str σ d env s

theorem wp_bool {Φ : Value → vProp} (b : Bool) : Φ (.bool b) ⊢ wpE d env (.bool b) Φ :=
  wpR_ret fun σ => EvalE.bool σ d env b

theorem wp_null {Φ : Value → vProp} : Φ .null ⊢ wpE d env .null Φ :=
  wpR_ret fun σ => EvalE.null σ d env

theorem wp_var {Φ : Value → vProp} (x : String) : wpGet env x Φ ⊢ wpE d env (.var x) Φ :=
  wpR_weaken (Nat.le_refl _) fun σ _ v ⟨h1, h2⟩ => h1 ▸ EvalE.var σ d env x v h2

theorem wp_assign {Φ : Value → vProp} (x : String) (e : Expr) :
    wpE d env e (fun v => wpSet env x v (Φ v)) ⊢ wpE d env (.assign x e) Φ := by
  refine wpR_bind' (R2 := fun v σ σ' w => ∃ u : Unit,
      (σ.store.set? env x v = some σ'.store ∧ σ'.out = σ.out) ∧ w = (fun _ => v) u)
    (Nat.le_refl _) (fun v => wpR_map) ?_
  rintro σ σ1 ⟨st2, out2⟩ v w hE ⟨_, ⟨hset, hout⟩, hw⟩
  simp only at hset hout hw; subst hout; rw [hw]
  exact EvalE.assign σ d env x e σ1 v st2 hE hset

theorem wp_binary {Φ : Value → vProp} (op : BinOp) (l r : Expr) :
    wpE d env l (fun lv => wpE d env r (fun rv => wpBin op lv rv Φ)) ⊢
      wpE d env (.binary op l r) Φ := by
  refine wpR_bind' (R2 := fun lv σ σ2 v => ∃ σ1 rv, EvalE σ d env r σ1 rv ∧
      σ2 = σ1 ∧ binOpSem σ1.store op lv rv = some v) (Nat.le_refl _)
    (fun lv => wpR_bind (Nat.zero_le _) fun σ σ1 σ2 rv v h1 ⟨h2, h3⟩ => ⟨σ1, rv, h1, h2, h3⟩) ?_
  rintro σ σ1 σ2 lv v hl ⟨σm, rv, hr, hσ, hop⟩
  subst σ2
  exact EvalE.binary σ d env op l r σ1 σm lv rv v hl hr hop

theorem wp_bin {Φ : Value → vProp} {op : BinOp} {lv rv v : Value}
    (h : ∀ s, binOpSem s op lv rv = some v) : Φ v ⊢ wpBin op lv rv Φ :=
  wpR_ret fun _ => ⟨rfl, h _⟩

theorem wp_or {Φ : Value → vProp} (l r : Expr) :
    wpE d env l (fun lv => bif lv.truthy then Φ (.bool true)
      else wpE d env r (fun rv => Φ (.bool rv.truthy))) ⊢
    wpE d env (.logical .or l r) Φ := by
  refine wpR_bind' (R2 := fun lv σ σ1 v => (lv.truthy = true ∧ σ1 = σ ∧ v = .bool true) ∨
      (lv.truthy = false ∧ ∃ rv, EvalE σ d env r σ1 rv ∧ v = .bool rv.truthy))
    (Nat.le_refl _) (fun lv => ?_) ?_
  · cases ht : lv.truthy
    · exact wpR_map.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inr ⟨rfl, h⟩)
    · exact wpR_ret (Φ := Φ) (a := Value.bool _) fun _ => Or.inl ⟨rfl, rfl, rfl⟩
  · rintro σ σ1 σ2 lv v hl (⟨ht, hσ, hv⟩ | ⟨ht, rv, hr, hv⟩) <;> subst v
    · subst σ2; exact EvalE.orTrue σ d env l r σ1 lv hl ht
    · exact EvalE.orFalse σ d env l r σ1 σ2 lv rv hl ht hr

theorem wp_and {Φ : Value → vProp} (l r : Expr) :
    wpE d env l (fun lv => bif lv.truthy then wpE d env r (fun rv => Φ (.bool rv.truthy))
      else Φ (.bool false)) ⊢
    wpE d env (.logical .and l r) Φ := by
  refine wpR_bind' (R2 := fun lv σ σ1 v => (lv.truthy = false ∧ σ1 = σ ∧ v = .bool false) ∨
      (lv.truthy = true ∧ ∃ rv, EvalE σ d env r σ1 rv ∧ v = .bool rv.truthy))
    (Nat.le_refl _) (fun lv => ?_) ?_
  · cases ht : lv.truthy
    · exact wpR_ret (Φ := Φ) (a := Value.bool _) fun _ => Or.inl ⟨rfl, rfl, rfl⟩
    · exact wpR_map.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inr ⟨rfl, h⟩)
  · rintro σ σ1 σ2 lv v hl (⟨ht, hσ, hv⟩ | ⟨ht, rv, hr, hv⟩) <;> subst v
    · subst σ2; exact EvalE.andFalse σ d env l r σ1 lv hl ht
    · exact EvalE.andTrue σ d env l r σ1 σ2 lv rv hl ht hr

theorem wp_neg {Φ : Value → vProp} (e : Expr) :
    wpE d env e (fun v => match v with
      | .int n => Φ (.int (wrap64 (-n)))
      | _ => iprop(False)) ⊢
    wpE d env (.unary .neg e) Φ := by
  refine wpR_bind' (R2 := fun v σ σ1 w => ∃ n, v = .int n ∧ σ1 = σ ∧ w = .int (wrap64 (-n)))
    (Nat.le_refl _) (fun v => ?_) ?_
  · cases v with
    | int n =>
      exact wpR_ret (Φ := Φ) (a := .int (wrap64 (-n))) fun _ => ⟨n, rfl, rfl, rfl⟩
    | _ => exact wpR_false
  · rintro σ σ1 σ2 v w he ⟨n, hv, hσ, hw⟩
    subst v σ2 w
    exact EvalE.neg σ d env e σ1 n he

theorem wp_not {Φ : Value → vProp} (e : Expr) :
    wpE d env e (fun v => Φ (.bool (!v.truthy))) ⊢ wpE d env (.unary .not e) Φ :=
  wpR_map.trans (wpR_weaken (Nat.le_refl _) fun σ σ1 _ ⟨v, he, h⟩ =>
    h ▸ EvalE.not σ d env e σ1 v he)

theorem wp_args_nil {Φ : List Value → vProp} : Φ [] ⊢ wpArgs d env [] Φ :=
  wpR_ret fun σ => EvalArgs.nil σ d env

theorem wp_args_cons {Φ : List Value → vProp} (e : Expr) (es : List Expr) :
    wpE d env e (fun v => wpArgs d env es (fun vs => Φ (v :: vs))) ⊢
      wpArgs d env (e :: es) Φ := by
  refine wpR_bind' (R2 := fun v σ σ1 ws => ∃ vs, EvalArgs σ d env es σ1 vs ∧ ws = v :: vs)
    (Nat.le_refl _) (fun v => wpR_map) ?_
  rintro σ σ1 σ2 v ws he ⟨vs, hes, hw⟩
  subst hw
  exact EvalArgs.cons σ d env e es σ1 σ2 v vs he hes

theorem wp_call {Φ : Value → vProp} (f : Expr) (args : List Expr)
    (hlen : args.length ≤ maxArgs) :
    wpE d env f (fun fv => wpArgs d env args (fun vs => wpCall d fv vs Φ)) ⊢
      wpE d env (.call f args) Φ := by
  refine wpR_bind' (R2 := fun fv σ σ2 v => ∃ σ1 vs, EvalArgs σ d env args σ1 vs ∧
      Call σ1 d fv vs σ2 v) (Nat.le_refl _)
    (fun fv => wpR_bind (Nat.zero_le _) fun σ σ1 σ2 vs v h1 h2 => ⟨σ1, vs, h1, h2⟩) ?_
  rintro σ σ1 σ3 fv v hf ⟨σ2, vs, hargs, hcall⟩
  exact EvalE.call σ d env f args σ1 σ2 σ3 fv vs v hf hlen hargs hcall

theorem wp_fn_with {Φ : Value → vProp} {Rest : vProp} (name : Option String)
    (params : List String) (body : List Stmt)
    (hK : ∀ c, iprop(c ↦c ⟨env, name, params, body⟩ ∗ Rest) ⊢ Φ (.closure c)) :
    Rest ⊢ wpE d env (.fn name params body) Φ := by
  have hsplit : Rest ⊢ iprop(UPred.ownM (UCMRA.unit : Res) ∗ Rest) := by
    iintro H; isplitr [H]
    · iapply (UPred.ownM_unit' (M := Res)).mpr; itrivial
    · iexact H
  refine hsplit.trans (wpR_prim (m := UCMRA.unit)
    (Q := fun a => match a with
      | .closure c => c ↦c ⟨env, name, params, body⟩
      | _ => iprop(False)) ?_ ?_)
  · intro σ w hwf hlo h
    let cd : ClosureData := ⟨env, name, params, body⟩
    let c := σ.store.closures.size
    have h' : abs σ = w := by rw [h]; exact UCMRA.unit_left_id
    have hw : abs σ = UCMRA.unit • w := h
    have hfresh : σ.store.closures[c]? = none := by simp [c]
    refine ⟨⟨(σ.store.allocClosure cd).1, σ.out⟩, .closure c, singC c cd,
      EvalE.fn σ d env name params body _ c rfl, hwf.allocClosure (Nat.lt_of_succ_le hlo),
      Nat.le_refl _, ?_, fun n h => ownM_self _ n h⟩
    have := rep_setC (σ' := ⟨(σ.store.allocClosure cd).1, σ.out⟩) (r := UCMRA.unit) (c := c)
      (cd := cd) hw (rep_freshC hw hfresh).2
      (fun b hb => by simp [Store.allocClosure, Array.getElem?_push, c, hb])
      (by simp [Store.allocClosure, c]) rfl rfl
    rw [this, setC_eq_sing_op _ _ _ rfl, unit_right_id]
  · intro a
    cases a with
    | closure c => exact hK c
    | _ => exact BI.sep_elim_left.trans BI.false_elim

theorem wp_fn {Φ : Value → vProp} (name : Option String) (params : List String)
    (body : List Stmt) :
    iprop(∀ c, c ↦c ⟨env, name, params, body⟩ -∗ Φ (.closure c)) ⊢
      wpE d env (.fn name params body) Φ :=
  wp_fn_with name params body fun c => by
    iintro ⟨Hc, H⟩; iapply H; iexact Hc

end expr

def retK (Φ : Value → vProp) : Status → vProp
  | .normal => Φ .null
  | .ret v => Φ v
  | _ => iprop(False)

def NoClosure (vs : List Value) : Prop := ∀ v ∈ vs, ∀ c, v ≠ .closure c

def printArgs₀ (vs : List Value) : String := printArgs ⟨#[], #[]⟩ vs

theorem printArgs_noClosure {vs : List Value} (h : NoClosure vs) (s : Store) :
    printArgs s vs = printArgs₀ vs := by
  unfold printArgs₀ printArgs
  congr 1
  refine List.map_congr_left fun v hv => ?_
  cases v with
  | closure c => exact absurd rfl (h _ hv c)
  | native f => cases f <;> rfl
  | _ => rfl

theorem step_out {σ : St} {w : Res} {o : String} (h : abs σ = singO o • w) (o' : String) :
    σ.out = o ∧ abs ⟨σ.store, o'⟩ = singO o' • w := by
  obtain ⟨h1, h2⟩ := rep_out h (singO_out o)
  exact ⟨h1, (rep_setO (σ' := ⟨σ.store, o'⟩) h h2 rfl).trans (by rw [singO_setO])⟩

section call

variable {d : Nat}

theorem wp_call_closure_with {Φ : Value → vProp} {Rest : vProp} {c : Nat}
    {cd : ClosureData} {vs : List Value}
    (hlen : vs.length = cd.params.length) (hd : d < maxCallDepth)
    (hK : ∀ fr, iprop(fr ↦f (Frame.bindAll ⟨some cd.env, []⟩ (cd.params.zip vs)) ∗
      (c ↦c cd ∗ Rest)) ⊢ wpSeq (d + 1) fr cd.body (retK Φ)) :
    iprop(c ↦c cd ∗ Rest) ⊢ wpCall d (.closure c) vs Φ := by
  intro n x H σ rf hwf _ hrep
  obtain ⟨x1, x2, hx, hc, _⟩ := sep_holds.mp H
  obtain ⟨z, hz⟩ := ownM_holds.mp hc
  have hz : x1 = singC c cd • z := hz
  have hcd : σ.store.closures[c]? = some cd := by
    refine (rep_closure (r := singC c cd) (rf := z • (x2 • rf)) ?_ (singC_at c cd)).1
    rw [hrep, hx, hz]; simp only [← assoc']
  have henv := hwf.closure_env c cd hcd
  let fr := σ.store.frames.size
  let l := cd.params.zip vs
  let F0 : Frame := Frame.bindAll ⟨some cd.env, []⟩ l
  let store' := (σ.store.allocFrame (some cd.env)).1
  obtain ⟨hfr, hcl, hsz, hwfl⟩ := Store.foldl_define fr l store'
  let σ1 : St := ⟨l.foldl (fun s (x, v) => s.define fr x v) store', σ.out⟩
  have hfresh : σ.store.frames[fr]? = none := by simp [fr]
  obtain ⟨hx1, hrf1⟩ := rep_fresh hrep hfresh
  have hrep1 : abs σ1 = (singF fr F0 • x.val) • rf := by
    rw [← setF_eq_sing_op _ _ _ hx1]
    refine rep_setF hrep hrf1 (fun b hb => ?_) ?_ ?_ rfl
    · show (l.foldl _ store').frames[b]? = _
      rw [hfr b]; simp only [Ne.symm hb, ↓reduceIte]
      simp [store', Store.allocFrame, Array.getElem?_push, fr, hb]
    · show (l.foldl _ store').frames[fr]? = _
      rw [hfr fr]; simp only [↓reduceIte]
      simp [store', Store.allocFrame, fr, F0]
    · show (l.foldl _ store').closures = _
      rw [hcl]; rfl
  have hwf1 : σ1.store.WF := hwfl (hwf.allocFrame henv)
  have hsz1 : σ1.store.frames.size = fr + 1 := by
    show (l.foldl _ store').frames.size = _
    rw [hsz]; simp [store', Store.allocFrame, fr]
  have hW := hK fr n ⟨singF fr F0 • x.val, validN_op_left (hrep1 ▸ abs_validN σ1 n)⟩
    (sep_holds.mpr ⟨singF fr F0, x.val, rfl, ownM_self _ _ _, H⟩)
  obtain ⟨σ', st, r', hex, hwf', hsz', hrep', hret⟩ := hW σ1 rf hwf1 (by omega) hrep1
  have hgrow : σ.store.frames.size ≤ σ'.store.frames.size := by omega
  cases st with
  | normal =>
    exact ⟨σ', .null, r', Call.closure σ d c cd vs store' fr σ' .normal .null hcd hlen hd rfl
      hex (.inl ⟨rfl, rfl⟩), hwf', hgrow, hrep', hret⟩
  | ret v =>
    exact ⟨σ', v, r', Call.closure σ d c cd vs store' fr σ' (.ret v) v hcd hlen hd rfl
      hex (.inr rfl), hwf', hgrow, hrep', hret⟩
  | brk => exact hret.elim
  | cont => exact hret.elim

theorem wp_call_closure {Φ : Value → vProp} {c : Nat} {cd : ClosureData} {vs : List Value}
    (hlen : vs.length = cd.params.length) (hd : d < maxCallDepth) :
    iprop(c ↦c cd ∗ (∀ fr, fr ↦f (Frame.bindAll ⟨some cd.env, []⟩ (cd.params.zip vs)) -∗
      c ↦c cd -∗ wpSeq (d + 1) fr cd.body (retK Φ))) ⊢ wpCall d (.closure c) vs Φ :=
  wp_call_closure_with hlen hd fun fr => by
    iintro ⟨Hf, Hc, H⟩
    ispecialize H $$ %fr Hf Hc
    iexact H

theorem wp_println_with {Φ : Value → vProp} {Rest : vProp} {o : String} {vs : List Value}
    (hvs : NoClosure vs) (hK : iprop(outIs (o ++ printArgs₀ vs ++ "\n") ∗ Rest) ⊢ Φ .null) :
    iprop(outIs o ∗ Rest) ⊢ wpCall d (.native .println) vs Φ := by
  refine wpR_prim (m := singO o)
    (Q := fun a => iprop(⌜a = .null⌝ ∧ outIs (o ++ printArgs₀ vs ++ "\n"))) ?_ ?_
  · intro σ w hwf _ h
    obtain ⟨ho, h'⟩ := step_out h (o ++ printArgs₀ vs ++ "\n")
    refine ⟨⟨σ.store, o ++ printArgs₀ vs ++ "\n"⟩, .null, singO _, ?_, hwf, Nat.le_refl _, h',
      fun n h => and_holds.mpr ⟨rfl, ownM_self _ n h⟩⟩
    have := Call.println σ d vs
    rwa [printArgs_noClosure hvs, ho] at this
  · intro a
    iintro ⟨⟨%ha, Ho⟩, HR⟩
    subst ha
    iapply hK
    isplitl [Ho]
    · iexact Ho
    · iexact HR

theorem wp_println {Φ : Value → vProp} {o : String} {vs : List Value} (hvs : NoClosure vs) :
    iprop(outIs o ∗ (outIs (o ++ printArgs₀ vs ++ "\n") -∗ Φ .null)) ⊢
      wpCall d (.native .println) vs Φ :=
  wp_println_with hvs (by iintro ⟨Ho, H⟩; iapply H; iexact Ho)

theorem wp_print_with {Φ : Value → vProp} {Rest : vProp} {o : String} {vs : List Value}
    (hvs : NoClosure vs) (hK : iprop(outIs (o ++ printArgs₀ vs) ∗ Rest) ⊢ Φ .null) :
    iprop(outIs o ∗ Rest) ⊢ wpCall d (.native .print) vs Φ := by
  refine wpR_prim (m := singO o)
    (Q := fun a => iprop(⌜a = .null⌝ ∧ outIs (o ++ printArgs₀ vs))) ?_ ?_
  · intro σ w hwf _ h
    obtain ⟨ho, h'⟩ := step_out h (o ++ printArgs₀ vs)
    refine ⟨⟨σ.store, o ++ printArgs₀ vs⟩, .null, singO _, ?_, hwf, Nat.le_refl _, h',
      fun n h => and_holds.mpr ⟨rfl, ownM_self _ n h⟩⟩
    have := Call.print σ d vs
    rwa [printArgs_noClosure hvs, ho] at this
  · intro a
    iintro ⟨⟨%ha, Ho⟩, HR⟩
    subst ha
    iapply hK
    isplitl [Ho]
    · iexact Ho
    · iexact HR

theorem wp_print {Φ : Value → vProp} {o : String} {vs : List Value} (hvs : NoClosure vs) :
    iprop(outIs o ∗ (outIs (o ++ printArgs₀ vs) -∗ Φ .null)) ⊢
      wpCall d (.native .print) vs Φ :=
  wp_print_with hvs (by iintro ⟨Ho, H⟩; iapply H; iexact Ho)

theorem wp_assert {Φ : Value → vProp} {vs : List Value} {v m : Value}
    (hvs : vs = [v] ∨ vs = [v, m]) (ht : v.truthy = true) :
    Φ .null ⊢ wpCall d (.native .assert) vs Φ :=
  wpR_ret fun σ => Call.assertOk σ d vs v m hvs ht

end call

def loopK (Φ : Status → vProp) (Ψ : vProp) : Status → vProp
  | .normal => Ψ
  | .cont => Ψ
  | .brk => Φ .normal
  | .ret v => Φ (.ret v)

def seqK (Φ : Status → vProp) (Ψ : vProp) : Status → vProp
  | .normal => Ψ
  | .brk => Φ .brk
  | .cont => Φ .cont
  | .ret v => Φ (.ret v)

theorem loopK_mono {Φ : Status → vProp} {Ψ Ψ' : vProp} (h : Ψ ⊢ Ψ') (st : Status) :
    loopK Φ Ψ st ⊢ loopK Φ Ψ' st := by
  cases st <;> first | exact h | exact .rfl

section stmt

variable {d env : Nat}

theorem wp_expr {Φ : Status → vProp} (e : Expr) :
    wpE d env e (fun _ => Φ .normal) ⊢ wpS d env (.expr e) Φ :=
  (wpR_map (f := fun _ => Status.normal)).trans (wpR_weaken (Nat.le_refl _)
    fun σ σ1 _ ⟨v, he, h⟩ => h ▸ ExecS.expr σ d env e σ1 v he)

theorem wp_varInit {Φ : Status → vProp} (x : String) (e : Expr) :
    wpE d env e (fun v => wpDef env x v (Φ .normal)) ⊢ wpS d env (.varDecl x (some e)) Φ := by
  refine wpR_bind' (R2 := fun v σ σ1 st => ∃ _u : Unit,
      σ1 = ⟨σ.store.define env x v, σ.out⟩ ∧ st = (fun _ => Status.normal) _u)
    (Nat.le_refl _) (fun v => wpR_map) ?_
  rintro σ σ1 σ2 v st he ⟨_, hσ, hst⟩
  subst σ2; subst st
  exact ExecS.varInit σ d env x e σ1 v he

theorem wp_varNull {Φ : Status → vProp} (x : String) :
    wpDef env x .null (Φ .normal) ⊢ wpS d env (.varDecl x none) Φ :=
  (wpR_map (f := fun _ => Status.normal)).trans (wpR_weaken (Nat.le_refl _)
    fun σ _ _ ⟨_, hσ, h⟩ => h ▸ hσ ▸ ExecS.varNull σ d env x)

theorem wpR_allocFrame {α : Type} {Φ : α → vProp} {Rest : vProp}
    {R2 : Nat → St → St → α → Prop} {R' : St → St → α → Prop}
    (hK : ∀ a, iprop(a ↦f ⟨some env, []⟩ ∗ Rest) ⊢ wpR (a + 1) (R2 a) Φ)
    (hR : ∀ σ σ2 r, R2 σ.store.frames.size ⟨(σ.store.allocFrame (some env)).1, σ.out⟩ σ2 r →
      R' σ σ2 r) :
    Rest ⊢ wpR (env + 1) R' Φ := by
  intro n x H σ rf hwf hlo hrep
  let a := σ.store.frames.size
  let F0 : Frame := ⟨some env, []⟩
  let σ1 : St := ⟨(σ.store.allocFrame (some env)).1, σ.out⟩
  have hfresh : σ.store.frames[a]? = none := by simp [a]
  obtain ⟨hx1, hrf1⟩ := rep_fresh hrep hfresh
  have hrep1 : abs σ1 = (singF a F0 • x.val) • rf := by
    rw [← setF_eq_sing_op _ _ _ hx1]
    refine rep_setF hrep hrf1 (fun b hb => ?_) ?_ rfl rfl
    · simp [σ1, Store.allocFrame, Array.getElem?_push, a, hb]
    · simp [σ1, Store.allocFrame, a, F0]
  have hwf1 : σ1.store.WF := hwf.allocFrame (Nat.lt_of_succ_le hlo)
  have hsz1 : σ1.store.frames.size = a + 1 := by simp [σ1, Store.allocFrame, a]
  have hW := hK a n ⟨singF a F0 • x.val, validN_op_left (hrep1 ▸ abs_validN σ1 n)⟩
    (sep_holds.mpr ⟨singF a F0, x.val, rfl, ownM_self _ _ _, H⟩)
  obtain ⟨σ', r, r', hex, hwf', hsz', hrep', hΦ⟩ := hW σ1 rf hwf1 (by omega) hrep1
  exact ⟨σ', r, r', hR σ σ' r hex, hwf', by omega, hrep', hΦ⟩

theorem wp_block_with {Φ : Status → vProp} {Rest : vProp} (ss : List Stmt)
    (hK : ∀ a, iprop(a ↦f ⟨some env, []⟩ ∗ Rest) ⊢ wpSeq d a ss Φ) :
    Rest ⊢ wpS d env (.block ss) Φ :=
  wpR_allocFrame hK fun σ σ2 st h => ExecS.block σ d env ss _ _ σ2 st rfl h

theorem wp_block {Φ : Status → vProp} (ss : List Stmt) :
    iprop(∀ a, a ↦f ⟨some env, []⟩ -∗ wpSeq d a ss Φ) ⊢ wpS d env (.block ss) Φ :=
  wp_block_with ss fun a => by iintro ⟨Ha, H⟩; iapply H; iexact Ha

theorem wp_if {Φ : Status → vProp} (c : Expr) (t : Stmt) (e : Option Stmt) :
    wpE d env c (fun v => bif v.truthy then wpS d env t Φ else
      match e with
      | some e' => wpS d env e' Φ
      | none => Φ .normal) ⊢
    wpS d env (.ifStmt c t e) Φ := by
  refine wpR_bind' (R2 := fun v σ σ1 st => (v.truthy = true ∧ ExecS σ d env t σ1 st) ∨
      (v.truthy = false ∧ match e with
        | some e' => ExecS σ d env e' σ1 st
        | none => σ1 = σ ∧ st = .normal))
    (Nat.le_refl _) (fun v => ?_) ?_
  · cases ht : v.truthy
    · cases e with
      | some e' => exact wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inr ⟨rfl, h⟩
      | none => exact wpR_ret (Φ := Φ) (a := .normal) fun _ => .inr ⟨rfl, rfl, rfl⟩
    · exact wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨rfl, h⟩
  · rintro σ σ1 σ2 v st hc (⟨ht, hb⟩ | ⟨ht, hb⟩)
    · exact ExecS.ifTrue σ d env c t e σ1 σ2 v st hc ht hb
    · cases e with
      | some e' => exact ExecS.ifFalse σ d env c t e' σ1 σ2 v st hc ht hb
      | none =>
        obtain ⟨hσ, hst⟩ := hb
        subst σ2; subst st
        exact ExecS.ifNone σ d env c t σ1 v hc ht

theorem wp_while_unfold {Φ : Status → vProp} (c : Expr) (b : Stmt) :
    wpE d env c (fun v => bif v.truthy
      then wpS d env b (loopK Φ (wpS d env (.whileStmt c b) Φ))
      else Φ .normal) ⊢
    wpS d env (.whileStmt c b) Φ := by
  let W := Stmt.whileStmt c b
  let rest : Status → St → St → Status → Prop := fun stb σ1 σ2 st =>
    ((stb = .normal ∨ stb = .cont) ∧ ExecS σ1 d env W σ2 st) ∨
    (stb = .brk ∧ σ2 = σ1 ∧ st = .normal) ∨
    (∃ rv, stb = .ret rv ∧ σ2 = σ1 ∧ st = .ret rv)
  have hbody : wpS d env b (loopK Φ (wpS d env W Φ)) ⊢
      wpR (env + 1) (fun σ σ2 st => ∃ σ1 stb, ExecS σ d env b σ1 stb ∧ rest stb σ1 σ2 st) Φ := by
    refine wpR_bind' (R2 := rest) (Nat.le_refl _) (fun stb => ?_)
      fun σ σ1 σ2 stb st h1 h2 => ⟨σ1, stb, h1, h2⟩
    cases stb with
    | normal => exact wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨.inl rfl, h⟩
    | cont => exact wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨.inr rfl, h⟩
    | brk => exact wpR_ret (Φ := Φ) (a := .normal) fun _ => .inr (.inl ⟨rfl, rfl, rfl⟩)
    | ret rv => exact wpR_ret (Φ := Φ) (a := .ret rv) fun _ => .inr (.inr ⟨rv, rfl, rfl, rfl⟩)
  refine wpR_bind' (R2 := fun v σ σ2 st =>
      (v.truthy = true ∧ ∃ σ1 stb, ExecS σ d env b σ1 stb ∧ rest stb σ1 σ2 st) ∨
      (v.truthy = false ∧ σ2 = σ ∧ st = .normal))
    (Nat.le_refl _) (fun v => ?_) ?_
  · cases ht : v.truthy
    · exact wpR_ret (Φ := Φ) (a := .normal) fun _ => .inr ⟨rfl, rfl, rfl⟩
    · exact hbody.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨rfl, h⟩)
  · rintro σ σ1 σ3 v st hc (⟨ht, σ2, stb, hb, hr⟩ | ⟨ht, hσ, hst⟩)
    · rcases hr with ⟨hstb, hW⟩ | ⟨hstb, hσ, hst⟩ | ⟨rv, hstb, hσ, hst⟩
      · exact ExecS.whileLoop σ d env c b σ1 σ2 σ3 v stb st hc ht hb hstb hW
      · subst stb σ3 st; exact ExecS.whileBreak σ d env c b σ1 σ2 v hc ht hb
      · subst stb σ3 st; exact ExecS.whileRet σ d env c b σ1 σ2 v rv hc ht hb
    · subst σ3 st; exact ExecS.whileFalse σ d env c b σ1 v hc ht

theorem wp_while {Φ : Status → vProp} (c : Expr) (b : Stmt) (I : Nat → vProp)
    (hI : ∀ k, I k ⊢ wpE d env c (fun v => bif v.truthy
      then wpS d env b (loopK Φ iprop(∃ k', ⌜k' < k⌝ ∧ I k'))
      else Φ .normal)) :
    ∀ k, I k ⊢ wpS d env (.whileStmt c b) Φ := by
  intro k
  refine Nat.strongRecOn k fun k ih => ?_
  · have hdown : iprop(∃ k', ⌜k' < k⌝ ∧ I k') ⊢ wpS d env (.whileStmt c b) Φ := by
      iintro ⟨%k', %hk, H⟩
      iapply (ih k' hk)
      iexact H
    refine (hI k).trans ((wpR_mono fun v => ?_).trans (wp_while_unfold c b))
    cases v.truthy
    · exact .rfl
    · exact wpR_mono fun st => loopK_mono hdown st

end stmt

abbrev wpFor (d env : Nat) (cnd step : Option Expr) (b : Stmt) (Φ : Status → vProp) : vProp :=
  wpR (env + 1) (fun σ σ' st => ForLoop σ d env cnd step b σ' st) Φ

def initK (d env : Nat) : Option Stmt → vProp → vProp
  | none, K => K
  | some s, K => wpS d env s (fun _ => K)

def stepK (d env : Nat) : Option Expr → vProp → vProp
  | none, K => K
  | some e, K => wpE d env e (fun _ => K)

def condK (d env : Nat) (Φ : Status → vProp) : Option Expr → vProp → vProp
  | none, K => K
  | some c, K => wpE d env c (fun v => bif v.truthy then K else Φ .normal)

theorem initK_mono {d env : Nat} {K K' : vProp} (h : K ⊢ K') :
    ∀ i, initK d env i K ⊢ initK d env i K'
  | none => h
  | some _ => wpR_mono fun _ => h

theorem stepK_mono {d env : Nat} {K K' : vProp} (h : K ⊢ K') :
    ∀ e, stepK d env e K ⊢ stepK d env e K'
  | none => h
  | some _ => wpR_mono fun _ => h

theorem condK_mono {d env : Nat} {Φ : Status → vProp} {K K' : vProp} (h : K ⊢ K') :
    ∀ c, condK d env Φ c K ⊢ condK d env Φ c K'
  | none => h
  | some _ => wpR_mono fun v => by cases v.truthy; exact .rfl; exact h

section forLoop

variable {d env : Nat}

theorem initK_wp {Φ : Status → vProp} {K : vProp} {R : St → St → Status → Prop}
    (hK : K ⊢ wpR (env + 1) R Φ) :
    ∀ i, initK d env i K ⊢
      wpR (env + 1) (fun σ σ2 st => ∃ σ1, ExecInit σ d env i σ1 ∧ R σ1 σ2 st) Φ
  | none => hK.trans (wpR_weaken (Nat.le_refl _) fun σ _ _ h => ⟨σ, ExecInit.none σ d env, h⟩)
  | some s => wpR_bind' (Nat.le_refl _) (fun _ => hK)
      fun σ σ1 _ _ _ hs h => ⟨σ1, ExecInit.some σ d env s σ1 _ hs, h⟩

theorem stepK_wp {Φ : Status → vProp} {K : vProp} {R : St → St → Status → Prop}
    (hK : K ⊢ wpR (env + 1) R Φ) :
    ∀ e, stepK d env e K ⊢
      wpR (env + 1) (fun σ σ2 st => ∃ σ1, ExecStep σ d env e σ1 ∧ R σ1 σ2 st) Φ
  | none => hK.trans (wpR_weaken (Nat.le_refl _) fun σ _ _ h => ⟨σ, ExecStep.none σ d env, h⟩)
  | some e => wpR_bind' (Nat.le_refl _) (fun _ => hK)
      fun σ σ1 _ v _ he h => ⟨σ1, ExecStep.some σ d env e σ1 v he, h⟩

theorem wp_for_unfold {Φ : Status → vProp} (cnd step : Option Expr) (b : Stmt) :
    condK d env Φ cnd (wpS d env b (loopK Φ (stepK d env step (wpFor d env cnd step b Φ)))) ⊢
      wpFor d env cnd step b Φ := by
  let rest : Status → St → St → Status → Prop := fun stb σ1 σ2 st =>
    ((stb = .normal ∨ stb = .cont) ∧
      ∃ σs, ExecStep σ1 d env step σs ∧ ForLoop σs d env cnd step b σ2 st) ∨
    (stb = .brk ∧ σ2 = σ1 ∧ st = .normal) ∨
    (∃ rv, stb = .ret rv ∧ σ2 = σ1 ∧ st = .ret rv)
  let body : St → St → Status → Prop := fun σ σ2 st =>
    ∃ σ1 stb, ExecS σ d env b σ1 stb ∧ rest stb σ1 σ2 st
  have hstep := stepK_wp (d := d) (Φ := Φ) (K := wpFor d env cnd step b Φ) .rfl step
  have hbody : wpS d env b (loopK Φ (stepK d env step (wpFor d env cnd step b Φ))) ⊢
      wpR (env + 1) body Φ := by
    refine wpR_bind' (R2 := rest) (Nat.le_refl _) (fun stb => ?_)
      fun σ σ1 σ2 stb st h1 h2 => ⟨σ1, stb, h1, h2⟩
    cases stb with
    | normal => exact hstep.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨.inl rfl, h⟩)
    | cont => exact hstep.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨.inr rfl, h⟩)
    | brk => exact wpR_ret (Φ := Φ) (a := .normal) fun _ => .inr (.inl ⟨rfl, rfl, rfl⟩)
    | ret rv => exact wpR_ret (Φ := Φ) (a := .ret rv) fun _ => .inr (.inr ⟨rv, rfl, rfl, rfl⟩)

  have hloop : ∀ σ σ1 σ3 st, ForCond σ d env cnd σ1 → body σ1 σ3 st →
      ForLoop σ d env cnd step b σ3 st := by
    rintro σ σ1 σ3 st hc ⟨σ2, stb, hb, hr⟩
    rcases hr with ⟨hstb, σs, hs, hl⟩ | ⟨hstb, hσ, hst⟩ | ⟨rv, hstb, hσ, hst⟩
    · exact ForLoop.loop σ d env cnd step b σ1 σ2 σs σ3 stb st hc hb hstb hs hl
    · subst stb σ3 st; exact ForLoop.bodyBreak σ d env cnd step b σ1 σ2 hc hb
    · subst stb σ3 st; exact ForLoop.bodyRet σ d env cnd step b σ1 σ2 rv hc hb
  cases cnd with
  | none =>
    exact hbody.trans (wpR_weaken (Nat.le_refl _) fun σ _ _ h =>
      hloop σ σ _ _ (ForCond.none σ d env) h)
  | some c =>
    refine wpR_bind' (R2 := fun v σ σ2 st => (v.truthy = true ∧ body σ σ2 st) ∨
        (v.truthy = false ∧ σ2 = σ ∧ st = .normal)) (Nat.le_refl _) (fun v => ?_) ?_
    · cases ht : v.truthy
      · exact wpR_ret (Φ := Φ) (a := .normal) fun _ => .inr ⟨rfl, rfl, rfl⟩
      · exact hbody.trans (wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨rfl, h⟩)
    · rintro σ σ1 σ2 v st hc (⟨ht, hb⟩ | ⟨ht, hσ, hst⟩)
      · exact hloop σ σ1 σ2 st (ForCond.some σ d env c σ1 v hc ht) hb
      · subst σ2 st; exact ForLoop.condFalse σ d env c step b σ1 v hc ht

theorem wp_for_loop {Φ : Status → vProp} (cnd step : Option Expr) (b : Stmt)
    (I : Nat → vProp)
    (hI : ∀ k, I k ⊢ condK d env Φ cnd
      (wpS d env b (loopK Φ (stepK d env step iprop(∃ k', ⌜k' < k⌝ ∧ I k'))))) :
    ∀ k, I k ⊢ wpFor d env cnd step b Φ := by
  intro k
  refine Nat.strongRecOn k fun k ih => ?_
  have hdown : iprop(∃ k', ⌜k' < k⌝ ∧ I k') ⊢ wpFor d env cnd step b Φ := by
    iintro ⟨%k', %hk, H⟩
    iapply (ih k' hk)
    iexact H
  exact (hI k).trans ((condK_mono (wpR_mono fun st =>
    loopK_mono (stepK_mono hdown step) st) cnd).trans (wp_for_unfold cnd step b))

theorem wp_for_with {Φ : Status → vProp} {Rest : vProp} (init : Option Stmt)
    (cnd step : Option Expr) (b : Stmt)
    (hK : ∀ a, iprop(a ↦f ⟨some env, []⟩ ∗ Rest) ⊢ initK d a init (wpFor d a cnd step b Φ)) :
    Rest ⊢ wpS d env (.forStmt init cnd step b) Φ :=
  wpR_allocFrame (fun a => (hK a).trans (initK_wp .rfl init))
    fun σ σ2 st ⟨σ1, hi, hl⟩ => ExecS.forStart σ d env init cnd step b _ _ σ1 σ2 st rfl hi hl

theorem wp_for {Φ : Status → vProp} (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) :
    iprop(∀ a, a ↦f ⟨some env, []⟩ -∗ initK d a init (wpFor d a cnd step b Φ)) ⊢
      wpS d env (.forStmt init cnd step b) Φ :=
  wp_for_with init cnd step b fun a => by iintro ⟨Ha, H⟩; iapply H; iexact Ha

end forLoop

section stmt'

variable {d env : Nat}

theorem wp_ret {Φ : Status → vProp} (e : Expr) :
    wpE d env e (fun v => Φ (.ret v)) ⊢ wpS d env (.ret (some e)) Φ :=
  wpR_map.trans (wpR_weaken (Nat.le_refl _)
    fun σ σ1 _ ⟨v, he, h⟩ => h ▸ ExecS.ret σ d env e σ1 v he)

theorem wp_retNull {Φ : Status → vProp} : Φ (.ret .null) ⊢ wpS d env (.ret none) Φ :=
  wpR_ret fun σ => ExecS.retNull σ d env

theorem wp_brk {Φ : Status → vProp} : Φ .brk ⊢ wpS d env .brk Φ :=
  wpR_ret fun σ => ExecS.brk σ d env

theorem wp_cont {Φ : Status → vProp} : Φ .cont ⊢ wpS d env .cont Φ :=
  wpR_ret fun σ => ExecS.cont σ d env

theorem wp_seq_nil {Φ : Status → vProp} : Φ .normal ⊢ wpSeq d env [] Φ :=
  wpR_ret fun σ => ExecSeq.nil σ d env

theorem wp_seq_cons {Φ : Status → vProp} (s : Stmt) (ss : List Stmt) :
    wpS d env s (seqK Φ (wpSeq d env ss Φ)) ⊢ wpSeq d env (s :: ss) Φ := by
  refine wpR_bind' (R2 := fun st σ σ1 st' => (st = .normal ∧ ExecSeq σ d env ss σ1 st') ∨
      (st ≠ .normal ∧ σ1 = σ ∧ st' = st)) (Nat.le_refl _) (fun st => ?_) ?_
  · cases st with
    | normal => exact wpR_weaken (Nat.le_refl _) fun _ _ _ h => .inl ⟨rfl, h⟩
    | brk => exact wpR_ret (Φ := Φ) (a := .brk) fun _ => .inr ⟨by decide, rfl, rfl⟩
    | cont => exact wpR_ret (Φ := Φ) (a := .cont) fun _ => .inr ⟨by decide, rfl, rfl⟩
    | ret v => exact wpR_ret (Φ := Φ) (a := .ret v) fun _ => .inr ⟨by simp, rfl, rfl⟩
  · rintro σ σ1 σ2 st st' hs (⟨hst, hss⟩ | ⟨hst, hσ, hst'⟩)
    · subst st; exact ExecSeq.consNormal σ d env s ss σ1 σ2 st' hs hss
    · subst σ2 st'; exact ExecSeq.consAbrupt σ d env s ss σ1 st hs hst

end stmt'

theorem wpS_frame {d env : Nat} {P : vProp} {s : Stmt} {Φ : Status → vProp} :
    iprop(P ∗ wpS d env s Φ) ⊢ wpS d env s (fun st => iprop(P ∗ Φ st)) := wpR_frame

theorem wpSeq_frame {d env : Nat} {P : vProp} {ss : List Stmt} {Φ : Status → vProp} :
    iprop(P ∗ wpSeq d env ss Φ) ⊢ wpSeq d env ss (fun st => iprop(P ∗ Φ st)) := wpR_frame

theorem wpE_frame {d env : Nat} {P : vProp} {e : Expr} {Φ : Value → vProp} :
    iprop(P ∗ wpE d env e Φ) ⊢ wpE d env e (fun v => iprop(P ∗ Φ v)) := wpR_frame

theorem wpCall_frame {d : Nat} {P : vProp} {fv : Value} {vs : List Value}
    {Φ : Value → vProp} :
    iprop(P ∗ wpCall d fv vs Φ) ⊢ wpCall d fv vs (fun v => iprop(P ∗ Φ v)) := wpR_frame

def Triple (d env : Nat) (P : vProp) (s : Stmt) (Q : Status → vProp) : Prop :=
  P ⊢ wpS d env s Q

theorem Triple.frame {d env : Nat} {P R : vProp} {s : Stmt} {Q : Status → vProp}
    (h : Triple d env P s Q) : Triple d env iprop(R ∗ P) s (fun st => iprop(R ∗ Q st)) :=
  (BI.sep_mono .rfl h).trans wpS_frame

theorem Triple.conseq {d env : Nat} {P P' : vProp} {s : Stmt} {Q Q' : Status → vProp}
    (hP : P' ⊢ P) (h : Triple d env P s Q) (hQ : ∀ st, Q st ⊢ Q' st) :
    Triple d env P' s Q' :=
  hP.trans (h.trans (wpR_mono hQ))

end Vsa.While.Logic
