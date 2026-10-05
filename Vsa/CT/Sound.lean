import Vsa.CT.Low
import Vsa.CT.Inj

namespace Vsa.CT

open Vsa.While

def TyV : Ty → Value → Prop
  | .int, v => ∃ n, v = .int n
  | .bool, v => ∃ b, v = .bool b

theorem ctE_var {sec : String → Bool} {x : String} {ty : Ty} {lab : Bool}
    (h : ctE sec (.var x) = some (ty, lab)) : isNat x = false ∧ ty = .int ∧ lab = sec x := by
  simp only [ctE] at h
  split at h
  · cases h
  · rename_i hx; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by simpa using hx, h.1.symm, h.2.symm⟩

theorem ctE_assign {sec : String → Bool} {x : String} {e : Expr} {ty : Ty} {lab : Bool}
    (h : ctE sec (.assign x e) = some (ty, lab)) :
    ctE sec e = some (.int, lab) ∧ ty = .int ∧ isNat x = false ∧ (sec x = false → lab = false) := by
  simp only [ctE] at h
  split at h
  · rename_i l he
    split at h
    · cases h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or,
        not_and] at hc
      refine ⟨he, rfl, by simpa using hc.1, fun hs => ?_⟩
      cases l
      · rfl
      · exact absurd hs (by simpa using hc.2 rfl)
  · cases h

theorem ctE_bin {sec : String → Bool} {op : BinOp} {l r : Expr} {ty : Ty} {lab : Bool}
    (h : ctE sec (.binary op l r) = some (ty, lab)) :
    ∃ a b, ctE sec l = some (.int, a) ∧ ctE sec r = some (.int, b) ∧
      (divB op = true → a = false ∧ b = false ∧ lab = false ∧ ty = .int) ∧
      (divB op = false → lab = (a || b) ∧ ty = if arithB op then .int else .bool) := by
  simp only [ctE] at h
  split at h
  · rename_i a b ha hb
    refine ⟨a, b, ha, hb, fun hd => ?_, fun hd => ?_⟩
    · rw [if_pos hd] at h
      split at h
      · cases h
      · rename_i hab
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.or_eq_true, not_or] at hab
        exact ⟨by simpa using hab.1, by simpa using hab.2, rfl, rfl⟩
    · rw [if_neg (by simp [hd])] at h
      split at h
      · rename_i har
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, by simp [har]⟩
      · rename_i har
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, by simp [har]⟩
  · cases h

theorem ctE_neg {sec : String → Bool} {e : Expr} {ty : Ty} {lab : Bool}
    (h : ctE sec (.unary .neg e) = some (ty, lab)) : ctE sec e = some (.int, lab) ∧ ty = .int := by
  simp only [ctE] at h
  split at h
  · rename_i l he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨he, rfl⟩
  · cases h

theorem ctE_not {sec : String → Bool} {e : Expr} {ty : Ty} {lab : Bool}
    (h : ctE sec (.unary .not e) = some (ty, lab)) : ∃ t, ctE sec e = some (t, lab) ∧ ty = .bool := by
  simp only [ctE] at h
  split at h
  · rename_i t l he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t, he, rfl⟩
  · cases h

theorem binOpSem_store (s s' : Store) (op : BinOp) (a b : Int) :
    binOpSem s op (.int a) (.int b) = binOpSem s' op (.int a) (.int b) := by
  cases op <;> rfl

theorem binOpSem_some (s : Store) (op : BinOp) (a b : Int) (hd : divB op = false) :
    ∃ v, binOpSem s op (.int a) (.int b) = some v := by
  cases op <;> simp_all [binOpSem, divB]

theorem binOpSem_ty {s : Store} {op : BinOp} {a b : Int} {v : Value}
    (h : binOpSem s op (.int a) (.int b) = some v) :
    TyV (if arithB op then .int else .bool) v := by
  cases op <;> simp [binOpSem] at h <;> first
    | (obtain ⟨-, rfl⟩ := h; exact ⟨_, rfl⟩)
    | (subst h; exact ⟨_, rfl⟩)

theorem divInfo_nondiv {op : BinOp} (hd : divB op = false) (l r : Value) : divInfo op l r = none := by
  cases op <;> simp_all [divInfo, divB]

theorem natOK_int {v : Value} {x : String} (h : NatOK v x) (hx : isNat x = false) : ∃ n, v = .int n :=
  h.1 hx

theorem natOK_of_int {x : String} {n : Int} (hx : isNat x = false) : NatOK (.int n) x := by
  refine ⟨fun _ => ⟨n, rfl⟩, fun h => ?_, fun h => ?_⟩
  · subst h; simp [isNat] at hx
  · subst h; simp [isNat] at hx

theorem evalL_ni (sec : String → Bool) : ∀ (e : Expr) {ty : Ty} {lab : Bool} {st1 st2 : St} {d : Nat}
    {env : Addr} {st1' : St} {v1 : Value} {l : EL}, ctE sec e = some (ty, lab) → Low sec st1 st2 →
    EvalL st1 d env e st1' v1 l →
    ∃ st2' v2, EvalL st2 d env e st2' v2 l ∧ Low sec st1' st2' ∧ st1'.out = st1.out ∧
      st2'.out = st2.out ∧ (lab = false → v1 = v2) ∧ TyV ty v1 ∧ TyV ty v2
  | .int n, _, _, _, st2, _, _, _, _, _, hct, hlow, h => by
    cases h
    simp only [ctE, Option.some.injEq, Prod.mk.injEq] at hct
    obtain ⟨rfl, rfl⟩ := hct
    exact ⟨st2, _, .int .., hlow, rfl, rfl, fun _ => rfl, ⟨n, rfl⟩, ⟨n, rfl⟩⟩
  | .bool b, _, _, _, st2, _, _, _, _, _, hct, hlow, h => by
    cases h
    simp only [ctE, Option.some.injEq, Prod.mk.injEq] at hct
    obtain ⟨rfl, rfl⟩ := hct
    exact ⟨st2, _, .bool .., hlow, rfl, rfl, fun _ => rfl, ⟨b, rfl⟩, ⟨b, rfl⟩⟩
  | .var x, _, _, st1, st2, _, _, _, _, _, hct, hlow, h => by
    cases h with
    | var _ _ _ _ _ hg =>
      obtain ⟨hx, rfl, rfl⟩ := ctE_var hct
      obtain ⟨v2, hg2, heq, hn2⟩ := get_low hlow.1 hlow.2.2 hg
      have hn1 := get_good hlow.2.1 _ hg
      exact ⟨st2, v2, .var _ _ _ _ _ hg2, hlow, rfl, rfl, heq, hn1.1 hx, hn2.1 hx⟩
  | .assign x e, _, _, st1, st2, _, _, _, _, _, hct, hlow, h => by
    cases h with
    | assign _ _ _ _ _ st1' v1 s1'' l he hs =>
      obtain ⟨hce, rfl, hx, hsx⟩ := ctE_assign hct
      obtain ⟨st2', v2, he2, hlow', ho1, ho2, heq, ⟨n1, rfl⟩, ⟨n2, rfl⟩⟩ := evalL_ni sec e hce hlow he
      obtain ⟨s2'', hs2, hl''⟩ := set?_low hlow'.1 (fun h => heq (hsx h)) hs
      refine ⟨⟨s2'', st2'.out⟩, _, .assign _ _ _ _ _ _ _ _ _ he2 hs2,
        ⟨hl'', ?_, ?_⟩, ho1, ho2, heq, ⟨n1, rfl⟩, ⟨n2, rfl⟩⟩
      · exact set_good hlow'.2.1 (natOK_of_int hx) _ _ hs
      · exact set_good hlow'.2.2 (natOK_of_int hx) _ _ hs2
  | .binary op l r, _, _, st1, st2, _, _, st1'', v, _, hct, hlow, h => by
    cases h with
    | binary _ _ _ _ _ _ st1' _ lv rv _ ll lr hl hr hb =>
      obtain ⟨a, b, hca, hcb, hdv, hnd⟩ := ctE_bin hct
      obtain ⟨st2', lv2, hl2, hlow', ho1, ho2, heqa, ⟨na, rfl⟩, ⟨na2, rfl⟩⟩ := evalL_ni sec l hca hlow hl
      obtain ⟨st2'', rv2, hr2, hlow'', ho1', ho2', heqb, ⟨nb, rfl⟩, ⟨nb2, rfl⟩⟩ :=
        evalL_ni sec r hcb hlow' hr
      cases hd : divB op
      · obtain ⟨rfl, hty⟩ := hnd hd
        obtain ⟨v2, hb2⟩ := binOpSem_some st2''.store op na2 nb2 hd
        refine ⟨st2'', v2, ?_, hlow'', ho1'.trans ho1, ho2'.trans ho2, fun hab => ?_, ?_, ?_⟩
        · have := EvalL.binary _ _ _ op _ _ _ _ _ _ _ _ _ hl2 hr2 hb2
          rwa [divInfo_nondiv hd, ← divInfo_nondiv hd (.int na) (.int nb)] at this
        · simp only [Bool.or_eq_false_iff] at hab
          rw [heqa hab.1, heqb hab.2, binOpSem_store st1''.store st2''.store] at hb
          rw [hb] at hb2; cases hb2; rfl
        · rw [hty]; exact binOpSem_ty hb
        · rw [hty]; exact binOpSem_ty hb2
      · obtain ⟨ha, hb', rfl, rfl⟩ := hdv hd
        have e1 := heqa ha
        have e2 := heqb hb'
        cases e1; cases e2
        rw [binOpSem_store st1''.store st2''.store] at hb
        have hty := binOpSem_ty hb
        have har : arithB op = true := by cases op <;> first | rfl | (simp [divB] at hd)
        rw [har] at hty
        exact ⟨st2'', v, .binary _ _ _ _ _ _ _ _ _ _ _ _ _ hl2 hr2 hb, hlow'', ho1'.trans ho1,
          ho2'.trans ho2, fun _ => rfl, hty, hty⟩
  | .unary .neg e, _, _, st1, st2, _, _, _, _, _, hct, hlow, h => by
    cases h with
    | neg _ _ _ _ st1' n l he =>
      obtain ⟨hce, rfl⟩ := ctE_neg hct
      obtain ⟨st2', v2, he2, hlow', ho1, ho2, heq, -, ⟨n2, rfl⟩⟩ := evalL_ni sec e hce hlow he
      refine ⟨st2', _, .neg _ _ _ _ _ _ _ he2, hlow', ho1, ho2, fun hl => ?_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
      cases heq hl; rfl
  | .unary .not e, _, _, st1, st2, _, _, _, _, _, hct, hlow, h => by
    cases h with
    | not _ _ _ _ st1' v l he =>
      obtain ⟨t, hce, rfl⟩ := ctE_not hct
      obtain ⟨st2', v2, he2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec e hce hlow he
      refine ⟨st2', _, .not _ _ _ _ _ _ _ he2, hlow', ho1, ho2, fun hl => ?_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
      rw [heq hl]
  | .str _, _, _, _, _, _, _, _, _, _, hct, _, _ => by simp [ctE] at hct
  | .null, _, _, _, _, _, _, _, _, _, hct, _, _ => by simp [ctE] at hct
  | .logical _ _ _, _, _, _, _, _, _, _, _, _, hct, _, _ => by simp [ctE] at hct
  | .call _ _, _, _, _, _, _, _, _, _, _, hct, _, _ => by simp [ctE] at hct
  | .fn _ _ _, _, _, _, _, _, _, _, _, _, hct, _, _ => by simp [ctE] at hct

theorem intArg_ct {sec : String → Bool} {e : Expr} (h : intArg sec e = true) :
    ∃ lab, ctE sec e = some (.int, lab) := by
  unfold intArg at h
  split at h
  · rename_i l he; exact ⟨l, he⟩
  · cases h

theorem evalArgsL_ni (sec : String → Bool) : ∀ (args : List Expr) {st1 st2 : St} {d : Nat}
    {env : Addr} {st1' : St} {vs1 : List Value} {ls : List EL}, args.all (intArg sec) = true →
    Low sec st1 st2 → EvalArgsL st1 d env args st1' vs1 ls →
    ∃ st2' vs2, EvalArgsL st2 d env args st2' vs2 ls ∧ Low sec st1' st2' ∧ st1'.out = st1.out ∧
      st2'.out = st2.out ∧ (∀ v ∈ vs1, ∃ n, v = .int n) ∧ (∀ v ∈ vs2, ∃ n, v = .int n)
  | [], _, st2, _, _, _, _, _, _, hlow, h => by
    cases h
    exact ⟨st2, [], .nil .., hlow, rfl, rfl, by simp, by simp⟩
  | e :: es, _, st2, _, _, _, _, _, hall, hlow, h => by
    cases h with
    | cons _ _ _ _ _ st1' _ v1 vs1 l ls he hes =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨lab, hce⟩ := intArg_ct hall.1
      obtain ⟨st2', v2, he2, hlow', ho1, ho2, -, hv1, hv2⟩ := evalL_ni sec e hce hlow he
      obtain ⟨st2'', vs2, hes2, hlow'', ho1', ho2', hvs1, hvs2⟩ := evalArgsL_ni sec es hall.2 hlow' hes
      refine ⟨st2'', v2 :: vs2, .cons _ _ _ _ _ _ _ _ _ _ _ he2 hes2, hlow'', ho1'.trans ho1,
        ho2'.trans ho2, ?_, ?_⟩
      · intro v hv; rcases List.mem_cons.mp hv with rfl | hv
        · exact hv1
        · exact hvs1 v hv
      · intro v hv; rcases List.mem_cons.mp hv with rfl | hv
        · exact hv2
        · exact hvs2 v hv

theorem printArgs_store (s s' : Store) : ∀ (vs : List Value), (∀ v ∈ vs, ∃ n, v = .int n) →
    printArgs s vs = printArgs s' vs := by
  intro vs h
  unfold printArgs
  congr 1
  apply List.map_congr_left
  intro v hv
  obtain ⟨n, rfl⟩ := h v hv
  rfl

theorem pubC_ct {sec : String → Bool} {c : Expr} (h : pubC sec c = true) :
    ∃ t, ctE sec c = some (t, false) := by
  unfold pubC at h
  split at h
  · rename_i t he; exact ⟨t, he⟩
  · cases h

end Vsa.CT
