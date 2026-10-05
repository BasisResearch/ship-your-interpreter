import Vsa.CT.SoundS

namespace Vsa.CT

open Vsa.While

def chunkI (n : Int) (j : Nat) : Int :=
  (((BitVec.ofInt 64 n).toNat / 2 ^ (11 * (5 - j)) % 2048 : Nat) : Int)

def encAux (n : Int) : Nat → Expr
  | 0 => .int (chunkI n 0)
  | j + 1 => .binary .add (.binary .mul (encAux n j) (.int 2048)) (.int (chunkI n (j + 1)))

def encLit (n : Int) : Expr := encAux n 5

def encL : Nat → EL
  | 0 => .leaf
  | j + 1 => .bin (.bin (encL j) .leaf none) .leaf none

def inDecl (sec : String → Bool) (p : String × Int) : Stmt :=
  .varDecl p.1 (some (if sec p.1 then encLit p.2 else .int p.2))

def prog (sec : String → Bool) (ins : List (String × Int)) (body : Program) : Program :=
  ins.map (inDecl sec) ++ body

inductive LowIns (sec : String → Bool) : List (String × Int) → List (String × Int) → Prop where
  | nil : LowIns sec [] []
  | cons {x : String} {a b : Int} {l1 l2 : List (String × Int)} :
    (sec x = false → a = b) → LowIns sec l1 l2 → LowIns sec ((x, a) :: l1) ((x, b) :: l2)

theorem encAux_val (n : Int) : ∀ j, j ≤ 5 →
    ∃ z, (∀ st d env, EvalL st d env (encAux n j) st (.int z) (encL j)) ∧ wrap64 z = z ∧
      BitVec.ofInt 64 z = BitVec.ofNat 64 ((BitVec.ofInt 64 n).toNat / 2 ^ (11 * (5 - j)))
  | 0, _ => by
    refine ⟨chunkI n 0, fun st d env => .int .., wrap64_eq_self ?_, ?_⟩
    · have : (BitVec.ofInt 64 n).toNat / 2 ^ (11 * (5 - 0)) % 2048 < 2048 := Nat.mod_lt _ (by decide)
      simp only [chunkI]; omega
    have hN := (BitVec.ofInt 64 n).isLt
    apply BitVec.eq_of_toNat_eq
    simp only [chunkI, BitVec.toNat_ofNat, Nat.sub_zero, BitVec.ofInt_natCast]
    omega
  | j + 1, hj => by
    obtain ⟨z, hev, -, hz⟩ := encAux_val n j (by omega)
    refine ⟨wrap64 (wrap64 (z * 2048) + chunkI n (j + 1)), fun st d env => ?_, ?_, ?_⟩
    · exact .binary _ _ _ _ _ _ _ _ _ _ _ _ _
        (.binary _ _ _ _ _ _ _ _ _ _ _ _ _ (hev st d env) (.int ..) rfl) (.int ..) rfl
    · unfold wrap64; rw [BitVec.ofInt_toInt]
    · rw [ofInt_wrap64, BitVec.ofInt_add, ofInt_wrap64, BitVec.ofInt_mul, hz]
      have hN := (BitVec.ofInt 64 n).isLt
      have hc : BitVec.ofInt 64 (chunkI n (j + 1)) = BitVec.ofNat 64
          ((BitVec.ofInt 64 n).toNat / 2 ^ (11 * (5 - (j + 1))) % 2048) := BitVec.ofInt_natCast ..
      rw [hc, show BitVec.ofInt 64 2048 = BitVec.ofNat 64 2048 from rfl]
      generalize (BitVec.ofInt 64 n).toNat = N at hN
      have e1 : 11 * (5 - j) = 11 * (5 - (j + 1)) + 11 := by omega
      have hq : N / 2 ^ (11 * (5 - j)) = N / 2 ^ (11 * (5 - (j + 1))) / 2048 := by
        rw [e1, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      rw [hq]
      have hM : N / 2 ^ (11 * (5 - (j + 1))) ≤ N := Nat.div_le_self _ _
      generalize N / 2 ^ (11 * (5 - (j + 1))) = M at hM ⊢
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega

theorem encLit_val (n : Int) :
    ∃ z, (∀ st d env, EvalL st d env (encLit n) st (.int z) (encL 5)) ∧ z = wrap64 n := by
  obtain ⟨z, hev, hr, hz⟩ := encAux_val n 5 (by omega)
  refine ⟨z, hev, ?_⟩
  have hz' : BitVec.ofInt 64 z = BitVec.ofInt 64 n := by
    rw [hz, show 11 * (5 - 5) = 0 from rfl, Nat.pow_zero, Nat.div_one, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  rw [← hr]; unfold wrap64; rw [hz']

theorem encAux_leak (n : Int) : ∀ (j : Nat) {st : St} {d : Nat} {env : Addr} {st' : St} {v : Value}
    {l : EL}, EvalL st d env (encAux n j) st' v l → l = encL j ∧ st' = st ∧ ∃ z, v = .int z
  | 0, _, _, _, _, _, _, h => by cases h; exact ⟨rfl, rfl, _, rfl⟩
  | j + 1, _, _, _, _, _, _, h => by
    cases h with
    | binary _ _ _ _ _ _ _ _ lv rv v ll lr hl hr hb =>
      cases hl with
      | binary _ _ _ _ _ _ _ _ lv' rv' v' ll' lr' hl' hr' hb' =>
        obtain ⟨rfl, rfl, z, rfl⟩ := encAux_leak n j hl'
        cases hr'
        cases hr
        simp only [binOpSem, Option.some.injEq] at hb'
        subst hb'
        simp only [binOpSem, Option.some.injEq] at hb
        subst hb
        exact ⟨rfl, rfl, _, rfl⟩

theorem seq_cons_inv {st : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {ss : List Stmt}
    {st' : St} {t : Status} {ℓ : List SL}
    (h : ExecSeqL st d env (.varDecl x (some e) :: ss) st' t ℓ) :
    ∃ st1 v l ls, EvalL st d env e st1 v l ∧
      ExecSeqL ⟨st1.store.define env x v, st1.out⟩ d env ss st' t ls ∧ ℓ = .varInit l :: ls := by
  cases h with
  | consNormal _ _ _ _ _ _ _ _ l ls h1 h2 =>
    cases h1 with
    | varInit _ _ _ _ _ st1 v l he => exact ⟨st1, v, l, ls, he, h2, rfl⟩
  | consAbrupt _ _ _ _ _ _ _ l h1 hne =>
    cases h1 with
    | varInit => exact absurd rfl hne

theorem input_eval (sec : String → Bool) (x : String) (a : Int) :
    ∃ z, (∀ st d env, EvalL st d env (if sec x then encLit a else .int a) st (.int z)
      (if sec x then encL 5 else .leaf)) := by
  by_cases hs : sec x = true
  · obtain ⟨z, hev, -⟩ := encLit_val a
    exact ⟨z, by simpa [hs] using hev⟩
  · exact ⟨a, by simp [hs]; exact fun st d env => .int ..⟩

theorem input_leak (sec : String → Bool) (x : String) (a : Int) {st : St} {d : Nat} {env : Addr}
    {st' : St} {v : Value} {l : EL}
    (h : EvalL st d env (if sec x then encLit a else .int a) st' v l) :
    l = (if sec x then encL 5 else .leaf) ∧ st' = st ∧ ∃ z, v = .int z ∧ (sec x = false → z = a) := by
  by_cases hs : sec x = true
  · simp only [hs, ite_true] at h ⊢
    obtain ⟨rfl, rfl, z, rfl⟩ := encAux_leak a 5 h
    exact ⟨rfl, rfl, z, rfl, by simp [hs]⟩
  · simp only [hs, ite_false, Bool.false_eq_true] at h ⊢
    cases h
    exact ⟨rfl, rfl, a, rfl, fun _ => rfl⟩

theorem ct_prefix (sec : String → Bool) (body : Program) (hct : ctSeq sec body = true) :
    ∀ {ins1 ins2 : List (String × Int)}, LowIns sec ins1 ins2 → (∀ p ∈ ins1, isNat p.1 = false) →
    ∀ {st1 st2 : St} {d : Nat} {env : Addr} {st1' : St} {t : Status} {ℓ1 : List SL},
    Low sec st1 st2 → ExecSeqL st1 d env (prog sec ins1 body) st1' t ℓ1 →
    ∃ st2' ℓ2, ExecSeqL st2 d env (prog sec ins2 body) st2' t ℓ2 ∧ skelSs ℓ1 = skelSs ℓ2 ∧
      (st1.out = st2.out → outsSs ℓ1 = outsSs ℓ2 → st1'.out = st2'.out)
  | _, _, .nil, _, _, _, _, _, _, _, _, hlow, h => by
    obtain ⟨st2', ℓ2, h2, -, hsk, hout⟩ := execSeqL_ni sec h hct hlow
    exact ⟨st2', ℓ2, h2, hsk, hout⟩
  | _, _, .cons (x := x) (a := a) (b := b) (l1 := l1) (l2 := l2) hab hrest, hnat, st1, st2, d, env,
      st1', t, _, hlow, h => by
    have hx : isNat x = false := hnat (x, a) (List.mem_cons_self ..)
    have hnat' : ∀ p ∈ l1, isNat p.1 = false := fun p hp => hnat p (List.mem_cons_of_mem _ hp)
    have h' : ExecSeqL st1 d env (.varDecl x (some (if sec x then encLit a else .int a)) ::
        prog sec l1 body) st1' t _ := h
    obtain ⟨st1m, v1, l1x, ls1, he1, hseq1, hℓ⟩ := seq_cons_inv h'
    obtain ⟨hl1, hst1, z1, hv1, hz1⟩ := input_leak sec x a he1
    rw [hst1, hv1] at hseq1
    subst hl1 hℓ
    obtain ⟨z2, hev2⟩ := input_eval sec x b
    have hlow' : Low sec ⟨st1.store.define env x (.int z1), st1.out⟩
        ⟨st2.store.define env x (.int z2), st2.out⟩ := by
      refine ⟨define_low hlow.1 env x (fun hs => ?_), define_good hlow.2.1 env x (natOK_of_int hx),
        define_good hlow.2.2 env x (natOK_of_int hx)⟩
      obtain ⟨-, -, z2', hz2', hz2b⟩ := input_leak sec x b (hev2 st2 d env)
      cases hz2'
      rw [hz1 hs, hz2b hs, hab hs]
    obtain ⟨st2', ℓ2, h2, hsk, hout⟩ := ct_prefix sec body hct hrest hnat' hlow' hseq1
    refine ⟨st2', _, .consNormal _ _ _ _ _ _ _ _ _ _ (.varInit _ _ _ _ _ _ _ _ (hev2 st2 d env)) h2,
      by simp [skelSs, SL.skel, hsk], fun ho hos => ?_⟩
    simp only [outsSs, SL.outs] at hos
    obtain ⟨-, e2⟩ := List.append_inj hos (by rfl)
    exact hout ho e2

theorem lowS_refl (sec : String → Bool) (s : Store) : LowS sec s s := by
  have hv : ∀ l : List (String × Value), VarsRel sec l l := by
    intro l; induction l with
    | nil => exact .nil
    | cons p l ih => exact .cons ⟨rfl, fun _ => rfl⟩ ih
  refine ⟨rfl, fun a f1 f2 h1 h2 => ?_⟩
  rw [h1] at h2; cases h2
  exact ⟨rfl, hv _⟩

theorem good_init : Good initSt.store := by
  refine ⟨rfl, fun a f h p hp => ?_⟩
  simp only [initSt] at h
  cases a with
  | zero =>
    simp at h; subst h
    simp at hp
    rcases hp with rfl | rfl | rfl <;>
      exact ⟨fun h => by simp [isNat] at h, fun h => by simp_all, fun h => by simp_all⟩
  | succ a => simp at h

theorem ct_sound {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hct : ctSeq sec body = true) (hnat : ∀ p ∈ ins1, isNat p.1 = false) (hlow : LowIns sec ins1 ins2)
    {o1 : String} {ℓ1 : List SL} (h1 : BigStepL (prog sec ins1 body) o1 ℓ1) :
    ∃ o2 ℓ2, BigStepL (prog sec ins2 body) o2 ℓ2 ∧ skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → ℓ1 = ℓ2 ∧ o1 = o2) := by
  obtain ⟨st1', h, rfl⟩ := h1
  obtain ⟨st2', ℓ2, h2, hsk, hout⟩ := ct_prefix sec body hct hlow hnat
    ⟨lowS_refl sec _, good_init, good_init⟩ h
  exact ⟨st2'.out, ℓ2, ⟨st2', h2, rfl⟩, hsk, fun ho => ⟨skel_outs_inj hsk ho, hout rfl ho⟩⟩

end Vsa.CT
