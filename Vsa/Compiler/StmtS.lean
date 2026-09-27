import Vsa.Compiler.StmtT

/-!
# Statements without an execution

If a supported statement (list) has no execution from a related state, its code
reaches the runtime-error exit or runs for at least `n` steps, for every `n`
(`noS`/`noSeq`, by strong induction on `n` and structural recursion on the
syntax). Executions of the parts that do exist are run with the forward
simulation.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The code fails within `n` steps: the error exit, or `n` steps of running. -/
def Fail (code : List Ins) (n : Nat) (A : AM) : Prop :=
  (∃ B, Star code A B ∧ astep code B = some (.halt 70)) ∨ (∃ B, StarN code n A B)

theorem StarN.truncate {code : List Ins} : ∀ {m : Nat} {A B : AM}, StarN code m A B →
    ∀ n, n ≤ m → ∃ B', StarN code n A B'
  | _, A, _, .refl _, n, h => ⟨A, by rw [Nat.le_zero.mp h]; exact .refl _⟩
  | _, A, _, .step hs rest, n, h => by
    cases n with
    | zero => exact ⟨A, .refl _⟩
    | succ n =>
      obtain ⟨B', h'⟩ := rest.truncate n (by omega)
      exact ⟨B', .step hs h'⟩

/-- A run of `k` steps followed by failure within `n - k` steps fails within `n`. -/
theorem Fail.of_prefix {code : List Ins} {n k : Nat} {A A' : AM} (hr : StarN code k A A')
    (hf : Fail code (n - k) A') : Fail code n A := by
  rcases hf with ⟨B, hB, hh⟩ | ⟨B, hB⟩
  · exact .inl ⟨B, Star.trans ⟨k, hr⟩ hB, hh⟩
  · by_cases hk : k ≤ n
    · exact .inr ⟨B, by have := hr.trans hB; rwa [Nat.add_sub_cancel' hk] at this⟩
    · exact .inr (hr.truncate n (by omega))

theorem Fail.of_star {code : List Ins} {n : Nat} {A A' : AM} (hr : Star code A A')
    (hf : Fail code n A') : Fail code n A := by
  obtain ⟨k, hk⟩ := hr
  exact Fail.of_prefix hk (by
    rcases hf with h | ⟨B, hB⟩
    · exact .inl h
    · exact .inr (hB.truncate _ (by omega)))

/-- Failure of one statement without an execution. -/
def SFail (code : List Ins) (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM), At code C pos → SupS C.Γ.names loop s →
    Seg code pos (cstmt C pos s).1 → PosOK (pos + (cstmt C pos s).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    (¬ ∃ st' t, ExecS st d env s st' t) → Fail code n A

/-- Failure of one statement list without an execution. -/
def SeqFail (code : List Ins) (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM) (f : List (String × Nat)) (g : Scope),
    C.Γ = f :: g → At code C pos → SupSeq C.Γ.names loop ss →
    Seg code pos (cseq C pos ss).1 → PosOK (pos + (cseq C pos ss).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    (¬ ∃ st' t, ExecSeq st d env ss st' t) → Fail code n A

theorem pcOf_inj {a b : Nat} (ha : PosOK a) (hb : PosOK b) (h : pcOf a = pcOf b) : a = b := by
  have := congrArg BitVec.toNat h
  unfold PosOK at ha hb
  rw [pcOf_toNat (by have : tohostAddr = 0x8001ad00 := rfl; omega),
    pcOf_toNat (by have : tohostAddr = 0x8001ad00 := rfl; omega)] at this
  omega

/-- A run between different code positions takes at least one step. -/
theorem StarN.pos_of_pc {code : List Ins} {k : Nat} {A B : AM} (h : StarN code k A B)
    (hne : A.pc ≠ B.pc) : 1 ≤ k := by
  cases h with
  | refl => exact absurd rfl hne
  | step => omega

section
variable {code : List Ins}

theorem StmtOK.fail {C : Ctx} {pos : Nat} {s : Stmt} {st : St} {d : Nat} {env : Addr} {B : AM}
    (h : StmtOK code C pos s st d env B) (hne : ¬ ∃ st' t, ExecS st d env s st' t) (n : Nat)
    {A : AM} (r : Star code A B) : Fail code n A := by
  rcases h with ⟨st', t, D, -⟩ | ⟨hh, -⟩
  · exact absurd ⟨st', t, D⟩ hne
  · exact .inl ⟨B, r, hh⟩

theorem fExpr {n : Nat} {st : St} {d : Nat} {env : Addr} {e : Expr} : SFail code n st d env (.expr e) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  rcases SupS_expr hs with ⟨f, args, rfl, hs'⟩ | ⟨hc, hnc⟩
  · obtain ⟨B, r, hB⟩ := sim_printStmt (d := d) hAt hs' hseg hpos hA hsr
    exact hB.fail hne n r
  · obtain ⟨B, r, hB⟩ := sim_exprStmt (d := d) hAt hc hnc hseg hA hsr
    exact hB.fail hne n r

theorem fBrk {n : Nat} {st : St} {d : Nat} {env : Addr} : SFail code n st d env .brk :=
  fun _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨st, .brk, .brk _ _ _⟩ hne

theorem fCont {n : Nat} {st : St} {d : Nat} {env : Addr} : SFail code n st d env .cont :=
  fun _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨st, .cont, .cont _ _ _⟩ hne

theorem fBlock {n : Nat} {st : St} {d : Nat} {env : Addr} {ss : List Stmt}
    (ih : ∀ st' env', SeqFail code n st' d env' ss) : SFail code n st d env (.block ss) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  rw [cstmt_block] at hseg hpos
  dsimp only at hseg hpos
  have hc0 : Chain (st.store.allocFrame (some env)).1 A.mem (st.store.allocFrame (some env)).2
      ([] :: C.Γ) := hsr.1.alloc
  exact ih ⟨(st.store.allocFrame (some env)).1, st.out⟩ _ ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ loop pos A
    [] C.Γ rfl hAt.block hs hseg hpos hloop hA ⟨hc0, hsr.2⟩
    (fun ⟨st', t, D⟩ => hne ⟨st', t, .block _ _ _ _ _ _ _ _ rfl D⟩)

theorem fIfNone {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {s : Stmt}
    (ih : ∀ st', SFail code n st' d env s) : SFail code n st d env (.ifStmt c s none) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  obtain ⟨hc, hst⟩ := hs
  rw [cstmt_ifNone] at hseg hpos
  dsimp only at hseg hpos
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos
  obtain ⟨hs12, hs3⟩ := hseg.append
  obtain ⟨B1, r1, hB1⟩ := sim_cond (d := d) hAt hc hs12 (by unfold PosOK at *; omega) hA hsr
  rcases hB1 with ⟨st1, v, hev, hsr1, -, hpc1⟩ | ⟨hh, -⟩
  · by_cases ht : v.truthy
    · rw [if_pos ht] at hpc1
      have hpos1 := Seg.end_ok hAt.fits hs12 (by simp)
      simp only [List.length_append, List.length_cons, List.length_nil] at hpos1
      exact Fail.of_star r1 (ih st1 C loop _ B1 (hAt.mono (by omega) (by simpa [Nat.add_assoc] using hpos1))
        hst (Seg.pos_eq (by simp; omega) hs3) (by unfold PosOK at *; omega) hloop hpc1 hsr1
        (fun ⟨st', t, D⟩ => hne ⟨st', t, .ifTrue _ _ _ _ _ _ _ _ _ _ hev ht D⟩))
    · exact absurd ⟨st1, .normal, .ifNone _ _ _ _ _ _ _ hev (by simpa using ht)⟩ hne
  · exact .inl ⟨B1, r1, hh⟩

theorem fIfSome {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {s1 s2 : Stmt}
    (ih1 : ∀ st', SFail code n st' d env s1) (ih2 : ∀ st', SFail code n st' d env s2) :
    SFail code n st d env (.ifStmt c s1 (some s2)) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  obtain ⟨hc, hst1, hst2⟩ := hs
  rw [cstmt_ifSome] at hseg hpos
  dsimp only at hseg hpos
  generalize hct : cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) s1 = ct at hseg hpos
  generalize hce : cstmt ⟨C.Γ, ct.2, C.brk, C.cont⟩ (pos + (cexpr C.Γ 0 pos c).length + 2 +
    ct.1.length + 1) s2 = ce at hseg hpos
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos
  obtain ⟨hs1234, hs5⟩ := hseg.append
  obtain ⟨hs123, hs4⟩ := hs1234.append
  obtain ⟨hs12, hs3⟩ := hs123.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hs5 hs4 hs3
  have hpe : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length + 1) := by unfold PosOK at *; omega
  obtain ⟨B1, r1, hB1⟩ := sim_cond (d := d) hAt hc hs12 hpe hA hsr
  rcases hB1 with ⟨st1, v, hev, hsr1, -, hpc1⟩ | ⟨hh, -⟩
  · by_cases ht : v.truthy
    · rw [if_pos ht] at hpc1
      exact Fail.of_star r1 (ih1 st1 C loop _ B1 (hAt.mono (by omega) (by unfold PosOK at *; omega))
        hst1 (by rw [hct]; exact Seg.pos_eq (by omega) hs3) (by rw [hct]; unfold PosOK at *; omega)
        hloop hpc1 hsr1 (fun ⟨st', t, D⟩ => hne ⟨st', t, .ifTrue _ _ _ _ _ _ _ _ _ _ hev ht D⟩))
    · rw [if_neg ht] at hpc1
      have hle := (cstmt_next C (pos + (cexpr C.Γ 0 pos c).length + 2) s1)
      rw [hct] at hle
      exact Fail.of_star r1 (ih2 st1 ⟨C.Γ, ct.2, C.brk, C.cont⟩ loop _ B1
        ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi) hle.1, hAt.nat,
          by show ct.2 ≤ _; have := hAt.nextle; omega, hpe⟩ hst2
        (by rw [hce]; exact Seg.pos_eq (by omega) hs5) (by rw [hce]; unfold PosOK at *; omega) hloop
        hpc1 hsr1 (fun ⟨st', t, D⟩ => hne ⟨st', t, .ifFalse _ _ _ _ _ _ _ _ _ _ hev (by simpa using ht) D⟩))
  · exact .inl ⟨B1, r1, hh⟩

theorem fWhile {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt}
    (ihb : ∀ st', SFail code n st' d env b)
    (IHn : ∀ m < n, ∀ st', SFail code m st' d env (.whileStmt c b)) :
    SFail code n st d env (.whileStmt c b) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact .inr ⟨A, .refl _⟩
  have hs0 := hs
  obtain ⟨hc, hsb⟩ := hs
  have hseg0 := hseg
  have hpos0 := hpos
  rw [cstmt_while] at hseg hpos
  dsimp only at hseg hpos
  have ht1 := cstmt_targets C 0 0 (pos + (cexpr C.Γ 0 pos c).length + 2) b
  have ht2 := cstmt_targets C (pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1) pos
    (pos + (cexpr C.Γ 0 pos c).length + 2) b
  generalize hcb : cstmt ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩
    (pos + (cexpr C.Γ 0 pos c).length + 2) b = cb at hseg hpos ht2
  generalize hbl : (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length = blen
    at hseg hpos ht1 ht2 hcb
  have hlen : cb.1.length = blen := by rw [ht2.1, ← ht1.1]
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos
  obtain ⟨hs123, hs4⟩ := hseg.append
  obtain ⟨hs12, hs3⟩ := hs123.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hs4 hs3
  have hpe : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1) := by unfold PosOK at *; omega
  have hbpos : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2) := by unfold PosOK at *; omega
  obtain ⟨B1, r1, hB1⟩ := sim_cond (d := d) hAt hc hs12 hpe hA hsr
  rcases hB1 with ⟨st1, v, hev, hsr1, -, hpc1⟩ | ⟨hh, -⟩
  rotate_left
  · exact .inl ⟨B1, r1, hh⟩
  by_cases ht : v.truthy
  rotate_left
  · exact absurd ⟨st1, .normal, .whileFalse _ _ _ _ _ _ _ hev (by simpa using ht)⟩ hne
  rw [if_pos ht] at hpc1
  have hAtb : At code ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1, pos⟩
      (pos + (cexpr C.Γ 0 pos c).length + 2) :=
    ⟨hAt.lay, hAt.ne, hAt.nd, hAt.lt, hAt.nat, by have := hAt.nextle; simp only; omega, hbpos⟩
  have hsegb : Seg code (pos + (cexpr C.Γ 0 pos c).length + 2)
      (cstmt ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1, pos⟩
        (pos + (cexpr C.Γ 0 pos c).length + 2) b).1 := by rw [hcb]; exact Seg.pos_eq (by omega) hs3
  have hposb : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1, pos⟩
        (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length) := by
    rw [hcb]; unfold PosOK at *; omega
  by_cases hb : ∃ st2 tb, ExecS st1 d env b st2 tb
  rotate_left
  · exact Fail.of_star r1 (ihb st1 _ true _ B1 hAtb hsb hsegb hposb (fun _ => ⟨hpe, hAt.posok⟩) hpc1 hsr1
      (fun ⟨st', t, D⟩ => hb ⟨st', t, D⟩))
  obtain ⟨st2, tb, D⟩ := hb
  obtain ⟨B2, r2, hpc2, hsr2, -, hret2, -⟩ := stmtT (code := code) D _ true _ B1 hAtb hsb hsegb hposb
    (fun _ => ⟨hpe, hAt.posok⟩) hpc1 hsr1
  rw [hcb] at hpc2
  have hrest : ∃ B3, Star code B2 B3 ∧ B3.pc = pcOf pos ∧ B3.mem = B2.mem ∧ B3.out = B2.out ∧
      ¬ ∃ st' t, ExecS st2 d env (.whileStmt c b) st' t := by
    cases tb with
    | normal =>
      simp only [exitPos] at hpc2
      refine ⟨_, Star.single (step_jump hAt.fits (Seg.pos_eq (pos' := pos + (cexpr C.Γ 0 pos c).length
        + 2 + cb.1.length) (by omega) hs4).head hpc2 (by unfold PosOK at *; omega) hAt.posok),
        rfl, rfl, rfl, fun ⟨st', t, D'⟩ => hne ⟨st', t, .whileLoop _ _ _ _ _ _ _ _ _ _ _ hev ht D (.inl rfl) D'⟩⟩
    | cont =>
      exact ⟨B2, Star.refl _ _, hpc2, rfl, rfl,
        fun ⟨st', t, D'⟩ => hne ⟨st', t, .whileLoop _ _ _ _ _ _ _ _ _ _ _ hev ht D (.inr rfl) D'⟩⟩
    | brk => exact absurd ⟨st2, .normal, .whileBreak _ _ _ _ _ _ _ _ hev ht D⟩ hne
    | ret rv => exact absurd rfl (hret2 rv)
  obtain ⟨B3, r3, hpc3, hm3, ho3, hne3⟩ := hrest
  obtain ⟨k1, hk1⟩ := r1
  have hk1pos : 1 ≤ k1 := hk1.pos_of_pc (by
    rw [hA, hpc1]; intro h; have := pcOf_inj hAt.posok hbpos h; omega)
  obtain ⟨k2, hk2⟩ := r2.trans r3
  have hall := hk1.trans hk2
  refine Fail.of_prefix hall (IHn (n - (k1 + k2)) (by omega) st2 C loop pos B3 hAt hs0 hseg0 hpos0 hloop
    hpc3 ⟨by rw [hm3]; exact hsr2.1, by simp only [outStr] at *; rw [ho3]; exact hsr2.2⟩ hne3)

theorem fNil {n : Nat} {st : St} {d : Nat} {env : Addr} : SeqFail code n st d env [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne => absurd ⟨st, .normal, .nil _ _ _⟩ hne

theorem fDecl {n : Nat} {st : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {ss : List Stmt}
    (ih : ∀ st', SeqFail code n st' d env ss) :
    SeqFail code n st d env (.varDecl x (some e) :: ss) := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr hne
  obtain ⟨hnat, he, hss⟩ := hs
  rw [cseq_decl] at hseg hpos
  dsimp only at hseg hpos
  obtain ⟨hs1, hs2⟩ := hseg.append
  obtain ⟨B1, r1, hB1⟩ := sim_decl (d := d) hAt hnat he hs1 hA hsr
  rcases hB1 with ⟨st1, D, -, hpc1, hsr1, -, hAt1⟩ | ⟨hh, -⟩
  · obtain ⟨f0, g0, hΓ0, hdi⟩ := declInfo_cases C x hAt.ne
    rw [hΓ] at hΓ0; cases hΓ0
    have hΓ' : ∃ f', (declInfo C x).1 = f' :: g := by
      rcases hdi with ⟨i, -, hdi⟩ | ⟨-, hdi⟩
      · exact ⟨f, by rw [hdi, hΓ]⟩
      · exact ⟨_, by rw [hdi]⟩
    obtain ⟨f1, hf1⟩ := hΓ'
    simp only [List.length_append] at hpos
    exact Fail.of_star r1 (ih st1 ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ loop _ B1 f1 g
      hf1 hAt1 (by rw [declInfo_names C x hAt.ne]; exact hss) hs2
      (by rw [← Nat.add_assoc] at hpos; exact hpos) hloop hpc1 hsr1
      (fun ⟨st', t, D'⟩ => hne ⟨st', t, .consNormal _ _ _ _ _ _ _ _ D D'⟩))
  · exact .inl ⟨B1, r1, hh⟩

theorem fCons {n : Nat} {st : St} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt}
    (hd : ∀ x e, s ≠ .varDecl x (some e)) (ihs : ∀ st', SFail code n st' d env s)
    (ihss : ∀ st', SeqFail code n st' d env ss) : SeqFail code n st d env (s :: ss) := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr hne
  obtain ⟨hs1, hss⟩ := SupSeq_other hd hs
  rw [cseq_other C pos s ss hd] at hseg hpos
  dsimp only at hseg hpos
  obtain ⟨hsg1, hsg2⟩ := hseg.append
  simp only [List.length_append] at hpos
  have hp1 : PosOK (pos + (cstmt C pos s).1.length) := by unfold PosOK at *; omega
  by_cases hex : ∃ st1 t1, ExecS st d env s st1 t1
  · obtain ⟨st1, t1, D⟩ := hex
    by_cases ht1 : t1 = .normal
    · subst ht1
      obtain ⟨B1, r1, hpc1, hsr1, -, -, -⟩ := stmtT (code := code) D C loop pos A hAt hs1 hsg1 hp1 hloop hA hsr
      have hn := cstmt_next C pos s
      exact Fail.of_star r1 (ihss st1 ⟨C.Γ, (cstmt C pos s).2, C.brk, C.cont⟩ loop _ B1 f g hΓ
        ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi) hn.1, hAt.nat,
          by show (cstmt C pos s).2 ≤ _; have := hAt.nextle; omega, hp1⟩
        hss hsg2 (by rw [← Nat.add_assoc] at hpos; exact hpos) hloop hpc1 hsr1
        (fun ⟨st', t, D'⟩ => hne ⟨st', t, .consNormal _ _ _ _ _ _ _ _ D D'⟩))
    · exact absurd ⟨st1, t1, .consAbrupt _ _ _ _ _ _ _ D ht1⟩ hne
  · exact ihs st C loop pos A hAt hs1 hsg1 hp1 hloop hA hsr hex

end

mutual

theorem noS {code : List Ins} (n : Nat) (IHn : ∀ m < n, ∀ st d env s, SFail code m st d env s) :
    ∀ (s : Stmt) (st : St) (d : Nat) (env : Addr), SFail code n st d env s
  | .expr _, _, _, _ => fExpr
  | .block ss, _, _, _ => fBlock (fun st' env' => noSeq n IHn ss st' _ env')
  | .ifStmt _ s none, _, _, _ => fIfNone (fun st' => noS n IHn s st' _ _)
  | .ifStmt _ s1 (some s2), _, _, _ =>
    fIfSome (fun st' => noS n IHn s1 st' _ _) (fun st' => noS n IHn s2 st' _ _)
  | .whileStmt _ b, _, d, env => fWhile (fun st' => noS n IHn b st' _ _) (fun m hm st' => IHn m hm st' d env _)
  | .brk, _, _, _ => fBrk
  | .cont, _, _, _ => fCont
  | .varDecl _ _, _, _, _ => fun _ _ _ _ _ hs => hs.elim
  | .forStmt _ _ _ _, _, _, _ => fun _ _ _ _ _ hs => hs.elim
  | .ret _, _, _, _ => fun _ _ _ _ _ hs => hs.elim

theorem noSeq {code : List Ins} (n : Nat) (IHn : ∀ m < n, ∀ st d env s, SFail code m st d env s) :
    ∀ (ss : List Stmt) (st : St) (d : Nat) (env : Addr), SeqFail code n st d env ss
  | [], _, _, _ => fNil
  | .varDecl _ (some _) :: ss, _, _, _ => fDecl (fun st' => noSeq n IHn ss st' _ _)
  | .varDecl x none :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .expr e :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .block b :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .ifStmt c t e :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .whileStmt c b :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .forStmt i c s b :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .ret e :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .brk :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .cont :: ss, _, _, _ =>
    fCons (fun _ _ h => by cases h) (fun st' => noS n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)

end

theorem sfail_all {code : List Ins} : ∀ n st d env s, SFail code n st d env s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact fun st d env s => noS n ih s st d env

theorem seqFail_all {code : List Ins} (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) :
    SeqFail code n st d env ss :=
  noSeq n (fun m _ => sfail_all m) ss st d env

end Vsa.Compiler
