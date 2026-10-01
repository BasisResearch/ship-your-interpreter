import Vsa.Compiler.StmtT
import Vsa.Compiler.Fail
import Vsa.Compiler.R6Old

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def SFail (code : List Ins) (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM), At code C pos → SupS C.Γ.names loop s →
    Seg code pos (cstmt C pos s).1 → PosOK (pos + (cstmt C pos s).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    (¬ HasExec st d env s) → Fail code n A

def SeqFail (code : List Ins) (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM) (f : List (String × Nat)) (g : Scope),
    C.Γ = f :: g → At code C pos → SupSeq C.Γ.names loop ss →
    Seg code pos (cseq C pos ss).1 → PosOK (pos + (cseq C pos ss).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    (¬ HasSeqExec st d env ss) → Fail code n A

section
variable {code : List Ins}

theorem StmtOK.fail {C : Ctx} {pos : Nat} {s : Stmt} {st : St} {d : Nat} {env : Addr} {B : AM}
    (h : StmtOK code C pos s st d env B) (hne : ¬ HasExec st d env s) (n : Nat)
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

theorem fIfNone₀ {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {s : Stmt}
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

theorem fIfSome₀ {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {s1 s2 : Stmt}
    (ih1 : ∀ st', SFail code n st' d env s1) (ih2 : ∀ st', SFail code n st' d env s2) :
    SFail code n st d env (.ifStmt c s1 (some s2)) := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr hne
  rw [cstmt_ifSome] at hseg hpos
  have h := And.intro hseg hpos
  simp only [List.append_assoc, ↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, p2⟩, ⟨g3, p3⟩, ⟨-, p4⟩, g5, p5⟩ := h
  refine Fail.cond (d := d) hAt hs.1 g1 g2 p4 hA hsr fun st1 v B1 hev hsr1 hpc1 => ?_
  cases ht : v.truthy <;> simp only [ht, Bool.cond_true, Bool.cond_false] at hpc1
  · exact ih2 st1 _ loop _ B1 (hAt.after s1 (by omega) (by omega) p4) hs.2.2 g5 p5 hloop hpc1 hsr1
      (fun ⟨st', t, D⟩ => hne ⟨st', t, .ifFalse _ _ _ _ _ _ _ _ _ _ hev ht D⟩)
  · exact ih1 st1 C loop _ B1 (hAt.mono (by omega) p2) hs.2.1 g3 p3 hloop hpc1 hsr1
      (fun ⟨st', t, D⟩ => hne ⟨st', t, .ifTrue _ _ _ _ _ _ _ _ _ _ hev ht D⟩)

theorem fWhile₀ {n : Nat} {st : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt}
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
  by_cases hb : HasExec st1 d env b
  rotate_left
  · exact Fail.of_star r1 (ihb st1 _ true _ B1 hAtb hsb hsegb hposb (fun _ => ⟨hpe, hAt.posok⟩) hpc1 hsr1
      (fun ⟨st', t, D⟩ => hb ⟨st', t, D⟩))
  obtain ⟨st2, tb, D⟩ := hb
  obtain ⟨B2, r2, hpc2, hsr2, -, hret2, -⟩ := stmtT (code := code) D _ true _ B1 hAtb hsb hsegb hposb
    (fun _ => ⟨hpe, hAt.posok⟩) hpc1 hsr1
  rw [hcb] at hpc2
  have hrest : Reaches code B2 fun B3 => B3.pc = pcOf pos ∧ B3.mem = B2.mem ∧ B3.out = B2.out ∧
      ¬ HasExec st2 d env (.whileStmt c b) := by
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

theorem fNil₀ {n : Nat} {st : St} {d : Nat} {env : Addr} : SeqFail code n st d env [] :=
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
  · have hf1 := declInfo_cons x hΓ
    simp only [List.length_append] at hpos
    exact Fail.of_star r1 (ih st1 ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ loop _ B1 _ g
      hf1 hAt1 (by rw [declInfo_names C x hAt.ne]; exact hss) hs2
      (by rw [← Nat.add_assoc] at hpos; exact hpos) hloop hpc1 hsr1
      (fun ⟨st', t, D'⟩ => hne ⟨st', t, .consNormal _ _ _ _ _ _ _ _ D D'⟩))
  · exact .inl ⟨B1, r1, hh⟩

theorem fCons₀ {n : Nat} {st : St} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt}
    (hd : ∀ x e, s ≠ .varDecl x (some e)) (ihs : ∀ st', SFail code n st' d env s)
    (ihss : ∀ st', SeqFail code n st' d env ss) : SeqFail code n st d env (s :: ss) := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr hne
  obtain ⟨hs1, hss⟩ := SupSeq_other hd hs
  rw [cseq_other C pos s ss hd] at hseg hpos
  obtain ⟨⟨hsg1, hp1⟩, hsg2, hp2⟩ := segP_app.mp ⟨hseg, hpos⟩
  by_cases hex : HasExec st d env s
  · obtain ⟨st1, t1, D⟩ := hex
    by_cases ht1 : t1 = .normal
    · subst ht1
      refine (stmtT D).fail hAt hs1 hsg1 hp1 hloop hA hsr fun B1 hpc1 hsr1 => ?_
      exact ihss st1 _ loop _ B1 f g (by exact hΓ) (hAt.after s (Nat.le_refl _) (Nat.le_refl _) hp1) hss hsg2 hp2 hloop
        hpc1 hsr1 (fun ⟨st', t, D'⟩ => hne ⟨st', t, .consNormal _ _ _ _ _ _ _ _ D D'⟩)
    · exact absurd ⟨st1, t1, .consAbrupt _ _ _ _ _ _ _ D ht1⟩ hne
  · exact ihs st C loop pos A hAt hs1 hsg1 hp1 hloop hA hsr hex

end

mutual

theorem noS₀ {code : List Ins} (n : Nat) (IHn : ∀ m < n, ∀ st d env s, SFail code m st d env s) :
    ∀ (s : Stmt) (st : St) (d : Nat) (env : Addr), SFail code n st d env s
  | .expr _, _, _, _ => fExpr
  | .block ss, _, _, _ => fBlock (fun st' env' => noSeq n IHn ss st' _ env')
  | .ifStmt _ s none, _, _, _ => fIfNone₀ (fun st' => noS₀ n IHn s st' _ _)
  | .ifStmt _ s1 (some s2), _, _, _ =>
    fIfSome₀ (fun st' => noS₀ n IHn s1 st' _ _) (fun st' => noS₀ n IHn s2 st' _ _)
  | .whileStmt _ b, _, d, env => fWhile₀ (fun st' => noS₀ n IHn b st' _ _) (fun m hm st' => IHn m hm st' d env _)
  | .brk, _, _, _ => fBrk
  | .cont, _, _, _ => fCont
  | .varDecl _ _, _, _, _ => fun _ _ _ _ _ hs => hs.elim
  | .forStmt _ _ _ _, _, _, _ => fun _ _ _ _ _ hs => hs.elim
  | .ret _, _, _, _ => fun _ _ _ _ _ hs => hs.elim

theorem noSeq {code : List Ins} (n : Nat) (IHn : ∀ m < n, ∀ st d env s, SFail code m st d env s) :
    ∀ (ss : List Stmt) (st : St) (d : Nat) (env : Addr), SeqFail code n st d env ss
  | [], _, _, _ => fNil₀
  | .varDecl _ (some _) :: ss, _, _, _ => fDecl (fun st' => noSeq n IHn ss st' _ _)
  | .varDecl x none :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .expr e :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .block b :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .ifStmt c t e :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .whileStmt c b :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .forStmt i c s b :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .ret e :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .brk :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)
  | .cont :: ss, _, _, _ =>
    fCons₀ (fun _ _ h => by cases h) (fun st' => noS₀ n IHn _ st' _ _) (fun st' => noSeq n IHn ss st' _ _)

end

theorem sfail_all {code : List Ins} : ∀ n st d env s, SFail code n st d env s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact fun st d env s => noS₀ n ih s st d env

theorem seqFail_all {code : List Ins} (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) :
    SeqFail code n st d env ss :=
  noSeq n (fun m _ => sfail_all m) ss st d env

end Vsa.Compiler
