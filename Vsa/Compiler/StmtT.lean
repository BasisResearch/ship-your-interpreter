import Vsa.Compiler.StmtShape

/-!
# Forward simulation of statements

For every execution of a supported statement (list), its code runs from a
related state to the exit of the execution's completion status, re-establishing
the store relation. One lemma per derivation rule; `stmtT`/`seqT` recurse over
the derivation.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Forward simulation of one statement execution. -/
def TSpec (code : List Ins) (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (t : Status) :
    Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM), At code C pos → SupS C.Γ.names loop s →
    Seg code pos (cstmt C pos s).1 → PosOK (pos + (cstmt C pos s).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    ∃ B, Star code A B ∧ B.pc = pcOf (exitPos C (pos + (cstmt C pos s).1.length) t) ∧
      SR C.Γ env st' B ∧ SameParents st.store st'.store ∧ (∀ v, t ≠ .ret v) ∧
      (loop = false → t = .normal)

/-- Forward simulation of one statement-list execution. -/
def SeqSpec (code : List Ins) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (st' : St)
    (t : Status) : Prop :=
  ∀ (C : Ctx) (loop : Bool) (pos : Nat) (A : AM) (f : List (String × Nat)) (g : Scope),
    C.Γ = f :: g → At code C pos → SupSeq C.Γ.names loop ss →
    Seg code pos (cseq C pos ss).1 → PosOK (pos + (cseq C pos ss).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    ∃ B, Star code A B ∧ B.pc = pcOf (exitPos C (pos + (cseq C pos ss).1.length) t) ∧
      outStr B = st'.out ∧ SameParents st.store st'.store ∧ (∀ v, t ≠ .ret v) ∧
      (loop = false → t = .normal) ∧
      ∃ f', Chain st'.store B.mem env (f' :: g) ∧ (t = .normal → (cseq C pos ss).2.1 = f' :: g)

theorem SupS_expr {Γn : NScope} {loop : Bool} {e : Expr} (h : SupS Γn loop (.expr e)) :
    (∃ f args, e = .call (.var f) args ∧ SupS Γn false (.expr (.call (.var f) args))) ∨
      (CondE Γn e ∧ ∀ f args, e ≠ .call f args) := by
  cases e with
  | call f args =>
    cases f with
    | var x => exact .inl ⟨x, args, rfl, h⟩
    | _ => exact absurd h (by simp [SupS, CondE, IntE, BoolE])
  | _ => exact .inr ⟨h, fun _ _ h => by cases h⟩

theorem StmtOK.exec {code : List Ins} {C : Ctx} {pos : Nat} {s : Stmt} {st : St} {d : Nat}
    {env : Addr} {B : AM} (h : StmtOK code C pos s st d env B) {st' : St} {t : Status}
    (D : ExecS st d env s st' t) :
    B.pc = pcOf (exitPos C (pos + (cstmt C pos s).1.length) t) ∧ SR C.Γ env st' B ∧
      SameParents st.store st'.store ∧ (∀ v, t ≠ .ret v) := by
  rcases h with ⟨st1, t1, _, huniq, hpc, hsr, hsp, hret⟩ | ⟨_, hne⟩
  · obtain ⟨rfl, rfl⟩ := huniq _ _ D
    exact ⟨hpc, hsr, hsp, hret⟩
  · exact absurd D (hne _ _)

section
variable {code : List Ins}

theorem tExpr {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value}
    (he : EvalE st d env e st' v) : TSpec code st d env (.expr e) st' .normal := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  have D : ExecS st d env (.expr e) st' .normal := .expr _ _ _ _ _ _ he
  rcases SupS_expr hs with ⟨f, args, rfl, hs'⟩ | ⟨hc, hnc⟩
  · obtain ⟨B, r, hB⟩ := sim_printStmt (d := d) hAt hs' hseg hpos hA hsr
    obtain ⟨hpc, hsr', hsp, hret⟩ := hB.exec D
    exact ⟨B, r, hpc, hsr', hsp, hret, fun _ => rfl⟩
  · obtain ⟨B, r, hB⟩ := sim_exprStmt (d := d) hAt hc hnc hseg hA hsr
    obtain ⟨hpc, hsr', hsp, hret⟩ := hB.exec D
    exact ⟨B, r, hpc, hsr', hsp, hret, fun _ => rfl⟩

theorem tBrk {st : St} {d : Nat} {env : Addr} : TSpec code st d env .brk st .brk := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  have hl : loop = true := hs
  obtain ⟨hb, -⟩ := hloop hl
  exact ⟨_, Star.single (step_jump hAt.fits hseg.head hA hAt.posok hb), rfl, hsr, .refl _,
    by simp, fun h => by rw [hl] at h; cases h⟩

theorem tCont {st : St} {d : Nat} {env : Addr} : TSpec code st d env .cont st .cont := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  have hl : loop = true := hs
  obtain ⟨-, hc⟩ := hloop hl
  exact ⟨_, Star.single (step_jump hAt.fits hseg.head hA hAt.posok hc), rfl, hsr, .refl _,
    by simp, fun h => by rw [hl] at h; cases h⟩

theorem tBlock {st : St} {d : Nat} {env : Addr} {ss : List Stmt} {store' : Store} {inner : Addr}
    {st' : St} {t : Status} (halloc : st.store.allocFrame (some env) = (store', inner))
    (ih : SeqSpec code ⟨store', st.out⟩ d inner ss st' t) : TSpec code st d env (.block ss) st' t := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  rw [cstmt_block] at hseg hpos
  dsimp only at hseg hpos
  have hc0 : Chain store' A.mem inner ([] :: C.Γ) := by
    have := hsr.1.alloc; rw [halloc] at this; exact this
  obtain ⟨B, r, hpc, hout, hsp, hret, hnorm, f', hc, -⟩ :=
    ih ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ loop pos A [] C.Γ rfl hAt.block hs hseg hpos hloop hA
      ⟨hc0, hsr.2⟩
  have hsp0 : SameParents st.store store' := by
    have := sameParents_alloc st.store (some env); rw [halloc] at this; exact this
  have hpar : (st'.store.frames[inner]?).map Frame.parent = some (some env) := hsp.parent (by
    have := parent_of_alloc st.store env; rw [halloc] at this; exact this)
  exact ⟨B, r, by rw [cstmt_block]; exact hpc, ⟨hc.tail hAt.ne hpar, hout⟩, hsp0.trans hsp, hret, hnorm⟩

theorem At.mono {C : Ctx} {pos pos' : Nat} (h : At code C pos) (hle : pos ≤ pos') (hp : PosOK pos') :
    At code C pos' := ⟨h.lay, h.ne, h.nd, h.lt, h.nat, Nat.le_trans h.nextle hle, hp⟩

/-- The truthy branch of an `if`/`while` condition, from its derivation. -/
theorem condT {C : Ctx} {pos L : Nat} {c : Expr} {st st1 : St} {d : Nat} {env : Addr} {v : Value}
    {A : AM} (hAt : At code C pos) (hc : CondE C.Γ.names c)
    (hseg : Seg code pos (cexpr C.Γ 0 pos c ++ [.br .ne a0 0 (bSkip 1),
      .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1) L)]))
    (hL : PosOK L) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A) (hev : EvalE st d env c st1 v) :
    ∃ B, Star code A B ∧ SR C.Γ env st1 B ∧ SameParents st.store st1.store ∧
      B.pc = pcOf (if v.truthy then pos + (cexpr C.Γ 0 pos c).length + 2 else L) := by
  obtain ⟨B, r, hB⟩ := sim_cond (d := d) hAt hc hseg hL hA hsr
  rcases hB with ⟨st1', v', hev', hsr', hsp, hpc⟩ | ⟨_, hne⟩
  · obtain ⟨rfl, rfl⟩ := EvalE.det c (CondE.simple hc) hev' hev
    exact ⟨B, r, hsr', hsp, hpc⟩
  · exact absurd hev (hne _ _)

theorem tIfNone {st st1 st2 : St} {d : Nat} {env : Addr} {c : Expr} {s : Stmt} {v : Value}
    {t : Status} (hev : EvalE st d env c st1 v)
    (hbr : (v.truthy = true ∧ TSpec code st1 d env s st2 t) ∨ (v.truthy = false ∧ st2 = st1 ∧ t = .normal)) :
    TSpec code st d env (.ifStmt c s none) st2 t := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  obtain ⟨hc, hst⟩ := hs
  rw [cstmt_ifNone] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos ⊢
  obtain ⟨hs12, hs3⟩ := hseg.append
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condT hAt hc hs12 (by unfold PosOK at *; omega) hA hsr hev
  rcases hbr with ⟨ht, ih⟩ | ⟨hf, rfl, rfl⟩
  · rw [if_pos ht] at hpc1
    have hpos1 := Seg.end_ok hAt.fits hs12 (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil] at hpos1
    obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := ih C loop _ B1
      (hAt.mono (by omega) (by simpa [Nat.add_assoc] using hpos1)) hst
      (Seg.pos_eq (by simp; omega) hs3) (by unfold PosOK at *; omega) hloop hpc1 hsr1
    refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, hret, hnorm⟩
    rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega
  · rw [if_neg (by simp [hf])] at hpc1
    exact ⟨B1, r1, by rw [hpc1]; simp only [exitPos]; congr 1; omega, hsr1, hsp1, by simp, fun _ => rfl⟩

theorem tIfSome {st st1 st2 : St} {d : Nat} {env : Addr} {c : Expr} {s1 s2 : Stmt} {v : Value}
    {t : Status} (hev : EvalE st d env c st1 v)
    (hbr : (v.truthy = true ∧ TSpec code st1 d env s1 st2 t) ∨
      (v.truthy = false ∧ TSpec code st1 d env s2 st2 t)) :
    TSpec code st d env (.ifStmt c s1 (some s2)) st2 t := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  obtain ⟨hc, hst1, hst2⟩ := hs
  rw [cstmt_ifSome] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  generalize hct : cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) s1 = ct at hseg hpos ⊢
  generalize hce : cstmt ⟨C.Γ, ct.2, C.brk, C.cont⟩ (pos + (cexpr C.Γ 0 pos c).length + 2 +
    ct.1.length + 1) s2 = ce at hseg hpos ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos ⊢
  obtain ⟨hs1234, hs5⟩ := hseg.append
  obtain ⟨hs123, hs4⟩ := hs1234.append
  obtain ⟨hs12, hs3⟩ := hs123.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hs5 hs4 hs3
  have hpe : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length + 1) := by unfold PosOK at *; omega
  have hpend : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length + 1 + ce.1.length) := by
    unfold PosOK at *; omega
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condT hAt hc hs12 hpe hA hsr hev
  have hend : pos + ((cexpr C.Γ 0 pos c).length + (0 + 1 + 1) + ct.1.length + (0 + 1) + ce.1.length)
      = pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length + 1 + ce.1.length := by omega
  rcases hbr with ⟨ht, ih⟩ | ⟨hf, ih⟩
  · rw [if_pos ht] at hpc1
    obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := ih C loop _ B1
      (hAt.mono (by omega) (by unfold PosOK at *; omega)) hst1
      (by rw [hct]; exact Seg.pos_eq (by omega) hs3) (by rw [hct]; unfold PosOK at *; omega)
      hloop hpc1 hsr1
    rw [hct] at hpc2
    cases t with
    | normal =>
      simp only [exitPos] at hpc2
      have e3 := step_jump hAt.fits (Seg.pos_eq (pos' := pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length)
        (by omega) hs4).head hpc2 (by unfold PosOK at *; omega) hpend
      refine ⟨⟨pcOf (pos + (cexpr C.Γ 0 pos c).length + 2 + ct.1.length + 1 + ce.1.length), B2.regs,
        B2.mem, B2.out⟩, r1.trans (r2.trans (Star.single ?_)), by simp only [exitPos]; rw [hend], ?_,
        hsp1.trans hsp2, hret, hnorm⟩
      · exact e3
      · exact hsr2
    | _ => exact ⟨B2, r1.trans r2, hpc2, hsr2, hsp1.trans hsp2, hret, hnorm⟩
  · rw [if_neg (by simp [hf])] at hpc1
    have hle := (cstmt_next C (pos + (cexpr C.Γ 0 pos c).length + 2) s1).2
    rw [hct] at hle
    obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := ih ⟨C.Γ, ct.2, C.brk, C.cont⟩ loop _ B1
      ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi)
        (by have := (cstmt_next C (pos + (cexpr C.Γ 0 pos c).length + 2) s1).1; rw [hct] at this; exact this),
        hAt.nat, by show ct.2 ≤ _; have := hAt.nextle; omega, hpe⟩ hst2
      (by rw [hce]; exact Seg.pos_eq (by omega) hs5) (by rw [hce]; exact hpend) hloop hpc1 hsr1
    rw [hce] at hpc2
    refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, hret, hnorm⟩
    rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega

theorem tWhile {st st1 st' : St} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {v : Value}
    {t : Status} (hev : EvalE st d env c st1 v)
    (hcase : (v.truthy = false ∧ st' = st1 ∧ t = .normal) ∨
      (v.truthy = true ∧ ∃ st2 tb, TSpec code st1 d env b st2 tb ∧
        ((tb = .brk ∧ st' = st2 ∧ t = .normal) ∨ (∃ rv, tb = .ret rv) ∨
          ((tb = .normal ∨ tb = .cont) ∧ TSpec code st2 d env (.whileStmt c b) st' t)))) :
    TSpec code st d env (.whileStmt c b) st' t := by
  intro C loop pos A hAt hs hseg hpos hloop hA hsr
  have hs0 := hs
  obtain ⟨hc, hsb⟩ := hs
  have hseg0 := hseg
  have hpos0 := hpos
  rw [cstmt_while] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  have ht1 := cstmt_targets C 0 0 (pos + (cexpr C.Γ 0 pos c).length + 2) b
  have ht2 := cstmt_targets C (pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1) pos
    (pos + (cexpr C.Γ 0 pos c).length + 2) b
  generalize hcb : cstmt ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩
    (pos + (cexpr C.Γ 0 pos c).length + 2) b = cb at hseg hpos ⊢ ht2
  generalize hbl : (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length = blen
    at hseg hpos ⊢ ht1 ht2 hcb
  have hlen : cb.1.length = blen := by rw [ht2.1, ← ht1.1]
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos ⊢
  obtain ⟨hs123, hs4⟩ := hseg.append
  obtain ⟨hs12, hs3⟩ := hs123.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hs4 hs3
  have hpe : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1) := by unfold PosOK at *; omega
  have hend : pos + ((cexpr C.Γ 0 pos c).length + (0 + 1 + 1) + cb.1.length + (0 + 1)) =
      pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1 := by omega
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condT hAt hc hs12 hpe hA hsr hev
  rcases hcase with ⟨hf, rfl, rfl⟩ | ⟨ht, st2, tb, ihb, hk⟩
  · rw [if_neg (by simp [hf])] at hpc1
    exact ⟨B1, r1, by rw [hpc1]; simp only [exitPos]; rw [hend], hsr1, hsp1, by simp, fun _ => rfl⟩
  rw [if_pos ht] at hpc1
  have hbpos : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2) := by unfold PosOK at *; omega
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret2, -⟩ := ihb ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 + blen + 1, pos⟩ true _ B1
    ⟨hAt.lay, hAt.ne, hAt.nd, hAt.lt, hAt.nat, by have := hAt.nextle; simp only; omega, hbpos⟩
    hsb (by rw [hcb]; exact Seg.pos_eq (by omega) hs3) (by rw [hcb]; unfold PosOK at *; omega)
    (fun _ => ⟨hpe, hAt.posok⟩) hpc1 hsr1
  rw [hcb] at hpc2
  rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rv, rfl⟩ | ⟨htb, ihw⟩
  · refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, by simp, fun _ => rfl⟩
    rw [hpc2]; simp only [exitPos]; rw [hend]
  · exact absurd rfl (hret2 rv)
  · -- back to the loop head
    have hback : ∃ B3, Star code B2 B3 ∧ B3.pc = pcOf pos ∧ B3.mem = B2.mem ∧ B3.out = B2.out := by
      rcases htb with rfl | rfl
      · simp only [exitPos] at hpc2
        refine ⟨_, Star.single (step_jump hAt.fits (Seg.pos_eq (pos' := pos + (cexpr C.Γ 0 pos c).length
          + 2 + cb.1.length) (by omega) hs4).head hpc2 (by unfold PosOK at *; omega) hAt.posok),
          rfl, rfl, rfl⟩
      · exact ⟨B2, Star.refl _ _, hpc2, rfl, rfl⟩
    obtain ⟨B3, r3, hpc3, hm3, ho3⟩ := hback
    obtain ⟨B4, r4, hpc4, hsr4, hsp4, hret4, hnorm4⟩ := ihw C loop pos B3 hAt hs0 hseg0 hpos0 hloop hpc3
      ⟨by rw [hm3]; exact hsr2.1, by simp only [outStr] at *; rw [ho3]; exact hsr2.2⟩
    refine ⟨B4, r1.trans (r2.trans (r3.trans r4)), ?_, hsr4, hsp1.trans (hsp2.trans hsp4), hret4, hnorm4⟩
    rw [hpc4, cstmt_while]; dsimp only; rw [hbl, hcb]; simp only [List.length_append, List.length_cons, List.length_nil]

theorem SupSeq_other {Γn : NScope} {loop : Bool} {s : Stmt} {ss : List Stmt}
    (hd : ∀ x e, s ≠ .varDecl x (some e)) (h : SupSeq Γn loop (s :: ss)) :
    SupS Γn loop s ∧ SupSeq Γn loop ss := by
  cases s with
  | varDecl x i =>
    cases i with
    | some e => exact absurd rfl (hd x e)
    | none => exact h
  | _ => exact h

theorem exitPos_abrupt (C : Ctx) (a b : Nat) {t : Status} (ht : t ≠ .normal) :
    exitPos C a t = exitPos C b t := by
  cases t <;> first | rfl | exact absurd rfl ht

theorem sNil {st : St} {d : Nat} {env : Addr} : SeqSpec code st d env [] st .normal := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr
  exact ⟨A, Star.refl _ _, by simp [cseq, exitPos, hA], hsr.2, .refl _, by simp, fun _ => rfl,
    f, by rw [← hΓ]; exact hsr.1, fun _ => by simp [cseq, hΓ]⟩

theorem sConsDecl {st st1 st' : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {ss : List Stmt}
    {t : Status} (D : ExecS st d env (.varDecl x (some e)) st1 .normal)
    (ih : SeqSpec code st1 d env ss st' t) : SeqSpec code st d env (.varDecl x (some e) :: ss) st' t := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr
  obtain ⟨hnat, he, hss⟩ := hs
  rw [cseq_decl] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  obtain ⟨hs1, hs2⟩ := hseg.append
  obtain ⟨B1, r1, hB1⟩ := sim_decl (d := d) hAt hnat he hs1 hA hsr
  rcases hB1 with ⟨st1', hD', huniq, hpc1, hsr1, hsp1, hAt1⟩ | ⟨_, hne⟩
  rotate_left
  · exact absurd D (hne _ _)
  obtain ⟨rfl, -⟩ := huniq _ _ D
  obtain ⟨f0, g0, hΓ0, hdi⟩ := declInfo_cases C x hAt.ne
  rw [hΓ] at hΓ0; cases hΓ0
  have hΓ' : ∃ f', (declInfo C x).1 = f' :: g := by
    rcases hdi with ⟨i, -, hdi⟩ | ⟨-, hdi⟩
    · exact ⟨f, by rw [hdi, hΓ]⟩
    · exact ⟨_, by rw [hdi]⟩
  obtain ⟨f1, hf1⟩ := hΓ'
  simp only [List.length_append] at hpos ⊢
  obtain ⟨B2, r2, hpc2, hout2, hsp2, hret2, hnorm2, f', hc2, hΓ2⟩ :=
    ih ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ loop _ B1 f1 g hf1 hAt1
      (by rw [declInfo_names C x hAt.ne]; exact hss) hs2 (by rw [← Nat.add_assoc] at hpos; exact hpos)
      hloop hpc1 hsr1
  refine ⟨B2, r1.trans r2, by rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega,
    hout2, hsp1.trans hsp2, hret2, hnorm2, f', hc2, hΓ2⟩

theorem sConsStmt {st st1 st' : St} {d : Nat} {env : Addr} {s : Stmt} {ss : List Stmt}
    {t1 t : Status} (hd : ∀ x e, s ≠ .varDecl x (some e)) (h1 : TSpec code st d env s st1 t1)
    (hk : (t1 = .normal ∧ SeqSpec code st1 d env ss st' t) ∨ (t1 ≠ .normal ∧ st' = st1 ∧ t = t1)) :
    SeqSpec code st d env (s :: ss) st' t := by
  intro C loop pos A f g hΓ hAt hs hseg hpos hloop hA hsr
  obtain ⟨hs1, hss⟩ := SupSeq_other hd hs
  rw [cseq_other C pos s ss hd] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  obtain ⟨hsg1, hsg2⟩ := hseg.append
  simp only [List.length_append] at hpos ⊢
  have hp1 : PosOK (pos + (cstmt C pos s).1.length) := by unfold PosOK at *; omega
  obtain ⟨B1, r1, hpc1, hsr1, hsp1, hret1, hnorm1⟩ := h1 C loop pos A hAt hs1 hsg1 hp1 hloop hA hsr
  rcases hk with ⟨rfl, ih⟩ | ⟨hne, rfl, rfl⟩
  · have hn := cstmt_next C pos s
    obtain ⟨B2, r2, hpc2, hout2, hsp2, hret2, hnorm2, f', hc2, hΓ2⟩ :=
      ih ⟨C.Γ, (cstmt C pos s).2, C.brk, C.cont⟩ loop _ B1 f g hΓ
        ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi) hn.1, hAt.nat,
          by show (cstmt C pos s).2 ≤ _; have := hAt.nextle; omega, hp1⟩
        hss hsg2 (by rw [← Nat.add_assoc] at hpos; exact hpos) hloop hpc1 hsr1
    refine ⟨B2, r1.trans r2, by rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega,
      hout2, hsp1.trans hsp2, hret2, hnorm2, f', hc2, hΓ2⟩
  · refine ⟨B1, r1, by rw [hpc1, exitPos_abrupt C _ _ hne], hsr1.2, hsp1, hret1, hnorm1, f,
      by rw [← hΓ]; exact hsr1.1, fun h => absurd h hne⟩

end

mutual

theorem stmtT {code : List Ins} : ∀ {st : St} {d : Nat} {env : Addr} {s : Stmt} {st' : St} {t : Status},
    ExecS st d env s st' t → TSpec code st d env s st' t
  | _, _, _, _, _, _, .expr _ _ _ _ _ _ he => tExpr he
  | _, _, _, _, _, _, .varInit _ _ _ _ _ _ _ _ => fun _ _ _ _ _ hs => hs.elim
  | _, _, _, _, _, _, .varNull _ _ _ _ => fun _ _ _ _ _ hs => hs.elim
  | _, _, _, _, _, _, .block _ _ _ _ _ _ _ _ halloc hseq => tBlock halloc (seqT hseq)
  | _, _, _, _, _, _, .ifTrue _ _ _ _ _ e _ _ _ _ hev ht hsub => by
    cases e with
    | none => exact tIfNone hev (.inl ⟨ht, stmtT hsub⟩)
    | some e => exact tIfSome hev (.inl ⟨ht, stmtT hsub⟩)
  | _, _, _, _, _, _, .ifFalse _ _ _ _ _ _ _ _ _ _ hev hf hsub => tIfSome hev (.inr ⟨hf, stmtT hsub⟩)
  | _, _, _, _, _, _, .ifNone _ _ _ _ _ _ _ hev hf => tIfNone hev (.inr ⟨hf, rfl, rfl⟩)
  | _, _, _, _, _, _, .whileFalse _ _ _ _ _ _ _ hev hf => tWhile hev (.inl ⟨hf, rfl, rfl⟩)
  | _, _, _, _, _, _, .whileBreak _ _ _ _ _ _ _ _ hev ht hb =>
    tWhile hev (.inr ⟨ht, _, _, stmtT hb, .inl ⟨rfl, rfl, rfl⟩⟩)
  | _, _, _, _, _, _, .whileRet _ _ _ _ _ _ _ _ rv hev ht hb =>
    tWhile hev (.inr ⟨ht, _, _, stmtT hb, .inr (.inl ⟨rv, rfl⟩)⟩)
  | _, _, _, _, _, _, .whileLoop _ _ _ _ _ _ _ _ _ _ _ hev ht hb hst hrest =>
    tWhile hev (.inr ⟨ht, _, _, stmtT hb, .inr (.inr ⟨hst, stmtT hrest⟩)⟩)
  | _, _, _, _, _, _, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun _ _ _ _ _ hs => hs.elim
  | _, _, _, _, _, _, .ret _ _ _ _ _ _ _ => fun _ _ _ _ _ hs => hs.elim
  | _, _, _, _, _, _, .retNull _ _ _ => fun _ _ _ _ _ hs => hs.elim
  | _, _, _, _, _, _, .brk _ _ _ => tBrk
  | _, _, _, _, _, _, .cont _ _ _ => tCont

theorem seqT {code : List Ins} : ∀ {st : St} {d : Nat} {env : Addr} {ss : List Stmt} {st' : St}
    {t : Status}, ExecSeq st d env ss st' t → SeqSpec code st d env ss st' t
  | _, _, _, _, _, _, .nil _ _ _ => sNil
  | _, _, _, _, _, _, .consNormal _ _ _ s _ _ _ _ h1 h2 => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      exact sConsDecl h1 (seqT h2)
    · exact sConsStmt (fun x e h => hd ⟨x, e, h⟩) (stmtT h1) (.inl ⟨rfl, seqT h2⟩)
  | _, _, _, _, _, _, .consAbrupt _ _ _ s _ _ _ h1 hne => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      cases h1 with | varInit => exact absurd rfl hne
    · exact sConsStmt (fun x e h => hd ⟨x, e, h⟩) (stmtT h1) (.inr ⟨hne, rfl, rfl⟩)

end

end Vsa.Compiler
