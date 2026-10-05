import Vsa.CT.TExpr
import Vsa.CT.Status
import Vsa.Compiler.StmtT

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def TPost (C : Ctx) (e : Nat) (st : St) (env : Addr) (st' : St) (t : Status) (loop : Bool) (B : AM) :
    Prop :=
  B.pc = pcOf (exitPos C e t) ∧ SR C.Γ env st' B ∧ SameParents st.store st'.store ∧
    (∀ v, t ≠ .ret v) ∧ (loop = false → t = .normal)

def STr (C : Ctx) (pos : Nat) (s : Stmt) (ℓ : SL) : Prop :=
  ∃ τ : List Obs, ∀ (code : List Ins) (st : St) (d : Nat) (env : Addr) (st' : St) (t : Status)
    (loop : Bool) (A : AM), ExecL st d env s st' t ℓ → At code C pos → SupS C.Γ.names loop s →
    Seg code pos (cstmt C pos s).1 → PosOK (pos + (cstmt C pos s).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    ReachesT code A τ (TPost C (pos + (cstmt C pos s).1.length) st env st' t loop)

def QPost (C : Ctx) (pos : Nat) (ss : List Stmt) (g : Scope) (st : St) (env : Addr) (st' : St)
    (t : Status) (loop : Bool) (B : AM) : Prop :=
  B.pc = pcOf (exitPos C (pos + (cseq C pos ss).1.length) t) ∧ outStr B = st'.out ∧
    SameParents st.store st'.store ∧ (∀ v, t ≠ .ret v) ∧ (loop = false → t = .normal) ∧
    ∃ f', Chain st'.store B.mem env (f' :: g) ∧ (t = .normal → (cseq C pos ss).2.1 = f' :: g)

def QTr (C : Ctx) (pos : Nat) (ss : List Stmt) (ℓ : List SL) : Prop :=
  ∃ τ : List Obs, ∀ (code : List Ins) (st : St) (d : Nat) (env : Addr) (st' : St) (t : Status)
    (loop : Bool) (A : AM) (f : List (String × Nat)) (g : Scope), ExecSeqL st d env ss st' t ℓ →
    C.Γ = f :: g → At code C pos → SupSeq C.Γ.names loop ss →
    Seg code pos (cseq C pos ss).1 → PosOK (pos + (cseq C pos ss).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    ReachesT code A τ (QPost C pos ss g st env st' t loop)

theorem truthy_word {Γn : NScope} {e : Expr} {v : Value} (he : CondE Γn e) (hv : ValTy Γn e v) :
    (!(word v == 0)) = v.truthy := by
  have := word_truthy he hv
  cases ht : v.truthy
  · simp [this.mpr ht]
  · have h0 : (word v == 0) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h => by rw [this.mp h] at ht; cases ht
    rw [h0]; rfl

section
variable {code : List Ins}

theorem condTT {C : Ctx} {pos L : Nat} {c : Expr} {st st1 : St} {d : Nat} {env : Addr} {v : Value}
    {lc : EL} {A : AM} (hAt : At code C pos) (hc : CondE C.Γ.names c)
    (hseg : Seg code pos (cexpr C.Γ 0 pos c ++ [.br .ne a0 0 (bSkip 1),
      .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1) L)]))
    (hL : PosOK L) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A) (hev : EvalL st d env c st1 v lc) :
    ReachesT code A (etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) v.truthy)
      fun B => SR C.Γ env st1 B ∧ SameParents st.store st1.store ∧
        B.pc = pcOf (if v.truthy then pos + (cexpr C.Γ 0 pos c).length + 2 else L) := by
  have hs := CondE.simple hc
  obtain ⟨hs1, hs2⟩ := hseg.append
  have hend := Seg.end_ok hAt.fits hseg (by simp)
  simp only [List.length_append, List.length_cons, List.length_nil] at hend
  obtain ⟨B1, r1, hev', hty, hout, hBo, hBpc, hB0, hBc, -⟩ :=
    simT_expr hAt.lay hAt.nd hAt.slot_bound c hs 0 pos st d env A st1 v lc hc
    (by have := tdepth_le C.Γ c 0 pos hs; have := hend.small; omega) hs1
    (by unfold PosOK at *; omega) hA hsr.1 hev
  have r2 := run_condT hAt.fits hs2 hBpc (by unfold PosOK at *; omega) hL hB0
  rw [truthy_word hc hty] at r2
  refine ⟨_, r1.trans r2, ⟨hBc, ?_⟩, EvalE.sameParents c hs hev', ?_⟩
  · simp only [outStr]; rw [hBo, hout]; exact hsr.2
  · have := word_truthy hc hty
    by_cases ht : v.truthy
    · simp only [ht, ite_true]
      rw [if_neg (fun h => by rw [this.mp h] at ht; cases ht)]
    · simp only [ht, Bool.false_eq_true, ite_false]
      rw [if_pos (this.mpr (by simpa using ht))]

theorem tExprT {C : Ctx} {pos : Nat} {e : Expr} {l : EL} (hnc : ∀ f args, e ≠ .call f args) :
    STr C pos (.expr e) (.expr l) := by
  have hce : cstmt C pos (.expr e) = (cexpr C.Γ 0 pos e, C.next) := by
    cases e with
    | call f args => exact absurd rfl (hnc f args)
    | _ => rfl
  refine ⟨etr C.Γ 0 pos e l, fun code st d env st' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | expr _ _ _ _ _ v _ he =>
  have hc : CondE C.Γ.names e := by
    rcases SupS_expr hs with ⟨f, args, rfl, -⟩ | ⟨hc, -⟩
    · exact absurd rfl (hnc (.var f) args)
    · exact hc
  rw [hce] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  have hsm := CondE.simple hc
  obtain ⟨B, r, hev, -, hout, hBo, hBpc, -, hBc, -⟩ := simT_expr hAt.lay hAt.nd hAt.slot_bound e hsm 0 pos
    st d env A st' v l hc (by have := tdepth_le C.Γ e 0 pos hsm; have := hpos.small; omega) hseg hpos hA
    hsr.1 he
  exact ⟨B, r, hBpc, ⟨hBc, by rw [outStr, hBo, hout]; exact hsr.2⟩, EvalE.sameParents e hsm hev,
    by simp, fun _ => rfl⟩

theorem tBrkT {C : Ctx} {pos : Nat} : STr C pos .brk .brk := by
  refine ⟨[pobs pos], fun code st d env st' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D
  have hl : loop = true := hs
  obtain ⟨hb, -⟩ := hloop hl
  exact ⟨_, jumpT hAt.fits hseg.head hA hAt.posok hb, rfl, hsr, .refl _, by simp,
    fun h => by rw [hl] at h; cases h⟩

theorem tContT {C : Ctx} {pos : Nat} : STr C pos .cont .cont := by
  refine ⟨[pobs pos], fun code st d env st' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D
  have hl : loop = true := hs
  obtain ⟨-, hc⟩ := hloop hl
  exact ⟨_, jumpT hAt.fits hseg.head hA hAt.posok hc, rfl, hsr, .refl _, by simp,
    fun h => by rw [hl] at h; cases h⟩

theorem tBlockT {C : Ctx} {pos : Nat} {ss : List Stmt} {ls : List SL}
    (ih : QTr ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ pos ss ls) : STr C pos (.block ss) (.block ls) := by
  obtain ⟨τ, hτ⟩ := ih
  refine ⟨τ, fun code st d env st' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | block _ _ _ _ store' inner _ _ _ halloc hseq =>
  rw [cstmt_block] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  have hc0 : Chain store' A.mem inner ([] :: C.Γ) := by
    have := hsr.1.alloc; rw [halloc] at this; exact this
  obtain ⟨B, r, hpc, hout, hsp, hret, hnorm, f', hc, -⟩ :=
    hτ code _ d inner st' t loop A [] C.Γ hseq rfl hAt.block hs hseg hpos hloop hA ⟨hc0, hsr.2⟩
  have hsp0 : SameParents st.store store' := by
    have := sameParents_alloc st.store (some env); rw [halloc] at this; exact this
  have hpar : (st'.store.frames[inner]?).map Frame.parent = some (some env) := hsp.parent (by
    have := parent_of_alloc st.store env; rw [halloc] at this; exact this)
  exact ⟨B, r, hpc, ⟨hc.tail hAt.ne hpar, hout⟩, hsp0.trans hsp, hret, hnorm⟩

theorem tIfTNoneT {C : Ctx} {pos : Nat} {c : Expr} {th : Stmt} {lc : EL} {lt : SL}
    (ih : STr C (pos + (cexpr C.Γ 0 pos c).length + 2) th lt) :
    STr C pos (.ifStmt c th none) (.ifT lc lt) := by
  obtain ⟨τ, hτ⟩ := ih
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) true ++ τ,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | ifTrue _ _ _ _ _ _ st1 _ v _ _ _ hev htr hth =>
  obtain ⟨hc, hst⟩ := hs
  rw [cstmt_ifNone] at hseg hpos ⊢
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, p2⟩, g3, p3⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc (seg_app_iff.mpr ⟨g1, g2⟩) p3 hA hsr hev
  rw [htr] at r1
  rw [if_pos htr] at hpc1
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := hτ code st1 d env st'' t loop B1 hth
    (hAt.mono (by omega) p2) hst g3 p3 hloop hpc1 hsr1
  refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, hret, hnorm⟩
  rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega

theorem tIfNT {C : Ctx} {pos : Nat} {c : Expr} {th : Stmt} {lc : EL} :
    STr C pos (.ifStmt c th none) (.ifN lc) := by
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) false,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | ifNone _ _ _ _ _ _ v _ hev hfa =>
  obtain ⟨hc, hst⟩ := hs
  rw [cstmt_ifNone] at hseg hpos ⊢
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, p2⟩, g3, p3⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc (seg_app_iff.mpr ⟨g1, g2⟩) p3 hA hsr hev
  rw [hfa] at r1
  rw [if_neg (by simp [hfa])] at hpc1
  exact ⟨B1, r1, by rw [hpc1]; simp only [exitPos]; congr 1; omega, hsr1, hsp1, by simp, fun _ => rfl⟩

theorem tIfTSomeT {C : Ctx} {pos : Nat} {c : Expr} {th el : Stmt} {lc : EL} {lt : SL}
    (ih : STr C (pos + (cexpr C.Γ 0 pos c).length + 2) th lt) :
    STr C pos (.ifStmt c th (some el)) (.ifT lc lt) := by
  obtain ⟨τ, hτ⟩ := ih
  let q := pos + (cexpr C.Γ 0 pos c).length
  let ct := cstmt C (q + 2) th
  refine ⟨etr C.Γ 0 pos c lc ++ condTr q true ++ τ ++
      (if lt.st = .normal then [pobs (q + 2 + ct.1.length)] else []),
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | ifTrue _ _ _ _ _ _ st1 _ v _ _ _ hev htr hth =>
  obtain ⟨hc, hst1, hst2⟩ := hs
  rw [cstmt_ifSome] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  generalize hct : cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) th = ct' at hseg hpos ⊢
  generalize hce : cstmt ⟨C.Γ, ct'.2, C.brk, C.cont⟩ (pos + (cexpr C.Γ 0 pos c).length + 2 +
    ct'.1.length + 1) el = ce at hseg hpos ⊢
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, p2⟩, ⟨g3, p3⟩, ⟨g4, hpe⟩, g5, hpend⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc (seg_app_iff.mpr ⟨g1, g2⟩) hpe hA hsr hev
  rw [htr] at r1
  have hend : pos + ((cexpr C.Γ 0 pos c).length + (0 + 1 + 1) + ct'.1.length + (0 + 1) + ce.1.length)
      = pos + (cexpr C.Γ 0 pos c).length + 2 + ct'.1.length + 1 + ce.1.length := by omega
  rw [if_pos htr] at hpc1
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := hτ code st1 d env st'' t loop B1 hth
    (hAt.mono (by omega) p2) hst1 (by rw [hct]; exact g3) (by rw [hct]; exact p3) hloop hpc1 hsr1
  rw [hct] at hpc2
  have hstt := execL_st hth hret
  have hq : q + 2 + ct.1.length = pos + (cexpr C.Γ 0 pos c).length + 2 + ct'.1.length := by
    simp only [q, ct, hct]
  rw [hq]
  cases t with
  | normal =>
    rw [← hstt, if_pos rfl]
    simp only [exitPos] at hpc2
    have e3 := jumpT hAt.fits g4.head hpc2 p3 hpend
    refine ⟨_, (r1.trans r2).trans e3, by simp only [exitPos]; rw [hend], hsr2,
      hsp1.trans hsp2, hret, hnorm⟩
  | _ =>
    rw [← hstt, if_neg (by simp)]
    exact ⟨B2, by simpa using r1.trans r2, hpc2, hsr2, hsp1.trans hsp2, hret, hnorm⟩

theorem tIfFT {C : Ctx} {pos : Nat} {c : Expr} {th el : Stmt} {lc : EL} {le : SL}
    (ih : STr ⟨C.Γ, (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) th).2, C.brk, C.cont⟩
      (pos + (cexpr C.Γ 0 pos c).length + 2 + (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) th).1.length + 1)
      el le) :
    STr C pos (.ifStmt c th (some el)) (.ifF lc le) := by
  obtain ⟨τ, hτ⟩ := ih
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) false ++ τ,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | ifFalse _ _ _ _ _ _ st1 _ v _ _ _ hev hfa hel =>
  obtain ⟨hc, hst1, hst2⟩ := hs
  rw [cstmt_ifSome] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  generalize hct : cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) th = ct at hseg hpos ⊢ hτ
  generalize hce : cstmt ⟨C.Γ, ct.2, C.brk, C.cont⟩ (pos + (cexpr C.Γ 0 pos c).length + 2 +
    ct.1.length + 1) el = ce at hseg hpos ⊢ hτ
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, p2⟩, ⟨g3, p3⟩, ⟨g4, hpe⟩, g5, hpend⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc (seg_app_iff.mpr ⟨g1, g2⟩) hpe hA hsr hev
  rw [hfa] at r1
  rw [if_neg (by simp [hfa])] at hpc1
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret, hnorm⟩ := hτ code st1 d env st'' t loop B1 hel
    (by have := hAt.after (p := pos + (cexpr C.Γ 0 pos c).length + 2) th (by omega) (Nat.le_succ _)
          (by rw [hct]; exact hpe); rwa [hct] at this) hst2
    g5 hpend hloop hpc1 hsr1
  refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, hret, hnorm⟩
  rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega

def wBodyC (C : Ctx) (pos : Nat) (c : Expr) (b : Stmt) : Ctx :=
  ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩

structure WSetup (code : List Ins) (C : Ctx) (pos : Nat) (c : Expr) (b : Stmt) : Prop where
  g12 : Seg code pos (cexpr C.Γ 0 pos c ++ [.br .ne a0 0 (bSkip 1),
    .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1)
      (pos + (cexpr C.Γ 0 pos c).length + 2 +
        (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1))])
  bpos : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2)
  g3 : Seg code (pos + (cexpr C.Γ 0 pos c).length + 2)
    (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1
  p3 : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length)
  g4 : code[pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length]? =
    some (.jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length) pos))
  pe : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1)
  len : (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length =
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length
  total : pos + (cstmt C pos (.whileStmt c b)).1.length = pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1

theorem wsetup {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt}
    (hseg : Seg code pos (cstmt C pos (.whileStmt c b)).1)
    (hpos : PosOK (pos + (cstmt C pos (.whileStmt c b)).1.length)) : WSetup code C pos c b := by
  have ht1 := cstmt_targets C 0 0 (pos + (cexpr C.Γ 0 pos c).length + 2) b
  have ht2 := cstmt_targets C (pos + (cexpr C.Γ 0 pos c).length + 2 +
    (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1) pos
    (pos + (cexpr C.Γ 0 pos c).length + 2) b
  have hlen : (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length =
      (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length := by
    rw [wBodyC, ht2.1, ← ht1.1]
  rw [cstmt_while] at hseg hpos
  dsimp only at hseg hpos
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨⟨g1, -⟩, ⟨g2, hbpos⟩, ⟨g3, p3⟩, g4, p4⟩ := h
  refine ⟨seg_app_iff.mpr ⟨g1, g2⟩, hbpos, g3, p3, g4.head, ?_, hlen, ?_⟩
  · have : PosOK (pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1) := p4
    rwa [hlen] at this
  · rw [cstmt_while]; dsimp only
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length =
      (cstmt ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
        (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩
        (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length := rfl
    omega

theorem wBodyC_at {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt} (hAt : At code C pos) (hw : WSetup code C pos c b) :
    At code (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) :=
  ⟨hAt.lay, hAt.ne, hAt.nd, hAt.lt, hAt.nat, by have := hAt.nextle; simp only [wBodyC]; omega, hw.bpos⟩

theorem tWhileFT {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt} {lc : EL} :
    STr C pos (.whileStmt c b) (.whileF lc) := by
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) false,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | whileFalse _ _ _ _ _ _ v _ hev hfa =>
  obtain ⟨hc, hsb⟩ := hs
  have hw := wsetup hseg hpos
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc hw.g12 hw.pe hA hsr hev
  rw [hfa] at r1
  rw [if_neg (by simp [hfa])] at hpc1
  exact ⟨B1, r1, by rw [hpc1]; simp only [exitPos]; rw [hw.total], hsr1, hsp1, by simp, fun _ => rfl⟩

theorem tWhileBrkT {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt} {lc : EL} {lb : SL}
    (ihb : STr (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b lb) :
    STr C pos (.whileStmt c b) (.whileBrk lc lb) := by
  obtain ⟨τ, hτ⟩ := ihb
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) true ++ τ,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | whileBreak _ _ _ _ _ st1 _ v _ _ hev htr hb =>
  obtain ⟨hc, hsb⟩ := hs
  have hw := wsetup hseg hpos
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc hw.g12 hw.pe hA hsr hev
  rw [htr] at r1
  rw [if_pos htr] at hpc1
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, -, -⟩ := hτ code st1 d env _ .brk true B1 hb (wBodyC_at hAt hw) hsb
    hw.g3 hw.p3 (fun _ => ⟨hw.pe, hAt.posok⟩) hpc1 hsr1
  refine ⟨B2, r1.trans r2, ?_, hsr2, hsp1.trans hsp2, by simp, fun _ => rfl⟩
  rw [hpc2]; simp only [exitPos, wBodyC]; rw [hw.total]

theorem tWhileRetT {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt} {lc : EL} {lb : SL}
    (ihb : STr (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b lb) :
    STr C pos (.whileStmt c b) (.whileRet lc lb) := by
  obtain ⟨τ, hτ⟩ := ihb
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) true ++ τ,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | whileRet _ _ _ _ _ st1 _ v rv _ _ hev htr hb =>
  obtain ⟨hc, hsb⟩ := hs
  have hw := wsetup hseg hpos
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc hw.g12 hw.pe hA hsr hev
  rw [if_pos htr] at hpc1
  obtain ⟨B2, -, -, -, -, hret, -⟩ := hτ code st1 d env _ _ true B1 hb (wBodyC_at hAt hw) hsb
    hw.g3 hw.p3 (fun _ => ⟨hw.pe, hAt.posok⟩) hpc1 hsr1
  exact absurd rfl (hret rv)

def backTr (C : Ctx) (pos : Nat) (c : Expr) (b : Stmt) (lb : SL) : List Obs :=
  if lb.st = .normal then
    [pobs (pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length)]
  else []

theorem tWhileLoopT {C : Ctx} {pos : Nat} {c : Expr} {b : Stmt} {lc : EL} {lb lr : SL}
    (ihb : STr (wBodyC C pos c b) (pos + (cexpr C.Γ 0 pos c).length + 2) b lb)
    (ihr : STr C pos (.whileStmt c b) lr) :
    STr C pos (.whileStmt c b) (.whileLoop lc lb lr) := by
  obtain ⟨τ, hτ⟩ := ihb
  obtain ⟨τr, hτr⟩ := ihr
  refine ⟨etr C.Γ 0 pos c lc ++ condTr (pos + (cexpr C.Γ 0 pos c).length) true ++ τ ++
      backTr C pos c b lb ++ τr,
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D with
  | whileLoop _ _ _ _ _ st1 st2 _ v tb _ _ _ _ hev htr hb htb hrest =>
  have hs0 := hs
  obtain ⟨hc, hsb⟩ := hs
  have hw := wsetup hseg hpos
  obtain ⟨B1, r1, hsr1, hsp1, hpc1⟩ := condTT hAt hc hw.g12 hw.pe hA hsr hev
  rw [htr] at r1
  rw [if_pos htr] at hpc1
  obtain ⟨B2, r2, hpc2, hsr2, hsp2, hret2, -⟩ := hτ code st1 d env st2 tb true B1 hb (wBodyC_at hAt hw) hsb
    hw.g3 hw.p3 (fun _ => ⟨hw.pe, hAt.posok⟩) hpc1 hsr1
  have hst := execL_st hb hret2
  have hback : ReachesT code B2 (backTr C pos c b lb)
      fun B3 => B3.pc = pcOf pos ∧ B3.mem = B2.mem ∧ B3.out = B2.out := by
    rcases htb with rfl | rfl
    · simp only [exitPos] at hpc2
      simp only [backTr, ← hst, ite_true]
      exact ⟨_, jumpT hAt.fits hw.g4 hpc2 hw.p3 hAt.posok, rfl, rfl, rfl⟩
    · simp only [backTr, ← hst]
      exact ⟨B2, .refl _, hpc2, rfl, rfl⟩
  obtain ⟨B3, r3, hpc3, hm3, ho3⟩ := hback
  obtain ⟨B4, r4, hpc4, hsr4, hsp4, hret4, hnorm4⟩ := hτr code st2 d env st'' t loop B3 hrest hAt hs0
    hseg hpos hloop hpc3 ⟨by rw [hm3]; exact hsr2.1, by simp only [outStr] at *; rw [ho3]; exact hsr2.2⟩
  exact ⟨B4, (((r1.trans r2).trans r3).trans r4), hpc4, hsr4, hsp1.trans (hsp2.trans hsp4), hret4, hnorm4⟩

theorem sim_declT {C : Ctx} {pos : Nat} {x : String} {e : Expr} {st st' : St} {d : Nat} {env : Addr}
    {v : Value} {l : EL} {A : AM} (hAt : At code C pos) (hnat : ¬ IsNative x) (he : IntE C.Γ.names e)
    (hseg : Seg code pos (declCode C pos x e)) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A)
    (hev : EvalL st d env e st' v l) :
    ReachesT code A (etr C.Γ 0 pos e l ++ stTr (pos + (cexpr C.Γ 0 pos e).length)
      (varAddr (declInfo C x).2.1)) fun B =>
      B.pc = pcOf (pos + (declCode C pos x e).length) ∧
      SR (declInfo C x).1 env ⟨st'.store.define env x v, st'.out⟩ B ∧
      SameParents st.store (st'.store.define env x v) ∧
      At code ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ (pos + (declCode C pos x e).length) := by
  have hs := IntE.simple he
  have hend := Seg.end_ok hAt.fits hseg (by simp [declCode])
  unfold declCode at hseg
  rw [List.append_assoc] at hseg
  obtain ⟨⟨hs1, p1⟩, hs2, -⟩ := segP_app.mp ⟨hseg, by rwa [declCode, List.append_assoc] at hend⟩
  obtain ⟨B1, r1, hev', hty, hout, hBo, hBpc, hB0, hBc, -⟩ := simT_expr hAt.lay hAt.nd hAt.slot_bound e hs
    0 pos st d env A st' v l (.inl he)
    (by have := tdepth_le C.Γ e 0 pos hs; have := p1.small; omega) hs1 p1 hA hsr.1 hev
  obtain ⟨n, rfl, hn⟩ := hty.1 he
  obtain ⟨f, g, hΓ, hdi⟩ := declInfo_cases C x hAt.ne
  have hslot : (declInfo C x).2.1 < 2 ^ 24 := by
    have := hAt.nextle; have := hAt.posok.small
    rcases hdi with ⟨i, hl, hdi⟩ | ⟨hl, hdi⟩
    · rw [hdi]; exact hAt.slot_bound i (resolve_mem (x := x) (by simp [hΓ, Scope.resolve, hl]))
    · rw [hdi]; simp; omega
  have r2 := run_stAT hAt.fits hs2 hBpc hB0 (by decide) (varAddr_st hslot)
  refine ⟨_, r1.trans r2, by simp only [declCode, List.length_append]; congr 1; simp; omega, ?_,
    (EvalE.sameParents e hs hev').trans (sameParents_define _ _ _ _), ?_⟩
  · refine ⟨?_, by simp only [outStr]; rw [hBo]; exact hsr.2.trans hout.symm⟩
    have hc := hBc
    rw [hΓ] at hc
    have hnd := hAt.nd
    rw [hΓ] at hnd
    rcases hdi with ⟨i, hl, hdi⟩ | ⟨hl, hdi⟩
    · rw [hdi, hΓ]
      exact hc.define_old hl hnd (slotV_write_self _ _ _ hn) (fun j _ hj => slotV_write_other _ _ _ _ hj)
    · rw [hdi]
      dsimp only
      refine hc.define_new hl hnat (fun h => ?_) (slotV_write_self _ _ _ hn)
        (fun j hj => slotV_write_other _ _ _ _ ?_)
      · have := hAt.lt _ (hΓ ▸ h); omega
      · intro e; subst e; have := hAt.lt _ (hΓ ▸ hj); omega
  · have hn0 := hAt.nextle
    have hlt := hAt.lt
    have hnat0 := hAt.nat
    have hnd0 := hAt.nd
    rw [hΓ] at hlt hnat0 hnd0
    refine ⟨hAt.lay, ?_, ?_, ?_, ?_, ?_, hend⟩ <;>
      rcases hdi with ⟨i, hl, hdi⟩ | ⟨hl, hdi⟩ <;> simp only [hdi]
    · rw [hΓ]; simp
    · simp
    · rw [hΓ]; exact hnd0
    · simp only [slots_cons, List.map_cons, List.cons_append] at hnd0 ⊢
      exact List.nodup_cons.mpr ⟨fun h => (by have := hlt _ (by rw [slots_cons]; exact h); omega), hnd0⟩
    · rw [hΓ]; exact hlt
    · intro j hj
      simp only [slots_cons, List.map_cons, List.cons_append, List.mem_cons] at hj
      rcases hj with rfl | hj
      · omega
      · have := hlt j (by rw [slots_cons]; exact hj); omega
    · rw [hΓ]; exact hnat0
    · intro fr hfr y hy
      rcases List.mem_cons.mp hfr with rfl | hfr
      · have hyx : y ≠ x := fun e => hnat (e ▸ hy)
        simp only [List.lookup_cons, show (y == x) = false by simpa using hyx]
        exact hnat0 f (List.mem_cons_self ..) y hy
      · exact hnat0 fr (List.mem_cons_of_mem _ hfr) y hy
    · simp only [declCode, List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [declCode, List.length_append, List.length_cons, List.length_nil]; omega

theorem sNilT {C : Ctx} {pos : Nat} : QTr C pos [] [] := by
  refine ⟨[], fun code st d env st' t loop A f g D hΓ hAt hs hseg hpos hloop hA hsr => ?_⟩
  cases D
  exact ⟨A, .refl _, by simp [cseq, exitPos, hA], hsr.2, .refl _, by simp, fun _ => rfl,
    f, by rw [← hΓ]; exact hsr.1, fun _ => by simp [cseq, hΓ]⟩

theorem sConsDeclT {C : Ctx} {pos : Nat} {x : String} {e : Expr} {ss : List Stmt} {l : EL} {ls : List SL}
    (ih : QTr ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ (pos + (declCode C pos x e).length)
      ss ls) :
    QTr C pos (.varDecl x (some e) :: ss) (.varInit l :: ls) := by
  obtain ⟨τ, hτ⟩ := ih
  refine ⟨etr C.Γ 0 pos e l ++ stTr (pos + (cexpr C.Γ 0 pos e).length) (varAddr (declInfo C x).2.1) ++ τ,
    fun code st d env st'' t loop A f g D hΓ hAt hs hseg hpos hloop hA hsr => ?_⟩
  obtain ⟨hnat, he, hss⟩ := hs
  cases D with
  | consNormal _ _ _ _ _ st1 _ _ _ _ h1 h2 =>
    cases h1 with
    | varInit _ _ _ _ _ st' v _ hev =>
    unfold QPost
    rw [cseq_decl] at hseg hpos ⊢
    dsimp only at hseg hpos ⊢
    obtain ⟨⟨hs1, -⟩, hs2, hp2⟩ := segP_app.mp ⟨hseg, hpos⟩
    obtain ⟨B1, r1, hpc1, hsr1, hsp1, hAt1⟩ := sim_declT hAt hnat he hs1 hA hsr hev
    have hf1 := declInfo_cons x hΓ
    simp only [List.length_append]
    obtain ⟨B2, r2, hpc2, hout2, hsp2, hret2, hnorm2, f', hc2, hΓ2⟩ :=
      hτ code _ d env st'' t loop B1 _ g h2 hf1 hAt1
        (by rw [declInfo_names C x hAt.ne]; exact hss) hs2 hp2 hloop hpc1 hsr1
    refine ⟨B2, r1.trans r2, by rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega,
      hout2, hsp1.trans hsp2, hret2, hnorm2, f', hc2, hΓ2⟩
  | consAbrupt _ _ _ _ _ _ _ _ h1 hne =>
    cases h1 with | varInit => exact absurd rfl hne

theorem sConsStmtT {C : Ctx} {pos : Nat} {s : Stmt} {ss : List Stmt} {l : SL} {ls : List SL}
    (hd : ∀ x e, s ≠ .varDecl x (some e)) (h1 : STr C pos s l)
    (ih : QTr ⟨C.Γ, (cstmt C pos s).2, C.brk, C.cont⟩ (pos + (cstmt C pos s).1.length) ss ls) :
    QTr C pos (s :: ss) (l :: ls) := by
  obtain ⟨τ1, h1⟩ := h1
  obtain ⟨τ, hτ⟩ := ih
  refine ⟨τ1 ++ (if ls = [] ∧ l.st ≠ .normal then [] else τ),
    fun code st d env st'' t loop A f g D hΓ hAt hs hseg hpos hloop hA hsr => ?_⟩
  obtain ⟨hs1, hss⟩ := SupSeq_other hd hs
  unfold QPost
  rw [cseq_other C pos s ss hd] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  obtain ⟨⟨hsg1, hp1⟩, hsg2, hp2⟩ := segP_app.mp ⟨hseg, hpos⟩
  simp only [List.length_append]
  cases D with
  | consNormal _ _ _ _ _ st1 _ _ _ _ D1 D2 =>
    obtain ⟨B1, r1, hpc1, hsr1, hsp1, hret1, hnorm1⟩ := h1 code st d env st1 .normal loop A D1 hAt hs1
      hsg1 hp1 hloop hA hsr
    have hst := execL_st D1 hret1
    have hif : (if ls = [] ∧ l.st ≠ .normal then ([] : List Obs) else τ) = τ := by
      rw [if_neg (fun h => h.2 hst.symm)]
    rw [hif]
    obtain ⟨B2, r2, hpc2, hout2, hsp2, hret2, hnorm2, f', hc2, hΓ2⟩ :=
      hτ code st1 d env st'' t loop B1 f g D2 hΓ (hAt.after s (Nat.le_refl _) (Nat.le_refl _) hp1)
        hss hsg2 hp2 hloop hpc1 hsr1
    refine ⟨B2, r1.trans r2, by rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega,
      hout2, hsp1.trans hsp2, hret2, hnorm2, f', hc2, hΓ2⟩
  | consAbrupt _ _ _ _ _ _ _ _ D1 hne =>
    obtain ⟨B1, r1, hpc1, hsr1, hsp1, hret1, hnorm1⟩ := h1 code st d env st'' t loop A D1 hAt hs1
      hsg1 hp1 hloop hA hsr
    have hst := execL_st D1 hret1
    have hif : (if ([] : List SL) = [] ∧ l.st ≠ .normal then ([] : List Obs) else τ) = [] := by
      rw [if_pos ⟨rfl, fun h => hne (hst.trans h)⟩]
    rw [hif, List.append_nil]
    refine ⟨B1, r1, by rw [hpc1, exitPos_abrupt C _ _ hne], hsr1.2, hsp1, hret1, hnorm1, f,
      by rw [← hΓ]; exact hsr1.1, fun h => absurd h hne⟩

end

end Vsa.Compiler
