import Vsa.CT.TOps
import Vsa.CT.Agree

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def cbinTr (p : Nat) (op : BinOp) (d : Option (Int × Int)) : List Obs :=
  match op with
  | .add | .sub | .lt | .gt => lin p 1
  | .le | .ge => lin p 3
  | .eq => lin p 6
  | .ne => lin p 4
  | .mul => mulTr p
  | .div | .mod =>
    match d with
    | some (a, b) => [pobs p, pobs (p + 2), pobs (p + 3), lobs (p + 4) (BitVec.ofInt 64 a) (BitVec.ofInt 64 b)]
    | none => []

def etr (Γ : Scope) (k pos : Nat) : Expr → EL → List Obs
  | .int n, _ => lin pos (li a0 (BitVec.ofInt 64 n)).length
  | .bool _, _ => lin pos 1
  | .var x, _ => ldTr pos (varAddr ((Γ.resolve x).getD 0))
  | .assign x e, .asg l =>
    etr Γ k pos e l ++ stTr (pos + (cexpr Γ k pos e).length) (varAddr ((Γ.resolve x).getD 0))
  | .binary op l r, .bin ll lr d =>
    let p1 := pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length
    let p2 := p1 + (cexpr Γ (k + 1) p1 r).length
    let p4 := p2 + ([mv a1 a0] ++ liN s2 (tempAddr k) ++ [Ins.ld a0 s2]).length
    etr Γ k pos l ll ++ stTr (pos + (cexpr Γ k pos l).length) (tempAddr k) ++
      etr Γ (k + 1) p1 r lr ++ [pobs p2] ++ ldTr (p2 + 1) (tempAddr k) ++ cbinTr p4 op d
  | .unary .neg e, .un l => etr Γ k pos e l ++ lin (pos + (cexpr Γ k pos e).length) 1
  | .unary .not e, .un l => etr Γ k pos e l ++ lin (pos + (cexpr Γ k pos e).length) 5
  | _, _ => []

section
variable {code : List Ins}

theorem tail_doneT {op : BinOp} {a b : Int} {p len : Nat} {A : AM} {v : Value} {τ : List Obs}
    (h : ∃ L, StarT code τ A ⟨pcOf (p + len), L, A.mem, A.out⟩ ∧ Has L a0 (word v))
    (hsem : ∀ s, binOpSem s op (.int a) (.int b) = some v)
    (har : ArithOp op → IsInt v) (hcm : CmpOp op → IsBool v) :
    ReachesT code A τ (fun B => TailDone op a b p len A B v) := by
  obtain ⟨L, hs, hl⟩ := h
  exact ⟨_, hs, rfl, hsem, rfl, rfl, hl, har, hcm⟩

theorem sim_sltT (hfit : Fits code) {r1 r2 p : Nat} {A : AM} {x y : BitVec 64}
    (hseg : Seg code p [.slt a0 r1 r2]) (hA : A.pc = pcOf p)
    (h1 : Has A.regs r1 x) (h2 : Has A.regs r2 y) :
    ∃ L, StarT code (lin p 1) A ⟨pcOf (p + 1), L, A.mem, A.out⟩ ∧ Has L a0 (sltW x y) :=
  ⟨_, singleP hfit hseg.head trivial hA (step_slt hfit hseg.head hA (by decide) h1 h2),
    Has.set_self _ _ (by decide) (by decide)⟩

theorem sim_sltFlipT (hfit : Fits code) {r1 r2 p : Nat} {A : AM} {a b : Int}
    (hseg : Seg code p ([.slt a0 r1 r2] ++ flip)) (hA : A.pc = pcOf p)
    (ha : InRange a) (hb : InRange b)
    (h1 : Has A.regs r1 (BitVec.ofInt 64 a)) (h2 : Has A.regs r2 (BitVec.ofInt 64 b)) :
    ∃ L, StarT code (lin p 3) A ⟨pcOf (p + 3), L, A.mem, A.out⟩ ∧
      Has L a0 (if decide (a < b) then 0 else 1) := by
  obtain ⟨s1, s2⟩ := hseg.append
  obtain ⟨L, r1, hl⟩ := sim_sltT hfit s1 hA h1 h2
  rw [sltW_ofInt ha hb] at hl
  obtain ⟨L', r2, hl'⟩ := run_flipT hfit s2 (A := ⟨_, L, A.mem, A.out⟩) rfl hl
  exact ⟨L', by simpa [lin] using r1.trans r2, hl'⟩

theorem sim_eqneT (hfit : Fits code) {p : Nat} {A : AM} {a b : Int}
    (hseg : Seg code p ([.sub a0 a0 a1] ++ nez)) (hA : A.pc = pcOf p)
    (ha : InRange a) (hb : InRange b)
    (h0 : Has A.regs a0 (BitVec.ofInt 64 a)) (h1 : Has A.regs a1 (BitVec.ofInt 64 b)) :
    ∃ L, StarT code (lin p 4) A ⟨pcOf (p + 4), L, A.mem, A.out⟩ ∧
      Has L a0 (if decide (a ≠ b) then 1 else 0) := by
  obtain ⟨s1, s2⟩ := hseg.append
  have e := step_sub hfit s1.head hA (by decide) h0 h1
  obtain ⟨L, r2, hl⟩ := run_nezT hfit s2 (A := ⟨_, _, A.mem, A.out⟩) rfl
    (Has.set_self (rd := a0) _ (BitVec.ofInt 64 a - BitVec.ofInt 64 b) (by decide) (by decide))
  rw [nezW_sub ha hb] at hl
  exact ⟨L, by simpa [lin] using stepP hfit s1.head trivial hA e r2, hl⟩

theorem sim_cbinT (hL : Layout code) {op : BinOp} (hop : ArithOp op ∨ CmpOp op) {p : Nat} {A : AM}
    {a b : Int} {v : Value} (ha : InRange a) (hb : InRange b)
    (hseg : Seg code p (cbin p op)) (hA : A.pc = pcOf p) (hpos : PosOK (p + (cbin p op).length))
    (h0 : Has A.regs a0 (BitVec.ofInt 64 a)) (h1 : Has A.regs a1 (BitVec.ofInt 64 b))
    {s : Store} (hv : binOpSem s op (.int a) (.int b) = some v) :
    ReachesT code A (cbinTr p op (divInfo op (.int a) (.int b)))
      (fun B => TailDone op a b p (cbin p op).length A B v) := by
  have hfit := hL.1
  have hxa : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_range ha
  have hxb : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_range hb
  have hsem : ∀ s', binOpSem s' op (.int a) (.int b) = some v := fun s' => by
    rw [← hv]; cases op <;> rfl
  rcases hop with hop | hop
  · have hna : ¬ CmpOp op := by
      rcases hop with rfl|rfl|rfl|rfl|rfl <;> simp [CmpOp]
    rcases hop with rfl|rfl|rfl|rfl|rfl
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      have e := step_add hfit hseg.head hA (by decide) h0 h1
      refine tail_doneT ⟨_, singleP hfit hseg.head trivial hA e, ?_⟩ hsem
        (fun _ => ⟨_, rfl, InRange.wrap64 _⟩) (fun h => absurd h hna)
      simp only [word, ofInt_wrap64, BitVec.ofInt_add]
      exact Has.set_self _ _ (by decide) (by decide)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      have e := step_sub hfit hseg.head hA (by decide) h0 h1
      refine tail_doneT ⟨_, singleP hfit hseg.head trivial hA e, ?_⟩ hsem
        (fun _ => ⟨_, rfl, InRange.wrap64 _⟩) (fun h => absurd h hna)
      have : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
        rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
      simp only [word, ofInt_wrap64, this]
      exact Has.set_self (rd := a0) _ _ (by decide) (by decide)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      have hc : cbin p .mul = ctMul := rfl
      rw [hc] at hseg hpos ⊢
      obtain ⟨L, hs, hl⟩ := run_ctMulT hfit hseg hA hpos h0 h1
      refine tail_doneT ⟨L, hs, ?_⟩ hsem (fun _ => ⟨_, rfl, InRange.wrap64 _⟩) (fun h => absurd h hna)
      simpa only [word, ofInt_wrap64, BitVec.ofInt_mul] using hl
    · have hb0 : b ≠ 0 := by
        intro h; subst h; simp [binOpSem] at hv
      simp only [binOpSem, hb0, beq_iff_eq, if_false, Option.some.injEq] at hv; subst hv
      have hc : cbin p .div = [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (p + 1) errPos)] ++
          libc (p + 2) divPC := rfl
      rw [hc] at hseg hpos ⊢
      obtain ⟨h12, h3⟩ := hseg.append
      have hbb : codeBase = 0x80004800 := rfl
      have ht0 : tohostAddr = 0x8001ad00 := rfl
      have hlen : (libc (p + 2) divPC).length = 3 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, hlen] at hpos
      have hs := pcOf_skip p 1 (by unfold PosOK at *; omega) (by decide)
      have e1 := step_br hfit h12.head hA h1 (Has.zero _)
        (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
      rw [hs] at e1
      have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 b) 0 = true := by
        simp only [BrOp.bop, guardB]
        have : BitVec.ofInt 64 b ≠ 0 := fun e => hb0 (by
          have := congrArg BitVec.toInt e; rw [hxb] at this; simpa using this)
        simpa using this
      rw [hg, if_pos rfl] at e1
      have r2 := run_libcT (A := ⟨pcOf (p + 1 + 1), A.regs, A.mem, A.out⟩) hfit
        h3 (by simp) (by unfold PosOK at *; omega) (.inr (by simp [divPC, modPC, mulPC])) h0 h1
        (r := BitVec.ofInt 64 (a.tdiv b)) (by simp [libRes, mulPC, divPC, modPC, hxa, hxb, hb0])
      refine ⟨_, stepP hfit h12.head trivial hA e1 r2, rfl, hsem, ?_, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩
      · simp only [List.length_append, hlen]; simp
      · simp only [word, ofInt_wrap64]
        exact Has.cons_self _ 10 _ (by decide) (by decide)
    · have hb0 : b ≠ 0 := by
        intro h; subst h; simp [binOpSem] at hv
      simp only [binOpSem, hb0, beq_iff_eq, if_false, Option.some.injEq] at hv; subst hv
      have hc : cbin p .mod = [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (p + 1) errPos)] ++
          libc (p + 2) modPC := rfl
      rw [hc] at hseg hpos ⊢
      obtain ⟨h12, h3⟩ := hseg.append
      have hbb : codeBase = 0x80004800 := rfl
      have ht0 : tohostAddr = 0x8001ad00 := rfl
      have hlen : (libc (p + 2) modPC).length = 3 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, hlen] at hpos
      have hs := pcOf_skip p 1 (by unfold PosOK at *; omega) (by decide)
      have e1 := step_br hfit h12.head hA h1 (Has.zero _)
        (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
      rw [hs] at e1
      have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 b) 0 = true := by
        simp only [BrOp.bop, guardB]
        have : BitVec.ofInt 64 b ≠ 0 := fun e => hb0 (by
          have := congrArg BitVec.toInt e; rw [hxb] at this; simpa using this)
        simpa using this
      rw [hg, if_pos rfl] at e1
      have r2 := run_libcT (A := ⟨pcOf (p + 1 + 1), A.regs, A.mem, A.out⟩) hfit
        h3 (by simp) (by unfold PosOK at *; omega) (.inr (by simp [divPC, modPC, mulPC])) h0 h1
        (r := BitVec.ofInt 64 (a.tmod b)) (by simp [libRes, mulPC, divPC, modPC, hxa, hxb, hb0])
      refine ⟨_, stepP hfit h12.head trivial hA e1 r2, rfl, hsem, ?_, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩
      · simp only [List.length_append, hlen]; simp
      · simp only [word, ofInt_wrap64]
        exact Has.cons_self _ 10 _ (by decide) (by decide)
  · have hna : ¬ ArithOp op := by
      rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [ArithOp]
    have hb1 : ∀ c : Bool, (CmpOp op → IsBool (.bool c)) := fun c _ => ⟨c, rfl⟩
    have hn1 : ∀ v, ArithOp op → IsInt v := fun _ h => absurd h hna
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      obtain ⟨L, hs, hl⟩ := sim_sltT hfit hseg hA h0 h1
      rw [sltW_ofInt ha hb, ← word_bool] at hl
      exact tail_doneT ⟨L, hs, hl⟩ hsem (hn1 _) (hb1 _)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      obtain ⟨L, hs, hl⟩ := sim_sltFlipT hfit hseg hA hb ha h1 h0
      have : (if decide (b < a) then (0 : BitVec 64) else 1) = word (.bool (decide (a ≤ b))) := by
        by_cases h : b < a
        · simp [h, word, show ¬ a ≤ b by omega]
        · simp [h, word, show a ≤ b by omega]
      rw [this] at hl
      exact tail_doneT ⟨L, hs, hl⟩ hsem (hn1 _) (hb1 _)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      obtain ⟨L, hs, hl⟩ := sim_sltT hfit hseg hA h1 h0
      rw [sltW_ofInt hb ha, ← word_bool] at hl
      exact tail_doneT ⟨L, hs, hl⟩ hsem (hn1 _) (hb1 _)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      obtain ⟨L, hs, hl⟩ := sim_sltFlipT hfit hseg hA ha hb h0 h1
      have : (if decide (a < b) then (0 : BitVec 64) else 1) = word (.bool (decide (a ≥ b))) := by
        by_cases h : a < b
        · simp [h, word, show ¬ a ≥ b by omega]
        · simp [h, word, show a ≥ b by omega]
      rw [this] at hl
      exact tail_doneT ⟨L, hs, hl⟩ hsem (hn1 _) (hb1 _)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      have hseg' : Seg code p ([.sub a0 a0 a1] ++ nez ++ flip) := hseg
      obtain ⟨s12, s3⟩ := hseg'.append
      have s3' : Seg code (p + 4) flip := s3
      obtain ⟨L, r1, hl⟩ := sim_eqneT hfit s12 hA ha hb h0 h1
      obtain ⟨L', r2, hl'⟩ := run_flipT hfit s3' (A := ⟨_, L, A.mem, A.out⟩) rfl hl
      have htr : cbinTr p .eq (divInfo .eq (.int a) (.int b)) = lin p 4 ++ lin (p + 4) 2 := by
        rw [← lin_add]; rfl
      have hlen : (cbin p .eq).length = 4 + 2 := rfl
      have : (if decide (a ≠ b) then (0 : BitVec 64) else 1) = word (.bool (Value.equal (.int a) (.int b))) := by
        by_cases h : a = b
        · simp [h, word, Value.equal]
        · simp [h, word, Value.equal]
      rw [this] at hl'
      rw [htr, hlen]
      exact tail_doneT ⟨L', r1.trans r2, hl'⟩ hsem (hn1 _) (hb1 _)
    · simp only [binOpSem, Option.some.injEq] at hv; subst hv
      obtain ⟨L, hs, hl⟩ := sim_eqneT hfit hseg hA ha hb h0 h1
      have : (if decide (a ≠ b) then (1 : BitVec 64) else 0) =
          word (.bool (!Value.equal (.int a) (.int b))) := by
        by_cases h : a = b
        · simp [h, word, Value.equal]
        · simp [h, word, Value.equal]
      rw [this] at hl
      exact tail_doneT ⟨L, hs, hl⟩ hsem (hn1 _) (hb1 _)

end

end Vsa.Compiler

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section
variable {code : List Ins}

def SimET (code : List Ins) (Γ : Scope) (e : Expr) : Prop :=
  ∀ (k pos : Nat) (st : St) (d : Nat) (env : Addr) (A : AM) (st' : St) (v : Value) (l : EL),
    CondE Γ.names e → k + tdepth e < 2 ^ 17 → Seg code pos (cexpr Γ k pos e) →
    PosOK (pos + (cexpr Γ k pos e).length) → A.pc = pcOf pos → Chain st.store A.mem env Γ →
    EvalL st d env e st' v l →
    ReachesT code A (etr Γ k pos e l) (fun B => ExprDone Γ e k pos st d env A B v st')

theorem simT_int (hL : Layout code) {Γ : Scope} {n : Int} : SimET code Γ (.int n) := by
  intro k pos st d env A st' v l hE hk hseg hpos hA hc hev
  have hn : InRange n := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  cases hev
  exact ⟨_, run_liT hL.1 hseg hA (by decide), .int _ _ _ _, ⟨fun _ => ⟨n, rfl, hn⟩, fun h => h.elim⟩,
    rfl, rfl, rfl, Has.set_self _ _ (by decide) (by decide), hc, fun _ _ => rfl⟩

theorem simT_bool (hL : Layout code) {Γ : Scope} {b : Bool} : SimET code Γ (.bool b) := by
  intro k pos st d env A st' v l hE hk hseg hpos hA hc hev
  cases hev
  have e := step_addi hL.1 hseg.head hA (by decide) (Has.zero _)
  refine ⟨_, singleP hL.1 hseg.head trivial hA e, .bool _ _ _ _, ⟨fun h => h.elim, fun _ => ⟨b, rfl⟩⟩,
    rfl, rfl, rfl, ?_, hc, fun _ _ => rfl⟩
  cases b <;> exact Has.set_self _ _ (by decide) (by decide)

theorem simT_var (hL : Layout code) {Γ : Scope} (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {x : String} :
    SimET code Γ (.var x) := by
  intro k pos st d env A st' v l hE hk hseg hpos hA hc hev
  have hm : Γ.names.Mem x := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  cases hev with
  | var _ _ _ _ _ hg =>
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolve_of_mem hm)
  have hseg' : Seg code pos (liN s2 (varAddr i) ++ [.ld a0 s2]) := by simpa [cexpr, hi] using hseg
  have r := run_ldAT hL.1 hseg' hA (by decide) (varAddr_ld (hsl i (resolve_mem hi)))
  have hg' := hc.get? hi
  rw [hg] at hg'; cases hg'
  have het : etr Γ k pos (.var x) .leaf = ldTr pos (varAddr i) := by simp [etr, hi]
  rw [het]
  refine ⟨_, r, ?_⟩
  refine ⟨.var _ _ _ _ _ (hc.get? hi), ⟨fun _ => ⟨_, rfl, InRange.toInt _⟩, fun h => h.elim⟩, rfl, rfl,
    by simp [cexpr, hi, Nat.add_assoc], ?_, hc, fun _ _ => rfl⟩
  simp only [word, slotV, BitVec.ofInt_toInt]
  exact Has.set_self _ _ (by decide) (by decide)

theorem simT_assign (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {x : String} {e : Expr} (ih : SimET code Γ e) :
    SimET code Γ (.assign x e) := by
  intro k pos st d env A st'' v l hE hk hseg hpos hA hc hev
  have hE' : Γ.names.Mem x ∧ IntE Γ.names e := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolve_of_mem hE'.1)
  have hil := hsl i (resolve_mem hi)
  cases hev with
  | assign _ _ _ _ _ st' _ s'' l0 he hset =>
  have hcx : cexpr Γ k pos (.assign x e) = cexpr Γ k pos e ++ (liN s2 (varAddr i) ++ [.sd a0 s2]) := by
    simp [cexpr, hi]
  rw [hcx] at hseg hpos
  obtain ⟨⟨hs1, p1⟩, hs2, -⟩ := segP_app.mp ⟨hseg, hpos⟩
  obtain ⟨B1, r1, hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ :=
    ih k pos st d env A st' v l0 (.inl hE'.2) (by simpa [tdepth] using hk) hs1 p1 hA hc he
  obtain ⟨n, rfl, hn⟩ := hty.1 hE'.2
  have r2 := run_stAT hL.1 hs2 hBpc hB0 (by decide) (varAddr_st hil)
  obtain ⟨s2', hset2, hc'', -, -⟩ := hBc.set (v := n) st'.store.frames.size hBc.env_lt hi hnd
    (slotV_write_self _ _ _ hn) (fun j _ hj => slotV_write_other _ _ _ _ hj)
  have hsame : s2' = s'' := by
    have : st'.store.set? env x (.int n) = some s2' := hset2
    rw [hset] at this; cases this; rfl
  subst hsame
  have het : etr Γ k pos (.assign x e) (.asg l0) =
      etr Γ k pos e l0 ++ stTr (pos + (cexpr Γ k pos e).length) (varAddr i) := by simp [etr, hi]
  rw [het]
  refine ⟨_, r1.trans r2, ?_⟩
  refine ⟨.assign _ _ _ _ _ _ _ _ hev hset,
    ⟨fun _ => ⟨n, rfl, hn⟩, fun h => h.elim⟩, hout, hBo, by simp [hcx, Nat.add_assoc],
    (hB0.set_other (by decide)), hc'', fun j hj => ?_⟩
  rw [rdW_write_other _ _ _ _ (.inl (slots_ne_temp hil (by simp [tdepth] at hk; omega))), hBt j hj]

theorem simT_binary (hL : Layout code) {Γ : Scope} {op : BinOp} {l r : Expr}
    (ihl : SimET code Γ l) (ihr : SimET code Γ r) : SimET code Γ (.binary op l r) := by
  intro k pos st d env A st'' v lk hE hk hseg hpos hA hc hev
  have hE' : (ArithOp op ∨ CmpOp op) ∧ IntE Γ.names l ∧ IntE Γ.names r := by
    rcases hE with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨.inl h1, h2, h3⟩
    · exact ⟨.inr h1, h2, h3⟩
  simp only [tdepth] at hk
  have hk0 : k < 2 ^ 17 := by omega
  cases hev with
  | binary _ _ _ _ _ _ st1 _ lv rv _ ll lr hl hr hb =>
  let cl := cexpr Γ k pos l
  let stc := liN s2 (tempAddr k) ++ [Ins.sd a0 s2]
  let p1 := pos + cl.length + stc.length
  let cr := cexpr Γ (k + 1) p1 r
  let ldc := [mv a1 a0] ++ liN s2 (tempAddr k) ++ [Ins.ld a0 s2]
  let p4 := p1 + cr.length + ldc.length
  have hcx : cexpr Γ k pos (.binary op l r) = cl ++ stc ++ cr ++ ldc ++ cbin p4 op := rfl
  have l1 : cl.length = (cexpr Γ k pos l).length := rfl
  have l3 : cr.length = (cexpr Γ (k + 1) p1 r).length := rfl
  have lp1 : p1 = pos + cl.length + stc.length := rfl
  have lp4 : p4 = p1 + cr.length + ldc.length := rfl
  have lst : stc.length = (liN s2 (tempAddr k)).length + 1 := by simp [stc]
  have lld : ldc.length = (liN s2 (tempAddr k)).length + 2 := by simp [ldc]
  rw [hcx] at hseg hpos
  have h := And.intro hseg hpos
  simp only [List.append_assoc] at h
  simp only [↓segP_app] at h
  obtain ⟨⟨hs1, p1'⟩, ⟨hs2, -⟩, ⟨hs3', p3⟩, ⟨hs4, -⟩, hs5', hpos4⟩ := h
  have hs4' : Seg code (p1 + cr.length) ldc := hs4
  obtain ⟨B1, r1, hevl, htyl, houtl, hB1o, hB1pc, hB1a0, hB1c, hB1t⟩ :=
    ihl k pos st d env A st1 lv ll (.inl hE'.2.1) (by omega) hs1 p1' hA hc hl
  obtain ⟨a, rfl, ha⟩ := htyl.1 hE'.2.1
  have r2 := run_stAT hL.1 hs2 hB1pc hB1a0 (by decide) (tempAddr_st hk0)
  have hc2 : Chain st1.store (applyW B1.mem (tempAddr k, 8, word (.int a))) env Γ :=
    hB1c.transport fun i _ => slotV_write_low _ _ _ _ (tempAddr_low hk0)
  obtain ⟨B3, r3, hevr, htyr, houtr, hB3o, hB3pc, hB3a0, hB3c, hB3t⟩ := ihr (k + 1) p1 st1 d env
    ⟨pcOf (pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k)).length + 1),
      gset B1.regs s2 (BitVec.ofNat 64 (tempAddr k)),
      applyW B1.mem (tempAddr k, 8, word (.int a)), B1.out⟩ st'' rv lr (.inl hE'.2.2) (by omega) hs3'
    p3 (by simp only [lp1, lst, l1]; congr 1) hc2 hr
  obtain ⟨b, rfl, hb'⟩ := htyr.1 hE'.2.2
  rw [← l3] at hB3pc
  have hmv : astep code B3 = some (.run ⟨pcOf (p1 + cr.length + 1),
      gset B3.regs a1 (BitVec.ofInt 64 b), B3.mem, B3.out⟩) := by
    rw [step_addi hL.1 hs4'.head hB3pc (by decide) hB3a0]
    have : (sign_extend (0#12) : BitVec 64) = 0 := by decide
    simp [word, this]
  have hs4'' : Seg code (p1 + cr.length + 1) (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]) :=
    (Seg.append (s := [mv a1 a0]) (t := liN s2 (tempAddr k) ++ [Ins.ld a0 s2])
      (by simpa [ldc] using hs4')).2
  have r4 := run_ldAT hL.1 hs4'' (A := ⟨pcOf (p1 + cr.length + 1), gset B3.regs a1 (BitVec.ofInt 64 b),
    B3.mem, B3.out⟩) rfl (by decide) (tempAddr_ld hk0)
  have hlv : rdW B3.mem (tempAddr k) = BitVec.ofInt 64 a := by
    rw [hB3t k (by omega)]; exact rdW_write _ _ _
  rw [hlv] at r4
  obtain ⟨B5, r5, hB5o, hsem, hB5pc, hB5m, hB5a0, hari, hcmp⟩ := sim_cbinT hL hE'.1 ha hb'
    (A := ⟨pcOf p4, gset (gset (gset B3.regs a1
    (BitVec.ofInt 64 b)) s2 (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 a), B3.mem, B3.out⟩)
    hs5' rfl hpos4
    (Has.set_self _ _ (by decide) (by decide))
    (((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other (by decide)) hb
  have r4' : StarT code (pobs (p1 + cr.length) :: ldTr (p1 + cr.length + 1) (tempAddr k)) B3
      ⟨pcOf p4, gset (gset (gset B3.regs a1 (BitVec.ofInt 64 b)) s2
      (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 a), B3.mem, B3.out⟩ := by
    refine stepP hL.1 hs4'.head trivial hB3pc hmv ?_
    have e : p1 + cr.length + 1 + (liN s2 (tempAddr k)).length + 1 = p4 := by rw [lp4, lld]; omega
    rw [e] at r4; exact r4
  have run := r1.trans (r2.trans (r3.trans (r4'.trans r5)))
  have het : etr Γ k pos (.binary op l r) (.bin ll lr (divInfo op (.int a) (.int b))) =
      etr Γ k pos l ll ++ (stTr (pos + (cexpr Γ k pos l).length) (tempAddr k) ++
      (etr Γ (k + 1) p1 r lr ++ (pobs (p1 + cr.length) :: ldTr (p1 + cr.length + 1) (tempAddr k) ++
      cbinTr p4 op (divInfo op (.int a) (.int b))))) := by
    simp only [etr, List.append_assoc, List.cons_append, List.singleton_append]; rfl
  rw [het]
  refine ⟨B5, by simpa only [List.append_assoc, List.cons_append] using run, ?_⟩
  refine ⟨.binary _ _ _ _ _ _ _ _ _ _ _ hevl hevr (hsem _),
    ⟨fun h => hari (by rcases h with ⟨h1, -⟩; exact h1), fun h => hcmp h.1⟩,
    houtr.trans houtl, ?_, ?_, hB5a0, ?_, ?_⟩
  · rw [hB5o]; exact hB3o.trans hB1o
  · rw [hB5pc, hcx]; congr 1; simp only [List.length_append]; rw [lp4, lp1]; omega
  · rw [hB5m]; exact hB3c
  · intro j hj
    rw [hB5m, hB3t j (by omega), rdW_write_other _ _ _ _ (by unfold tempAddr; omega), hB1t j hj]

theorem simT_neg (hL : Layout code) {Γ : Scope} {e : Expr} (ih : SimET code Γ e) :
    SimET code Γ (.unary .neg e) := by
  intro k pos st d env A st' v l hE hk hseg hpos hA hc hev
  have hE' : IntE Γ.names e := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  cases hev with
  | neg _ _ _ _ _ n l0 he =>
  have hcx : cexpr Γ k pos (.unary .neg e) = cexpr Γ k pos e ++ [.sub a0 0 a0] := rfl
  rw [hcx] at hseg hpos
  obtain ⟨⟨hs1, p1⟩, hs2, -⟩ := segP_app.mp ⟨hseg, hpos⟩
  obtain ⟨B1, r1, hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ :=
    ih k pos st d env A st' (.int n) l0 (.inl hE') (by simpa [tdepth] using hk) hs1 p1 hA hc he
  obtain ⟨n', hn', hn⟩ := hty.1 hE'
  cases hn'
  have e1 := step_sub hL.1 hs2.head hBpc (by decide) (Has.zero _) hB0
  have het : etr Γ k pos (.unary .neg e) (.un l0) = etr Γ k pos e l0 ++
      lin (pos + (cexpr Γ k pos e).length) 1 := rfl
  rw [het]
  refine ⟨_, r1.trans (singleP hL.1 hs2.head trivial hBpc e1), ?_⟩
  refine ⟨.neg _ _ _ _ _ _ hev, ⟨fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => h.elim⟩, hout, hBo,
    by simp [hcx, Nat.add_assoc], ?_, hBc, hBt⟩
  simp only [word, ofInt_wrap64, BitVec.ofInt_neg, BitVec.zero_sub]
  exact Has.set_self _ _ (by decide) (by decide)

theorem simT_not (hL : Layout code) {Γ : Scope} {e : Expr} (ih : SimET code Γ e) :
    SimET code Γ (.unary .not e) := by
  intro k pos st d env A st' v l hE hk hseg hpos hA hc hev
  have hE' : CondE Γ.names e := by
    rcases hE with h | h
    · exact h.elim
    · exact h
  cases hev with
  | not _ _ _ _ _ v0 l0 he =>
  have hcx : cexpr Γ k pos (.unary .not e) = cexpr Γ k pos e ++ (nez ++ flip) := by
    simp [cexpr]
  rw [hcx] at hseg hpos
  obtain ⟨⟨hs1, p1⟩, hs2, p2⟩ := segP_app.mp ⟨hseg, hpos⟩
  obtain ⟨B1, r1, hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ :=
    ih k pos st d env A st' v0 l0 hE' (by simpa [tdepth] using hk) hs1 p1 hA hc he
  obtain ⟨s2a, s2b⟩ := hs2.append
  obtain ⟨L, r2, hL0⟩ := run_nezT hL.1 s2a hBpc hB0
  have hg : nezW (word v0) = if v0.truthy then 1 else 0 := by
    rcases hE' with hi | hb
    · obtain ⟨n, rfl, hn⟩ := hty.1 hi
      simp only [word, Value.truthy, nezW]
      by_cases h : n = 0
      · subst h; decide
      · have : BitVec.ofInt 64 n ≠ (0 : BitVec 64) := fun e => h (by
          have := congrArg BitVec.toInt e; rwa [toInt_ofInt_range hn] at this)
        rw [if_neg this]; simp [h]
    · obtain ⟨b, rfl⟩ := hty.2 hb
      cases b <;> decide
  rw [hg] at hL0
  obtain ⟨L', r3, hL1⟩ := run_flipT hL.1 s2b (A := ⟨_, L, B1.mem, B1.out⟩) rfl hL0
  have het : etr Γ k pos (.unary .not e) (.un l0) = etr Γ k pos e l0 ++
      (lin (pos + (cexpr Γ k pos e).length) 3 ++ lin (pos + (cexpr Γ k pos e).length + nez.length) 2) := by
    simp only [etr]; rw [show nez.length = 3 from rfl, ← lin_add]
  rw [het]
  refine ⟨_, r1.trans (r2.trans r3), ?_⟩
  refine ⟨.not _ _ _ _ _ _ hev, ⟨fun h => h.elim, fun _ => ⟨_, rfl⟩⟩, hout, hBo, ?_, ?_, hBc, hBt⟩
  · simp [hcx, nez, flip, Nat.add_assoc]
  · cases hv : v0.truthy <;> simp [word, hv] at hL1 ⊢ <;> exact hL1

theorem simT_expr (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) : ∀ (e : Expr), Simple e → SimET code Γ e
  | .int _, _ => simT_int hL
  | .bool _, _ => simT_bool hL
  | .var _, _ => simT_var hL hsl
  | .assign _ e, hs => simT_assign hL hnd hsl (simT_expr hL hnd hsl e hs)
  | .binary _ l r, hs => simT_binary hL (simT_expr hL hnd hsl l hs.1) (simT_expr hL hnd hsl r hs.2)
  | .unary .neg e, hs => simT_neg hL (simT_expr hL hnd hsl e hs)
  | .unary .not e, hs => simT_not hL (simT_expr hL hnd hsl e hs)
  | .str _, hs => hs.elim
  | .null, hs => hs.elim
  | .logical _ _ _, hs => hs.elim
  | .call _ _, hs => hs.elim
  | .fn _ _ _, hs => hs.elim

end

end Vsa.Compiler
