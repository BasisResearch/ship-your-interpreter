import Vsa.Compiler.Rel

/-!
# Expression simulation

`sim_expr`: the code `cexpr Γ k pos e` of a supported expression either runs to
its end with the value of `e` in `a0` and the store relation re-established for
the state the (deterministic) semantics reaches, or reaches the runtime-error
exit while `e` has no evaluation.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Determinism of the supported expressions -/

/-- Expressions without calls or closures. -/
def Simple : Expr → Prop
  | .int _ | .bool _ | .var _ => True
  | .assign _ e => Simple e
  | .binary _ l r => Simple l ∧ Simple r
  | .unary _ e => Simple e
  | _ => False

theorem EvalE.det : ∀ (e : Expr), Simple e → ∀ {st : St} {d : Nat} {env : Addr} {s1 s2 : St}
    {v1 v2 : Value}, EvalE st d env e s1 v1 → EvalE st d env e s2 v2 → s1 = s2 ∧ v1 = v2
  | .int _, _, _, _, _, _, _, _, _, h1, h2 => by cases h1; cases h2; exact ⟨rfl, rfl⟩
  | .bool _, _, _, _, _, _, _, _, _, h1, h2 => by cases h1; cases h2; exact ⟨rfl, rfl⟩
  | .var _, _, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | var _ _ _ _ _ g1 =>
    cases h2 with | var _ _ _ _ _ g2 =>
    rw [g1] at g2; cases g2; exact ⟨rfl, rfl⟩
  | .assign _ e, hs, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | assign _ _ _ _ _ _ _ _ he1 hs1 =>
    cases h2 with | assign _ _ _ _ _ _ _ _ he2 hs2 =>
    obtain ⟨rfl, rfl⟩ := EvalE.det e hs he1 he2
    rw [hs1] at hs2; cases hs2; exact ⟨rfl, rfl⟩
  | .binary _ l r, hs, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | binary _ _ _ _ _ _ _ _ _ _ _ hl1 hr1 ho1 =>
    cases h2 with | binary _ _ _ _ _ _ _ _ _ _ _ hl2 hr2 ho2 =>
    obtain ⟨rfl, rfl⟩ := EvalE.det l hs.1 hl1 hl2
    obtain ⟨rfl, rfl⟩ := EvalE.det r hs.2 hr1 hr2
    rw [ho1] at ho2; cases ho2; exact ⟨rfl, rfl⟩
  | .unary .neg e, hs, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | neg _ _ _ _ _ _ he1 =>
    cases h2 with | neg _ _ _ _ _ _ he2 =>
    obtain ⟨rfl, h⟩ := EvalE.det e hs he1 he2
    cases h; exact ⟨rfl, rfl⟩
  | .unary .not e, hs, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | not _ _ _ _ _ _ he1 =>
    cases h2 with | not _ _ _ _ _ _ he2 =>
    obtain ⟨rfl, rfl⟩ := EvalE.det e hs he1 he2
    exact ⟨rfl, rfl⟩
  | .str _, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .null, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .logical _ _ _, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .call _ _, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .fn _ _ _, h, _, _, _, _, _, _, _, _, _ => h.elim

/-! ## Helper fragments -/

/-- The fixed parts of the code image: error exit and print subroutine. -/
def Layout (code : List Ins) : Prop :=
  Fits code ∧ Seg code errPos errCode ∧ Seg code printPos printCode

section
variable {code : List Ins}

theorem run_ldA (hfit : Fits code) {pos a rd : Nat} {A : AM}
    (hseg : Seg code pos (liN s2 a ++ [.ld rd s2])) (hA : A.pc = pcOf pos)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (ha : LdOK a) :
    Star code A ⟨pcOf (pos + (liN s2 a).length + 1),
      gset (gset A.regs s2 (BitVec.ofNat 64 a)) rd (rdW A.mem a), A.mem, A.out⟩ := by
  obtain ⟨h1, h2⟩ := hseg.append
  have hat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; unfold LdOK at ha; omega
  refine (run_li hfit h1 hA (by decide)).trans (Star.single ?_)
  rw [step_ld hfit h2.head rfl hrd (Has.set_self _ _ (by decide) (by decide)) (by rw [hat]; exact ha),
    hat]

theorem run_stA (hfit : Fits code) {pos a rs : Nat} {A : AM} {w : BitVec 64}
    (hseg : Seg code pos (liN s2 a ++ [.sd rs s2])) (hA : A.pc = pcOf pos)
    (hw : Has A.regs rs w) (hrs : rs ≠ s2) (ha : StOK a) :
    Star code A ⟨pcOf (pos + (liN s2 a).length + 1),
      gset A.regs s2 (BitVec.ofNat 64 a), applyW A.mem (a, 8, w), A.out⟩ := by
  obtain ⟨h1, h2⟩ := hseg.append
  have hat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; unfold StOK at ha; omega
  refine (run_li hfit h1 hA (by decide)).trans (Star.single ?_)
  rw [step_sd hfit h2.head rfl (Has.set_self _ _ (by decide) (by decide)) (hw.set_other hrs)
    (by rw [hat]; exact ha), hat]

/-- A jump to the error exit halts with code 70. -/
theorem run_err (hL : Layout code) {p : Nat} {A : AM}
    (hk : code[p]? = some (.jal 0 (jOff p errPos))) (hA : A.pc = pcOf p) (hp : PosOK p) :
    ∃ B, Star code A B ∧ astep code B = some (.halt 70) := by
  obtain ⟨hfit, herr, -⟩ := hL
  have he : PosOK errPos := by unfold PosOK errPos; unfold Fits at hfit; decide
  have hj := pcOf_jump p errPos hp he
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  have e1 := step_j hfit hk hA (by rw [hj, pcOf_toNat (by unfold PosOK at he; omega)]; decide)
  rw [hj] at e1
  obtain ⟨B, hB, -, -, hh⟩ := run_exit hfit (by decide : (70 : Nat) = 0 ∨ 70 = 70) herr
    (A := ⟨pcOf errPos, A.regs, A.mem, A.out⟩) rfl
  exact ⟨B, Star.step e1 hB, hh⟩

end

theorem varAddr_ld {i : Nat} (hi : i < 2 ^ 24) : LdOK (varAddr i) := by
  unfold LdOK varAddr varBase tohostAddr; omega

theorem varAddr_st {i : Nat} (hi : i < 2 ^ 24) : StOK (varAddr i) := by
  unfold StOK varAddr varBase tohostAddr; omega

theorem tempAddr_ld {k : Nat} (hk : k < 2 ^ 17) : LdOK (tempAddr k) := by
  unfold LdOK tempAddr tempBase tohostAddr; omega

theorem tempAddr_st {k : Nat} (hk : k < 2 ^ 17) : StOK (tempAddr k) := by
  unfold StOK tempAddr tempBase tohostAddr; omega

theorem tempAddr_low {k : Nat} (hk : k < 2 ^ 17) : tempAddr k + 8 ≤ varBase := by
  unfold tempAddr tempBase varBase; omega

/-! ## Values as words -/

/-- The machine word representing a value (integers and booleans). -/
def word : Value → BitVec 64
  | .int n => BitVec.ofInt 64 n
  | .bool b => if b then 1 else 0
  | _ => 0

theorem toInt_ofInt_range {n : Int} (h : InRange n) : (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]; obtain ⟨h1, h2⟩ := h
  apply Int.bmod_eq_of_le <;> simp <;> omega

theorem InRange.wrap64 (z : Int) : InRange (wrap64 z) := wrap64_range z

theorem InRange.toInt (x : BitVec 64) : InRange x.toInt :=
  ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩

theorem ofInt_inj_range {a b : Int} (ha : InRange a) (hb : InRange b) :
    BitVec.ofInt 64 a = BitVec.ofInt 64 b ↔ a = b := by
  constructor
  · intro h; rw [← toInt_ofInt_range ha, ← toInt_ofInt_range hb, h]
  · intro h; rw [h]

/-! ## Branch comparisons -/

section
variable {code : List Ins}

/-- `s3 := 1; b r1 r2 skip; s3 := 0; a0 := s3`. -/
theorem run_cmp (hfit : Fits code) {p r1 r2 : Nat} {b : BrOp} {A : AM} {x y : BitVec 64}
    (hseg : Seg code p [.addi s3 0 1, .br b r1 r2 (bSkip 1), .addi s3 0 0, mv a0 s3])
    (hA : A.pc = pcOf p) (hp : PosOK (p + 4))
    (h1 : Has A.regs r1 x) (h2 : Has A.regs r2 y) (hr1 : r1 ≠ s3) (hr2 : r2 ≠ s3) :
    ∃ L, Star code A ⟨pcOf (p + 4), L, A.mem, A.out⟩ ∧
      Has L a0 (if guardB b.bop x y then 1 else 0) := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hone : (0 : BitVec 64) + (sign_extend (1 : BitVec 12) : BitVec 64) = 1 := by decide
  have hzero : (0 : BitVec 64) + (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide
  have hmv : ∀ v : BitVec 64, v + (sign_extend (0 : BitVec 12) : BitVec 64) = v := by
    intro v; rw [show (sign_extend (0 : BitVec 12) : BitVec 64) = 0 by decide]; simp
  have e1 := step_addi hfit hseg.head hA (by decide) (Has.zero _)
  rw [hone] at e1
  have hs := pcOf_skip (p + 1) 1 (by unfold PosOK at *; omega) (by decide)
  have e2 := step_br hfit hseg.tail.head (A := ⟨pcOf (p + 1), gset A.regs s3 1, A.mem, A.out⟩) rfl
    (h1.set_other hr1) (h2.set_other hr2)
    (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
  rw [hs] at e2
  by_cases hg : guardB b.bop x y
  · rw [if_pos hg] at e2
    have e4 : astep code ⟨pcOf (p + 3), gset A.regs s3 1, A.mem, A.out⟩ =
        some (.run ⟨pcOf (p + 4), gset (gset A.regs s3 1) a0 1, A.mem, A.out⟩) := by
      rw [step_addi hfit (hseg.sub 3 1).head rfl (by decide)
        (Has.set_self _ _ (by decide) (by decide)), hmv]
    refine ⟨gset (gset A.regs s3 1) a0 1, Star.step e1 (Star.step ?_ (Star.single e4)), ?_⟩
    · rw [e2]
    · rw [if_pos hg]; exact Has.set_self _ _ (by decide) (by decide)
  · rw [if_neg hg] at e2
    have e3 : astep code ⟨pcOf (p + 2), gset A.regs s3 1, A.mem, A.out⟩ =
        some (.run ⟨pcOf (p + 3), gset A.regs s3 0, A.mem, A.out⟩) := by
      rw [step_addi hfit (hseg.sub 2 1).head rfl (by decide) (Has.zero _), hzero, gset_gset]
    have e4 : astep code ⟨pcOf (p + 3), gset A.regs s3 0, A.mem, A.out⟩ =
        some (.run ⟨pcOf (p + 4), gset (gset A.regs s3 0) a0 0, A.mem, A.out⟩) := by
      rw [step_addi hfit (hseg.sub 3 1).head rfl (by decide)
        (Has.set_self _ _ (by decide) (by decide)), hmv]
    refine ⟨gset (gset A.regs s3 0) a0 0, Star.step e1 (Star.step ?_ (Star.step e3 (Star.single e4))), ?_⟩
    · rw [e2]
    · rw [if_neg hg]; exact Has.set_self _ _ (by decide) (by decide)

end

/-! ## Operator tails -/

theorem guard_lt {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BLT (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) := by
  simp [guardB, zopz0zI_s, toInt_ofInt_range ha, toInt_ofInt_range hb]

theorem guard_ge {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BGE (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a ≥ b) := by
  simp [guardB, zopz0zKzJ_s, toInt_ofInt_range ha, toInt_ofInt_range hb]

theorem guard_eq {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BEQ (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a = b) := by
  simp only [guardB, beq_iff_eq]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofInt 64 a ≠ BitVec.ofInt 64 b := fun e => h ((ofInt_inj_range ha hb).mp e)
    simp [h, this]

theorem guard_ne {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BNE (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a ≠ b) := by
  simp only [guardB]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofInt 64 a ≠ BitVec.ofInt 64 b := fun e => h ((ofInt_inj_range ha hb).mp e)
    simp [h, this]

theorem Has.cons_self (L : GRegs) (n : Nat) (v : BitVec 64) (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    Has ((n, v) :: L) n v := ⟨h31, .inr ⟨by omega, by simp [lookupG]⟩⟩

section
variable {code : List Ins}

/-- The result of an arithmetic operator tail. -/
def TailOK (op : BinOp) (a b : Int) (p len : Nat) (A B : AM) : Prop :=
  ((∃ v, B.out = A.out ∧ (∀ s, binOpSem s op (.int a) (.int b) = some v) ∧ B.pc = pcOf (p + len) ∧
      B.mem = A.mem ∧ Has B.regs a0 (word v) ∧ (ArithOp op → ∃ n, v = .int n ∧ InRange n) ∧
      (CmpOp op → ∃ c, v = .bool c)) ∨
    (astep code B = some (.halt 70) ∧ ∀ s, binOpSem s op (.int a) (.int b) = none))

theorem sim_cmp (hfit : Fits code) {op : BinOp} {br : BrOp} {r1 r2 : Nat} {p : Nat} {A : AM}
    {a b : Int} {c : Bool} (hcb : cmpBranch op = some (br, r1, r2))
    (hsem : ∀ s, binOpSem s op (.int a) (.int b) = some (.bool c))
    (hg : ∀ x y, Has A.regs r1 x → Has A.regs r2 y → guardB br.bop x y = c)
    (hx : ∃ x, Has A.regs r1 x) (hy : ∃ y, Has A.regs r2 y) (hr1 : r1 ≠ s3) (hr2 : r2 ≠ s3)
    (hseg : Seg code p (cbin p op)) (hA : A.pc = pcOf p) (hpos : PosOK (p + (cbin p op).length))
    (hcmp : CmpOp op) (hna : ¬ ArithOp op) :
    ∃ B, Star code A B ∧ @TailOK code op a b p (cbin p op).length A B := by
  have hc : cbin p op = [.addi s3 0 1, .br br r1 r2 (bSkip 1), .addi s3 0 0, mv a0 s3] := by
    rcases hcmp with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [cbin, cmpBranch]
  rw [hc] at hseg hpos ⊢
  obtain ⟨x, hx⟩ := hx; obtain ⟨y, hy⟩ := hy
  obtain ⟨L, hs, hL⟩ := run_cmp hfit hseg hA hpos hx hy hr1 hr2
  refine ⟨_, hs, .inl ⟨.bool c, rfl, hsem, rfl, rfl, ?_, fun h => absurd h hna, fun _ => ⟨c, rfl⟩⟩⟩
  rw [hg x y hx hy] at hL
  cases c <;> simpa [word] using hL

end

theorem Has.a0a1 {L : GRegs} {x : BitVec 64} (h : Has L a0 x) : Has L 10 x := h

theorem lookup_of_has {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) (hn : n ≠ 0) :
    lookupG n L = some v := by
  obtain ⟨-, (⟨h0, -⟩ | ⟨-, h⟩)⟩ := h
  · exact absurd h0 hn
  · exact h

section
variable {code : List Ins}

theorem sim_lib (hfit : Fits code) {op : BinOp} {tgt p : Nat} {A : AM} {a b : Int} {r : BitVec 64}
    (hseg : Seg code p (libc p tgt)) (hA : A.pc = pcOf p) (hpos : PosOK (p + 3))
    (ht : tgt = mulPC ∨ tgt = divPC ∨ tgt = modPC)
    (h0 : Has A.regs a0 (BitVec.ofInt 64 a)) (h1 : Has A.regs a1 (BitVec.ofInt 64 b))
    (hr : libRes tgt (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = some r) :
    ∃ L, Star code A ⟨pcOf (p + 3), L, A.mem, A.out⟩ ∧ Has L a0 r :=
  ⟨_, run_libc hfit hseg hA hpos ht h0 h1 hr, Has.cons_self _ _ _ (by decide) (by decide)⟩

theorem sim_cbin (hL : Layout code) {op : BinOp} (hop : ArithOp op ∨ CmpOp op) {p : Nat} {A : AM}
    {a b : Int} (ha : InRange a) (hb : InRange b)
    (hseg : Seg code p (cbin p op)) (hA : A.pc = pcOf p) (hpos : PosOK (p + (cbin p op).length))
    (h0 : Has A.regs a0 (BitVec.ofInt 64 a)) (h1 : Has A.regs a1 (BitVec.ofInt 64 b)) :
    ∃ B, Star code A B ∧ @TailOK code op a b p (cbin p op).length A B := by
  have hfit := hL.1
  have hxa : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_range ha
  have hxb : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_range hb
  rcases hop with hop | hop
  · have hna : ¬ CmpOp op := by
      rcases hop with rfl|rfl|rfl|rfl|rfl <;> simp [CmpOp]
    rcases hop with rfl|rfl|rfl|rfl|rfl
    · -- add
      have e := step_add hfit hseg.head hA (by decide) h0 h1
      refine ⟨_, Star.single e, .inl ⟨.int (wrap64 (a + b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      simp only [word, ofInt_wrap64, BitVec.ofInt_add]
      exact Has.set_self _ _ (by decide) (by decide)
    · -- sub
      have e := step_sub hfit hseg.head hA (by decide) h0 h1
      refine ⟨_, Star.single e, .inl ⟨.int (wrap64 (a - b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      have : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
        rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
      simp only [word, ofInt_wrap64, this]
      exact Has.set_self (rd := a0) _ _ (by decide) (by decide)
    · -- mul
      obtain ⟨L, hs, hl⟩ := sim_lib (op := .mul) hfit hseg hA hpos (.inl rfl) h0 h1
        (r := BitVec.ofInt 64 a * BitVec.ofInt 64 b) (by simp [libRes])
      refine ⟨_, hs, .inl ⟨.int (wrap64 (a * b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      simpa only [word, ofInt_wrap64, BitVec.ofInt_mul] using hl
    · -- div
      have hc : cbin p .div = [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (p + 1) errPos)] ++
          libc (p + 2) divPC := rfl
      rw [hc] at hseg hpos ⊢
      obtain ⟨h12, h3⟩ := hseg.append
      have hb0 : codeBase = 0x80004800 := rfl
      have ht0 : tohostAddr = 0x8001ad00 := rfl
      have hlen : (libc (p + 2) divPC).length = 3 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, hlen] at hpos
      have hs := pcOf_skip p 1 (by unfold PosOK at *; omega) (by decide)
      have e1 := step_br hfit h12.head hA h1 (Has.zero _)
        (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
      rw [hs] at e1
      by_cases hb0' : b = 0
      · subst hb0'
        have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 0) 0 = false := by decide
        rw [hg] at e1
        simp only [Bool.false_eq_true, if_false] at e1
        obtain ⟨B, hB, hh⟩ := run_err hL (p := p + 1) (A := ⟨pcOf (p + 1), A.regs, A.mem, A.out⟩)
          (by simpa using h12.tail.head) rfl (by unfold PosOK at *; omega)
        exact ⟨B, Star.step e1 hB, .inr ⟨hh, fun s => by simp [binOpSem]⟩⟩
      · have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 b) 0 = true := by
          simp only [BrOp.bop, guardB]
          have : BitVec.ofInt 64 b ≠ 0 := fun e => hb0' (by
            have := congrArg BitVec.toInt e; rw [hxb] at this; simpa using this)
          simpa using this
        rw [hg, if_pos rfl] at e1
        obtain ⟨L, hs2, hl⟩ := sim_lib (op := .div) hfit (A := ⟨pcOf (p + 1 + 1), A.regs, A.mem, A.out⟩)
          h3 (by simp) (by unfold PosOK at *; omega) (.inr (by simp [divPC, modPC, mulPC])) h0 h1
          (r := BitVec.ofInt 64 (a.tdiv b)) (by simp [libRes, mulPC, divPC, modPC, hxa, hxb, hb0'])
        refine ⟨_, Star.step e1 hs2, .inl ⟨.int (wrap64 (a.tdiv b)), rfl,
          fun s => by simp [binOpSem, hb0'], by simp only [List.length_append, hlen]; simp, rfl, ?_,
          fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
        simpa only [word, ofInt_wrap64] using hl
    · -- mod
      have hc : cbin p .mod = [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (p + 1) errPos)] ++
          libc (p + 2) modPC := rfl
      rw [hc] at hseg hpos ⊢
      obtain ⟨h12, h3⟩ := hseg.append
      have hb0 : codeBase = 0x80004800 := rfl
      have ht0 : tohostAddr = 0x8001ad00 := rfl
      have hlen : (libc (p + 2) modPC).length = 3 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, hlen] at hpos
      have hs := pcOf_skip p 1 (by unfold PosOK at *; omega) (by decide)
      have e1 := step_br hfit h12.head hA h1 (Has.zero _)
        (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
      rw [hs] at e1
      by_cases hb0' : b = 0
      · subst hb0'
        have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 0) 0 = false := by decide
        rw [hg] at e1
        simp only [Bool.false_eq_true, if_false] at e1
        obtain ⟨B, hB, hh⟩ := run_err hL (p := p + 1) (A := ⟨pcOf (p + 1), A.regs, A.mem, A.out⟩)
          (by simpa using h12.tail.head) rfl (by unfold PosOK at *; omega)
        exact ⟨B, Star.step e1 hB, .inr ⟨hh, fun s => by simp [binOpSem]⟩⟩
      · have hg : guardB BrOp.ne.bop (BitVec.ofInt 64 b) 0 = true := by
          simp only [BrOp.bop, guardB]
          have : BitVec.ofInt 64 b ≠ 0 := fun e => hb0' (by
            have := congrArg BitVec.toInt e; rw [hxb] at this; simpa using this)
          simpa using this
        rw [hg, if_pos rfl] at e1
        obtain ⟨L, hs2, hl⟩ := sim_lib (op := .mod) hfit (A := ⟨pcOf (p + 1 + 1), A.regs, A.mem, A.out⟩)
          h3 (by simp) (by unfold PosOK at *; omega) (.inr (by simp [divPC, modPC, mulPC])) h0 h1
          (r := BitVec.ofInt 64 (a.tmod b)) (by simp [libRes, mulPC, divPC, modPC, hxa, hxb, hb0'])
        refine ⟨_, Star.step e1 hs2, .inl ⟨.int (wrap64 (a.tmod b)), rfl,
          fun s => by simp [binOpSem, hb0'], by simp only [List.length_append, hlen]; simp, rfl, ?_,
          fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
        simpa only [word, ofInt_wrap64] using hl
  · have hna : ¬ ArithOp op := by
      rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [ArithOp]
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl
    · exact sim_cmp hfit (by rfl) (c := decide (a < b)) (fun s => rfl)
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _)]
          exact guard_lt ha hb)
        ⟨_, h0⟩ ⟨_, h1⟩ (by decide) (by decide) hseg hA hpos (.inl rfl) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≤ b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h1.src.2 : x = _), (hy.src.2.symm.trans h0.src.2 : y = _),
            guard_ge hb ha])
        ⟨_, h1⟩ ⟨_, h0⟩ (by decide) (by decide) hseg hA hpos (.inr (.inl rfl)) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a > b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h1.src.2 : x = _), (hy.src.2.symm.trans h0.src.2 : y = _),
            guard_lt hb ha])
        ⟨_, h1⟩ ⟨_, h0⟩ (by decide) (by decide) hseg hA hpos (.inr (.inr (.inl rfl))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≥ b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_ge ha hb])
        ⟨_, h0⟩ ⟨_, h1⟩ (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inl rfl)))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a = b)) (fun s => by simp [binOpSem, Value.equal]; rfl)
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_eq ha hb])
        ⟨_, h0⟩ ⟨_, h1⟩ (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inr (.inl rfl))))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≠ b)) (fun s => by simp [binOpSem, Value.equal]; rfl)
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_ne ha hb])
        ⟨_, h0⟩ ⟨_, h1⟩ (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inr (.inr rfl))))) hna

end

end Vsa.Compiler
