import Vsa.Compiler.Rel
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

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

theorem run_err (hL : Layout code) {p : Nat} {A : AM}
    (hk : code[p]? = some (.jal 0 (jOff p errPos))) (hA : A.pc = pcOf p) (hp : PosOK p) :
    Reaches code A (fun B => astep code B = some (.halt 70)) := by
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

abbrev IsInt (v : Value) : Prop := ∃ n, v = .int n ∧ InRange n

abbrev IsBool (v : Value) : Prop := ∃ b, v = .bool b

section
variable {code : List Ins}

theorem run_cmp₀ (hfit : Fits code) {p r1 r2 : Nat} {b : BrOp} {A : AM} {x y : BitVec 64}
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

theorem guard_lt₀ {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BLT (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) := by
  simp [guardB, zopz0zI_s, toInt_ofInt_range ha, toInt_ofInt_range hb]

theorem guard_ge₀ {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BGE (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a ≥ b) := by
  simp [guardB, zopz0zKzJ_s, toInt_ofInt_range ha, toInt_ofInt_range hb]

theorem guard_eq₀ {a b : Int} (ha : InRange a) (hb : InRange b) :
    guardB bop.BEQ (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a = b) := by
  simp only [guardB, beq_iff_eq]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofInt 64 a ≠ BitVec.ofInt 64 b := fun e => h ((ofInt_inj_range ha hb).mp e)
    simp [h, this]

theorem guard_ne₀ {a b : Int} (ha : InRange a) (hb : InRange b) :
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

structure TailDone (op : BinOp) (a b : Int) (p len : Nat) (A B : AM) (v : Value) : Prop where
  out : B.out = A.out
  sem : ∀ s, binOpSem s op (.int a) (.int b) = some v
  pc : B.pc = pcOf (p + len)
  mem : B.mem = A.mem
  res : Has B.regs a0 (word v)
  arith : ArithOp op → IsInt v
  cmp : CmpOp op → IsBool v

def TailOK (op : BinOp) (a b : Int) (p len : Nat) (A B : AM) : Prop :=
  (∃ v, TailDone op a b p len A B v) ∨
    (astep code B = some (.halt 70) ∧ ∀ s, binOpSem s op (.int a) (.int b) = none)

theorem sim_cmp (hfit : Fits code) {op : BinOp} {br : BrOp} {r1 r2 : Nat} {p : Nat} {A : AM}
    {a b : Int} {c : Bool} (hcb : cmpBranch op = some (br, r1, r2))
    (hsem : ∀ s, binOpSem s op (.int a) (.int b) = some (.bool c))
    (hg : ∀ x y, Has A.regs r1 x → Has A.regs r2 y → guardB br.bop x y = c)
    {x y : BitVec 64} (hx : Has A.regs r1 x) (hy : Has A.regs r2 y) (hr1 : r1 ≠ s3) (hr2 : r2 ≠ s3)
    (hseg : Seg code p (cbin p op)) (hA : A.pc = pcOf p) (hpos : PosOK (p + (cbin p op).length))
    (hcmp : CmpOp op) (hna : ¬ ArithOp op) :
    Reaches code A (@TailOK code op a b p (cbin p op).length A) := by
  have hc : cbin p op = [.addi s3 0 1, .br br r1 r2 (bSkip 1), .addi s3 0 0, mv a0 s3] := by
    rcases hcmp with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [cbin, cmpBranch]
  rw [hc] at hseg hpos ⊢
  obtain ⟨L, hs, hL⟩ := run_cmp₀ hfit hseg hA hpos hx hy hr1 hr2
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
    Reaches code A (@TailOK code op a b p (cbin p op).length A) := by
  have hfit := hL.1
  have hxa : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_range ha
  have hxb : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_range hb
  rcases hop with hop | hop
  · have hna : ¬ CmpOp op := by
      rcases hop with rfl|rfl|rfl|rfl|rfl <;> simp [CmpOp]
    rcases hop with rfl|rfl|rfl|rfl|rfl
    ·
      have e := step_add hfit hseg.head hA (by decide) h0 h1
      refine ⟨_, Star.single e, .inl ⟨.int (wrap64 (a + b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      simp only [word, ofInt_wrap64, BitVec.ofInt_add]
      exact Has.set_self _ _ (by decide) (by decide)
    ·
      have e := step_sub hfit hseg.head hA (by decide) h0 h1
      refine ⟨_, Star.single e, .inl ⟨.int (wrap64 (a - b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      have : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
        rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
      simp only [word, ofInt_wrap64, this]
      exact Has.set_self (rd := a0) _ _ (by decide) (by decide)
    ·
      obtain ⟨L, hs, hl⟩ := sim_lib (op := .mul) hfit hseg hA hpos (.inl rfl) h0 h1
        (r := BitVec.ofInt 64 a * BitVec.ofInt 64 b) (by simp [libRes])
      refine ⟨_, hs, .inl ⟨.int (wrap64 (a * b)), rfl, fun s => rfl, rfl, rfl, ?_,
        fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => absurd h hna⟩⟩
      simpa only [word, ofInt_wrap64, BitVec.ofInt_mul] using hl
    ·
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
    ·
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
          exact guard_lt₀ ha hb)
        h0 h1 (by decide) (by decide) hseg hA hpos (.inl rfl) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≤ b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h1.src.2 : x = _), (hy.src.2.symm.trans h0.src.2 : y = _),
            guard_ge₀ hb ha])
        h1 h0 (by decide) (by decide) hseg hA hpos (.inr (.inl rfl)) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a > b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h1.src.2 : x = _), (hy.src.2.symm.trans h0.src.2 : y = _),
            guard_lt₀ hb ha])
        h1 h0 (by decide) (by decide) hseg hA hpos (.inr (.inr (.inl rfl))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≥ b)) (fun s => by simp [binOpSem])
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_ge₀ ha hb])
        h0 h1 (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inl rfl)))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a = b)) (fun s => by simp [binOpSem, Value.equal]; rfl)
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_eq₀ ha hb])
        h0 h1 (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inr (.inl rfl))))) hna
    · exact sim_cmp hfit (by rfl) (c := decide (a ≠ b)) (fun s => by simp [binOpSem, Value.equal]; rfl)
        (fun x y hx hy => by
          simp only [BrOp.bop]
          rw [(hx.src.2.symm.trans h0.src.2 : x = _), (hy.src.2.symm.trans h1.src.2 : y = _),
            guard_ne₀ ha hb])
        h0 h1 (by decide) (by decide) hseg hA hpos (.inr (.inr (.inr (.inr (.inr rfl))))) hna

end

def tdepth : Expr → Nat
  | .assign _ e => tdepth e
  | .unary _ e => tdepth e
  | .binary _ l r => 1 + max (tdepth l) (tdepth r)
  | _ => 0

def ValTy (Γn : NScope) (e : Expr) (v : Value) : Prop :=
  (IntE Γn e → IsInt v) ∧ (BoolE Γn e → IsBool v)

structure ExprDone (Γ : Scope) (e : Expr) (k pos : Nat) (st : St) (d : Nat) (env : Addr)
    (A B : AM) (v : Value) (st' : St) : Prop where
  eval : EvalE st d env e st' v
  ty : ValTy Γ.names e v
  out : st'.out = st.out
  bout : B.out = A.out
  pc : B.pc = pcOf (pos + (cexpr Γ k pos e).length)
  res : Has B.regs a0 (word v)
  rel : Chain st'.store B.mem env Γ
  temps : ∀ j < k, rdW B.mem (tempAddr j) = rdW A.mem (tempAddr j)

def ExprOK (code : List Ins) (Γ : Scope) (e : Expr) (k pos : Nat) (st : St) (d : Nat) (env : Addr)
    (A B : AM) : Prop :=
  (∃ v st', ExprDone Γ e k pos st d env A B v st') ∨
    (astep code B = some (.halt 70) ∧ ∀ v st', ¬ EvalE st d env e st' v)

theorem resolve_of_mem {x : String} : ∀ {Γ : Scope}, Γ.names.Mem x → (Γ.resolve x).isSome
  | [], ⟨f, hf, _⟩ => by simp [Scope.names] at hf
  | f :: g, h => by
    simp only [Scope.resolve]
    cases hl : f.lookup x with
    | some i => rfl
    | none =>
      obtain ⟨f', hf', hx⟩ := h
      simp only [Scope.names, List.map_cons, List.mem_cons] at hf'
      rcases hf' with rfl | hf'
      · exfalso
        obtain ⟨⟨y, i⟩, hy, rfl⟩ := List.mem_map.mp hx
        have : f.lookup y ≠ none := by
          clear hl hx
          induction f with
          | nil => simp at hy
          | cons q f ih =>
            obtain ⟨z, j⟩ := q
            simp only [List.lookup_cons]
            split
            · simp
            · next hne =>
              rcases List.mem_cons.mp hy with h | h
              · cases h; simp at hne
              · exact ih h
        exact this hl
      · exact resolve_of_mem ⟨f', hf', hx⟩

section
variable {code : List Ins}

theorem sim_int (hL : Layout code) {Γ : Scope} {n : Int} {k pos : Nat} {st : St} {d : Nat}
    {env : Addr} {A : AM} (hE : CondE Γ.names (.int n))
    (hseg : Seg code pos (cexpr Γ k pos (.int n))) (hA : A.pc = pcOf pos)
    (hc : Chain st.store A.mem env Γ) :
    Reaches code A (ExprOK code Γ (.int n) k pos st d env A) := by
  have hn : InRange n := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  refine ⟨_, run_li hL.1 hseg hA (by decide), .inl ⟨.int n, st, .int _ _ _ _, ⟨fun _ => ⟨n, rfl, hn⟩,
    fun h => h.elim⟩, rfl, rfl, rfl, Has.set_self _ _ (by decide) (by decide), hc, fun _ _ => rfl⟩⟩

theorem sim_bool (hL : Layout code) {Γ : Scope} {b : Bool} {k pos : Nat} {st : St} {d : Nat}
    {env : Addr} {A : AM} (hseg : Seg code pos (cexpr Γ k pos (.bool b))) (hA : A.pc = pcOf pos)
    (hc : Chain st.store A.mem env Γ) :
    Reaches code A (ExprOK code Γ (.bool b) k pos st d env A) := by
  have e := step_addi hL.1 hseg.head hA (by decide) (Has.zero _)
  refine ⟨_, Star.single e, .inl ⟨.bool b, st, .bool _ _ _ _, ⟨fun h => h.elim,
    fun _ => ⟨b, rfl⟩⟩, rfl, rfl, rfl, ?_, hc, fun _ _ => rfl⟩⟩
  cases b <;> exact Has.set_self _ _ (by decide) (by decide)

theorem sim_var (hL : Layout code) {Γ : Scope} (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {x : String}
    {k pos : Nat} {st : St} {d : Nat} {env : Addr} {A : AM} (hE : CondE Γ.names (.var x))
    (hseg : Seg code pos (cexpr Γ k pos (.var x))) (hA : A.pc = pcOf pos)
    (hc : Chain st.store A.mem env Γ) :
    Reaches code A (ExprOK code Γ (.var x) k pos st d env A) := by
  have hm : Γ.names.Mem x := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolve_of_mem hm)
  have hseg' : Seg code pos (liN s2 (varAddr i) ++ [.ld a0 s2]) := by simpa [cexpr, hi] using hseg
  have r := run_ldA hL.1 hseg' hA (by decide) (varAddr_ld (hsl i (resolve_mem hi)))
  refine ⟨_, r, .inl ⟨.int (slotV A.mem i), st, .var _ _ _ _ _ (hc.get? hi),
    ⟨fun _ => ⟨_, rfl, InRange.toInt _⟩, fun h => h.elim⟩, rfl, rfl, by simp [cexpr, hi, Nat.add_assoc], ?_,
    hc, fun _ _ => rfl⟩⟩
  simp only [word, slotV, BitVec.ofInt_toInt]
  exact Has.set_self _ _ (by decide) (by decide)

def SimE (code : List Ins) (Γ : Scope) (e : Expr) : Prop :=
  ∀ (k pos : Nat) (st : St) (d : Nat) (env : Addr) (A : AM), CondE Γ.names e →
    k + tdepth e < 2 ^ 17 → Seg code pos (cexpr Γ k pos e) →
    PosOK (pos + (cexpr Γ k pos e).length) → A.pc = pcOf pos → Chain st.store A.mem env Γ →
    Reaches code A (ExprOK code Γ e k pos st d env A)

theorem Seg.pos_eq {code : List Ins} {pos pos' : Nat} {s : List Ins} (h : pos = pos')
    (hs : Seg code pos s) : Seg code pos' s := h ▸ hs

theorem slots_ne_temp {i j : Nat} (hi : i < 2 ^ 24) (hj : j < 2 ^ 17) :
    tempAddr j + 8 ≤ varAddr i := by
  unfold tempAddr varAddr tempBase varBase; omega

theorem sim_assign (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {x : String} {e : Expr} (ih : SimE code Γ e) :
    SimE code Γ (.assign x e) := by
  intro k pos st d env A hE hk hseg hpos hA hc
  have hE' : Γ.names.Mem x ∧ IntE Γ.names e := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolve_of_mem hE'.1)
  have hil := hsl i (resolve_mem hi)
  have hcx : cexpr Γ k pos (.assign x e) = cexpr Γ k pos e ++ (liN s2 (varAddr i) ++ [.sd a0 s2]) := by
    simp [cexpr, hi]
  rw [hcx] at hseg hpos
  obtain ⟨hs1, hs2⟩ := hseg.append
  simp only [List.length_append] at hpos
  obtain ⟨B1, r1, hB1⟩ := ih k pos st d env A (.inl hE'.2) (by simpa [tdepth] using hk) hs1
    (by unfold PosOK at *; omega) hA hc
  rcases hB1 with ⟨v, st', hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ | ⟨hh, hne⟩
  · obtain ⟨n, rfl, hn⟩ := hty.1 hE'.2
    have r2 := run_stA hL.1 hs2 hBpc hB0 (by decide) (varAddr_st hil)
    obtain ⟨s'', hset, hc'', -, -⟩ := hBc.set (v := n) st'.store.frames.size hBc.env_lt hi hnd
      (slotV_write_self _ _ _ hn) (fun j _ hj => slotV_write_other _ _ _ _ hj)
    refine ⟨_, r1.trans r2, .inl ⟨.int n, ⟨s'', st'.out⟩, .assign _ _ _ _ _ _ _ _ hev hset,
      ⟨fun _ => ⟨n, rfl, hn⟩, fun h => h.elim⟩, hout, hBo, by simp [hcx, Nat.add_assoc],
      (hB0.set_other (by decide)), hc'', fun j hj => ?_⟩⟩
    rw [rdW_write_other _ _ _ _ (.inl (slots_ne_temp hil (by simp [tdepth] at hk; omega))), hBt j hj]
  · refine ⟨B1, r1, .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | assign _ _ _ _ _ _ _ _ he _ => exact hne _ _ he

theorem sim_binary (hL : Layout code) {Γ : Scope} {op : BinOp} {l r : Expr}
    (ihl : SimE code Γ l) (ihr : SimE code Γ r) (hsl : Simple l) (hsr : Simple r) :
    SimE code Γ (.binary op l r) := by
  intro k pos st d env A hE hk hseg hpos hA hc
  have hE' : (ArithOp op ∨ CmpOp op) ∧ IntE Γ.names l ∧ IntE Γ.names r := by
    rcases hE with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨.inl h1, h2, h3⟩
    · exact ⟨.inr h1, h2, h3⟩
  simp only [tdepth] at hk
  have hk0 : k < 2 ^ 17 := by omega

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
  simp only [List.length_append] at hpos
  obtain ⟨hs1234, hs5⟩ := hseg.append
  obtain ⟨hs123, hs4⟩ := hs1234.append
  obtain ⟨hs12, hs3⟩ := hs123.append
  obtain ⟨hs1, hs2⟩ := hs12.append
  have hs3' : Seg code p1 cr :=
    Seg.pos_eq (by simp only [List.length_append]; rw [lp1]; omega) hs3
  have hs4' : Seg code (p1 + cr.length) ldc :=
    Seg.pos_eq (by simp only [List.length_append]; rw [lp1]; omega) hs4
  have hs5' : Seg code p4 (cbin p4 op) :=
    Seg.pos_eq (by simp only [List.length_append]; rw [lp4, lp1]; omega) hs5
  have hpos4 : PosOK (p4 + (cbin p4 op).length) := by
    unfold PosOK at *; have h4 := lp4; have h1' := lp1; omega

  obtain ⟨B1, r1, hB1⟩ := ihl k pos st d env A (.inl hE'.2.1) (by omega) hs1
    (by unfold PosOK at *; omega) hA hc
  rcases hB1 with ⟨lv, st1, hevl, htyl, houtl, hB1o, hB1pc, hB1a0, hB1c, hB1t⟩ | ⟨hh, hne⟩
  rotate_left
  · refine ⟨B1, r1, .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | binary _ _ _ _ _ _ _ _ _ _ _ hl _ _ => exact hne _ _ hl
  obtain ⟨a, rfl, ha⟩ := htyl.1 hE'.2.1

  have r2 := run_stA hL.1 hs2 hB1pc hB1a0 (by decide) (tempAddr_st hk0)
  have hc2 : Chain st1.store (applyW B1.mem (tempAddr k, 8, word (.int a))) env Γ :=
    hB1c.transport fun i _ => slotV_write_low _ _ _ _ (tempAddr_low hk0)

  obtain ⟨B3, r3, hB3⟩ := ihr (k + 1) p1 st1 d env
    ⟨pcOf (pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k)).length + 1),
      gset B1.regs s2 (BitVec.ofNat 64 (tempAddr k)),
      applyW B1.mem (tempAddr k, 8, word (.int a)), B1.out⟩ (.inl hE'.2.2) (by omega) hs3'
    (by rw [← l3]; unfold PosOK at *; omega) (by simp only [lp1, lst, l1]; congr 1) hc2
  rcases hB3 with ⟨rv, st3, hevr, htyr, houtr, hB3o, hB3pc, hB3a0, hB3c, hB3t⟩ | ⟨hh, hne⟩
  rotate_left
  · refine ⟨B3, r1.trans (r2.trans r3), .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | binary _ _ _ _ _ _ _ _ _ _ _ hl hr _ =>
    obtain ⟨rfl, -⟩ := EvalE.det l hsl hl hevl
    exact hne _ _ hr
  obtain ⟨b, rfl, hb⟩ := htyr.1 hE'.2.2
  rw [← l3] at hB3pc

  have hmv : astep code B3 = some (.run ⟨pcOf (p1 + cr.length + 1),
      gset B3.regs a1 (BitVec.ofInt 64 b), B3.mem, B3.out⟩) := by
    rw [step_addi hL.1 hs4'.head hB3pc (by decide) hB3a0]
    have : (sign_extend (0#12) : BitVec 64) = 0 := by decide
    simp [word, this]
  have hs4'' : Seg code (p1 + cr.length + 1) (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]) :=
    (Seg.append (s := [mv a1 a0]) (t := liN s2 (tempAddr k) ++ [Ins.ld a0 s2])
      (by simpa [ldc] using hs4')).2
  have r4 := run_ldA hL.1 hs4'' (A := ⟨pcOf (p1 + cr.length + 1), gset B3.regs a1 (BitVec.ofInt 64 b),
    B3.mem, B3.out⟩) rfl (by decide) (tempAddr_ld hk0)
  have hlv : rdW B3.mem (tempAddr k) = BitVec.ofInt 64 a := by
    rw [hB3t k (by omega)]; exact rdW_write _ _ _
  rw [hlv] at r4

  obtain ⟨B5, r5, hB5⟩ := sim_cbin hL hE'.1 ha hb (A := ⟨pcOf p4, gset (gset (gset B3.regs a1
    (BitVec.ofInt 64 b)) s2 (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 a), B3.mem, B3.out⟩)
    hs5' rfl hpos4
    (Has.set_self _ _ (by decide) (by decide))
    (((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other (by decide))
  have r4' : Star code B3 ⟨pcOf p4, gset (gset (gset B3.regs a1 (BitVec.ofInt 64 b)) s2
      (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 a), B3.mem, B3.out⟩ := by
    refine Star.step hmv ?_
    have e : p1 + cr.length + 1 + (liN s2 (tempAddr k)).length + 1 = p4 := by rw [lp4, lld]; omega
    rw [e] at r4; exact r4
  have run := r1.trans (r2.trans (r3.trans (r4'.trans r5)))
  rcases hB5 with ⟨v, hB5o, hsem, hB5pc, hB5m, hB5a0, hari, hcmp⟩ | ⟨hh, hnone⟩
  · refine ⟨B5, run, .inl ⟨v, st3, .binary _ _ _ _ _ _ _ _ _ _ _ hevl hevr (hsem _),
      ⟨fun h => hari (by rcases h with ⟨h1, -⟩; exact h1), fun h => hcmp h.1⟩,
      houtr.trans houtl, ?_, ?_, hB5a0, ?_, ?_⟩⟩
    · rw [hB5o]; exact hB3o.trans hB1o
    · rw [hB5pc, hcx]; congr 1; simp only [List.length_append]; rw [lp4, lp1]; omega
    · rw [hB5m]; exact hB3c
    · intro j hj
      rw [hB5m, hB3t j (by omega), rdW_write_other _ _ _ _ (by unfold tempAddr; omega), hB1t j hj]
  · refine ⟨B5, run, .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | binary _ _ _ _ _ _ _ _ _ _ _ hl hr hop =>
    obtain ⟨rfl, rfl⟩ := EvalE.det l hsl hl hevl
    obtain ⟨rfl, rfl⟩ := EvalE.det r hsr hr hevr
    rw [hnone] at hop; cases hop

theorem sim_neg (hL : Layout code) {Γ : Scope} {e : Expr} (ih : SimE code Γ e) :
    SimE code Γ (.unary .neg e) := by
  intro k pos st d env A hE hk hseg hpos hA hc
  have hE' : IntE Γ.names e := by
    rcases hE with h | h
    · exact h
    · exact h.elim
  have hcx : cexpr Γ k pos (.unary .neg e) = cexpr Γ k pos e ++ [.sub a0 0 a0] := rfl
  rw [hcx] at hseg hpos
  obtain ⟨hs1, hs2⟩ := hseg.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hpos
  obtain ⟨B1, r1, hB1⟩ := ih k pos st d env A (.inl hE') (by simpa [tdepth] using hk) hs1
    (by unfold PosOK at *; omega) hA hc
  rcases hB1 with ⟨v, st', hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ | ⟨hh, hne⟩
  · obtain ⟨n, rfl, hn⟩ := hty.1 hE'
    have e1 := step_sub hL.1 hs2.head hBpc (by decide) (Has.zero _) hB0
    refine ⟨_, r1.trans (Star.single e1), .inl ⟨.int (wrap64 (-n)), st', .neg _ _ _ _ _ _ hev,
      ⟨fun _ => ⟨_, rfl, InRange.wrap64 _⟩, fun h => h.elim⟩, hout, hBo, by simp [hcx, Nat.add_assoc],
      ?_, hBc, hBt⟩⟩
    simp only [word, ofInt_wrap64, BitVec.ofInt_neg, BitVec.zero_sub]
    exact Has.set_self _ _ (by decide) (by decide)
  · refine ⟨B1, r1, .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | neg _ _ _ _ _ _ he => exact hne _ _ he

theorem sim_not (hL : Layout code) {Γ : Scope} {e : Expr} (ih : SimE code Γ e) :
    SimE code Γ (.unary .not e) := by
  intro k pos st d env A hE hk hseg hpos hA hc
  have hE' : CondE Γ.names e := by
    rcases hE with h | h
    · exact h.elim
    · exact h
  have hcx : cexpr Γ k pos (.unary .not e) = cexpr Γ k pos e ++
      [.addi s3 0 1, .br .eq a0 0 (bSkip 1), .addi s3 0 0, mv a0 s3] := rfl
  rw [hcx] at hseg hpos
  obtain ⟨⟨hs1, p1⟩, hs2, p2⟩ := segP_app.mp ⟨hseg, hpos⟩
  obtain ⟨B1, r1, hB1⟩ := ih k pos st d env A hE' (by simpa [tdepth] using hk) hs1 p1 hA hc
  rcases hB1 with ⟨v, st', hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ | ⟨hh, hne⟩
  · obtain ⟨L, r2, hL0⟩ := run_cmp₀ hL.1 hs2 hBpc p2 hB0 (Has.zero _) (by decide) (by decide)
    have hg : guardB BrOp.eq.bop (word v) 0 = !v.truthy := by
      rcases hE' with hi | hb
      · obtain ⟨n, rfl, hn⟩ := hty.1 hi
        simp only [BrOp.bop, word, Value.truthy, guardB]
        by_cases h : n = 0
        · subst h; decide
        · have : BitVec.ofInt 64 n ≠ (0 : BitVec 64) := fun e => h (by
            have := congrArg BitVec.toInt e; rwa [toInt_ofInt_range hn] at this)
          rw [beq_eq_false_iff_ne.mpr this]; simp [h]
      · obtain ⟨b, rfl⟩ := hty.2 hb
        cases b <;> decide
    rw [hg] at hL0
    refine ⟨_, r1.trans r2, .inl ⟨.bool (!v.truthy), st', .not _ _ _ _ _ _ hev,
      ⟨fun h => h.elim, fun _ => ⟨_, rfl⟩⟩, hout, hBo, by simp [hcx, Nat.add_assoc], ?_, hBc, hBt⟩⟩
    cases hv : v.truthy <;> simp [word, hv] at hL0 ⊢ <;> exact hL0
  · refine ⟨B1, r1, .inr ⟨hh, fun v st' h => ?_⟩⟩
    cases h with | not _ _ _ _ _ _ he => exact hne _ _ he

theorem sim_expr (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) : ∀ (e : Expr), Simple e → SimE code Γ e
  | .int _, _ => fun _ _ _ _ _ _ hE _ hseg _ hA hc => sim_int hL hE hseg hA hc
  | .bool _, _ => fun _ _ _ _ _ _ _ _ hseg _ hA hc => sim_bool hL hseg hA hc
  | .var _, _ => fun _ _ _ _ _ _ hE _ hseg _ hA hc => sim_var hL hsl hE hseg hA hc
  | .assign _ e, hs => sim_assign hL hnd hsl (sim_expr hL hnd hsl e hs)
  | .binary _ l r, hs =>
    sim_binary hL (sim_expr hL hnd hsl l hs.1) (sim_expr hL hnd hsl r hs.2) hs.1 hs.2
  | .unary .neg e, hs => sim_neg hL (sim_expr hL hnd hsl e hs)
  | .unary .not e, hs => sim_not hL (sim_expr hL hnd hsl e hs)
  | .str _, hs => hs.elim
  | .null, hs => hs.elim
  | .logical _ _ _, hs => hs.elim
  | .call _ _, hs => hs.elim
  | .fn _ _ _, hs => hs.elim

end

mutual
theorem IntE.simple {Γn : NScope} : ∀ {e : Expr}, IntE Γn e → Simple e
  | .int _, _ => trivial
  | .var _, _ => trivial
  | .assign _ e, h => IntE.simple (e := e) h.2
  | .binary _ l r, h => ⟨IntE.simple h.2.1, IntE.simple h.2.2⟩
  | .unary .neg e, h => IntE.simple (e := e) h
  | .unary .not _, h => h.elim
  | .str _, h => h.elim
  | .bool _, h => h.elim
  | .null, h => h.elim
  | .logical _ _ _, h => h.elim
  | .call _ _, h => h.elim
  | .fn _ _ _, h => h.elim

theorem BoolE.simple {Γn : NScope} : ∀ {e : Expr}, BoolE Γn e → Simple e
  | .bool _, _ => trivial
  | .binary _ l r, h => ⟨IntE.simple h.2.1, IntE.simple h.2.2⟩
  | .unary .not e, h => by
    rcases h with h | h
    · exact IntE.simple (e := e) h
    · exact BoolE.simple (e := e) h
  | .unary .neg _, h => h.elim
  | .int _, h => h.elim
  | .str _, h => h.elim
  | .var _, h => h.elim
  | .assign _ _, h => h.elim
  | .null, h => h.elim
  | .logical _ _ _, h => h.elim
  | .call _ _, h => h.elim
  | .fn _ _ _, h => h.elim
end

theorem CondE.simple {Γn : NScope} {e : Expr} (h : CondE Γn e) : Simple e := by
  rcases h with h | h
  · exact IntE.simple h
  · exact BoolE.simple h

end Vsa.Compiler
