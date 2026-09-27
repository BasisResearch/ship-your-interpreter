import Vsa.Compiler.Compile

/-!
# Runs of the abstract machine

`Star code A B`: `A` reaches `B` in zero or more steps; `StarN` counts them.
`Seg code pos seg` says `seg` sits in `code` at instruction index `pos`;
`pcOf k` is the address of instruction `k`. The lemmas here compute single
instructions and fixed sequences (`li`, the libgcc call sequence) at the
abstract level.
-/

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

inductive StarN (code : List Ins) : Nat → AM → AM → Prop where
  | refl (A : AM) : StarN code 0 A A
  | step {n : Nat} {A B C : AM} : astep code A = some (.run B) → StarN code n B C →
      StarN code (n + 1) A C

def Star (code : List Ins) (A B : AM) : Prop := ∃ n, StarN code n A B

theorem StarN.trans {code : List Ins} {m n : Nat} {A B C : AM}
    (h1 : StarN code m A B) (h2 : StarN code n B C) : StarN code (m + n) A C := by
  induction h1 with
  | refl => simpa using h2
  | step hs _ ih => rw [Nat.add_right_comm]; exact .step hs (ih h2)

theorem Star.refl (code : List Ins) (A : AM) : Star code A A := ⟨0, .refl A⟩

theorem Star.trans {code : List Ins} {A B C : AM} (h1 : Star code A B) (h2 : Star code B C) :
    Star code A C := by
  obtain ⟨m, h1⟩ := h1; obtain ⟨n, h2⟩ := h2; exact ⟨m + n, h1.trans h2⟩

theorem Star.step {code : List Ins} {A B C : AM} (h : astep code A = some (.run B))
    (h2 : Star code B C) : Star code A C := by
  obtain ⟨n, h2⟩ := h2; exact ⟨n + 1, .step h h2⟩

theorem Star.single {code : List Ins} {A B : AM} (h : astep code A = some (.run B)) :
    Star code A B := Star.step h (Star.refl _ _)

/-- `A` runs to some state satisfying `P`. -/
abbrev Reaches (code : List Ins) (A : AM) (P : AM → Prop) : Prop := ∃ B, Star code A B ∧ P B

theorem ex_step {code : List Ins} {A S : AM} {Q : AM → Prop} (e : astep code A = some (.run S))
    (h : Reaches code S Q) : Reaches code A Q := by
  obtain ⟨B, hs, hq⟩ := h; exact ⟨B, Star.step e hs, hq⟩

theorem ex_trans {code : List Ins} {A S : AM} {Q : AM → Prop} (e : Star code A S)
    (h : Reaches code S Q) : Reaches code A Q := by
  obtain ⟨B, hs, hq⟩ := h; exact ⟨B, e.trans hs, hq⟩

theorem ex_bind {code : List Ins} {A : AM} {P Q : AM → Prop} (h : Reaches code A P)
    (k : ∀ B, P B → Reaches code B Q) : Reaches code A Q := by
  obtain ⟨B, s, hp⟩ := h
  obtain ⟨C, s', hq⟩ := k B hp
  exact ⟨C, s.trans s', hq⟩

/-- `A` runs for `n` steps without halting. -/
abbrev Runs (code : List Ins) (n : Nat) (A : AM) : Prop := ∃ B, StarN code n A B

/-- The code fits below `tohost`. -/
def Fits (code : List Ins) : Prop := codeBase + 4 * code.length ≤ tohostAddr

/-- The address of instruction `k`. -/
def pcOf (k : Nat) : BitVec 64 := BitVec.ofNat 64 (codeBase + 4 * k)

/-- `seg` is placed at instruction index `pos`. -/
def Seg (code : List Ins) (pos : Nat) (seg : List Ins) : Prop :=
  ∀ j, j < seg.length → code[pos + j]? = seg[j]?

theorem Seg.append {code : List Ins} {pos : Nat} {s t : List Ins} (h : Seg code pos (s ++ t)) :
    Seg code pos s ∧ Seg code (pos + s.length) t := by
  constructor
  · intro j hj
    rw [h j (by simp; omega), List.getElem?_append_left hj]
  · intro j hj
    rw [Nat.add_assoc, h (s.length + j) (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp

theorem Seg.get {code : List Ins} {pos : Nat} {s : List Ins} (h : Seg code pos s) {j : Nat}
    {i : Ins} (hj : s[j]? = some i) : code[pos + j]? = some i := by
  have : j < s.length := by
    rcases Nat.lt_or_ge j s.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  rw [h j this, hj]

theorem Seg.head {code : List Ins} {pos : Nat} {i : Ins} {s : List Ins} (h : Seg code pos (i :: s)) :
    code[pos]? = some i := by
  simpa using h.get (j := 0) rfl

theorem Seg.tail {code : List Ins} {pos : Nat} {i : Ins} {s : List Ins} (h : Seg code pos (i :: s)) :
    Seg code (pos + 1) s := by
  simpa using (Seg.append (s := [i]) (t := s) h).2

theorem codeBase_lt : codeBase < tohostAddr := by decide

theorem pcOf_toNat {k : Nat} (hk : codeBase + 4 * k < 2 ^ 64) :
    (pcOf k).toNat = codeBase + 4 * k := by
  simp only [pcOf, BitVec.toNat_ofNat]; omega

theorem fetch_pcOf {code : List Ins} (hfit : Fits code) {k : Nat} {i : Ins}
    (hk : code[k]? = some i) : fetch code (pcOf k) = some i := by
  have hlt : k < code.length := by
    rcases Nat.lt_or_ge k code.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hk; cases hk
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  unfold Fits at hfit
  have hpc : (pcOf k).toNat = codeBase + 4 * k := pcOf_toNat (by omega)
  unfold fetch
  rw [if_pos (by rw [hpc]; omega), hpc]
  rw [show (codeBase + 4 * k - codeBase) / 4 = k by omega, hk]

theorem astep_pcOf {code : List Ins} (hfit : Fits code) {k : Nat} {i : Ins}
    (hk : code[k]? = some i) (A : AM) (hpc : A.pc = pcOf k) :
    astep code A = exec i A := by
  unfold astep; rw [hpc, fetch_pcOf hfit hk]

/-! ## PC arithmetic -/

/-- Instruction indices of fitting code are small. -/
abbrev PosOK (k : Nat) : Prop := codeBase + 4 * k ≤ tohostAddr

theorem pcOf_succ (k : Nat) : BitVec.addInt (pcOf k) 4 = pcOf (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [pcOf, Sail.BitVec.addInt, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_sext {n : Nat} (x : BitVec 64) (y : BitVec n) :
    x + sign_extend (m := 64) y = BitVec.ofInt 64 ((x.toNat : Int) + y.toInt) := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend, BitVec.ofInt_add]
  congr 1
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pcOf_eq_ofInt (k : Nat) : pcOf k = BitVec.ofInt 64 ((codeBase + 4 * k : Nat) : Int) := by
  rw [pcOf, BitVec.ofInt_natCast]

theorem evenB_self (o : BitVec 13) (h : o.toNat % 2 = 0) : evenB o = o := by
  apply BitVec.eq_of_toNat_eq; simp [evenB]; omega

theorem evenJ_self (o : BitVec 21) (h : o.toNat % 2 = 0) : evenJ o = o := by
  apply BitVec.eq_of_toNat_eq; simp [evenJ]; omega

theorem pcOf_skip (k n : Nat) (hk : PosOK k) (hn : 4 * (n + 1) < 2 ^ 12) :
    pcOf k + sign_extend (m := 64) (evenB (bSkip n)) = pcOf (k + n + 1) := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  rw [evenB_self _ (by simp [bSkip]; omega), add_sext, pcOf_toNat (by omega), pcOf_eq_ofInt]
  have : (bSkip n).toInt = 4 * (n + 1) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp [bSkip]; omega)]
    simp [bSkip]; omega
  rw [this]; congr 1; push_cast; omega

theorem pcOf_jump (src dst : Nat) (hs : PosOK src) (hd : PosOK dst) :
    pcOf src + sign_extend (m := 64) (evenJ (jOff src dst)) = pcOf dst := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hj : (jOff src dst).toInt = 4 * ((dst : Int) - src) := by
    unfold jOff
    rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  have he : (jOff src dst).toNat % 2 = 0 := by
    unfold jOff; rw [BitVec.toNat_ofInt]; omega
  rw [evenJ_self _ he, add_sext, pcOf_toNat (by omega), pcOf_eq_ofInt, hj]
  congr 1; push_cast; omega

/-! ## Register file -/

/-- Register `n` holds `v` (`x0` holds `0`). -/
def Has (L : GRegs) (n : Nat) (v : BitVec 64) : Prop :=
  n ≤ 31 ∧ ((n = 0 ∧ v = 0) ∨ (n ≠ 0 ∧ lookupG n L = some v))

/-- Write register `rd`. -/
def gset (L : GRegs) (rd : Nat) (v : BitVec 64) : GRegs := (rd, v) :: eraseG rd L

theorem lookupG_eraseG (n k : Nat) (L : GRegs) :
    lookupG n (eraseG k L) = if n = k then none else lookupG n L := by
  induction L with
  | nil => simp [eraseG, lookupG]
  | cons p L ih =>
    obtain ⟨m, w⟩ := p
    by_cases h1 : m = k <;> by_cases h2 : m = n <;> by_cases h3 : n = k <;>
      simp_all [eraseG, lookupG]

theorem lookupG_set (L : GRegs) (rd n : Nat) (v : BitVec 64) :
    lookupG n (gset L rd v) = if n = rd then some v else lookupG n L := by
  simp only [gset, lookupG]
  split
  · next h => subst h; simp
  · next h => rw [lookupG_eraseG]; simp [Ne.symm h]

theorem mem_keysG_of_lookup {n : Nat} {v : BitVec 64} :
    ∀ {L : GRegs}, lookupG n L = some v → n ∈ keysG L
  | [], h => by simp [lookupG] at h
  | (m, w) :: L, h => by
    simp only [lookupG] at h
    split at h
    · next e => subst e; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_keysG_of_lookup h)

theorem Has.src {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) :
    SrcOK n (keysG L) ∧ srcVal n L = v := by
  obtain ⟨hn, (⟨rfl, rfl⟩ | ⟨hne, hl⟩)⟩ := h
  · exact ⟨⟨hn, .inl rfl⟩, rfl⟩
  · refine ⟨⟨hn, .inr (mem_keysG_of_lookup hl)⟩, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [srcVal, hl]

theorem Has.zero (L : GRegs) : Has L 0 0 := ⟨by omega, .inl ⟨rfl, rfl⟩⟩

theorem Has.set_self (L : GRegs) {rd : Nat} (v : BitVec 64) (h1 : 1 ≤ rd) (h31 : rd ≤ 31) :
    Has (gset L rd v) rd v := ⟨h31, .inr ⟨by omega, by rw [lookupG_set]; simp⟩⟩

theorem Has.set_other {L : GRegs} {n rd : Nat} {v w : BitVec 64} (h : Has L n v) (hne : n ≠ rd) :
    Has (gset L rd w) n v := by
  obtain ⟨hn, (⟨rfl, rfl⟩ | ⟨hne0, hl⟩)⟩ := h
  · exact Has.zero _
  · exact ⟨hn, .inr ⟨hne0, by rw [lookupG_set, if_neg hne, hl]⟩⟩

/-! ## Single instructions -/

section
variable {code : List Ins} {k : Nat} {A : AM}

/-- Register-register/immediate ALU instructions. -/
def Ins.IsAlu : Ins → Prop
  | .addi .. | .ori .. | .slli .. | .add .. | .sub .. => True
  | _ => False

theorem exec_alu (i : Ins) (hi : i.IsAlu) (A : AM)
    (hK : KindOK (keysG A.regs) (i.toM A.pc).kind (i.toM A.pc).rd (i.toM A.pc).rs1 (i.toM A.pc).rs2) :
    exec i A = some (.run ⟨BitVec.addInt A.pc 4, stepGM (i.toM A.pc) A.regs [], A.mem, A.out⟩) := by
  cases i <;> first | exact hi.elim | (simp only [exec]; exact if_pos hK)

theorem step_addi (hfit : Fits code) {rd rs : Nat} {imm : BitVec 12} {v : BitVec 64}
    (hk : code[k]? = some (.addi rd rs imm)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hs : Has A.regs rs v) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (v + (sign_extend imm : BitVec 64)),
      A.mem, A.out⟩) := by
  obtain ⟨hs1, hs2⟩ := hs.src
  rw [astep_pcOf hfit hk A hA]
  rw [exec_alu (.addi rd rs imm) trivial A ⟨hrd, hs1⟩]
  simp only [Ins.toM, stepGM, wvalM]
  simp [hs2, hA, pcOf_succ, gset]

theorem step_ori (hfit : Fits code) {rd rs : Nat} {imm : BitVec 12} {v : BitVec 64}
    (hk : code[k]? = some (.ori rd rs imm)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hs : Has A.regs rs v) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (v ||| (sign_extend imm : BitVec 64)),
      A.mem, A.out⟩) := by
  obtain ⟨hs1, hs2⟩ := hs.src
  rw [astep_pcOf hfit hk A hA]
  rw [exec_alu (.ori rd rs imm) trivial A ⟨hrd, hs1⟩]
  simp only [Ins.toM, stepGM, wvalM]
  simp [hs2, hA, pcOf_succ, gset]

theorem step_slli (hfit : Fits code) {rd rs : Nat} {sh : BitVec 6} {v : BitVec 64}
    (hk : code[k]? = some (.slli rd rs sh)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hs : Has A.regs rs v) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (v <<< sh.toNat), A.mem, A.out⟩) := by
  obtain ⟨hs1, hs2⟩ := hs.src
  rw [astep_pcOf hfit hk A hA]
  rw [exec_alu (.slli rd rs sh) trivial A ⟨hrd, hs1⟩]
  simp only [Ins.toM, stepGM, wvalM]
  simp [hs2, hA, pcOf_succ, gset]
  simp only [shift_bits_left, shamtOf, Sail.BitVec.extractLsb, BitVec.extractLsb]
  have h : BitVec.extractLsb' 0 (5 - 0 + 1) (BitVec.extractLsb' 0 6 (BitVec.setWidth 12 sh)) = sh := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
    have := sh.isLt
    simp; omega
  rw [h]; rfl

theorem step_add (hfit : Fits code) {rd r1 r2 : Nat} {v w : BitVec 64}
    (hk : code[k]? = some (.add rd r1 r2)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (h1 : Has A.regs r1 v) (h2 : Has A.regs r2 w) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (v + w), A.mem, A.out⟩) := by
  obtain ⟨h11, h12⟩ := h1.src; obtain ⟨h21, h22⟩ := h2.src
  rw [astep_pcOf hfit hk A hA]
  rw [exec_alu (.add rd r1 r2) trivial A ⟨hrd, h11, h21⟩]
  simp only [Ins.toM, stepGM, wvalM]
  simp [h12, h22, hA, pcOf_succ, gset]

theorem step_sub (hfit : Fits code) {rd r1 r2 : Nat} {v w : BitVec 64}
    (hk : code[k]? = some (.sub rd r1 r2)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (h1 : Has A.regs r1 v) (h2 : Has A.regs r2 w) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (v - w), A.mem, A.out⟩) := by
  obtain ⟨h11, h12⟩ := h1.src; obtain ⟨h21, h22⟩ := h2.src
  rw [astep_pcOf hfit hk A hA]
  rw [exec_alu (.sub rd r1 r2) trivial A ⟨hrd, h11, h21⟩]
  simp only [Ins.toM, stepGM, wvalM]
  simp [h12, h22, hA, pcOf_succ, gset]

/-- The doubleword a load reads at `a`. -/
def rdW (m : Mem) (a : Nat) : BitVec 64 := bytesVal .ld (rd8 m a)

/-- Load-address window: RAM, outside the HTIF words. -/
def LdOK (a : Nat) : Prop :=
  0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000 ∧ (a + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a)

/-- Store-address window: aligned RAM above the HTIF words. -/
def StOK (a : Nat) : Prop :=
  0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000 ∧ tohostAddr + 16 ≤ a ∧ a % 8 = 0

theorem step_ld (hfit : Fits code) {rd rs : Nat} {v : BitVec 64}
    (hk : code[k]? = some (.ld rd rs)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hs : Has A.regs rs v) (ha : LdOK v.toNat) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd (rdW A.mem v.toNat), A.mem, A.out⟩) := by
  obtain ⟨hs1, hs2⟩ := hs.src
  rw [astep_pcOf hfit hk A hA]
  simp only [exec]
  rw [if_pos ⟨hrd, hs1⟩]
  simp only [hs2]
  unfold LdOK at ha
  rw [if_pos ha]
  simp [Ins.toM, stepGM, wvalM, rdW, hA, pcOf_succ, gset]

theorem step_sd (hfit : Fits code) {rs2 rs1 : Nat} {a w : BitVec 64}
    (hk : code[k]? = some (.sd rs2 rs1)) (hA : A.pc = pcOf k)
    (h1 : Has A.regs rs1 a) (h2 : Has A.regs rs2 w) (ha : StOK a.toNat) :
    astep code A = some (.run ⟨pcOf (k + 1), A.regs, applyW A.mem (a.toNat, 8, w), A.out⟩) := by
  obtain ⟨h11, h12⟩ := h1.src; obtain ⟨h21, h22⟩ := h2.src
  rw [astep_pcOf hfit hk A hA]
  simp only [exec]
  rw [if_pos ⟨h11, h21⟩]
  simp only [h12, h22]
  have hne : a.toNat ≠ tohostAddr := by unfold StOK at ha; omega
  unfold StOK at ha
  rw [if_neg hne, if_pos ha, hA, pcOf_succ]

theorem step_htif (hfit : Fits code) {rs2 rs1 : Nat} {a w : BitVec 64}
    (hk : code[k]? = some (.sd rs2 rs1)) (hA : A.pc = pcOf k)
    (h1 : Has A.regs rs1 a) (h2 : Has A.regs rs2 w) (ha : a.toNat = tohostAddr) :
    astep code A = htifOut w A := by
  obtain ⟨h11, h12⟩ := h1.src; obtain ⟨h21, h22⟩ := h2.src
  rw [astep_pcOf hfit hk A hA]
  simp only [exec]
  rw [if_pos ⟨h11, h21⟩]
  simp only [h12, h22]
  rw [if_pos ha]

theorem putcWord_low (c : BitVec 8) : (putcWord c).setWidth 8 = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [putcWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.zeroExtend]
  have hk : (0x0101000000000000#64).getLsbD i = false := by
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with h|h|h|h|h|h|h|h <;> subst h <;> decide
  have hb64 : (i < 64) = True := by simp; omega
  simp only [hk, hi, hb64, decide_true, Bool.true_and, Bool.false_or, BitVec.getLsbD_setWidth]

theorem putcWord_bit56 (c : BitVec 8) : (putcWord c).getLsbD 56 = true := by
  simp only [putcWord, BitVec.getLsbD_or, BitVec.zeroExtend, BitVec.getLsbD_setWidth]
  have : (0x0101000000000000#64).getLsbD 56 = true := by decide
  simp [this]

theorem putcWord_ne_exit (c : BitVec 8) (e : BitVec 64) (he : e.toNat < 2 ^ 40) :
    putcWord c ≠ exitWord e := by
  intro h
  have := congrArg (·.getLsbD 56) h
  simp only [putcWord_bit56] at this
  rw [eq_comm] at this
  simp only [exitWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft] at this
  simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow] at this
  have : e.toNat / 2 ^ 55 = 0 := Nat.div_eq_of_lt (by omega)
  simp_all

theorem htifOut_putc (c : BitVec 8) (A : AM) :
    htifOut (putcWord c) A = some (.run ⟨BitVec.addInt A.pc 4, A.regs, A.mem,
      A.out.push (toString (Char.ofNat c.toNat))⟩) := by
  unfold htifOut
  rw [if_neg (putcWord_ne_exit c 0 (by decide)), if_neg (putcWord_ne_exit c 70 (by decide)),
    putcWord_low, if_pos rfl]

theorem htifOut_exit (e : Nat) (he : e = 0 ∨ e = 70) (A : AM) :
    htifOut (exitWord (BitVec.ofNat 64 e)) A = some (.halt e) := by
  rcases he with rfl | rfl
  · simp [htifOut]
  · simp [htifOut]; decide

theorem step_br (hfit : Fits code) {op : BrOp} {r1 r2 : Nat} {off : BitVec 13} {v w : BitVec 64}
    (hk : code[k]? = some (.br op r1 r2 off)) (hA : A.pc = pcOf k)
    (h1 : Has A.regs r1 v) (h2 : Has A.regs r2 w)
    (hal : (pcOf k + (sign_extend (evenB off) : BitVec 64)).toNat % 4 = 0) :
    astep code A = some (.run ⟨if guardB op.bop v w then pcOf k + (sign_extend (evenB off) : BitVec 64)
      else pcOf (k + 1), A.regs, A.mem, A.out⟩) := by
  obtain ⟨h11, h12⟩ := h1.src; obtain ⟨h21, h22⟩ := h2.src
  rw [astep_pcOf hfit hk A hA]
  simp only [exec, hA]
  rw [if_pos ⟨h11, h21, hal⟩]
  simp [h12, h22, pcOf_succ]

theorem step_j (hfit : Fits code) {off : BitVec 21}
    (hk : code[k]? = some (.jal 0 off)) (hA : A.pc = pcOf k)
    (hal : (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat % 4 = 0) :
    astep code A = some (.run ⟨pcOf k + (sign_extend (evenJ off) : BitVec 64), A.regs, A.mem, A.out⟩) := by
  rw [astep_pcOf hfit hk A hA]
  simp only [exec, hA]
  rw [if_pos hal]
  simp

theorem step_call (hfit : Fits code) {off : BitVec 21}
    (hk : code[k]? = some (.jal 1 off)) (hA : A.pc = pcOf k)
    (hal : (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat % 4 = 0)
    (hnl : ¬ ((pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = mulPC ∨
      (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = divPC ∨
      (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = modPC)) :
    astep code A = some (.run ⟨pcOf k + (sign_extend (evenJ off) : BitVec 64),
      gset A.regs 1 (pcOf (k + 1)), A.mem, A.out⟩) := by
  rw [astep_pcOf hfit hk A hA]
  simp only [exec, hA]
  rw [if_pos hal]
  simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
  rw [if_neg hnl]
  simp [gset, pcOf_succ]

theorem step_lib (hfit : Fits code) {off : BitVec 21}
    (hk : code[k]? = some (.jal 1 off)) (hA : A.pc = pcOf k)
    (hal : (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat % 4 = 0)
    (hl : (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = mulPC ∨
      (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = divPC ∨
      (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat = modPC) :
    astep code A = libCall (pcOf k + (sign_extend (evenJ off) : BitVec 64)).toNat A := by
  rw [astep_pcOf hfit hk A hA]
  simp only [exec, hA]
  rw [if_pos hal]
  simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
  rw [if_pos hl]

theorem step_jalr (hfit : Fits code) {rs : Nat} {v : BitVec 64}
    (hk : code[k]? = some (.jalr rs)) (hA : A.pc = pcOf k) (hs : Has A.regs rs v)
    (hal : v.toNat % 4 = 0) :
    astep code A = some (.run ⟨v, A.regs, A.mem, A.out⟩) := by
  obtain ⟨h1, h2⟩ := hs.src
  have hv : BitVec.update (v + (sign_extend (0#12) : BitVec 64)) 0 0#1 = v := by
    have hz : (sign_extend (0#12) : BitVec 64) = 0 := by decide
    rw [hz]
    have h0 : v + (0 : BitVec 64) = v := by simp
    rw [h0]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.zeroExtend, BitVec.getLsbD_allOnes]
    by_cases h : i = 0
    · subst h
      have : v.getLsbD 0 = false := by
        simp [BitVec.getLsbD, Nat.testBit]; omega
      simp [this, ← BitVec.getLsbD_eq_getElem]
    · simp [h, hi]
  rw [astep_pcOf hfit hk A hA]
  simp only [exec, h2, hv]
  rw [if_pos ⟨h1, hal⟩]

end

end Vsa.Compiler
