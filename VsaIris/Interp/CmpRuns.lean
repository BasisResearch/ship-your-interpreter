import VsaIris.Interp.BinErr

/-!
The four comparison operators `<`, `<=`, `>`, `>=` as one descriptor `CmpOp`.

The machine code dispatches on the operator token, so each operator has its own reflected
segments (`CmpOp.intRun`, `CmpOp.strRun3`, `CmpOp.strRun4`, the shared epilogues); everything
above the segments (`cmpIntTail`, `cmpStrTail`) is proved once for any `MachWP`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

inductive CmpOp | lt | le | gt | ge

namespace CmpOp

def op : CmpOp → BinOp
  | lt => .lt | le => .le | gt => .gt | ge => .ge

/-- The `value_bool` call site of each operator. -/
def vb : CmpOp → JalAt valueBoolPC
  | lt => jal_site% 0x800036c8
  | le => jal_site% 0x80003b00
  | gt => jal_site% 0x80003aec
  | ge => jal_site% 0x800036c8

/-- The truth bit the integer path passes to `value_bool`. -/
def intBit : CmpOp → BitVec 64 → BitVec 64 → BitVec 64
  | lt, x, y => cmpRaw x y >>> 63
  | le, x, y => sltiV (cmpRaw x y) 1#64
  | gt, x, y => sltV 0#64 (cmpRaw x y)
  | ge, x, y => (cmpRaw x y ^^^ 0xffffffffffffffff#64) >>> 63

/-- The truth bit the string path computes from the `strcmp` result. -/
def strBit : CmpOp → BitVec 64 → BitVec 64
  | lt, r => r >>> 63
  | le, r => sltiV r 1#64
  | gt, r => sltV 0#64 r
  | ge, r => (r ^^^ 0xffffffffffffffff#64) >>> 63

def intSem : CmpOp → Int → Int → Bool
  | lt, a, b => decide (a < b)
  | le, a, b => decide (a ≤ b)
  | gt, a, b => decide (a > b)
  | ge, a, b => decide (a ≥ b)

def strSem : CmpOp → String → String → Bool
  | lt, x, y => decide (x < y)
  | le, x, y => decide (x < y) || x == y
  | gt, x, y => decide (y < x)
  | ge, x, y => decide (y < x) || x == y

/-- The operator name reported by the type error. -/
def opn : CmpOp → BitVec 64
  | lt => 0x800195c8#64 | le => 0x800195d0#64 | gt => 0x800195d8#64 | ge => 0x80019380#64

theorem opnName : ∀ o : CmpOp, OpName o.opn
  | lt => fun hro => rodata_cstrV hro 0x800195c8#64 1 (by decide) (by decide)
  | le => fun hro => rodata_cstrV hro 0x800195d0#64 2 (by decide) (by decide)
  | gt => fun hro => rodata_cstrV hro 0x800195d8#64 1 (by decide) (by decide)
  | ge => fun hro => rodata_cstrV hro 0x80019380#64 2 (by decide) (by decide)

theorem intBit_spec (o : CmpOp) (x y : BitVec 64) :
    (o.intBit x y != 0#64) = o.intSem x.toInt y.toInt := by
  cases o
  · exact cmp_lt_bit x y
  · exact cmp_le_bit x y
  · exact cmp_gt_bit x y
  · exact cmp_ge_bit x y

theorem strBit_spec (o : CmpOp) {res : BitVec 64} {x y : String} (h : StrcmpSign res x y) :
    (o.strBit res != 0#64) = o.strSem x y := by
  cases o
  · exact str_lt_bit h
  · exact str_le_bit h
  · exact str_gt_bit h
  · exact str_ge_bit h

theorem sem_int (o : CmpOp) (st : Store) (a b : Int) :
    binOpSem st o.op (.int a) (.int b) = some (.bool (o.intSem a b)) := by
  cases o <;> rfl

theorem sem_str (o : CmpOp) (st : Store) (x y : String) :
    binOpSem st o.op (.str x) (.str y) = some (.bool (o.strSem x y)) := by
  cases o <;> rfl

end CmpOp

/-- Post of the integer comparison path at the `value_bool` call. -/
structure CmpBoolPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s sret b : BitVec 64) : Prop where
  keep : HiKeep R R'
  a0 : R' 10 = sret
  a1 : R' 11 = b
  saved : ∀ {ret v8 v9 v18 v19}, EvalSaved Mt s ret v8 v9 v18 v19 → EvalSaved Mt' s ret v8 v9 v18 v19

def CmpOp.IntRun (o : CmpOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {a b : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok o.op) →
    BinMid s sret inp rv R Mt ret aX (.int a) (.int b) w0 w1 w2 u0 u1 u2 →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64
      (BitVec.ofNat 64 o.vb.i) R Mt (fun R' Mt' => CmpBoolPost R R' Mt Mt' s sret (o.intBit w1 u1))

set_option hygiene false in
macro "cmp_int_pre" : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt a b w0 w1 w2 u0 u1 u2 n g hn mid Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have hKL : ldv .ld Mt (s.toNat - 1088) = 2#64 := mid.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64 := mid.kr
  have hU : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = u1 := mid.q1
  clear g hn mid
  simp only [CmpOp.op, binOpTok, CmpOp.vb, CmpOp.intBit] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003678))

set_option hygiene false in
macro "cmp_int_post " pc:num : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, by ix_reg; rw [hU], fun h => ?_⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_saved h using hoff))

/-- Post of the string path at the `strcmp` call. -/
structure CmpStrPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s w1 u1 tag : BitVec 64) : Prop where
  keep : HiKeep R R'
  s1 : R' 9 = R 9
  a0 : R' 10 = w1
  a1 : R' 11 = u1
  saved : ∀ {ret v8 v9 v18 v19}, EvalSaved Mt s ret v8 v9 v18 v19 → EvalSaved Mt' s ret v8 v9 v18 v19
  tag : ldv .ld Mt' (s.toNat - 1088) = tag

def CmpOp.StrRun3 (o : CmpOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {x y : String} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok o.op) →
    BinMid s sret inp rv R Mt ret aX (.str x) (.str y) w0 w1 w2 u0 u1 u2 →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64 0x80003b18#64 R Mt
      (fun R' Mt' => CmpStrPost R R' Mt Mt' s w1 u1 (BitVec.ofNat 64 (binOpTok o.op)))

set_option hygiene false in
macro "cmp_str_pre" : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt x y w0 w1 w2 u0 u1 u2 n g hn mid Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have hKL : ldv .ld Mt (s.toNat - 1088) = 3#64 := mid.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 3#64 := mid.kr
  have hU : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = u1 := mid.q1
  clear g hn mid
  simp only [CmpOp.op, binOpTok] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003628))

set_option hygiene false in
macro "cmp_str_post" : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003b18
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, by ix_reg, by ix_reg; rw [hU],
    fun h => ?_, by e2_fwd hoff⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_saved h using hoff))

def CmpOp.StrRun4 (o : CmpOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → R 9 = sret → R 2 = evalSP s →
    ldv .ld Mt (s.toNat - 1088) = BitVec.ofNat 64 (binOpTok o.op) →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) 0x80003b1c#64 (BitVec.ofNat 64 o.vb.i) R Mt
      (fun R' Mt' => CmpBoolPost R R' Mt Mt' s sret (o.strBit (R 10)))

set_option hygiene false in
macro "cmp_str4 " pc:num : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n g h9 h2 hop Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  clear g h2
  simp only [CmpOp.op, binOpTok, CmpOp.vb, CmpOp.strBit] at hop hk ⊢
  ix_run hlive using [h9, h2', hop, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, by ix_reg, fun h => ?_⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_saved h using hoff))

/-- A reflected `eval_expr` epilogue from `pc` to the return address. -/
def EpiRun (pc : BitVec 64) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    {v8 v9 v18 v19 : BitVec 64},
    ArmGeo s ret sret n → R 2 = evalSP s → EvalSaved Mt s ret v8 v9 v18 v19 →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) pc ret R Mt
      (fun R' _ => EpiPost R R' s ret v8 v9 v18 v19)

set_option hygiene false in
macro "epi_run" : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n v8 v9 v18 v19 g h2 hsv Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al; have hal := g.ral
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    rw [hoff _ (by decide)]; exact hsv.ra
  have hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8 := by
    rw [hoff _ (by decide)]; exact hsv.s0
  have hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9 := by
    rw [hoff _ (by decide)]; exact hsv.s1
  have hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18 := by
    rw [hoff _ (by decide)]; exact hsv.s2
  have hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19 := by
    rw [hoff _ (by decide)]; exact hsv.s3
  clear g h2 hsv hoff
  ix_run hlive using [h2', hRA, hS0, hS1, hS2, hS3, hsf, hal]
  refine hk _ _ ⟨by ix_reg, by ix_reg; exact evalSP_restore s, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg, fun x hx => ?_⟩
  simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg))

theorem epi_800036cc : EpiRun 0x800036cc#64 := by epi_run
theorem epi_80003b04 : EpiRun 0x80003b04#64 := by epi_run
theorem epi_80003af0 : EpiRun 0x80003af0#64 := by epi_run

/-- The four type-error paths of a comparison: which operand is named, and the kind
checks that select the path. -/
def CmpOp.ErrRun (o : CmpOp) (left : Bool) (hyp : Value → Value → Prop) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok o.op) →
    BinMid s sret inp rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 → hyp lv rv' →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64 0x80003e7c#64 R Mt
      (fun R' Mt' => ErrPost R R' Mt' s (if left then w0 else u0) o.opn)

theorem ofNat_valTag_ne {v : Value} {k : Nat} (h : valTag v ≠ k) (hk : k < 2 ^ 31) :
    BitVec.ofNat 64 (valTag v) ≠ BitVec.ofNat 64 k := fun e => h (by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := valTag_lt v; omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact this)

/-- Left operand neither an integer nor paired with a string. -/
abbrev errL1 (lv rv' : Value) : Prop := valTag lv ≠ 2 ∧ valTag rv' ≠ 3
/-- Left operand neither an integer nor a string, right a string. -/
abbrev errL2 (lv rv' : Value) : Prop := valTag lv ≠ 2 ∧ valTag lv ≠ 3 ∧ valTag rv' = 3
/-- Left an integer, right neither an integer nor a string. -/
abbrev errR1 (lv rv' : Value) : Prop := valTag lv = 2 ∧ valTag rv' ≠ 2 ∧ valTag rv' ≠ 3
/-- Left an integer, right a string. -/
abbrev errR2 (lv rv' : Value) : Prop := valTag lv = 2 ∧ valTag rv' = 3

/-- The spilled kinds and the branch facts of a type-error path. -/
structure ErrFacts (lv rv' : Value) (kl kr : BitVec 64) (A B : Prop) : Prop where
  kl : BitVec.ofNat 64 (valTag lv) = kl
  kr : BitVec.ofNat 64 (valTag rv') = kr
  a : A
  b : B

theorem errL1_facts {lv rv' : Value} (h : errL1 lv rv') :
    ErrFacts lv rv' (BitVec.ofNat 64 (valTag lv)) (BitVec.ofNat 64 (valTag rv'))
      (BitVec.ofNat 64 (valTag lv) ≠ 2#64)
      (BitVec.ofNat 64 (valTag rv') + 18446744073709551613#64 ≠ 0#64) :=
  ⟨rfl, rfl, ofNat_valTag_ne h.1 (by decide), small_ne_three (valTag_lt _) h.2⟩

theorem errL2_facts {lv rv' : Value} (h : errL2 lv rv') :
    ErrFacts lv rv' (BitVec.ofNat 64 (valTag lv)) 3#64 (BitVec.ofNat 64 (valTag lv) ≠ 2#64)
      (BitVec.ofNat 64 (valTag lv) + 18446744073709551613#64 ≠ 0#64) :=
  ⟨rfl, by rw [h.2.2], ofNat_valTag_ne h.1 (by decide), small_ne_three (valTag_lt _) h.2.1⟩

theorem errR1_facts {lv rv' : Value} (h : errR1 lv rv') :
    ErrFacts lv rv' 2#64 (BitVec.ofNat 64 (valTag rv')) (BitVec.ofNat 64 (valTag rv') ≠ 2#64)
      (BitVec.ofNat 64 (valTag rv') + 18446744073709551613#64 ≠ 0#64) :=
  ⟨by rw [h.1], rfl, ofNat_valTag_ne h.2.1 (by decide), small_ne_three (valTag_lt _) h.2.2⟩

theorem errR2_facts {lv rv' : Value} (h : errR2 lv rv') :
    ErrFacts lv rv' 2#64 3#64 True True := ⟨by rw [h.1], by rw [h.2], trivial, trivial⟩

set_option hygiene false in
macro "cmp_err_pre " facts:ident : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt lv rv' w0 w1 w2 u0 u1 u2 n g hn mid hyp Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have F := $facts hyp
  have hKL := mid.kl.trans F.kl
  have hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = _ := mid.kr.trans F.kr
  have hA := F.a
  have hB := F.b
  have hL0 : ldv .ld Mt (s + 18446744073709550528#64 + 120#64).toNat = w0 := mid.l0
  have hQ0 : ldv .ld Mt (s + 18446744073709550528#64 + 144#64).toNat = u0 := mid.q0
  clear g hn mid hyp F
  simp only [CmpOp.op, binOpTok, CmpOp.opn, Bool.false_eq_true, ↓reduceIte] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003628))

set_option hygiene false in
macro "cmp_err_mid " pc:num : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at $pc))

set_option hygiene false in
macro "cmp_err_post" : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003e7c
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hL0' : ldv .ld Mt (s.toNat - 1088 + 120) = w0 := by rw [← hoff 120 (by decide)]; exact hL0
  have hQ0' : ldv .ld Mt (s.toNat - 1088 + 144) = u0 := by rw [← hoff 144 (by decide)]; exact hQ0
  refine hk _ _ ⟨by ix_reg, by ix_reg, by ix_reg, by e2_fwd hoff <;> simp only [hL0', hQ0'],
    by e2_fwd hoff⟩))

theorem rt_80003e80 : RtRun 0x80003e80#64 0x80003e98#64 := by rt_run

open Lean in
def tree3 (a b c d : Ident) : MacroM (TSyntax `command) := do
  let l ← `(ixtree| $d:ident)
  let n ← `(ixtree| $c:ident [$l:ixtree])
  `(#ix_tree $a:ident := $b:ident [$n:ixtree])

set_option hygiene false in
open Lean in
/-- `#cmp_runs o vb` proves the reflected segments of comparison operator `o` whose
`value_bool` call is at `vb`. -/
macro "#cmp_runs " o:ident vb:num : command => do
  let nm (s : String) : Ident := mkIdent (Name.mkStr (Name.mkStr .anonymous "CmpOp") s!"{s}_{o.getId}")
  let op : Ident := mkIdent (Name.mkStr (Name.mkStr .anonymous "CmpOp") o.getId.toString)
  let cs : Array (TSyntax `command) := #[
    ← `(#ix_seg $(nm "intRun1"):ident : CmpOp.IntRun $op:ident by cmp_int_pre),
    ← `(#ix_piece $(nm "intRun2"):ident from $(nm "intRun1"):ident by cmp_int_post $vb:num),
    ← `(theorem $(nm "intRun"):ident : CmpOp.IntRun $op:ident := $(nm "intRun1") $(nm "intRun2")),
    ← `(#ix_seg $(nm "strRun31"):ident : CmpOp.StrRun3 $op:ident by cmp_str_pre),
    ← `(#ix_piece $(nm "strRun32"):ident from $(nm "strRun31"):ident by cmp_str_post),
    ← `(theorem $(nm "strRun3"):ident : CmpOp.StrRun3 $op:ident := $(nm "strRun31") $(nm "strRun32")),
    ← `(theorem $(nm "strRun4"):ident : CmpOp.StrRun4 $op:ident := by cmp_str4 $vb:num),
    ← `(#ix_seg $(nm "errL11"):ident : CmpOp.ErrRun $op:ident true errL1 by cmp_err_pre errL1_facts),
    ← `(#ix_piece $(nm "errL12"):ident from $(nm "errL11"):ident by cmp_err_mid 0x80003e9c),
    ← `(#ix_piece $(nm "errL13"):ident from $(nm "errL12"):ident by cmp_err_post),
    ← tree3 (nm "errL1") (nm "errL11") (nm "errL12") (nm "errL13"),
    ← `(#ix_seg $(nm "errL21"):ident : CmpOp.ErrRun $op:ident true errL2 by cmp_err_pre errL2_facts),
    ← `(#ix_piece $(nm "errL22"):ident from $(nm "errL21"):ident by cmp_err_mid 0x80003e9c),
    ← `(#ix_piece $(nm "errL23"):ident from $(nm "errL22"):ident by cmp_err_post),
    ← tree3 (nm "errL2") (nm "errL21") (nm "errL22") (nm "errL23"),
    ← `(#ix_seg $(nm "errR11"):ident : CmpOp.ErrRun $op:ident false errR1 by cmp_err_pre errR1_facts),
    ← `(#ix_piece $(nm "errR12"):ident from $(nm "errR11"):ident by cmp_err_mid 0x80003e54),
    ← `(#ix_piece $(nm "errR13"):ident from $(nm "errR12"):ident by cmp_err_post),
    ← tree3 (nm "errR1") (nm "errR11") (nm "errR12") (nm "errR13"),
    ← `(#ix_seg $(nm "errR21"):ident : CmpOp.ErrRun $op:ident false errR2 by cmp_err_pre errR2_facts),
    ← `(#ix_piece $(nm "errR22"):ident from $(nm "errR21"):ident by cmp_err_mid 0x80003e54),
    ← `(#ix_piece $(nm "errR23"):ident from $(nm "errR22"):ident by cmp_err_post),
    ← tree3 (nm "errR2") (nm "errR21") (nm "errR22") (nm "errR23")]
  return ⟨mkNullNode cs⟩

end VsaIris.Interp
