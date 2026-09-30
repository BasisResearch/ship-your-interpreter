import VsaIris.Interp.BinErr
import VsaIris.Interp.BinEq

/-!
Equality operators `==`, `!=` as one descriptor `EqOp`: the reflected copy of both operands to
the `value_equal` argument slots (`EqOp.Run3`), the truth-bit staging for `value_bool`
(`EqOp.Run4`) and the epilogues.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

inductive EqOp | eq | ne

namespace EqOp

def op : EqOp → BinOp
  | eq => .eq | ne => .ne

def sem : EqOp → Bool → Bool
  | eq, c => c | ne, c => !c

def ve : EqOp → JalAt valueEqualPC
  | eq => jal_site% 0x8000371c | ne => jal_site% 0x8000376c

def vb : EqOp → JalAt valueBoolPC
  | eq => jal_site% 0x80003728 | ne => jal_site% 0x80003778

theorem sem_bin (o : EqOp) (st : Store) (a b : Value) :
    binOpSem st o.op a b = some (.bool (o.sem (a.equal b))) := by
  cases o <;> rfl

end EqOp

/-- State at the `value_equal` call: both operands copied to `+64` and `+32`. -/
structure EqCallPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s w0 w1 w2 u0 u1 u2 : BitVec 64) :
    Prop where
  keep : HiKeep R R'
  s1 : R' 9 = R 9
  a0 : R' 10 = evalSP s + 64#64
  a1 : R' 11 = evalSP s + 32#64
  saved : ∀ {ret v8 v9 v18 v19}, EvalSaved Mt s ret v8 v9 v18 v19 → EvalSaved Mt' s ret v8 v9 v18 v19
  la0 : ldv .ld Mt' (evalSP s + 64#64).toNat = w0
  la8 : ldv .ld Mt' ((evalSP s + 64#64).toNat + 8) = w1
  la16 : ldv .ld Mt' ((evalSP s + 64#64).toNat + 16) = w2
  lb0 : ldv .ld Mt' (evalSP s + 32#64).toNat = u0
  lb8 : ldv .ld Mt' ((evalSP s + 32#64).toNat + 8) = u1
  lb16 : ldv .ld Mt' ((evalSP s + 32#64).toNat + 16) = u2

def EqOp.Run3 (o : EqOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {n : Nat},
    ArmGeo s ret sret n → BinOpNode m P aX (binOpTok o.op) →
    BinMid s sret inp rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000351c#64
      (BitVec.ofNat 64 o.ve.i) R Mt (fun R' Mt' => EqCallPost R R' Mt Mt' s w0 w1 w2 u0 u1 u2)

/-- Post of the truth-bit staging at the `value_bool` call. -/
structure EqBoolPost (o : EqOp) (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s sret : BitVec 64) :
    Prop where
  keep : HiKeep R R'
  a0 : R' 10 = sret
  a1 : ∀ c : Bool, R 10 = (if c then 1#64 else 0#64) → R' 11 = (if o.sem c then 1#64 else 0#64)
  saved : ∀ {ret v8 v9 v18 v19}, EvalSaved Mt s ret v8 v9 v18 v19 → EvalSaved Mt' s ret v8 v9 v18 v19

def EqOp.Run4 (o : EqOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → R 9 = sret →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) (BitVec.ofNat 64 (o.ve.i + 4))
      (BitVec.ofNat 64 o.vb.i) R Mt (fun R' Mt' => EqBoolPost o R R' Mt Mt' s sret)

set_option hygiene false in
macro "eq_pre " pc:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp rv R Mt lv rv' w0 w1 w2 u0 u1 u2 n g hn mid Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have h8 := mid.r8; have h9 := mid.r9; have h19 := mid.r19
  have h2 : R 2 = s + 18446744073709550528#64 := mid.r2
  have hL0 := mid.l0; have hL1 := mid.l1; have hL2 := mid.l2
  have hQ0 := mid.q0; have hQ1 := mid.q1; have hQ2 := mid.q2
  clear g hn mid
  simp only [EqOp.op, binOpTok, EqOp.ve] at hop hk ⊢
  ix_run hlive using [h8, h2, h9, h19, hop, hsf] at $pc))

set_option hygiene false in
macro "eq_post " pc:num : tactic => `(tactic| (
  ix_run hlive using [h8, h2, h9, h19, hop, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  have e : ∀ c, c < 4096 → (s + 18446744073709550528#64 + BitVec.ofNat 64 c).toNat =
    s.toNat - 1088 + c := hoff
  simp only [e 120 (by decide), e 128 (by decide), e 136 (by decide), e 144 (by decide),
    e 152 (by decide), e 160 (by decide)] at hL0 hL1 hL2 hQ0 hQ1 hQ2
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, by ix_reg, by ix_reg, fun h => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_saved h using hoff
  all_goals (e2_fwd hoff <;> simp only [hL0, hL1, hL2, hQ0, hQ1, hQ2])))

#ix_seg EqOp.run3_eq1 : EqOp.eq.Run3 by eq_pre 0x800036e4
#ix_piece EqOp.run3_eq2 from EqOp.run3_eq1 by eq_post 0x8000371c
theorem EqOp.run3_eq : EqOp.eq.Run3 := EqOp.run3_eq1 EqOp.run3_eq2

#ix_seg EqOp.run3_ne1 : EqOp.ne.Run3 by eq_pre 0x80003734
#ix_piece EqOp.run3_ne2 from EqOp.run3_ne1 by eq_post 0x8000376c
theorem EqOp.run3_ne : EqOp.ne.Run3 := EqOp.run3_ne1 EqOp.run3_ne2

set_option hygiene false in
macro "eq_run4 " pc:num : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n g h9 Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  clear g
  simp only [EqOp.ve, EqOp.vb] at hk ⊢
  ix_run hlive using [h9, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, fun x hx => ?_⟩, by ix_reg, fun c hc => ?_, fun h => ?_⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  · ix_reg; rw [hc]; cases c <;> decide
  · ix_saved h using hoff))

theorem EqOp.run4_eq : EqOp.eq.Run4 := by eq_run4 0x80003728
theorem EqOp.run4_ne : EqOp.ne.Run4 := by eq_run4 0x80003778

theorem epi_8000372c : EpiRun 0x8000372c#64 := by epi_run
theorem epi_8000377c : EpiRun 0x8000377c#64 := by epi_run

theorem EqOp.run3 : ∀ o : EqOp, o.Run3
  | eq => EqOp.run3_eq | ne => EqOp.run3_ne
theorem EqOp.run4 : ∀ o : EqOp, o.Run4
  | eq => EqOp.run4_eq | ne => EqOp.run4_ne
theorem EqOp.epi : ∀ o : EqOp, EpiRun (BitVec.ofNat 64 (o.vb.i + 4))
  | eq => epi_8000372c | ne => epi_8000377c

end VsaIris.Interp
