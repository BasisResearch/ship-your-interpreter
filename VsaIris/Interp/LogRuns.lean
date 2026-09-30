import VsaIris.Interp.Arm3

/-!
The reflected segments of `&&` and `||`: the shared entry to the left call, per operator the
staging of `value_truthy`, the short-circuit and long paths, the right operand's truthiness, and
the shared `value_bool` staging.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

namespace LogOp'

/-- The `value_truthy` site on the left operand. -/
def tr : LogOp → JalAt valueTruthyPC
  | .and => jal_site% 0x80003594 | .or => jal_site% 0x80003990

/-- The left truthiness that short-circuits, which is also the short result. -/
def short : LogOp → Bool
  | .and => false | .or => true

/-- The `value_bool` site of the short path. -/
def vbS : LogOp → JalAt valueBoolPC
  | .and => jal_site% 0x800036dc | .or => jal_site% 0x800039a4

/-- The right operand's call site and result slot. -/
def rc : LogOp → JalAt evalEntryPC
  | .and => jal_site% 0x800035ac | .or => jal_site% 0x80003a0c
def rslot : LogOp → Nat
  | .and => 240 | .or => 144

end LogOp'

/-- Ready for a child call with result slot at frame offset `o`. -/
structure CallReady3 (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret aX inp aE : BitVec 64)
    (o : Nat) (aC : BitVec 64) : Prop where
  frame : Frame3 rv R Mt s ret sret aX inp aE
  regs : EvalRegs R (evalSP s + BitVec.ofNat 64 o) inp aC aE (evalSP s)

/-- Ready for `value_truthy` on the operand copied to frame offset `64`. -/
structure TruthyReady3 (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret aX inp aE : BitVec 64)
    (w0 w1 w2 : BitVec 64) : Prop where
  frame : Frame3 rv R Mt s ret sret aX inp aE
  a0 : R 10 = evalSP s + 64#64
  l0 : ldv .ld Mt (s.toNat - 1088 + 64) = w0
  l1 : ldv .ld Mt (s.toNat - 1088 + 72) = w1
  l2 : ldv .ld Mt (s.toNat - 1088 + 80) = w2

/-- Ready for `value_bool` on a known truth value. -/
structure BoolReady3 (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret aX inp aE : BitVec 64)
    (c : Bool) : Prop where
  frame : Frame3 rv R Mt s ret sret aX inp aE
  a0 : R 10 = sret
  a1 : R 11 = if c then 1#64 else 0#64

def LogEntryRun : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aE aL aR : BitVec 64} {rv : Nat → BitVec 64}
    {Mt : Mem} {n : Nat} {op : LogOp},
    ArmGeo s ret sret n → EvalRegs rv sret inp aX aE s → BinNode m P aX 7 (logOpTok op) aL aR →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) evalEntryPC 0x80003568#64
      (upd rv 1 ret) Mt (fun R' Mt' => CallReady3 rv R' Mt' s ret sret aX inp aE 120 aL)

set_option hygiene false in
macro "frame3_facts" : tactic => `(tactic| (
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have h2 : R 2 = s + 18446744073709550528#64 := f.r2
  have h8 := f.r8; have h9 := f.r9; have h18 := f.r18; have hA := f.ae))

set_option hygiene false in
macro "frame3_close" : tactic => `(tactic| (
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine f.regs (fun x hx => ?_) (by ix_saved3 f.saved using hoff)
    (by first | (ix_fwdF hoff; exact f.ae) | exact f.ae)
  simp only [keep3, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (ix_reg <;> first | rfl | exact h8 | exact h9 | exact h18)))

theorem logEntry : LogEntryRun := by
  intro live hlive m P aX s ret sret inp aE aL aR rv Mt n op g hr hn Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hK := hn.kind; have hKu := hn.kindu
  have hL := hn.left
  have h10 : upd rv 1 ret 10 = sret := by ix_reg; exact hr.a0
  have h11 : upd rv 1 ret 11 = inp := by ix_reg; exact hr.a1
  have h12 : upd rv 1 ret 12 = aX := by ix_reg; exact hr.a2
  have h13 : upd rv 1 ret 13 = aE := by ix_reg; exact hr.a3
  have h2 : upd rv 1 ret 2 = s := by ix_reg; exact hr.sp
  clear g hn
  unfold evalEntryPC
  ix_run hlive using [h10, h11, h12, h13, h2, hK, hKu, hsf] at 0x80003568
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg, fun x hx => ?_,
    ⟨?_, ?_, ?_, ?_⟩, by ix_fwd⟩,
    ⟨by ix_reg, by ix_reg; exact hr.a1, by ix_reg; exact hL, by ix_reg; exact hr.a3, by ix_reg⟩⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  all_goals (ix_fwd using [hoff]; try ix_reg)

def LogOp'.Run2 (o : LogOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aE aL aR : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat} {w0 w1 w2 : BitVec 64},
    ArmGeo s ret sret n → BinNode m P aX 7 (logOpTok o) aL aR →
    Frame3 rv R Mt s ret sret aX inp aE →
    ldv .ld Mt (evalSP s + 120#64).toNat = w0 → ldv .ld Mt (evalSP s + 128#64).toNat = w1 →
    ldv .ld Mt (evalSP s + 136#64).toNat = w2 →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x8000356c#64
      (BitVec.ofNat 64 (LogOp'.tr o).i) R Mt
      (fun R' Mt' => TruthyReady3 rv R' Mt' s ret sret aX inp aE w0 w1 w2)

set_option hygiene false in
macro "log_run2 " pc:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp aE aL aR rv R Mt n w0 w1 w2 g hn f hw0 hw1 hw2 Q hk
  frame3_facts
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  simp only [logOpTok, LogOp'.tr] at hop hk ⊢
  clear g hn
  ix_run hlive using [h8, h2, hop, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  simp only [hoff 120 (by decide), hoff 128 (by decide), hoff 136 (by decide)] at hw0 hw1 hw2
  refine hk _ _ ⟨?_, by ix_reg, by ix_fwdF hoff; exact hw0, by ix_fwdF hoff; exact hw1,
    by ix_fwdF hoff; exact hw2⟩
  frame3_close))

theorem LogOp'.run2_and : LogOp'.Run2 .and := by log_run2 0x80003594
theorem LogOp'.run2_or : LogOp'.Run2 .or := by log_run2 0x80003990

def LogOp'.Short (o : LogOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {aX s ret sret inp aE : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → Frame3 rv R Mt s ret sret aX inp aE →
    R 10 = (if LogOp'.short o then 1#64 else 0#64) →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) (BitVec.ofNat 64 ((LogOp'.tr o).i + 4))
      (BitVec.ofNat 64 (LogOp'.vbS o).i) R Mt
      (fun R' Mt' => BoolReady3 rv R' Mt' s ret sret aX inp aE (LogOp'.short o))

set_option hygiene false in
macro "log_short " pc:num : tactic => `(tactic| (
  intro live hlive m DA aX s ret sret inp aE rv R Mt n g f h10 Q hk
  frame3_facts
  dsimp only [LogOp'.tr, LogOp'.vbS, LogOp'.short] at h10 hk ⊢
  simp only [Nat.reduceAdd, ite_true, ite_false, Bool.false_eq_true] at h10 hk ⊢
  clear g
  refine iw_regFact h10 ?_
  ix_run hlive using [h2, hsf] at $pc
  refine hk _ _ ?_
  refine ⟨?_, by ix_reg <;> exact h9, by ix_reg <;> decide⟩
  frame3_close))

theorem LogOp'.short_and : LogOp'.Short .and := by log_short 0x800036dc
theorem LogOp'.short_or : LogOp'.Short .or := by log_short 0x800039a4

def LogOp'.Long (o : LogOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aE aL aR : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → BinNode m P aX 7 (logOpTok o) aL aR →
    Frame3 rv R Mt s ret sret aX inp aE → R 10 = (if !LogOp'.short o then 1#64 else 0#64) →
    MRun live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088))
      (BitVec.ofNat 64 ((LogOp'.tr o).i + 4)) (BitVec.ofNat 64 (LogOp'.rc o).i) R Mt
      (fun R' Mt' => CallReady3 rv R' Mt' s ret sret aX inp aE (LogOp'.rslot o) aR)

set_option hygiene false in
macro "log_long " pc:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp aE aL aR rv R Mt n g hn f h10 Q hk
  frame3_facts
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hright := hn.right
  dsimp only [LogOp'.tr, LogOp'.rc, LogOp'.rslot, LogOp'.short] at h10 hk ⊢
  simp only [Nat.reduceAdd, Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true] at h10 hk ⊢
  clear g hn
  refine iw_regFact h10 ?_
  ix_run hlive using [h8, h2, h18, hright, hA, hsf] at $pc
  refine hk _ _ ?_
  refine ⟨?_, ⟨by ix_reg, by ix_reg <;> exact h18, by ix_reg, by ix_reg, by ix_reg <;> exact h2⟩⟩
  frame3_close))

theorem LogOp'.long_and : LogOp'.Long .and := by log_long 0x800035ac
theorem LogOp'.long_or : LogOp'.Long .or := by log_long 0x80003a0c

def LogOp'.Run4 (o : LogOp) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {aX s ret sret inp aE : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat} {u0 u1 u2 : BitVec 64},
    ArmGeo s ret sret n → Frame3 rv R Mt s ret sret aX inp aE →
    ldv .ld Mt (evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat = u0 →
    ldv .ld Mt ((evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat + 8) = u1 →
    ldv .ld Mt ((evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat + 16) = u2 →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) (BitVec.ofNat 64 ((LogOp'.rc o).i + 4))
      0x800035cc#64 R Mt (fun R' Mt' => TruthyReady3 rv R' Mt' s ret sret aX inp aE u0 u1 u2)

set_option hygiene false in
macro "log_run4 " off:num : tactic => `(tactic| (
  intro live hlive m DA aX s ret sret inp aE rv R Mt n u0 u1 u2 g f hu0 hu1 hu2 Q hk
  frame3_facts
  dsimp only [LogOp'.rc, LogOp'.rslot] at hu0 hu1 hu2 hk ⊢
  simp only [Nat.reduceAdd] at hk ⊢
  clear g
  ix_run hlive using [h2, hsf] at 0x800035cc
  have hoff := evalSP_off (s := s) hsf (by omega)
  simp only [hoff $off (by decide)] at hu0 hu1 hu2
  refine hk _ _ ⟨?_, by ix_reg, by ix_fwdF hoff; exact hu0, by ix_fwdF hoff; exact hu1,
    by ix_fwdF hoff; exact hu2⟩
  frame3_close))

theorem LogOp'.run4_and : LogOp'.Run4 .and := by log_run4 240
theorem LogOp'.run4_or : LogOp'.Run4 .or := by log_run4 144

def LogRun5 : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {aX s ret sret inp aE : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat} {c : Bool},
    ArmGeo s ret sret n → Frame3 rv R Mt s ret sret aX inp aE → R 10 = (if c then 1#64 else 0#64) →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) 0x800035d0#64 0x800035d8#64 R Mt
      (fun R' Mt' => BoolReady3 rv R' Mt' s ret sret aX inp aE c)

theorem logRun5 : LogRun5 := by
  intro live hlive m DA aX s ret sret inp aE rv R Mt n c g f h10 Q hk
  frame3_facts
  clear g
  ix_run hlive using [h2, hsf] at 0x800035d8
  refine hk _ _ ?_
  refine ⟨?_, by ix_reg <;> first | rfl | exact h9, by ix_reg <;> first | rfl | exact h10⟩
  frame3_close

theorem epi3_800035dc : EpiRun3 0x800035dc#64 := by epi3_run
theorem epi3_800036e0 : EpiRun3 0x800036e0#64 := by epi3_run
theorem epi3_800039a8 : EpiRun3 0x800039a8#64 := by epi3_run

theorem LogOp'.run2 : ∀ o, LogOp'.Run2 o | .and => LogOp'.run2_and | .or => LogOp'.run2_or
theorem LogOp'.shortRun : ∀ o, LogOp'.Short o | .and => LogOp'.short_and | .or => LogOp'.short_or
theorem LogOp'.longRun : ∀ o, LogOp'.Long o | .and => LogOp'.long_and | .or => LogOp'.long_or
theorem LogOp'.run4 : ∀ o, LogOp'.Run4 o | .and => LogOp'.run4_and | .or => LogOp'.run4_or
theorem LogOp'.epiS : ∀ o : LogOp, EpiRun3 (BitVec.ofNat 64 ((LogOp'.vbS o).i + 4))
  | .and => epi3_800036e0 | .or => epi3_800039a8

end VsaIris.Interp
