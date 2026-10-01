import VsaIris.Interp.LogRuns
import VsaIris.Interp.IntOpArm
import VsaIris.Interp.SymInterp

/-!
Unary `-` and `!`: the shared entry to the operand call, the per-operator segments, the
Wp-generic tails, and the total and partial cases (with the `-` type error through the
shared `sub` error block).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- Entry of a unary arm to its operand call at `0x800035e8` (result slot `+144`). -/
def UnEntryRun : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aE aC : BitVec 64} {rv : Nat → BitVec 64}
    {Mt : Mem} {n tok : Nat},
    ArmGeo s ret sret n → EvalRegs rv sret inp aX aE s → UnNode m P aX tok aC →
    MRun live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) evalEntryPC 0x800035e8#64
      (upd rv 1 ret) Mt
      (fun R' Mt' => CallReady3 rv R' Mt' s ret sret aX inp (ldv .ld Mt (s.toNat - 1088)) 144 aC aE)

theorem unEntry : UnEntryRun := by
  intro live hlive m P aX s ret sret inp aE aC rv Mt n tok g hr hn Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hK := hn.kind; have hKu := hn.kindu
  have hC := hn.child
  have h10 : upd rv 1 ret 10 = sret := by ix_reg; exact hr.a0
  have h11 : upd rv 1 ret 11 = inp := by ix_reg; exact hr.a1
  have h12 : upd rv 1 ret 12 = aX := by ix_reg; exact hr.a2
  have h13 : upd rv 1 ret 13 = aE := by ix_reg; exact hr.a3
  have h2 : upd rv 1 ret 2 = s := by ix_reg; exact hr.sp
  clear g hn
  unfold evalEntryPC
  sym_run hlive using [h10, h11, h12, h13, h2, hK, hKu, hsf] at 0x800035e8
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg, fun x hx => ?_,
    ⟨?_, ?_, ?_, ?_⟩, by ix_fwd⟩,
    ⟨by ix_reg, by ix_reg; exact hr.a1, by ix_reg; exact hC, by ix_reg; exact hr.a3, by ix_reg⟩⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  all_goals (ix_fwd using [hoff]; try ix_reg)

/-- `-` on an integer operand: to the `value_int` call. -/
structure NegReady (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret u1 : BitVec 64) :
    Prop where
  frame : EpiFrame3 rv R Mt s ret
  a0 : R 10 = sret
  a1 : R 11 = -u1

def NegRun : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aF aC u1 : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → UnNode m P aX (unOpTok .neg) aC → Frame3 rv R Mt s ret sret aX inp aF →
    ldv .lw Mt (evalSP s + 144#64).toNat = 2#64 → ldv .ld Mt (evalSP s + 152#64).toNat = u1 →
    MRun live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x800035ec#64 0x800039d8#64 R Mt
      (fun R' Mt' => NegReady rv R' Mt' s ret sret u1)

theorem negRun : NegRun := by
  intro live hlive m P aX s ret sret inp aF aC u1 rv R Mt n g hn f hK hU Q hk
  frame3_facts
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have hK' : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64 := hK
  have hU' : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = u1 := hU
  simp only [unOpTok] at hop
  clear g hn hK hU
  sym_run hlive using [h8, h2, h9, hop, hK', hsf] at 0x800039d8
  refine hk _ _ ?_
  refine ⟨?_, by ix_reg <;> exact h9, by ix_reg; rw [hU', BitVec.zero_sub]⟩
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine ⟨by ix_reg <;> exact h2, by ix_reg; exact f.s3, fun x hx => ?_, by ix_saved3 f.saved using hoff⟩
  have e := f.hi x hx
  simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (ix_reg; exact e)

/-- `!`: the operand copy for `value_truthy`, then the negated bit for `value_bool`. -/
def NotRun2 : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aF aC : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat} {w0 w1 w2 : BitVec 64},
    ArmGeo s ret sret n → UnNode m P aX (unOpTok .not) aC → Frame3 rv R Mt s ret sret aX inp aF →
    ldv .ld Mt (evalSP s + 144#64).toNat = w0 → ldv .ld Mt (evalSP s + 152#64).toNat = w1 →
    ldv .ld Mt (evalSP s + 160#64).toNat = w2 →
    MRun live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x800035ec#64 0x80003614#64 R Mt
      (fun R' Mt' => TruthyReady3 rv R' Mt' s ret sret aX inp aF w0 w1 w2)

theorem notRun2 : NotRun2 := by
  intro live hlive m P aX s ret sret inp aF aC rv R Mt n w0 w1 w2 g hn f hw0 hw1 hw2 Q hk
  frame3_facts
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  simp only [unOpTok] at hop
  clear g hn
  sym_run hlive using [h8, h2, hop, hsf] at 0x80003614
  have hoff := evalSP_off (s := s) hsf (by omega)
  simp only [hoff 144 (by decide), hoff 152 (by decide), hoff 160 (by decide)] at hw0 hw1 hw2
  refine hk _ _ ?_
  refine ⟨?_, by ix_reg, by ix_fwdF hoff; exact hw0, by ix_fwdF hoff; exact hw1,
    by ix_fwdF hoff; exact hw2⟩
  frame3_close

structure NotReady (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret aX inp aF b : BitVec 64) :
    Prop where
  frame : Frame3 rv R Mt s ret sret aX inp aF
  a0 : R 10 = sret
  a1 : R 11 = seqzV b

def NotRun3 : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {aX s ret sret inp aF : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → Frame3 rv R Mt s ret sret aX inp aF →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) 0x80003618#64 0x80003620#64 R Mt
      (fun R' Mt' => NotReady rv R' Mt' s ret sret aX inp aF (R 10))

theorem notRun3 : NotRun3 := by
  intro live hlive m DA aX s ret sret inp aF rv R Mt n g f Q hk
  frame3_facts
  clear g
  sym_run hlive using [h2, hsf] at 0x80003620
  refine hk _ _ ?_
  refine ⟨?_, by ix_reg <;> exact h9, by ix_reg⟩
  frame3_close

theorem epi3_800039dc : EpiRun3 0x800039dc#64 := by epi3_run
theorem epi3_80003624 : EpiRun3 0x80003624#64 := by epi3_run

/-- The `-` type error: operand copy to `+64`, then to the shared `sub` error block. -/
def NegErrRun : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aF aC kR u0 : BitVec 64}
    {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → UnNode m P aX (unOpTok .neg) aC → Frame3 rv R Mt s ret sret aX inp aF →
    ldv .lw Mt (evalSP s + 144#64).toNat = kR → kR ≠ 2#64 →
    ldv .ld Mt (evalSP s + 144#64).toNat = u0 →
    MRun live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) 0x800035ec#64 0x80003b7c#64 R Mt
      (fun R' Mt' => ErrPost (opnConst 0x800196e8#64) R R' Mt' s u0 0x800196e8#64)

theorem negErr : NegErrRun := by
  intro live hlive m P aX s ret sret inp aF aC kR u0 rv R Mt n g hn f hK hkr hQ0 Q hk
  frame3_facts
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hop := hn.op
  have hK' : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = kR := hK
  simp only [unOpTok] at hop
  clear g hn hK
  sym_run hlive using [h8, h2, hop, hK', hsf] at 0x80003b7c
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hQ0' : ldv .ld Mt (s.toNat - 1088 + 144) = u0 := by rw [← hoff 144 (by decide)]; exact hQ0
  refine hk _ _ ⟨by ix_reg, by ix_reg, by ix_reg, by e2_fwd hoff <;> simp only [hQ0'],
    by simp only [opnConst]⟩

theorem unNeed (op : UnOp) (e : Expr) (d : Nat) : evalNeed e d + 1088 ≤ evalNeed (.unary op e) d := by
  have := evalNeed_unary op e d; unfold evalFrame at this; omega

theorem Expr.bodiesBound_unary' {P : Nat} {op : UnOp} {e : Expr}
    (h : (Expr.unary op e).bodiesBound P = true) : e.bodiesBound P = true := by
  simpa [Expr.bodiesBound] using h

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem valOf_int_pureK (N : NativeAddrs) {K : IProp GF} {a : Int} {w0 w1 w2 : BitVec 64}
    (hK : K ⊢ K ∗ □ valOf N (.int a) w0 w1 w2) :
    K ⊢ K ∗ ⌜w0.toNat % 2 ^ 32 = 2 ∧ w1.toInt = a⌝ := by
  iintro HK
  ihave ⟨HK, #Hv⟩ := hK $$ HK
  unfold valOf
  icases Hv with %h
  iframe HK; ipureintro; exact h

theorem negTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvi : ⊢ ∀ p n, valueIntSpec (vsaModel live) N Wp p n)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX inp aF aC : BitVec 64} {n : Nat} {rv R : Nat → BitVec 64} {Mt : Mem}
    {Wd K : IProp GF} {a : Int} {u0 u1 u2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : UnNode m P aX (unOpTok .neg) aC)
    (f : Frame3 rv R Mt s ret sret aX inp aF) (hsp : rv 2 = s)
    (hK : K ⊢ K ∗ □ valOf N (.int a) u0 u1 u2)
    (hkind : ldv .lw Mt (evalSP s + 144#64).toNat = BitVec.ofNat 64 (u0.toNat % 2 ^ 32))
    (hu1 : ldv .ld Mt (evalSP s + 152#64).toNat = u1)
    (hexit : ExitK Wp Φ N s ret sret rv n (.int (wrap64 (-a))) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) 0x800035ec#64 R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  refine ArmAt.pureK (valOf_int_pureK N hK) fun ⟨h0, h1⟩ => ?_
  refine ArmAt.run Wp hn.view (negRun hlive g hn f (by rw [hkind, h0]) hu1)
    fun R2 Mt2 p2 => ?_
  refine ArmAt.callInt Wp (jal_site% 0x800039d8) hlive hvi p2.a0
    (by rw [p2.a1, toInt_neg_wrap, h1]) g.slg fun R3 hk3 => ?_
  exact ArmAt.finish3 Wp hlive epi3_800039dc hn.view g p2.frame hsp hk3 (by decide) rfl hexit

theorem notTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvt : ⊢ ∀ p v, valueTruthySpec (vsaModel live) N Wp p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX inp aF aC : BitVec 64} {n : Nat} {rv R : Nat → BitVec 64} {Mt : Mem}
    {Wd K : IProp GF} {v : Value} {u0 u1 u2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : UnNode m P aX (unOpTok .not) aC)
    (f : Frame3 rv R Mt s ret sret aX inp aF) (hsp : rv 2 = s)
    (hK : K ⊢ K ∗ □ valOf N v u0 u1 u2)
    (hu0 : ldv .ld Mt (evalSP s + 144#64).toNat = u0) (hu1 : ldv .ld Mt (evalSP s + 152#64).toNat = u1)
    (hu2 : ldv .ld Mt (evalSP s + 160#64).toNat = u2)
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool (!v.truthy)) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) 0x800035ec#64 R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  refine ArmAt.run Wp hn.view (notRun2 hlive g hn f hu0 hu1 hu2) fun R2 Mt2 p2 => ?_
  refine ArmAt.callTruthy Wp (jal_site% 0x80003614) hlive hvt g hK p2.a0 p2.l0 p2.l1 p2.l2
    fun R3 Mt3 hk3 hb3 hag3 => ?_
  have f3 := p2.frame.helper hk3 (by decide) (by decide) (by decide) hag3
    (BitVec.ofNat 64 ((jal_site% 0x80003614 : JalAt valueTruthyPC).i + 4))
  refine ArmAt.run Wp hn.view (notRun3 hlive g f3) fun R4 Mt4 p4 => ?_
  exact ArmAt.boolFinish3 Wp (jal_site% 0x80003620) hlive hvb epi3_80003624 hn.view g p4.frame.epi hsp
    p4.a0 p4.a1 (by rw [upd_other _ _ (show (10 : Nat) ≠ 1 by decide), hb3]; exact seqzBit_ne _)
    hexit

theorem negT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st st1 : St} {d env : Nat} {e : Expr} {a : Int} {n : Nat}
    (De : EvalECost st d env e st1 (.int a) n)
    (D : EvalECost st d env (.unary .neg e) st1 (.int (wrap64 (-a))) n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st1 (.int a) n De)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p n) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.unary .neg e) st1
        (.int (wrap64 (-a))) n D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr ent.repr ent.ok
    have g := ent.geo
    refine ArmAt.run (twpW _) hn.view (unEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalT (jal_site% 0x800035e8) hlive De he g (unNeed .neg e d) (o := 144)
      (by decide) (by decide) (Expr.bodiesBound_unary' ent.bb) hrc ent.ok haC c1.regs
      fun R2 u0 u1 u2 hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 144) (by decide) (by decide) u0 u1 u2
      (BitVec.ofNat 64 ((jal_site% 0x800035e8 : JalAt evalEntryPC).i + 4))
    refine ArmAt.pureK (valOf_int_pureK N (valOf_dupK N _ u0 u1 u2)) fun ⟨h0, _⟩ => ?_
    have h0' : u0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [h0]; decide
    have hoff := g.off
    exact negTail (twpW _) hlive hvi g hn f2 ent.regs.sp (valOf_dupK N _ u0 u1 u2)
      (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (ExitK.frame _ evalKT_exit)

theorem notT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st st1 : St} {d env : Nat} {e : Expr} {v : Value} {n : Nat}
    (De : EvalECost st d env e st1 v n)
    (D : EvalECost st d env (.unary .not e) st1 (.bool (!v.truthy)) n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st1 v n De)
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.unary .not e) st1
        (.bool (!v.truthy)) n D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr ent.repr ent.ok
    have g := ent.geo
    refine ArmAt.run (twpW _) hn.view (unEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalT (jal_site% 0x800035e8) hlive De he g (unNeed .not e d) (o := 144)
      (by decide) (by decide) (Expr.bodiesBound_unary' ent.bb) hrc ent.ok haC c1.regs
      fun R2 u0 u1 u2 hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 144) (by decide) (by decide) u0 u1 u2
      (BitVec.ofNat 64 ((jal_site% 0x800035e8 : JalAt evalEntryPC).i + 4))
    have hoff := g.off
    exact notTail (twpW _) hlive hvt hvb g hn f2 ent.regs.sp (valOf_dupK N _ u0 u1 u2)
      (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (by ix_fwd using [hoff])
      (ExitK.frame _ evalKT_exit)

theorem notP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.unary .not e) :=
  evalEntryP hlive fun Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr ent.repr ent.ok
    have g := ent.geo
    refine ArmAt.run (wpW _) hn.view (unEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalP (jal_site% 0x800035e8) hlive .rfl (by iintro ⟨#H, -⟩; iexact H) g
      (unNeed .not e d) (o := 144) (by decide) (by decide) (Expr.bodiesBound_unary' ent.bb) hrc
      ent.ok haC c1.regs fun R2 u0 u1 u2 st1 v hE hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 144) (by decide) (by decide) u0 u1 u2
      (BitVec.ofNat 64 ((jal_site% 0x800035e8 : JalAt evalEntryPC).i + 4))
    have hoff := g.off
    exact notTail (wpW _) hlive hvt hvb (v := v) (u0 := u0) (u1 := u1) (u2 := u2) g hn f2
      ent.regs.sp (by iintro ⟨Hk, HX, #Hv⟩; iframe Hk HX Hv) (by ix_fwd using [hoff])
      (by ix_fwd using [hoff]) (by ix_fwd using [hoff])
      (evalKP_exit _ (EvalE.not st d env e st1 v hE))

theorem negP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p n)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v)
    (hE : ErrEnv (GF := GF) N L Room inp live Core) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.unary .neg e) :=
  evalEntryP hlive fun Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr ent.repr ent.ok
    have g := ent.geo
    refine ArmAt.run (wpW _) hn.view (unEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalP (jal_site% 0x800035e8) hlive .rfl (by iintro ⟨#H, -⟩; iexact H) g
      (unNeed .neg e d) (o := 144) (by decide) (by decide) (Expr.bodiesBound_unary' ent.bb) hrc
      ent.ok haC c1.regs fun R2 u0 u1 u2 st1 v hEv hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 144) (by decide) (by decide) u0 u1 u2
      (BitVec.ofNat 64 ((jal_site% 0x800035e8 : JalAt evalEntryPC).i + 4))
    refine ArmAt.pureK (φ := u0.toNat % 2 ^ 32 = valTag v) (by
      iintro ⟨Hk, HX, #Hv⟩
      ihave %ht := valOf_tag N v u0 u1 u2 $$ Hv
      iframe Hk HX Hv; ipureintro; exact ht) fun ht => ?_
    have ht' : u0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [ht]; exact valTag_lt _
    have hoff := g.off
    cases v
    case int a =>
      exact negTail (wpW _) hlive hvi (a := a) (u0 := u0) (u1 := u1) (u2 := u2) g hn f2 ent.regs.sp
        (by iintro ⟨Hk, HX, #Hv⟩; iframe Hk HX Hv)
        (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (evalKP_exit _ (EvalE.neg st d env e st1 a hEv))
    all_goals
      refine ArmAt.run (wpW _) hn.view (negErr hlive (kR := BitVec.ofNat 64 (u0.toNat % 2 ^ 32)) (u0 := u0) g hn f2
        (by ix_fwd using [hoff]) (by
        rw [ofNat_lo32 ht]; exact ofNat_valTag_ne (by simp [valTag]) (by decide))
        (by ix_fwd using [hoff])) fun _ _ p => ?_
      exact binErrTail (wpW _) hlive hE hvk (jal_site% 0x80003b7c) (jal_site% 0x80003b9c) IntOp.subRt
        opnConst_agree (fun hro => rodata_cstrV hro 0x800196e8#64 1 (by decide) (by decide)) g
        (by have := evalNeed_unary .neg e d; have := Expr.stackNeed_ge e
            unfold evalNeed stackBudget at *; unfold RtErr.rtErrNeed snprintfNeed evalFrame at *
            omega) hn.view p.a0 (p.s2.trans f2.r18) (p.sp.trans f2.r2) p.slot ht p.opn
        (evalKP_abort _ (by iintro ⟨⟨-, #H⟩, -⟩; iexact H))

end

end VsaIris.Interp
