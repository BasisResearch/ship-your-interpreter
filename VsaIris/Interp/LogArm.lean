import VsaIris.Interp.LogRuns
import VsaIris.Interp.BinPreludeP

/-!
`&&` and `||` for both operators: the Wp-generic pieces between the child calls
(`logAfterLeft`, `logShortTail`, `logAfterRight`) and the total and partial cases.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

theorem LogOp'.evalShort (o : LogOp) {st st1 : St} {d env : Nat} {l r : Expr} {lv : Value}
    (h : EvalE st d env l st1 lv) (ht : lv.truthy = LogOp'.short o) :
    EvalE st d env (.logical o l r) st1 (.bool (LogOp'.short o)) := by
  cases o
  · exact EvalE.andFalse st d env l r st1 lv h ht
  · exact EvalE.orTrue st d env l r st1 lv h ht

theorem LogOp'.evalLong (o : LogOp) {st st1 st2 : St} {d env : Nat} {l r : Expr} {lv rv : Value}
    (h : EvalE st d env l st1 lv) (ht : lv.truthy = !LogOp'.short o)
    (hr : EvalE st1 d env r st2 rv) : EvalE st d env (.logical o l r) st2 (.bool rv.truthy) := by
  cases o
  · exact EvalE.andTrue st d env l r st1 st2 lv rv h ht hr
  · exact EvalE.orFalse st d env l r st1 st2 lv rv h ht hr

theorem LogOp'.rslot_le (o : LogOp) : LogOp'.rslot o + 24 ≤ 1056 ∧ 8 ≤ LogOp'.rslot o ∧
    LogOp'.rslot o % 8 = 0 := by cases o <;> decide

theorem logNeed_left (op : LogOp) (l r : Expr) (d : Nat) :
    evalNeed l d + 1088 ≤ evalNeed (.logical op l r) d := by
  have := evalNeed_logical_left op l r d; unfold evalFrame at this; omega

theorem logNeed_right (op : LogOp) (l r : Expr) (d : Nat) :
    evalNeed r d + 1088 ≤ evalNeed (.logical op l r) d := by
  have := evalNeed_logical_right op l r d; unfold evalFrame at this; omega

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem logAfterLeft (o : LogOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvt : ⊢ ∀ p v, valueTruthySpec (vsaModel live) N Wp p v) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret aX inp aL aR : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF} {lv : Value} {w0 w1 w2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : BinNode m P aX 7 (logOpTok o) aL aR)
    (f : Frame3 rv R Mt s ret sret aX inp aE)
    (hw0 : ldv .ld Mt (evalSP s + 120#64).toNat = w0) (hw1 : ldv .ld Mt (evalSP s + 128#64).toNat = w1)
    (hw2 : ldv .ld Mt (evalSP s + 136#64).toNat = w2) (hK : K ⊢ K ∗ □ valOf N lv w0 w1 w2)
    (hk : ∀ R' Mt', Frame3 rv R' Mt' s ret sret aX inp aE →
      R' 10 = (if lv.truthy then 1#64 else 0#64) →
      ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 ((LogOp'.tr o).i + 4)) R'
        (InExt (s.toNat - 1088, 1088)) Mt') :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) 0x8000356c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  refine ArmAt.run Wp hn.view (LogOp'.run2 o hlive g hn f hw0 hw1 hw2) fun R2 Mt2 p2 => ?_
  refine ArmAt.callTruthy Wp (LogOp'.tr o) hlive hvt g hK p2.a0 p2.l0 p2.l1 p2.l2
    fun R3 Mt3 hk3 hb3 hag3 => ?_
  exact hk _ _ (p2.frame.helper hk3 (by decide) (by decide) (by decide) hag3 _)
    (by rw [upd_other _ _ (show (10 : Nat) ≠ 1 by decide)]; exact hb3)

theorem logShortTail (o : LogOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret aX inp aL aR : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    (g : ArmGeo s ret sret n) (hn : BinNode m P aX 7 (logOpTok o) aL aR)
    (f : Frame3 rv R Mt s ret sret aX inp aE) (hsp : rv 2 = s)
    (h10 : R 10 = (if LogOp'.short o then 1#64 else 0#64))
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool (LogOp'.short o)) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 ((LogOp'.tr o).i + 4)) R
      (InExt (s.toNat - 1088, 1088)) Mt :=
  ArmAt.run Wp hn.view (LogOp'.shortRun o hlive g f h10) fun _ _ p =>
    ArmAt.boolFinish3 Wp (LogOp'.vbS o) hlive hvb (LogOp'.epiS o) hn.view g p.frame.epi hsp p.a0 p.a1
      (boolBit_ne _) hexit

theorem logAfterRight (o : LogOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvt : ⊢ ∀ p v, valueTruthySpec (vsaModel live) N Wp p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret aX inp aL aR : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF} {rv' : Value} {u0 u1 u2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : BinNode m P aX 7 (logOpTok o) aL aR)
    (f : Frame3 rv R Mt s ret sret aX inp aE) (hsp : rv 2 = s)
    (hu0 : ldv .ld Mt (evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat = u0)
    (hu1 : ldv .ld Mt ((evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat + 8) = u1)
    (hu2 : ldv .ld Mt ((evalSP s + BitVec.ofNat 64 (LogOp'.rslot o)).toNat + 16) = u2)
    (hK : K ⊢ K ∗ □ valOf N rv' u0 u1 u2)
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool rv'.truthy) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s n sret Wd K) (BitVec.ofNat 64 ((LogOp'.rc o).i + 4)) R
      (InExt (s.toNat - 1088, 1088)) Mt := by
  refine ArmAt.run Wp hn.view (LogOp'.run4 o hlive g f hu0 hu1 hu2) fun R4 Mt4 p4 => ?_
  refine ArmAt.callTruthy Wp (jal_site% 0x800035cc) hlive hvt g hK p4.a0 p4.l0 p4.l1 p4.l2
    fun R5 Mt5 hk5 hb5 hag5 => ?_
  have f5 := p4.frame.helper hk5 (by decide) (by decide) (by decide) hag5
    (BitVec.ofNat 64 ((jal_site% 0x800035cc : JalAt valueTruthyPC).i + 4))
  refine ArmAt.run Wp hn.view (logRun5 hlive g f5
    (by rw [upd_other _ _ (show (10 : Nat) ≠ 1 by decide)]; exact hb5)) fun _ _ p6 => ?_
  exact ArmAt.boolFinish3 Wp (jal_site% 0x800035d8) hlive hvb epi3_800035dc hn.view g p6.frame.epi hsp
    p6.a0 p6.a1 (boolBit_ne _) hexit

theorem logShortT (o : LogOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 : St} {d env : Nat} {l r : Expr} {lv : Value} {nl : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (ht : lv.truthy = LogOp'.short o)
    (D : EvalECost st d env (.logical o l r) st1 (.bool (LogOp'.short o)) nl)
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.logical o l r) st1
        (.bool (LogOp'.short o)) nl D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := logNode_of_repr ent.repr ent.ok
    have g := ent.geo
    refine ArmAt.run (twpW _) hn.view (logEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalT (jal_site% 0x80003568) hlive Dl hl g (logNeed_left o l r d) (o := 120)
      (by decide) (by decide) (Expr.bodiesBound_logical ent.bb).1 hrl ent.ok haL c1.regs
      fun R2 w0 w1 w2 hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 120) (by decide) (by decide) w0 w1 w2
      (BitVec.ofNat 64 ((jal_site% 0x80003568 : JalAt evalEntryPC).i + 4))
    have hoff := g.off
    refine logAfterLeft o (twpW _) hlive hvt g hn f2 (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (by ix_fwd using [hoff])
      (valOf_dupK N lv w0 w1 w2) fun R3 Mt3 f3 hb3 => ?_
    rw [ht] at hb3
    exact logShortTail o (twpW _) hlive hvb g hn f3 ent.regs.sp hb3
      (ExitK.frame _ evalKT_exit)

theorem logLongT (o : LogOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {lv rv' : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (ht : lv.truthy = !LogOp'.short o)
    (Dr : EvalECost st1 d env r st2 rv' nr)
    (D : EvalECost st d env (.logical o l r) st2 (.bool rv'.truthy) (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.logical o l r) st2
        (.bool rv'.truthy) (nl + nr) D :=
  evalEntryT hlive D fun k Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := logNode_of_repr ent.repr ent.ok
    have g := ent.geo
    have hsl := LogOp'.rslot_le o
    rw [show k + (nl + nr) = k + nr + nl by omega]
    refine ArmAt.run (twpW _) hn.view (logEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalT (jal_site% 0x80003568) hlive Dl hl g (logNeed_left o l r d) (o := 120)
      (by decide) (by decide) (Expr.bodiesBound_logical ent.bb).1 hrl ent.ok haL c1.regs
      fun R2 w0 w1 w2 hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 120) (by decide) (by decide) w0 w1 w2
      (BitVec.ofNat 64 ((jal_site% 0x80003568 : JalAt evalEntryPC).i + 4))
    have hoff := g.off
    refine logAfterLeft o (twpW _) hlive hvt g hn f2 (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (by ix_fwd using [hoff])
      (valOf_dupK N lv w0 w1 w2) fun R3 Mt3 f3 hb3 => ?_
    rw [ht] at hb3
    refine ArmAt.run (twpW _) hn.view (LogOp'.longRun o hlive g hn f3 hb3) fun R4 Mt4 c4 => ?_
    refine ArmAt.callEvalT (LogOp'.rc o) hlive Dr hr g (logNeed_right o l r d)
      (o := LogOp'.rslot o) (by omega) hsl.2.2 (Expr.bodiesBound_logical ent.bb).2 hrr ent.ok haR
      c4.regs fun R5 u0 u1 u2 hk5 => ?_
    have f5 := c4.frame.child hk5 g hsl.2.1 hsl.1 u0 u1 u2
      (BitVec.ofNat 64 ((LogOp'.rc o).i + 4))
    have ho := g.off (LogOp'.rslot o) (by omega)
    exact logAfterRight o (twpW _) hlive hvt hvb g hn f5 ent.regs.sp
      (by unfold slotWrite; rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_ld_hit_eq _ _ rfl])
      (by unfold slotWrite; rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl])
      (by unfold slotWrite; rw [ldv_ld_hit_eq _ _ rfl])
      (valOf_dupK N rv' u0 u1 u2) (ExitK.frame _ (ExitK.frame _ evalKT_exit))

theorem logP (o : LogOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.logical o l r) :=
  evalEntryP hlive fun Φ sret aE aX s ret rv P m Mt0 ent => by
    obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := logNode_of_repr ent.repr ent.ok
    have g := ent.geo
    have hsl := LogOp'.rslot_le o
    refine ArmAt.run (wpW _) hn.view (logEntry hlive g ent.regs hn) fun R1 Mt1 c1 => ?_
    refine ArmAt.callEvalP (jal_site% 0x80003568) hlive .rfl (by iintro ⟨#H, -⟩; iexact H) g
      (logNeed_left o l r d) (o := 120) (by decide) (by decide) (Expr.bodiesBound_logical ent.bb).1
      hrl ent.ok haL c1.regs fun R2 w0 w1 w2 st1 lv hEl hk2 => ?_
    have f2 := c1.frame.child hk2 g (o := 120) (by decide) (by decide) w0 w1 w2
      (BitVec.ofNat 64 ((jal_site% 0x80003568 : JalAt evalEntryPC).i + 4))
    have hoff := g.off
    refine logAfterLeft o (wpW _) hlive hvt (lv := lv) (w0 := w0) (w1 := w1) (w2 := w2) g hn f2
      (by ix_fwd using [hoff]) (by ix_fwd using [hoff]) (by ix_fwd using [hoff])
      (by iintro ⟨Hk, HX, #Hv⟩; iframe Hk HX Hv) fun R3 Mt3 f3 hb3 => ?_
    by_cases hs : lv.truthy = LogOp'.short o
    · rw [hs] at hb3
      exact logShortTail o (wpW _) hlive hvb g hn f3 ent.regs.sp hb3
        (evalKP_exit _ (LogOp'.evalShort o hEl hs))
    · have ht : lv.truthy = !LogOp'.short o := by cases h : lv.truthy <;> cases o <;> simp_all [LogOp'.short]
      rw [ht] at hb3
      refine ArmAt.run (wpW _) hn.view (LogOp'.longRun o hlive g hn f3 hb3) fun R4 Mt4 c4 => ?_
      refine ArmAt.callEvalP (LogOp'.rc o) hlive .rfl (by iintro ⟨⟨#H, -⟩, -⟩; iexact H) g
        (logNeed_right o l r d) (o := LogOp'.rslot o) (by omega) hsl.2.2
        (Expr.bodiesBound_logical ent.bb).2 hrr ent.ok haR c4.regs
        fun R5 u0 u1 u2 st2 rv' hEr hk5 => ?_
      have f5 := c4.frame.child hk5 g hsl.2.1 hsl.1 u0 u1 u2
        (BitVec.ofNat 64 ((LogOp'.rc o).i + 4))
      have ho := g.off (LogOp'.rslot o) (by omega)
      exact logAfterRight o (wpW _) hlive hvt hvb g hn f5 ent.regs.sp
        (by unfold slotWrite; rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
          ldv_ld_hit_eq _ _ rfl])
        (by unfold slotWrite; rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl])
        (by unfold slotWrite; rw [ldv_ld_hit_eq _ _ rfl])
        (by iintro ⟨Hk, HX, #Hv⟩; iframe Hk HX Hv)
        (evalKP_exit _ (LogOp'.evalLong o hEl ht hEr))

end

end VsaIris.Interp
