import VsaIris.Interp.EqRuns
import VsaIris.Interp.BinPreludeP

/-!
The equality tails from the operator dispatch to the return, for both operators and any
`MachWP`; `eqT`/`eqP` compose them with the total and partial preludes.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- A tail that keeps both operand representations in its continuation. -/
theorem BinTail.keep {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat}
    {Out Wd K : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem} {lv rv' : Value}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd
      iprop(K ∗ □ valOf N lv w0 w1 w2 ∗ □ valOf N rv' u0 u1 u2)) 0x8000351c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N (evalArmF P m env aE s' n' Out Wd K) R s Mt lv rv' w0 w1 w2 u0 u1 u2 := by
  unfold BinTail
  iintro ⟨⟨#Hx, #Hy⟩, HF, Hms⟩
  iapply h
  iframe Hms
  unfold evalArmF
  icases HF with ⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, HK⟩
  iframe Hc Hr Hf Hs Ho Hw HK Hx Hy

/-- `value_equal` on the operand copies at `+64` and `+32`. -/
theorem ArmAt.callEqual (Wp : MachWP (GF := GF) (vsaModel live)) (J : JalAt valueEqualPC)
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout} {Room : RoomPred}
    {inp : Nat} (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (vsaModel live) N Wp pa pb s a b st B)
    (hsc : ⊢ strcmpSpecV (vsaModel live) Wp) (hni : NativeInj N)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret : BitVec 64}
    {n : Nat} {ρ : Regime} {st : St} {d : Nat} {K : IProp GF} {R : Nat → BitVec 64} {Mt : Mem}
    {a b : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (g : ArmGeo s ret sret n) (hn : 1088 + RtErr.rtErrNeed ≤ n)
    (h10 : R 10 = evalSP s + 64#64) (h11 : R 11 = evalSP s + 32#64) (h2 : R 2 = evalSP s)
    (ha0 : ldv .ld Mt (evalSP s + 64#64).toNat = w0)
    (ha8 : ldv .ld Mt ((evalSP s + 64#64).toNat + 8) = w1)
    (ha16 : ldv .ld Mt ((evalSP s + 64#64).toNat + 16) = w2)
    (hb0 : ldv .ld Mt (evalSP s + 32#64).toNat = u0)
    (hb8 : ldv .ld Mt ((evalSP s + 32#64).toNat + 8) = u1)
    (hb16 : ldv .ld Mt ((evalSP s + 32#64).toNat + 16) = u2)
    (hk : ∀ R' M', (∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x) →
      R' 10 = (if Value.equal a b then 1#64 else 0#64) →
      (∀ k, s.toNat - 1088 + 1048 ≤ k → k < s.toNat - 1088 + 1088 → imgM M' k = imgM Mt k) →
      ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat)
        (world N L Room inp ρ st d) iprop(K ∗ □ valOf N a w0 w1 w2 ∗ □ valOf N b u0 u1 u2))
        (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4)))
        (InExt (s.toNat - 1088, 1088)) M') :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat)
      (world N L Room inp ρ st d) iprop(K ∗ □ valOf N a w0 w1 w2 ∗ □ valOf N b u0 u1 u2))
      (BitVec.ofNat 64 J.i) R (InExt (s.toNat - 1088, 1088)) Mt := by
  have hoff := g.off
  have hsf := g.sf
  have hSa : ∀ k, InExt ((evalSP s + 64#64).toNat, 24) k → InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 64 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have hSb : ∀ k, InExt ((evalSP s + 32#64).toNat, 24) k → InExt (s.toNat - 1088, 1088) k := by
    intro k hk; rw [hoff 32 (by decide)] at hk; simp only [VsaIris.InExt] at hk ⊢; omega
  have hab : ∀ k, InExt ((evalSP s + 64#64).toNat, 24) k →
      ¬ InExt ((evalSP s + 32#64).toNat, 24) k := by
    intro k hk hk'; rw [hoff 64 (by decide)] at hk; rw [hoff 32 (by decide)] at hk'
    simp only [VsaIris.InExt] at hk hk'; omega
  unfold RtErr.rtErrNeed snprintfNeed at hn
  have g16 := evalCallGeom (nc := 16) (o := 0) g.sg (by omega) (by decide) (by decide)
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK, #Hva, #Hvb⟩, Hms⟩
  ihave #Hcmp := hsc
  ihave ⟨Hw, #Hbi⟩ := world_binImg N L Room inp _ st d $$ Hw
  ihave ⟨%B, Hsto, Hwk⟩ := world_store N L Room inp _ st d $$ Hw
  ihave ⟨Hslack, Hs16⟩ := stackScratch_narrow (s := evalSP s) (n := n - 1088) (m := 16)
    (by rw [hsf]; have := g.sg.le; omega) (by omega) $$ Hst
  iapply ms_callValueEqual Wp hve (J.exec live hlive) J.mem J.al (sp := evalSP s) (st := st.store)
    (B := B) hSa hSb hab (evalSlotGeom g.sg g.need (o := 64) (by decide) (by decide))
    (evalSlotGeom g.sg g.need (o := 32) (by decide) (by decide)) hni ha0 ha8 ha16 hb0 hb8 hb16
  iframe Hcode Hva Hvb Hms Hsto Hcmp Hbi
  isplitl []
  · ipureintro; exact ⟨h10, h11, h2⟩
  isplitl [Hs16]
  · unfold stackAt; iframe Hs16; ipureintro; exact g16.child
  iintro %R4 %M4 %hkeep4 %hr4 %hag4 Hms Hsto ⟨Hs16, -⟩
  ihave Hw := Hwk $$ Hsto
  ihave Hst := stackScratch_widen (s := evalSP s) (n := n - 1088) (m := 16)
    (by rw [hsf]; have := g.sg.le; omega) (by omega) $$ [Hslack Hs16]
  · iframe Hslack Hs16
  iapply hk R4 M4 hkeep4 hr4 (fun k h1 h2 => hag4 k (by simp only [VsaIris.InExt]; omega)
    (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)
    (by rw [hoff 32 (by decide)]; simp only [VsaIris.InExt]; omega))
  iframe Hms
  unfold evalArmF
  iframe Hcode Hro Hfb Hst Hslot Hw HK Hva Hvb

theorem eqTail (o : EqOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout} {Room : RoomPred}
    {inp : Nat} (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (vsaModel live) N Wp pa pb s a b st B)
    (hsc : ⊢ strcmpSpecV (vsaModel live) Wp)
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b) (hni : NativeInj N)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX : BitVec 64} {d : Nat} {l r : Expr} {rv R : Nat → BitVec 64} {Mt : Mem}
    {ρ : Regime} {st : St} {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary o.op l r) d)) (hn : BinOpNode m P aX (binOpTok o.op))
    (mid : BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed (.binary o.op l r) d)
      (.bool (o.sem (lv.equal rv'))) (world N L Room inp ρ st d) K) :
    BinTail Wp Φ N (binArmF N P m env aE s (evalNeed (.binary o.op l r) d) sret
      (world N L Room inp ρ st d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2 := by
  refine BinTail.keep ?_
  refine ArmAt.run Wp hn.view (o.run3 hlive g hn mid) fun R3 Mt3 p3 => ?_
  refine ArmAt.callEqual Wp o.ve hlive hve hsc hni g (evalNeed_binary_rtErr _ _ _ _) p3.a0 p3.a1
    (p3.keep.sp.trans mid.r2) p3.la0 p3.la8 p3.la16 p3.lb0 p3.lb8 p3.lb16
    fun R4 M4 hk4 hr4 hag4 => ?_
  have k4 := p3.keep.trans (HiKeep.helperRA hk4 (by decide) (by decide) (BitVec.ofNat 64 (o.ve.i + 4)))
  have sv4 := (p3.saved mid.saved).agree hag4
  refine ArmAt.run Wp hn.view (o.run4 hlive g (by
    rw [upd_other R4 _ (show (9 : Nat) ≠ 1 by decide), hk4 9 (by decide) (by decide), p3.s1, mid.r9]))
    fun R5 Mt5 p5 => ?_
  have h11 := p5.a1 _ (by rw [upd_other R4 _ (show (10 : Nat) ≠ 1 by decide), hr4])
  refine ArmAt.callBool Wp o.vb hlive hvb p5.a0 h11 g.slg fun R6 hk6 => ?_
  rw [show ((if o.sem (lv.equal rv') then 1#64 else 0#64) != 0#64) = o.sem (lv.equal rv') by
    cases o.sem (lv.equal rv') <;> decide]
  have k6 := k4.trans (p5.keep.trans (HiKeep.helperRA hk6 (by decide) (by decide)
    (BitVec.ofNat 64 (o.vb.i + 4))))
  refine ArmAt.run Wp hn.view (o.epi hlive g (k6.sp.trans mid.r2) (p5.saved sv4))
    fun R7 _ p7 => ?_
  exact ArmAt.finish Wp (ExitK.frame _ hexit) g.sg.le g.need p7.ra
    (p7.keep (fun x hx => (k6.hi x hx).trans (mid.hi x hx)) mid.sp)

theorem eqT (o : EqOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {lv rv' : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (Dr : EvalECost st1 d env r st2 rv' nr)
    (D : EvalECost st d env (.binary o.op l r) st2 (.bool (o.sem (lv.equal rv'))) (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (vsaModel live) N
      (twpW (vsaModel live)) pa pb s a b st B)
    (hsc : ⊢ strcmpSpecV (GF := GF) (vsaModel live) (twpW (vsaModel live)))
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b)
    (hni : NativeInj N) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary o.op l r) st2
        (.bool (o.sem (lv.equal rv'))) (nl + nr) D :=
  binPreludeT hlive Dl Dr D hl hr fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hn mid hexit =>
    eqTail o (twpW _) hlive hve hsc hvb hni g hn mid hexit

theorem eqP (o : EqOp) {op : BinOp} (hop : o.op = op) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (vsaModel live) N
      (wpW (vsaModel live)) pa pb s a b st B)
    (hsc : ⊢ strcmpSpecV (GF := GF) (vsaModel live) (wpW (vsaModel live)))
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b)
    (hni : NativeInj N) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.binary op l r) :=
  hop ▸ binPreludeP hlive fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lv rv' _ _ _ g hn mid hexit _ =>
    eqTail o (wpW _) hlive hve hsc hvb hni g hn mid (hexit _ (o.sem_bin _ lv rv'))

end

end VsaIris.Interp
