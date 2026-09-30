import VsaIris.Interp.CmpRunsLt
import VsaIris.Interp.CmpRunsLe
import VsaIris.Interp.CmpRunsGt
import VsaIris.Interp.CmpRunsGe
import VsaIris.Interp.BinPreludeP

/-!
The comparison tails from the operator dispatch to the return, proved once for all four
operators and for any `MachWP`; `cmpIntT`/`cmpStrT` compose them with the total prelude.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

theorem CmpOp.intRun : ∀ o : CmpOp, o.IntRun
  | lt => CmpOp.intRun_lt | le => CmpOp.intRun_le | gt => CmpOp.intRun_gt | ge => CmpOp.intRun_ge

theorem CmpOp.strRun3 : ∀ o : CmpOp, o.StrRun3
  | lt => CmpOp.strRun3_lt | le => CmpOp.strRun3_le | gt => CmpOp.strRun3_gt
  | ge => CmpOp.strRun3_ge

theorem CmpOp.strRun4 : ∀ o : CmpOp, o.StrRun4
  | lt => CmpOp.strRun4_lt | le => CmpOp.strRun4_le | gt => CmpOp.strRun4_gt
  | ge => CmpOp.strRun4_ge

theorem CmpOp.errL1 : ∀ o : CmpOp, o.ErrRun true errL1
  | lt => CmpOp.errL1_lt | le => CmpOp.errL1_le | gt => CmpOp.errL1_gt | ge => CmpOp.errL1_ge

theorem CmpOp.errL2 : ∀ o : CmpOp, o.ErrRun true errL2
  | lt => CmpOp.errL2_lt | le => CmpOp.errL2_le | gt => CmpOp.errL2_gt | ge => CmpOp.errL2_ge

theorem CmpOp.errR1 : ∀ o : CmpOp, o.ErrRun false errR1
  | lt => CmpOp.errR1_lt | le => CmpOp.errR1_le | gt => CmpOp.errR1_gt | ge => CmpOp.errR1_ge

theorem CmpOp.errR2 : ∀ o : CmpOp, o.ErrRun false errR2
  | lt => CmpOp.errR2_lt | le => CmpOp.errR2_le | gt => CmpOp.errR2_gt | ge => CmpOp.errR2_ge

theorem CmpOp.epi : ∀ o : CmpOp, EpiRun (BitVec.ofNat 64 (o.vb.i + 4))
  | lt => epi_800036cc | le => epi_80003b04 | gt => epi_80003af0 | ge => epi_800036cc

theorem HiKeep.helperRA {clob : List Nat} {R R' : Nat → BitVec 64}
    (h : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (h2 : 2 ∉ clob) (hc : ∀ x ∈ hiSaved, x ∉ clob)
    (v : BitVec 64) : HiKeep R (Sym.upd R' 1 v) :=
  (HiKeep.of_helper h h2 hc).upd (x := 1) v (by decide) (by decide)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem BinTail.ints {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {F : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem} {a b : Int}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : w1.toInt = a → u1.toInt = b →
      ArmAt Wp Φ F 0x8000351c#64 R (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N F R s Mt (.int a) (.int b) w0 w1 w2 u0 u1 u2 := by
  unfold BinTail valOf
  iintro ⟨⟨%⟨_, h1⟩, %⟨_, h2⟩⟩, HF, Hms⟩
  iapply (h h1 h2)
  iframe HF Hms

theorem BinTail.strs {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat}
    {Out Wd K : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem} {x y : String}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd
      iprop(K ∗ □ (strAt w1.toNat x ∗ strAt u1.toNat y))) 0x8000351c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N (evalArmF P m env aE s' n' Out Wd K) R s Mt (.str x) (.str y) w0 w1 w2 u0 u1 u2 := by
  unfold BinTail valOf
  iintro ⟨⟨⟨-, #Hx⟩, ⟨-, #Hy⟩⟩, HF, Hms⟩
  iapply h
  iframe Hms
  unfold evalArmF
  icases HF with ⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, HK⟩
  iframe Hc Hr Hf Hs Ho Hw HK
  iframe Hx Hy

theorem BinTail.drop {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {F : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem}
    {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : ArmAt Wp Φ F 0x8000351c#64 R (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N F R s Mt lv rv' w0 w1 w2 u0 u1 u2 := by
  unfold BinTail
  iintro ⟨-, HF, Hms⟩
  iapply h
  iframe HF Hms

theorem cmpIntTail (o : CmpOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret inp aX : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {a b : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    {Wd K : IProp GF}
    (g : ArmGeo s ret sret n) (hn : BinOpNode m P aX (binOpTok o.op))
    (mid : BinMid s sret inp rv R Mt ret aX (.int a) (.int b) w0 w1 w2 u0 u1 u2)
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool (o.intSem a b)) Wd K) :
    BinTail Wp Φ N (binArmF N P m env aE s n sret Wd K) R s Mt (.int a) (.int b)
      w0 w1 w2 u0 u1 u2 := by
  refine BinTail.ints fun h1 h2 => ?_
  refine ArmAt.run Wp hn.view (o.intRun hlive g hn mid) fun R3 Mt3 p3 => ?_
  refine ArmAt.callBool Wp o.vb hlive hvb p3.a0 p3.a1 g.slg fun R4 hk4 => ?_
  rw [o.intBit_spec, h1, h2]
  have k4 := p3.keep.trans (HiKeep.helperRA hk4 (by decide) (by decide) (BitVec.ofNat 64 (o.vb.i + 4)))
  refine ArmAt.run Wp hn.view (o.epi hlive g (k4.sp.trans mid.r2) (p3.saved mid.saved))
    fun R5 _ p5 => ?_
  exact ArmAt.finish Wp hexit g.sg.le g.need p5.ra
    (p5.keep (fun x hx => (k4.hi x hx).trans (mid.hi x hx)) mid.sp)

theorem cmpStrTail (o : CmpOp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hsc : ⊢ strcmpOrdSpec (vsaModel live) Wp)
    (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret inp aX : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {x y : String} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    {Wd K : IProp GF} (hbi : Wd ⊢ Wd ∗ Newlib.binImg)
    (g : ArmGeo s ret sret n) (hn : BinOpNode m P aX (binOpTok o.op))
    (mid : BinMid s sret inp rv R Mt ret aX (.str x) (.str y) w0 w1 w2 u0 u1 u2)
    (hexit : ExitK Wp Φ N s ret sret rv n (.bool (o.strSem x y)) Wd K) :
    BinTail Wp Φ N (binArmF N P m env aE s n sret Wd K) R s Mt (.str x) (.str y)
      w0 w1 w2 u0 u1 u2 := by
  refine BinTail.strs ?_
  refine ArmAt.run Wp hn.view (o.strRun3 hlive g hn mid) fun R3 Mt3 p3 => ?_
  refine ArmAt.callHelperPure Wp (jal_site% 0x80003b18) hlive
    (hsc.trans (strcmpOrdSpec_at (vsaModel live) w1 u1 x y)) ⟨p3.a0, p3.a1⟩ ?_ fun R4 hk4 hsign => ?_
  · iintro ⟨Hw, HK⟩
    ihave ⟨Hw, #Hb⟩ := hbi $$ Hw
    icases HK with ⟨HK, #Hxy⟩
    isplitl [Hw]
    · iexact Hw
    isplitl [HK]
    · iframe HK; iexact Hxy
    icases Hxy with ⟨#Hx, #Hy⟩
    iframe Hb Hx Hy
  have k4 := p3.keep.trans (HiKeep.helperRA hk4 (by decide) (by decide)
    (BitVec.ofNat 64 ((jal_site% 0x80003b18 : JalAt strcmpPCV).i + 4)))
  refine ArmAt.run Wp hn.view (o.strRun4 hlive g ?_ (k4.sp.trans mid.r2) p3.tag)
    fun R5 Mt5 p5 => ?_
  · rw [upd_other R4 _ (show (9 : Nat) ≠ 1 by decide), hk4 9 (by decide) (by decide), p3.s1, mid.r9]
  refine ArmAt.callBool Wp o.vb hlive hvb p5.a0 p5.a1 g.slg fun R6 hk6 => ?_
  rw [upd_other R4 _ (show (10 : Nat) ≠ 1 by decide), o.strBit_spec hsign]
  have k6 := p5.keep.trans (HiKeep.helperRA hk6 (by decide) (by decide) (BitVec.ofNat 64 (o.vb.i + 4)))
  have k6' := k4.trans k6
  refine ArmAt.run Wp hn.view
    (o.epi hlive g (k6'.sp.trans mid.r2) (p5.saved (p3.saved mid.saved))) fun R7 _ p7 => ?_
  exact ArmAt.finish Wp (ExitK.frame _ hexit) g.sg.le g.need p7.ra
    (p7.keep (fun x hx => (k6'.hi x hx).trans (mid.hi x hx)) mid.sp)

theorem cmpErrTail (o : CmpOp) {left : Bool} {hyp : Value → Value → Prop}
    (herr : o.ErrRun left hyp) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (vsaModel live) Wp p Mt v)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret aX : BitVec 64} {d : Nat} {l r : Expr} {rv R : Nat → BitVec 64} {Mt : Mem}
    {ρ : Regime} {st : St} {lv rv' : Value} {w0 w1 w2 u0 u1 u2 : BitVec 64} {K : IProp GF}
    (g : ArmGeo s ret sret (evalNeed (.binary o.op l r) d)) (hn : BinOpNode m P aX (binOpTok o.op))
    (mid : BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2)
    (h : hyp lv rv')
    (hab : AbortK Wp Φ inp Core s sret (evalNeed (.binary o.op l r) d) K) :
    BinTail Wp Φ N (binArmF N P m env aE s (evalNeed (.binary o.op l r) d) sret
      (world N L Room inp ρ st d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2 :=
  BinTail.drop (ArmAt.run Wp hn.view (herr hlive g hn mid h) fun _ _ p =>
    binErrTail Wp hlive hE hvk (jal_site% 0x80003e7c) (jal_site% 0x80003e98) rt_80003e80
      o.opnName g (evalNeed_binary_rtErr _ _ _ _) hn.view (v := if left then lv else rv')
      p.a0 (p.s2.trans mid.r18) (p.sp.trans mid.r2) p.slot
      (by cases left <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
        first | exact mid.tl | exact mid.tr) p.opn hab)

theorem cmpIntT (o : CmpOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {a b : Int} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 (.int a) nl) (Dr : EvalECost st1 d env r st2 (.int b) nr)
    (D : EvalECost st d env (.binary o.op l r) st2 (.bool (o.intSem a b)) (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 (.int a) nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 (.int b) nr Dr)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary o.op l r) st2
        (.bool (o.intSem a b)) (nl + nr) D :=
  binPreludeT hlive Dl Dr D hl hr fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hn mid hexit =>
    cmpIntTail o (twpW _) hlive hvb g hn mid hexit

theorem cmpStrT (o : CmpOp) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {x y : String} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 (.str x) nl) (Dr : EvalECost st1 d env r st2 (.str y) nr)
    (D : EvalECost st d env (.binary o.op l r) st2 (.bool (o.strSem x y)) (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 (.str x) nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 (.str y) nr Dr)
    (hsc : ⊢ strcmpOrdSpec (GF := GF) (vsaModel live) (twpW (vsaModel live)))
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary o.op l r) st2
        (.bool (o.strSem x y)) (nl + nr) D :=
  binPreludeT hlive Dl Dr D hl hr fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hn mid hexit =>
    cmpStrTail o (twpW _) hlive hsc hvb (world_binImg N L Room inp _ _ d) g hn mid hexit

theorem cmpP (o : CmpOp) {op : BinOp} (hop : o.op = op) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hE : ErrEnv (GF := GF) N L Room inp live Core)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b)
    (hsc : ⊢ strcmpOrdSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)))
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.binary op l r) :=
  hop ▸ binPreludeP hlive fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lv rv' _ _ _ g hn mid hexit hab => by
    rcases cmpRows lv rv' with ⟨a, b, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨hR3, hL⟩ |
      ⟨y, rfl, hL, hL3⟩ | ⟨a, rfl, hR, hR3⟩ | ⟨a, y, rfl, rfl⟩
    · exact cmpIntTail o (wpW _) hlive hvb g hn mid (hexit _ (o.sem_int _ a b))
    · exact cmpStrTail o (wpW _) hlive hsc hvb (world_binImg N L Room inp _ _ d) g hn mid
        (hexit _ (o.sem_str _ x y))
    · exact cmpErrTail o o.errL1 (wpW _) hlive hE hvk g hn mid ⟨hL, hR3⟩ hab
    · exact cmpErrTail o o.errL2 (wpW _) hlive hE hvk g hn mid ⟨hL, hL3, rfl⟩ hab
    · exact cmpErrTail o o.errR1 (wpW _) hlive hE hvk g hn mid ⟨rfl, hR, hR3⟩ hab
    · exact cmpErrTail o o.errR2 (wpW _) hlive hE hvk g hn mid ⟨rfl, rfl⟩ hab

end

end VsaIris.Interp
