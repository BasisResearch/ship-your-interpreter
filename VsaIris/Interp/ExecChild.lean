import VsaIris.Interp.ExecDispOf

/-!
The child-evaluation call of a statement arm, as one mode-generic rule.

`ChildCall Wp Φ Hyp ρin ρout … Kin Kfin` says: from the parked `jal eval` state, holding the
persistent context `Hyp`, the world at `ρin` and the continuation resource `Kin`, the caller
continues from the child's return with some result `(st', v)`, the world at `ρout` and
`Kfin st' v`. The total instance (`childCallT`) fixes the result and moves the counted world
from `k + n` to `k`; the partial instance (`childCallP`) quantifies the result, derives
`Kfin st' v` from the evaluation witness, and discharges the child's abort through `Kin`.
Statement arms are proved once against `ChildCall`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The mode-generic child-evaluation call rule for a statement arm with frame `(s0, n0)`. -/
def ChildCall (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (Hyp : IProp GF)
    (ρin ρout : Regime) (st : St) (d env : Nat) (e : Expr) (s0 : BitVec 64) (n0 : Nat)
    (Out Kin : IProp GF) (Kfin : St → Value → IProp GF) : Prop :=
  ∀ (i : Nat) (code : List (BitVec 8)), JalExec (vsaModel live) i code evalEntryPC →
    (∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText) →
    (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0 →
    ∀ {R : Nat → BitVec 64} {Mt : Mem} {slot aC aE sF : BitVec 64} {f m : Nat},
    sF = s0 - BitVec.ofNat 64 f → StackGeom sF (evalNeed e d) → evalNeed e d ≤ m →
    m ≤ sF.toNat → m + f = n0 → n0 ≤ s0.toNat → SlotGeom slot →
    e.bodiesBound perCallBudget = true →
    (⌜EvalRegs R slot (BitVec.ofNat 64 inp) aC aE sF ∧
      ∀ b, InExt (slot.toNat, 24) b → InExt (s0.toNat - f, f) b⌝ ∗
      □ Hyp ∗ codeRes ∗ □ astEG aC.toNat e ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R (InExt (s0.toNat - f, f)) Mt ∗ stackScratch sF m ∗
      world N L Room inp ρin st d ∗ Out ∗ Kin ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (st' : St) (v : Value),
        ⌜KeepRegs calleeSaved R R'⌝ -∗ □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4)))
          (InExt (s0.toNat - f, f)) (slotWrite Mt slot.toNat w0 w1 w2) -∗
        stackScratch sF m -∗ world N L Room inp ρout st' d -∗ Out -∗ Kfin st' v -∗ Wp.W Φ)
      ⊢ Wp.W Φ)

/-- The total child call: the result is the costed evaluation's, the world pays `n`. -/
theorem childCallT {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Φ : Nat × String → IProp GF} {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value}
    {n k : Nat} (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D)
    {s0 : BitVec 64} {n0 : Nat} {Out : IProp GF} {Kfin : St → Value → IProp GF} :
    ChildCall N L Room inp (twpW (vsaModel live)) Φ emp (.counted (k + n)) (.counted k) st d env e
      s0 n0 Out (Kfin st' v) Kfin := by
  intro i code hexec hcode hal R Mt slot aC aE sF f m _ hsg hm hms _ _ hslg hbb
  iintro ⟨%hr, #-, #Hcode, #Hast, #Hfr, Hms, Hst, Hw, HOut, HK, Hk⟩
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) hexec hcode hal D (k := k)
    (S := InExt (s0.toNat - f, f)) hsg hm hms hslg hbb
  iframe He Hcode Hast Hfr Hms Hst Hw
  isplitl []
  · ipureintro; exact hr
  iintro %R' %w0 %w1 %w2 %hkeep #Hv Hms Hst Hw
  iapply Hk $$ %R' %w0 %w1 %w2 %st' %v %hkeep Hv Hms Hst Hw HOut HK

/-- The partial child call: any evaluation result, `Kfin` from its witness, abort through
`Kin`'s right conjunct. -/
theorem childCallP {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Φ : Nat × String → IProp GF} {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    {s0 : BitVec 64} {n0 : Nat} {Out Kret : IProp GF} {Kfin : St → Value → IProp GF}
    (hK : ∀ st' v, EvalE st d env e st' v →
      (Kret ∧ (iprop(abortAt Core s0 n0 ∗ Out) -∗ (wpW (vsaModel live)).W Φ)) ⊢ Kfin st' v) :
    ChildCall N L Room inp (wpW (vsaModel live)) Φ (evalSpecsP (vsaModel live) N L Room inp Core)
      .uncounted .uncounted st d env e s0 n0 Out
      iprop(Kret ∧ (iprop(abortAt Core s0 n0 ∗ Out) -∗ (wpW (vsaModel live)).W Φ)) Kfin := by
  intro i code hexec hcode hal R Mt slot aC aE sF f m hsF hsg hm hms hn0 hn0s hslg hbb
  iintro ⟨%hr, #IH, #Hcode, #Hast, #Hfr, Hms, Hst, Hw, HOut, HK, Hk⟩
  ihave He := evalSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env e $$ IH
  iapply ms_callEvalPF (N := N) (L := L) (Room := Room) (inp := inp) hexec hcode hal
    (Kret := Kret) (Out := Out) (Core := Core) hsF hsg hm hms hn0 hn0s hslg hbb
  iframe He Hcode Hast Hfr Hms Hst Hw HOut HK
  isplitl []
  · ipureintro; exact hr
  iintro %R' %w0 %w1 %w2 %st' %v %hE %hkeep #Hv Hms Hst Hw HOut HK
  ihave HK := (hK st' v hE) $$ HK
  iapply Hk $$ %R' %w0 %w1 %w2 %st' %v %hkeep Hv Hms Hst Hw HOut HK

/-- The partial continuation instantiated at an arm's `ExecS` constructor. -/
theorem execKP_of {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Φ : Nat × String → IProp GF} {st st' : St} {d env : Nat} {sm : Stmt} {status : Status}
    {aRet s : BitVec 64} {R : Nat → BitVec 64} {ret v8 v9 v18 v19 : BitVec 64} {A : IProp GF}
    (hE : ExecS st d env sm st' status) :
    ((∀ (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d sm status
          aRet s R ret v8 v9 v18 v19) ∧ A) ⊢
      execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d sm status
        aRet s R ret v8 v9 v18 v19 := by
  iintro HK
  ihave HK := and_elim_l $$ HK
  iapply HK $$ %st' %status %hE


/-- A statement arm with one child evaluation whose result selects the status: proved once for
every child-call mode. -/
def ExecChildCore (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (st : St)
    (d env : Nat) (sm : Stmt) (e : Expr) (stat : Value → Status) : Prop :=
  ∀ (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (Hyp : IProp GF)
    (ρin ρout : Regime) (Kin : IProp GF) (aS aE aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64),
    ChildCall N L Room inp Wp Φ Hyp ρin ρout st d env e s (execNeed sm d) (slot24 aRet.toNat) Kin
      (fun st' v => execDispK (vsaModel live) N L Room inp Wp Φ ρout st' d sm (stat v) aRet s R
        ret v8 v9 v18 v19) →
    □ Hyp ∗ execDispPre N L Room inp ρin st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 ∗ Kin ⊢
      Wp.W Φ

theorem execChildT_of {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {sm : Stmt} {e : Expr} {stat : Value → Status} {st' : St} {v : Value}
    {n : Nat} (D : ExecSCost st d env sm st' (stat v) n) (De : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n De)
    (core : ExecChildCore (GF := GF) (live := live) N L Room inp st d env sm e stat) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env sm st' (stat v) n D := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  iapply core (twpW _) Φ emp (.counted (k + n)) (.counted k) _ aS aE aRet s R Mt ret v8 v9 v18
    v19 (childCallT De he)
  iframe Hpre HK
  exact (intuitionistically_emp (PROP := IProp GF)).2

theorem execChildP_of {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt} {e : Expr} {stat : Value → Status}
    (hmk : ∀ st' v, EvalE st d env e st' v → ExecS st d env sm st' (stat v))
    (core : ExecChildCore (GF := GF) (live := live) N L Room inp st d env sm e stat) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env sm := by
  iintro #IH
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  iapply core (wpW _) Φ _ .uncounted .uncounted _ aS aE aRet s R Mt ret v8 v9 v18 v19
    (childCallP (Core := Core) fun st' v h => execKP_of (hmk st' v h))
  iframe IH Hpre HK

end

end VsaIris.Interp
