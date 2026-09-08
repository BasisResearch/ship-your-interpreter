import Vsa.Sim.EvalBinSim
import Vsa.Sim.ExitFootprint

/-!
# `BinaryHeadFootprint` — the two-children head of the binary arm, with footprint

`blockB_binary_footprint` (`EvalBinSim.lean`) runs the binary arm from its entry
through both child calls and returns `TwoSubReturn` together with the head's
footprint `binaryHeadFoot Fl Fr SL A sp` (`ExitFootprint.lean`): the parent's
stack window and the two children's footprints at their geometry.  This file
states the head contract the footprint rows consume and discharges it:

* `BinaryHeadFootprintSupply Fl Fr` — the head contract the footprint rows
  consume: `blockB_binary_data`'s own Triple with both children at `EvalIHF Fl`
  / `EvalIHF Fr` and the head footprint retained at the actual return;
  `binaryHeadFootprintSupply` discharges it from `blockB_binary_footprint`
  (`EvalBinSim.lean`);
* `intLeftSurvives` — the `hVlSurv` premise of the head at an integer left
  operand (vacuous: the int value lives in the parent's frame), shared by every
  integer row's footprint sibling.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- The two-children head with its footprint retained: `blockB_binary_data` with
both children at `EvalIHF Fl` / `EvalIHF Fr` and
`MemFootprint (binaryHeadFoot Fl Fr SL A sp.toNat) m0` at the actual return.
Supplied by `binaryHeadFootprintSupply` below (from `blockB_binary_footprint`). -/
def BinaryHeadFootprintSupply (Fl Fr : FootFam) : Prop :=
  ∀ (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (op : BinOp) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalE st d env el st' vl →
    EvalIHF Fl st d env el st' vl →
    EvalIHF Fr st' d env er st'' vr →
    (∀ (φ : Addr → Nat) (m m' : Mem),
      ValueRepr m N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → m[k]? = m'[k]?) →
      ValueRepr m' N φ (sp.toNat - 968) vl) →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (ReturnedWith
        (TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' vl vr sp r sret v8 v9 v18 m0)
        (fun c => BinaryReturnData SL sp sret c ∧
          MemFootprint (binaryHeadFoot Fl Fr SL A sp.toNat) m0 c.σ.mem))

/-- The head's left-survival premise at an INTEGER left operand: the int value
lives in the parent's frame `[sp-968, sp-952)`, outside every window the right
child may touch (the head's geometry `BinExtras.sproom`/`.arenaStk`). -/
theorem intLeftSurvives {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp : BitVec 64} (a : Int)
    (hsproom : SL.lo + 3264 ≤ sp.toNat) (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) :
    ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) (.int a) →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) (.int a) := by
  intro φ mm mm' hv hag
  obtain ⟨hk, hp⟩ := hv
  have hAg : AgreeP (fun k => sp.toNat - 968 ≤ k ∧ k < sp.toNat - 952) mm mm' := by
    intro k hk'
    exact hag k (by omega) (by rcases harenaStk with h | h <;> omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [← read32_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hk
  · rw [readI64] at hp ⊢
    rw [← read64_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hp

/-- The head footprint premise is supplied by `blockB_binary_footprint`. -/
theorem binaryHeadFootprintSupply (Fl Fr : FootFam) : BinaryHeadFootprintSupply Fl Fr :=
  fun gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
      hLeft hIHl hIHr hVlSurv =>
    blockB_binary_footprint Fl Fr gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr hVlSurv

#print axioms binaryHeadFootprintSupply
#print axioms intLeftSurvives

end Vsa.Sim
