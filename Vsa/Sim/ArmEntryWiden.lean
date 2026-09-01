import Vsa.Sim.EvalSimCommon
import Vsa.Sim.EvalIntSim2

/-!
# `ArmEntryWiden` — the generic arm-entry widening (Task #48 proposal 1)

The three composite-arm oracles (`FnArmSpec`/`AssignArmSpec`/`CallArmSpec`) each
begin their `hArm` run from `EvalEntry` and must reach the arm's dispatch target
`ArmEntryK … armPC calleeLoaded e` before running the arm body.  `blockA_k`
(`EvalIntSim2`) already IS the callee-generic prologue+dispatch — but it consumes
the *case-independent subset* of `EvalEntry` packaged as an anonymous precondition
tower, not an `EvalEntry` value, and (per the armspec-oracle-family observation,
`experiments/observations.md`) `EvalEntry` bakes in the INT-specific callee facts
(`value_int_code`/`int_slot`/`vicode_stack_disjoint`/`table_stack_disjoint`), so
`blockA_k` cannot run at a non-int arm off `EvalEntry` *alone*.

`armEntry_widen` factors the marshalling `evalVarSim` (`EvalVarSim.lean`) did by
hand: it takes an `EvalEntry` PLUS the arm-specific dispatch facts (`hkind`/
`hslot`/`hcallee`/`hcalleeSurv`/`hexprSurv`/`harmAl`/`htableStk` — the fields
`EvalEntry` cannot carry because they are callee-generic, exactly the int-coupling
finding) and yields the `blockA_k` conclusion `∃ ment v8 v9 v18, ArmEntryK … armPC
calleeLoaded e`, with `out0 := c.σ.sailOutput`.  It serves EVERY composite arm at
once: the fn/call/assign `hArm` fields can START from `ArmEntryK` instead of
re-deriving the prologue, and any future leaf case (null/bool/str) reuses it too.

This is a pure `blockA_k`-application: the case-independent tower is reconstructed
from `EvalEntry`'s named fields (the same projection `evalVarSim` did inline), so
there is NO machine reasoning here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim

namespace Vsa.Sim

/-- **`armEntry_widen`** — the generic prologue+dispatch widening.  From an
`EvalEntry` (whose case-independent subset feeds `blockA_k`) plus the arm-specific
dispatch facts, reach the arm's `ArmEntryK … armPC calleeLoaded e`.  `out0` is
pinned to `c.σ.sailOutput` (so the `blockA_k` `sailOutput = out0` obligation is
`rfl`).  The arm-specific args are exactly the fields `EvalEntry` cannot carry
because they are callee-generic — supplied per arm (`KindSlotPinned k armPC`, the
callee-loaded predicate + its spill-survival, the `ExprRepr` spill-survival, the
arm-PC alignment, and the arm's own jump-table-slot stack-disjointness). -/
theorem armEntry_widen
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (e : Expr)
    (k : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    -- arm-specific dispatch data (the callee-generic facts `EvalEntry` cannot bake in):
    (hkle : k ≤ 10) (hklt : k < 128)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hslot : KindSlotPinned k armPC m0) (hcallee : calleeLoaded m0)
    (hcalleeSurv : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
      SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd))
    (hexprSurv : ∀ m' : Mem,
      (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → m0[aa]? = m'[aa]?) → ExprRepr m' aExpr.toNat e)
    (harmAl : armPC.toNat % 4 = 0)
    (htableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k) :
    Triple
      (EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0)
      (fun c => ∃ out0 ment v8 v9 v18,
        ArmEntryK g N A SL φf φc st armPC calleeLoaded e
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c) := by
  intro c hc
  -- reconstruct the case-independent `blockA_k` precondition tower from `EvalEntry`,
  -- with `out0 := c.σ.sailOutput` (so `sailOutput = out0` is `rfl`).
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st e k armPC calleeLoaded
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      hkle hklt hkind hslot hcallee hcalleeSurv hexprSurv harmAl htableStk
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        hc.spill_defined⟩, rfl⟩
  exact ⟨c1, hs1, c.σ.sailOutput, ment, v8, v9, v18, hArm⟩

#print axioms armEntry_widen

end Vsa.Sim
