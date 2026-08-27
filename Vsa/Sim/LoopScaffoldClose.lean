import Vsa.Sim.InductionScaffold

/-!
# Honest no-op rows for the loop scaffold

`ExecInit.none`, `ForCond.none`, and `ExecStep.none` do not change the
specification state. Their machine rows are identity triples only when the
entry and exit PCs coincide. This file provides that common proof once.

The current `TermSimAssembly` motives quantify independent `p` and `q` for
these constructors. That stronger shape cannot be discharged by an identity
row. Callers must supply the actual control-flow segment or first repair the
motive with relation-specific PCs and ABI/code pins. A no-op row must use one
shared PC.

Timing witness (2026-08-26): `lake env lean Vsa/Sim/LoopScaffoldClose.lean`
completed in 4.55 seconds.

-/

namespace Vsa.Sim.LoopScaffoldClose

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold

/-- A skeleton segment whose specification state and PC are unchanged. -/
theorem segIdentity
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d dLeft aLeft p : Nat) (m0 : Mem) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st p m0) := by
  intro c hc
  refine ⟨c, .refl c, ?_⟩
  exact
    { good := hc.good
      tick := hc.tick
      pc := hc.pc
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hc.store⟩
      out := hc.out
      frame := hc.frame
      memFrame := fun a _ _ => by rw [hc.mem] }

/-- Identity row with an explicit proof that the two PC parameters coincide. -/
theorem segIdentity_of_eq
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d dLeft aLeft p q : Nat) (m0 : Mem) (hpq : p = q) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st q m0) := by
  subst q
  exact segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- Honest `ExecInit.none` row at a shared control point. -/
theorem execInitNone_samePC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d env dLeft aLeft p : Nat) (m0 : Mem)
    (_h : ExecInit st d env none st) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- Honest `ForCond.none` row at the loop-head control point. -/
theorem forCondNone_samePC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d env dLeft aLeft p : Nat) (m0 : Mem)
    (_h : ForCond st d env none st) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- Honest `ExecStep.none` row at the loop-head control point. -/
theorem execStepNone_samePC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d env dLeft aLeft p : Nat) (m0 : Mem)
    (_h : ExecStep st d env none st) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

#print axioms segIdentity
#print axioms segIdentity_of_eq
#print axioms execInitNone_samePC
#print axioms forCondNone_samePC
#print axioms execStepNone_samePC

end Vsa.Sim.LoopScaffoldClose
