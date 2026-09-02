import Vsa.Sim.InductionScaffold

/-!
# Honest no-op rows for the loop scaffold

`ExecInit.none`, `ForCond.none`, and `ExecStep.none` do not change the
specification state. Their machine rows are identity triples only when the
entry and exit PCs coincide. This file provides that common proof once.

HISTORICAL (2026-08-31, ledgers `scaffold-motive-independent-pq` then
`scaffold-some-motive-unsatisfiable`): the `TermSimAssembly` scaffold motives
formerly quantified independent `p`/`q` (no identity row could discharge them);
amended to a single identity-PC `p`, which fixed `.none` (via `segIdentity`) but
left the DUAL `.some` obstruction (store-mutating span at the same PC is
unsatisfiable). FINAL amendment: `mExecInit`/`mForCond`/`mExecStep` are now `True`
(dead recursor plumbing — `execForStartSim` ignores these sub-derivations), so all
six premises (`hInit{None,Some}`/`hFc{None,Some}`/`hEs{None,Some}`) are LANDED as
`trivial` rows in `Vsa/Sim/rows/ScaffoldRows.lean`; the `.some` `*_resid` defs are
DELETED. `segIdentity` (this file) is STILL live: `mForLoop` remains an
identity-PC `SegEntry → SegExit` span and `ScaffoldRows`/`SeqForRows`'s `ForResid`
uses it. A no-op row uses one shared PC.

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
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st p m0) := by
  intro c hc
  refine ⟨c, .refl c, ?_⟩
  exact
    { good := hc.good
      tick := hc.tick
      pc := hc.pc
      store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hc.store⟩
      out := hc.out
      -- wave-45 guarded frame: the full `SegEntry.frame` supplies every
      -- register, so the `joinRestored` guard is ignored.
      frame := fun R hR _ => hc.frame R hR
      memFrame := fun a _ _ => by rw [hc.mem]
      -- zero-step identity: memory IS `m0`, so the stack window survives at any
      -- tabled exit PC (wave-38 clause).
      stackWin := fun _ _ _ _ a _ _ _ => by rw [hc.mem] }

/-- Identity row with an explicit proof that the two PC parameters coincide. -/
theorem segIdentity_of_eq
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d dLeft aLeft p q : Nat) (m0 : Mem) (hpq : p = q) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st q m0) := by
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
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- Honest `ForCond.none` row at the loop-head control point. -/
theorem forCondNone_samePC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d env dLeft aLeft p : Nat) (m0 : Mem)
    (_h : ForCond st d env none st) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- Honest `ExecStep.none` row at the loop-head control point. -/
theorem execStepNone_samePC
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d env dLeft aLeft p : Nat) (m0 : Mem)
    (_h : ExecStep st d env none st) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st p m0) :=
  segIdentity g N A SL φf φc st d dLeft aLeft p m0

#print axioms segIdentity
#print axioms segIdentity_of_eq
#print axioms execInitNone_samePC
#print axioms forCondNone_samePC
#print axioms execStepNone_samePC

end Vsa.Sim.LoopScaffoldClose
