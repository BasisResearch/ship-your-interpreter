import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ExecBlock

/-!
# Layer 4 — `WidenMeta`: ONE parametric exit-widener (the 5-widener zoo unified)

This file collapses the five bespoke exit-wideners — `LeafWiden` (EvalLeafD),
`ExecLeafWiden` (ExecCaseGeom), `ExecRecWiden` (ExecRecRows), `EvalRecWiden`
(CallRows), and the `evalExit_rebase`/`blockD_v_phic` φ-widened epilogue
(CallArmEpilogue) — into ONE relation-agnostic object, per
`experiments/abstraction-tower-design.md` §T1.2.

## What every widener does

Each answers the SAME question: upgrade a bare exit predicate (`EvalExit` /
`ExecExit`) to the motive's `*ExitD` by re-supplying the two clauses `*Exit`
forgets:

* **(a) presence monotonicity** — `MemExtends m0 mem` (`Widen.pres`);
* **(b) `[SL.lo,SL.hi)`-store-survival** — the re-represented `st'.store`, at ONE
  coherent extended φ-pair (`Widen.phiF`/`Widen.phiC`/`Widen.surv`), tolerates
  arbitrary further memory change confined to the survival footprint.

They differ only along three axes, ALL now parameters of `Widen`:

1. **which exit family** — `Eval` vs `Exec`.  `Widen` takes the FULLY-APPLIED
   exit predicate `ExitP : Config → Prop`, so it is relation-agnostic; the two
   family bridges (`evalExitD_of_widen`/`execExitD_of_widen`) marshal into the
   respective `*ExitD`.
2. **φ story** — identity (leaf: the sub-derivation allocates nothing, so the
   supplied `φf'/φc'` are `φf/φc` by `PhiExtends.refl`) vs extends (recursive:
   the sub-derivation grew the store maps, so `φf'/φc'` are genuine extensions).
   Both are the SAME `∃ φf' φc', PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧ …`
   shape — leaves witness it at `refl`.
3. **survival footprint** — a `Nat → Prop` predicate `foot` (the FrameMeta
   `memFrame` style): spill-only `[SL.lo,SL.hi)` for the leaves and the rec exits;
   `[SL.lo,SL.hi) ∪ [aRet,aRet+24)` for the retslot-writing statement cases
   (retNull/varNull).  A `Widen` at ANY footprint `foot ⊇ [SL.lo,SL.hi)`
   discharges the footprint-fixed `*ExitD` survival clause (`Widen.footMono`).

## Elaboration story

`Widen` is a projected named-field `structure … : Prop where` (R6/R7 gate: no
positional `.2`-towers); the bridges are term-level record reshapes.  No whnf of
Sail state — everything is stated on `MemExtends`/`StoreRepr` presence and the
`PhiExtends`/`≤` reindexing the sub-derivations already carry.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

/-! ## `stackFoot` — the canonical `[SL.lo,SL.hi)` survival footprint

The footprint every leaf/rec widener uses.  Named so callers reference it by name
rather than re-inlining the interval, and so `footMono` proofs are `fun _ h => h`. -/
def stackFoot (SL : StackLayout) : Nat → Prop := fun k => SL.lo ≤ k ∧ k < SL.hi

/-- The retslot-augmented footprint `[SL.lo,SL.hi) ∪ [aRet, aRet+24)` — the
survival window for the statement cases that write the caller retslot
(`retNull`/`varNull`).  A superset of `stackFoot`, so it still discharges the
`[SL.lo,SL.hi)`-fixed `*ExitD` survival clause. -/
def retslotFoot (SL : StackLayout) (aRet : BitVec 64) : Nat → Prop :=
  fun k => (SL.lo ≤ k ∧ k < SL.hi) ∨ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24)

/-! ## `Widen` — the ONE parametric exit-widener

For ANY config `c` satisfying the fully-applied exit predicate `ExitP`, yields the
two `*ExitD` upgrade clauses about `c`: presence monotonicity and the survival of
`st'.store` at one extended φ-pair over the footprint `foot`.  This is TRUE of
every leaf/recursive exit (the memory delta is a `writeMap` chain over `m0` —
presence-preserving — and the store footprint is disjoint from `foot`), and is the
honest re-supply of what `*Exit` forgets; the recursor's minor premise provides
it.  `ExitP` is fully applied, so `Widen` is relation-agnostic (Eval/Exec). -/
structure Widen (ExitP : Config → Prop)
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (nf nc : Nat)
    (st' : Vsa.While.St) (m0 : Mem) (foot : Nat → Prop) : Prop where
  /-- Presence monotonicity: the exit memory is a presence-superset of `m0`. -/
  pres : ∀ c : Config, ExitP c → MemExtends m0 c.σ.mem
  /-- Store survival at ONE extended φ-pair (`refl` for leaves).  For any exit
  config `c` and any memory `m'` agreeing with the exit outside `foot`,
  `st'.store` re-represents at some `φf'/φc'` extending the entry maps.  The φ
  pair is bound HERE (not as data fields — this is a `Prop` structure), matching
  the `*ExitD` existential shape.  For the leaves the recursor's residual supplies
  the pair at `PhiExtends.refl`. -/
  surv : ∀ c : Config, ExitP c →
    ∃ φf' φc' : Addr → Nat, PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧
      ∀ m' : Mem, (∀ k : Nat, ¬ foot k → c.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf' φc' st'.store

/-- **Footprint monotonicity.** A `Widen` at footprint `foot` whose `foot`
CONTAINS `stackFoot SL` also survives at the smaller `stackFoot SL` window: any
`m'` agreeing outside `stackFoot SL` a fortiori agrees outside `foot` (⊇), so the
survival clause fires.  This is the bridge from a retslot-augmented widener to the
`[SL.lo,SL.hi)`-fixed `*ExitD` survival clause. -/
theorem Widen.footMono
    {ExitP : Config → Prop} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St} {m0 : Mem} {SL : StackLayout} {foot : Nat → Prop}
    (hsub : ∀ k : Nat, (SL.lo ≤ k ∧ k < SL.hi) → foot k)
    (hW : Widen ExitP N A φf φc nf nc st' m0 foot) :
    Widen ExitP N A φf φc nf nc st' m0 (stackFoot SL) where
  pres := hW.pres
  surv := fun c hc =>
    let ⟨φf', φc', hpf, hpc, hsurv⟩ := hW.surv c hc
    ⟨φf', φc', hpf, hpc, fun m' hagree =>
      hsurv m' (fun k hk => hagree k (fun hstk => hk (hsub k hstk)))⟩

/-! ## The two family bridges — `Widen` at `stackFoot SL` → `*ExitD`

Both `EvalExitD` and `ExecExitD` are `*Exit ∧ MemExtends m0 mem ∧ ∃ φf' φc',
PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧ (survival at `[SL.lo,SL.hi)`)`.
Given the row's own `*Exit … c` and a `Widen` at `stackFoot SL`, the bridge is a
term-level record reshape — no new machine content. -/

/-- **`evalExitD_of_widen`** — the `EvalExit → EvalExitD` family bridge. -/
theorem evalExitD_of_widen
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St} {v : Value} {sp r sret : BitVec 64}
    {m0 : Mem} {c : Config}
    (hExit : EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c)
    (hW : Widen (EvalExit g N A SL φf φc nf nc st' v sp r sret m0)
      N A φf φc nf nc st' m0 (stackFoot SL)) :
    EvalExitD g N A SL φf φc nf nc st' v sp r sret m0 c :=
  ⟨hExit, hW.pres c hExit, hW.surv c hExit⟩

/-- **`execExitD_of_widen`** — the `ExecExit → ExecExitD` family bridge. -/
theorem execExitD_of_widen
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St} {status : Status} {sp r aRet : BitVec 64}
    {m0 : Mem} {c : Config}
    (hExit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m0 c)
    (hW : Widen (ExecExit g N A SL φf φc nf nc st' status sp r aRet m0)
      N A φf φc nf nc st' m0 (stackFoot SL)) :
    ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 c :=
  ⟨hExit, hW.pres c hExit, hW.surv c hExit⟩

end Vsa.Sim
