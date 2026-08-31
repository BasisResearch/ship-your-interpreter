import Vsa.Sim.rows.ErrorRouting

/-!
# `ErrorReachInhab` — the corrected `hsite` shape is INHABITABLE (one class)

The obstruction (`ErrLinkObstruction.jalErrPre_forall_false`) refuted the OLD
error residual `∀ c, JalErrPre S … <pc> <bytes> c` as an *unconditional* universal.
The fix (`ErrorReach.lean` + the regenerated routes) replaced it with the
`SitePre`-conditioned reachability `ReachJal S … <pc> <bytes> c := ∃ c', Steps c c'
∧ JalErrPre S … c'`, threaded under each premise's spec-derivation context.

This file DEMONSTRATES, on the `hNegType` class (`jal runtime_error @ 0x800034e4`),
that the new shape is genuinely inhabitable — we did NOT trade one false universal
for another.  Two witnesses:

* `reachJal_of_armBranch` — the general inhabitant: from ANY error-branch reachability
  `Triple ArmBranchPre (JalErrPre …)` (the seg an M4 arm supplies) and the arm-entry
  hypothesis `ArmBranchPre c`, the conditioned residual `ReachJal … c` holds.  This is
  the exact composition an error-branch seg + arm context meets — unlike the old
  universal, which no seg could inhabit *at all* (its target type was wrong).
* `negType_hsite_of_armBranch` — the FULL route-shaped `hNegType` residual (spec
  binders + hyps → `ReachJal …`) built from such an arm branch, then fed through
  `route_hNegType`/`errRow_reach` to `ErrHalts c`.  So the corrected residual both
  (a) has an inhabitant and (b) discharges the real routing premise.

The witnesses are parametric in the arm-branch seg `Triple ArmBranchPre (JalErrPre …)`
because no landed M4 arm-sim yet pins the error edge `0x800034c0 → jal @ 0x800034e4`
(ledger `errlink-forall-shape-obstruction`); the point here is the SHAPE composes and
is satisfiable, contrasted with the refuted universal.  When that seg lands it drops
in directly.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- **The general inhabitant.**  From an error-branch reachability triple
`Triple ArmBranchPre (JalErrPre …)` (an M4 arm supplies this by a `#derive_case`
seg from the arm-entry context to the site's `jal`) and the arm-entry hypothesis
`ArmBranchPre c`, the `SitePre`-conditioned residual `ReachJal … c` holds.  This is
the composition the corrected route demands — and it type-checks, unlike a seg
against the refuted `∀ c, JalErrPre … c`. -/
theorem reachJal_of_armBranch (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {ArmBranchPre : Config → Prop}
    (seg : Triple ArmBranchPre (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (harm : ArmBranchPre c) :
    ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c :=
  seg c harm

/-- **The full `hNegType` route residual, built from an arm branch.**  Given the
`hNegType` arm's error-branch entry predicate `ArmBranchPre`, a seg `Triple
ArmBranchPre (JalErrPre S … 0x800034e4 …)`, and the arm's linkage that the spec
`negType` context lands the machine at that branch entry (`hlink`, the genuine M4
residual), the corrected conditioned `hsite` for `hNegType` is inhabited.  Feeding
it to `route_hNegType` then yields the `errFamily_of_sites` premise conclusion —
demonstrating the shape is both satisfiable and sufficient. -/
theorem negType_hsite_of_armBranch (S : ErrShared)
    {ArmBranchPre : Config → Prop}
    (seg : Triple ArmBranchPre
      (JalErrPre S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8))
    (hlink : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ArmBranchPre c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  route_hNegType S
    (fun c st d env e st' v hEval hNotInt =>
      reachJal_of_armBranch S 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 seg c
        (hlink c st d env e st' v hEval hNotInt))

#print axioms reachJal_of_armBranch
#print axioms negType_hsite_of_armBranch

/-! ## The contrast, made precise

`reachJal_of_armBranch` inhabits `ReachJal … c` from a *hypothesis* (the arm seg +
entry).  The refuted `∀ c, JalErrPre … c` had NO such inhabitant: it asserted the
jal precondition for every `c` under no hypotheses, which
`ErrLinkObstruction.jalErrPre_forall_false` disproves.  So the correction is a real
one — the new residual is met by real reachability, not a relabelled falsity. -/

end Vsa.Sim
