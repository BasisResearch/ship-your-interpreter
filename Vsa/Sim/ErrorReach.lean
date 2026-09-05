import Vsa.Sim.ErrorSiteJal

/-!
# `ErrorReach` — the `SitePre`-conditioned reachability residual for error routing (L6)

## The obstruction this replaces

The generated error-routing wrappers (`rows/ErrorRouting.lean`) previously demanded,
per `jal runtime_error` site, an **unconditional universal**

```
hsite : ∀ c : Config, JalErrPre S.g S.inp S.m0 <pc> <bytes> c
```

claiming EVERY config `c` is already parked at that site's `jal runtime_error`.  That
proposition is machine-checked FALSE (`Vsa/Sim/rows/ErrLinkObstruction.lean :
jalErrPre_forall_false`: a config with `tick := 2` violates `JalErrPre`'s `tick < 2`).
The route emitted it because it DISCARDED each error premise's spec-derivation data
(`fun c _ _ … =>`) and fed `errRow`'s `hsite : SitePre c` at an arbitrary `c`.

## What `errRow` actually requires

`errRow … (SitePre := P) (T : Triple P (RuntimeErrorAt …)) c (hsite : P c) : ErrHalts c`
is polymorphic in `SitePre`.  Reading `errFamily_of_sites` (`InterpSimBundle.lean`),
the config `c` is the **top-level entry config**, bound once and threaded into every
premise as `(hVarUndef c)`; the premise carries the spec error-derivation as
hypotheses but NO machine facts.  So the honest, inhabitable requirement is not
"`c` is at the jal" but "`c` REACHES the jal": pick

```
SitePre := ReachJal S pc b0 b1 b2 b3
         := fun c => ∃ c', Steps c c' ∧ JalErrPre S.g S.inp S.m0 pc b0 b1 b2 b3 c'
```

Then `T := Triple.seq (reachJal_triple …) (errSite_<pc> …)` and the residual becomes
`hsite : ReachJal … c`, i.e. **reachability from the entry config into the site's
`jal`** — conditioned, in the route, on the retained spec-derivation binders.

`ReachJal` is genuinely inhabitable (unlike the old universal): from an arm-branch
entry context one exhibits the concrete `c'` parked at the jal (`Steps` via a
`#derive_case` error-branch seg, then the seg's post IS `JalErrPre`).  See
`ErrorReachInhab.lean` for the machine-checked demonstration on one class.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.While
open Register

namespace Vsa.Sim

/-- **The `SitePre`-conditioned reachability residual.**  Config `c` (the top-level
entry config) *reaches* a config `c'` parked at the site's `jal runtime_error`
(`JalErrPre …`).  This is the corrected, inhabitable shape of the per-route error
residual: not "`c` is at the jal" (the refuted universal) but "`c` runs to the jal". -/
def ReachJal (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (c : Config) : Prop :=
  ∃ c', Steps c c' ∧ JalErrPre g inp m0 pcJal b0 b1 b2 b3 c'

/-- **`ReachJal` is a triple into `JalErrPre`.**  The zero-extra-content step: the
existential witness `c'` with its `Steps c c'` IS the run, and its `JalErrPre c'` IS
the post.  So `Triple.seq reachJal_triple (errSite_<pc> …)` gives a
`Triple (ReachJal …) (RuntimeErrorAt …)` — exactly the `T` `errRow` consumes with
`SitePre := ReachJal …`. -/
theorem reachJal_triple (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    Triple (ReachJal g inp m0 pcJal b0 b1 b2 b3)
      (JalErrPre g inp m0 pcJal b0 b1 b2 b3) :=
  fun _ ⟨c', hsteps, hjal⟩ => ⟨c', hsteps, hjal⟩

/-! ## Faithful semantic routing for binary failures

`EvalErr.binaryOp` is one semantic constructor, but the executable has eight
different error sites.  Which site is reached depends on the operator and, for
division and modulo, on whether the right operand is zero or an operand has the
wrong type.  Keeping that distinction in an indexed proposition prevents an
encoder or caller from assigning every binary failure the same PC.
-/

/-- A binary semantic failure reaches the machine site for its exact cause.

There are eight executable PCs: add type, subtract type, multiply type,
division by zero, division type, modulo by zero, modulo type, and ordered
comparison type.  Equality and inequality have no constructors because their
semantics never returns `none`.
-/
inductive BinaryErrReach
    (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) (s : Store) : BinOp → Value → Value → Prop where
  | add {lv rv : Value} :
      binOpSem s .add lv rv = none →
      ReachJal g inp m0 0x80003d5c#64 0xef#8 0xf0#8 0xcf#8 0x84#8 c →
      BinaryErrReach g inp m0 c s .add lv rv
  | sub {lv rv : Value} :
      binOpSem s .sub lv rv = none →
      ReachJal g inp m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c →
      BinaryErrReach g inp m0 c s .sub lv rv
  | mul {lv rv : Value} :
      binOpSem s .mul lv rv = none →
      ReachJal g inp m0 0x80003c7c#64 0xef#8 0xf0#8 0xcf#8 0x92#8 c →
      BinaryErrReach g inp m0 c s .mul lv rv
  | divZero (a : Int) :
      ReachJal g inp m0 0x80003d14#64 0xef#8 0xf0#8 0x4f#8 0x89#8 c →
      BinaryErrReach g inp m0 c s .div (.int a) (.int 0)
  | divType {lv rv : Value} :
      (¬ ∃ a b : Int, lv = .int a ∧ rv = .int b) →
      binOpSem s .div lv rv = none →
      ReachJal g inp m0 0x80003f58#64 0xef#8 0xe0#8 0x1f#8 0xe5#8 c →
      BinaryErrReach g inp m0 c s .div lv rv
  | modZero (a : Int) :
      ReachJal g inp m0 0x80003bc8#64 0xef#8 0xf0#8 0x0f#8 0x9e#8 c →
      BinaryErrReach g inp m0 c s .mod (.int a) (.int 0)
  | modType {lv rv : Value} :
      (¬ ∃ a b : Int, lv = .int a ∧ rv = .int b) →
      binOpSem s .mod lv rv = none →
      ReachJal g inp m0 0x80003c10#64 0xef#8 0xf0#8 0x8f#8 0x99#8 c →
      BinaryErrReach g inp m0 c s .mod lv rv
  | lt {lv rv : Value} :
      binOpSem s .lt lv rv = none →
      ReachJal g inp m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c →
      BinaryErrReach g inp m0 c s .lt lv rv
  | le {lv rv : Value} :
      binOpSem s .le lv rv = none →
      ReachJal g inp m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c →
      BinaryErrReach g inp m0 c s .le lv rv
  | gt {lv rv : Value} :
      binOpSem s .gt lv rv = none →
      ReachJal g inp m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c →
      BinaryErrReach g inp m0 c s .gt lv rv
  | ge {lv rv : Value} :
      binOpSem s .ge lv rv = none →
      ReachJal g inp m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c →
      BinaryErrReach g inp m0 c s .ge lv rv

/-! ## The non-`jal` top-level abrupt path

Top-level `return`/`break`/`continue` is handled in `interp_run` after
`exec_stmt` returns.  It does not execute a `jal runtime_error`, so its residual
must not be represented by `ReachJal`.
-/

/-- The direct `interp_run` path from an abrupt top-level sequence result to
exit 70.  This is the exact semantic input the machine proof must consume.
-/
def InterpRunAbruptPath (p : Program) (c : Config) : Prop :=
  ∀ (st' : Vsa.While.St) (status : Status), status ≠ .normal →
    ExecSeq initSt 0 0 p st' status → ErrHalts c

/-- Package the direct `interp_run` path as the `TopAbrupt` recursor premise. -/
theorem errHalts_of_interpRunAbruptPath {p : Program} {c : Config}
    (hpath : InterpRunAbruptPath p c) : TopAbrupt p → ErrHalts c := by
  rintro ⟨st', status, habrupt, hseq⟩
  exact hpath st' status habrupt hseq

end Vsa.Sim
