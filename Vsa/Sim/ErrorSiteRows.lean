import Vsa.Sim.ErrorSites
import Vsa.Sim.ErrorSimFull
import Vsa.Sim.DeriveCase
import Vsa.Sim.Code.Eval_expr

/-!
# `ErrorSiteRows` — Wave-D error-site rows (PILOT)

Each `errorSimFull` minor premise (`Vsa/Sim/ErrorSimFull.lean`, the 42
per-error-site residuals `hVarUndef`/…/`hSeqTail`) has the shape "this error
node's compiled path reaches a `jal runtime_error` (0x80002da8) ⇒ `ErrHalts c`"
(`ErrHalts c := ∃ out, Halts c out 70`).  This file discharges a PILOT set of
those residuals through the **committed** L6 combinator `errHalts_exists_of_site`
(`Vsa/Sim/ErrorSites.lean`), validating the full error-row pipeline so the
remaining ~37 sites are a mechanical fan-out.

## The per-site recipe (the one this file establishes)

For an error node whose dispatch reaches its `jal runtime_error` at pc `J`:

1. **decode** the `(pc, word)` path from the node's dispatch entry up to (but not
   including) the `jal runtime_error` — reading the bytes from
   `experiments/disasm.txt` (see the census below);
2. **`#derive_case <site>_row chain […]`** for that straight-line body — the L3
   elaborator emits the plain-term `<site>_row_seg` run theorem in `SegEvalState`
   normal form (computed regs via `evalBlocks`, canonical `writeLog`, computed
   end PC), conditional only on the mechanical `ChainFacts`/`ChainOK`
   byte-pin+decode residuals;
3. **`marshal`/`geom`** the `<site>_row_seg` conclusion (at the `jal` pc, `x10`
   still the dispatch's `a0`, memory the canonical store log) plus one hand
   `stepObs_jal` step into `Triple SitePre (RuntimeErrorAt g inp m0)` — pinning
   `x10 = inp`, `mem = m0`, and the `g` frame at the runtime_error entry
   0x80002da8 (the segment→`RuntimeErrorAt` marshalling that `ErrorSites.lean`'s
   header flags as per-row work: `GHolds`→`x10` via `gholds_lookup`, memory via
   the store-window `FrameCalc`, the `g` frame via the block frame clause);
4. **`errHalts_exists_of_site … SC out HT T c hsite`** → the `ErrHalts c`
   residual, parametric on the shared `SC : SnprintfContract …` and
   `HT : ErrorTailChain 0x80004428 ExitStorePreExit out` (L7/L8 supplies those
   ONCE, shared by all 42 rows).

## What is discharged here vs. what stays a row hypothesis

The L6 combinator + the composition into the exact `errorSimFull` minor-premise
shape is discharged **green** (this file's `errRow`).  Its per-row inputs are:

* the shared `SC`/`HT` (L7/L8 — the SAME two hypotheses for every one of the 42
  rows);
* the site's marshalled segment `Triple SitePre (RuntimeErrorAt g inp m0)` — the
  `#derive_case`+`stepObs_jal`+`marshal` bundle of steps 1–3, per-row but
  mechanical, and explicitly declared per-row work by `ErrorSites.lean`;
* the reachability link `hsite : SitePre c` — that the fixed interpreter config
  `c` is parked at this error node's dispatch entry (the M4-side caller linkage;
  the term-sim assembly provides the analogous per-case entry facts).

`errRow` shows all three compose to exactly `ErrHalts c`, i.e. the minor-premise
conclusion `errorSimFull` demands, with NO extra glue.  Three concrete leaf
sites (`hNotCallable`, `hNegType`, `hAssertFail`) are instantiated below to show
the fan-out is one `errRow` application per site.

A real `#derive_case` segment is emitted (`erow_demo_seg`, a pure stack-spill
body from a real eval_expr `jal runtime_error` predecessor block) to exercise the
L3 elaborator on an actual error-site path and pin the recipe's step 2.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.

Timing witness (2026-08-26): `lake env lean Vsa/Sim/ErrorSiteRows.lean` — see the
commit gate.  The combinator adds no reflection of its own; the only reflective
cost is the emitted `#derive_case` segment's ONE `ChainOK` `decide` (small,
constant per row — rule 7).
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps Halts)
open Vsa.Logic (Triple)
open Vsa.While

namespace Vsa.Sim

/-- The WHILE spec state (`Vsa.While.St`), qualified to avoid the clash with the
`Vsa.Sim.St` register-bundle structure (from `Muldi3Spec`) in scope. -/
local notation "SpecSt" => Vsa.While.St

/-! ## §1. A real `#derive_case` segment from an eval_expr error-site path

The predecessor block of the `jal runtime_error` at `0x800034e4` (an eval_expr
type-error node) is the pure stack-spill

```
800034d0:  sd s3,1048(sp)
800034d4:  sd s4,1040(sp)
800034d8:  sd s5,1032(sp)
800034dc:  sd s6,1024(sp)
800034e0:  sd s7,1016(sp)     ── fall-through into  jal runtime_error @0x800034e4
```

`a0` (= the `struct ErrorIn` pointer that becomes `x10 = inp` at the
runtime_error entry) is already pinned on entry to this block (set earlier in the
node's dispatch), so the body is auipc-free and every instruction is a SegEval
`sd` (kind `.sd`).  `#derive_case` emits `erow_demo`/`erow_demo_seg` — the L3 run
theorem for this exact path, in `SegEvalState` normal form.  This pins step 2 of
the recipe on a genuine error-site body. -/

#derive_case erow_demo chain
  [(0x800034d0#64, 0x41313c23#32),   -- sd s3,1048(sp)
   (0x800034d4#64, 0x41413823#32),   -- sd s4,1040(sp)
   (0x800034d8#64, 0x41513423#32),   -- sd s5,1032(sp)
   (0x800034dc#64, 0x41613023#32),   -- sd s6,1024(sp)
   (0x800034e0#64, 0x3f713c23#32)]   -- sd s7,1016(sp)

#print axioms erow_demo_seg

/-! ## §2. The row template — `errRow`

`errRow` is the ONE lemma every Wave-D error row composes with: it takes the
site's marshalled segment `Triple SitePre (RuntimeErrorAt g inp m0)` (steps 1–3
of the recipe), the shared `SC`/`HT`, and the reachability link `hsite`, and
produces exactly the `errorSimFull` minor-premise conclusion `ErrHalts c`.  It is
a thin wrapper over the committed `errHalts_exists_of_site` (`ErrorSites.lean`)
whose only job is to expose the `ErrHalts` shape and thread `hsite`. -/

/-- **One error site, discharged into its `errorSimFull` residual.**  Given the
site's marshalled segment `Triple` into the runtime_error entry, the shared
`SnprintfContract`/`ErrorTailChain`, and the reachability link `hsite : SitePre
c`, the config `c` reaches `ErrHalts c` — precisely the shape each `errorSimFull`
minor premise demands. -/
theorem errRow (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ErrHalts c :=
  errHalts_exists_of_site g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v
    s11v spv m0 SC out HT T c hsite

#print axioms errRow

/-! ## §3. The pilot rows — three leaf error nodes

Each row discharges one `errorSimFull` minor premise (the exact `∀ …, → ErrHalts
c` shape from `Vsa/Sim/ErrorSimFull.lean`) by ONE `errRow` application.  The
site's segment `Triple` (`T`) and the reachability link (`hsite`) are the per-row
inputs (steps 1–3 + the caller linkage); `SC`/`HT`/`out` are the shared L7/L8
facts.  These three are `CallErr.notCallable`, `EvalErr.negType`, and
`CallErr.assertFail` — the simplest leaf nodes (no sub-derivation IH), whose
dispatch reaches a `jal runtime_error` directly.

The fan-out to the remaining ~37 sites is: state the minor premise's `∀`-closure,
`intro`, and apply `errRow` with the site's own `T`/`hsite`.  Nothing else
changes — the body is literally `errRow g inp … SC out HT T c hsite`. -/

section Rows

/-- Row for `CallErr.notCallable` (`hNotCallable`): calling a non-callable value
reaches its `jal runtime_error` node. -/
theorem row_hNotCallable
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c :=
  fun _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `EvalErr.negType` (`hNegType`): negating a non-int value reaches its
`jal runtime_error` node. -/
theorem row_hNegType
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

/-- Row for `CallErr.assertFail` (`hAssertFail`): a failed `assert(...)` reaches
its `jal runtime_error` node. -/
theorem row_hAssertFail
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c :=
  fun _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT T c hsite

end Rows

#print axioms row_hNotCallable
#print axioms row_hNegType
#print axioms row_hAssertFail

end Vsa.Sim
