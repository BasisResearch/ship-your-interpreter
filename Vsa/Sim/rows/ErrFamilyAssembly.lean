import Vsa.Sim.rows.ErrorRouting
import Vsa.Sim.IndexedErrorPrototype
import Vsa.Sim.ExitPathSpans
import Vsa.Sim.ExitPathSeg

/-!
# `ErrFamilyAssembly` — shared error tail + faithful leaf routes

Two pieces:

**1. `ErrSharedInputs` → `ErrShared`.**  The shared L7/L8 bundle `ErrShared`
(`rows/ErrorRouting.lean`) demands the `SnprintfContract SC` (M3) and the
`ErrorTailChain HT` (M6 exit tail).  The exit tail is DECOMPOSED
(`ExitPath.errorTailChain_of_segments`) into four segment `Triple`s, of which TWO
are landed conditional on named frame geometry (`interpContSeg_of` /
`exitPrologSeg`) and TWO are open decode spans (`MainErrorSeg`/`Crt0ExitSeg`).
`ErrSharedInputs` names EXACTLY the honest remaining inputs — the snprintf
contract, the two open segments, the two landed-segment geometry residuals, and
the entry-output pinning — and `ErrSharedInputs.toShared` builds the `ErrShared`
bundle once, at the concrete continuation `ra0 = 0x80004428`.

**2. `ErrWork`.** Only executable leaves carry machine reachability. Propagation
constructors reuse their child `ErrHalts` induction hypotheses, and binary
failures use the cause-indexed `BinaryErrReach`. `hBadClosure` remains a
specification adequacy obligation; top-level abrupt execution has its own
direct `interp_run` path.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps output)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr (NativeAddrs Arena)
open Vsa.Alloc (StackLayout)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## 1. `ErrShared` from its honest inputs -/

/-- **The honest remaining inputs of the shared error bundle.**  Every field is a
named residual; the landed layers (`runtime_error_spec`, `longjmp_spec`,
`errorTailChain_of_segments`, `interpContSeg_of`, `exitPrologSeg`,
`exitStoreHalts`) consume them without further hypotheses. -/
structure ErrSharedInputs where
  /-- The entry ghost frame of the `runtime_error` transfer. -/
  g : (R : Register) → Option (RegisterType R)
  /-- The `Interp*` pointer (`a0` at `runtime_error` entry). -/
  inp : BitVec 64
  /-- setjmp-time `s0`..`s11` buffer contents. -/
  s0v : BitVec 64
  s1v : BitVec 64
  s2v : BitVec 64
  s3v : BitVec 64
  s4v : BitVec 64
  s5v : BitVec 64
  s6v : BitVec 64
  s7v : BitVec 64
  s8v : BitVec 64
  s9v : BitVec 64
  s10v : BitVec 64
  s11v : BitVec 64
  /-- setjmp-time `sp` buffer content. -/
  spv : BitVec 64
  /-- The entry memory at `runtime_error`. -/
  m0 : Std.ExtHashMap Nat (BitVec 8)
  /-- The console output the error path reports. -/
  out : String
  /-- **OPEN (M3)** — the pre-`longjmp` snprintf contract at the concrete
  interp_run setjmp-continuation `ra0 = 0x80004428` (`Vsa/Sim/JmpSpec.lean`;
  supplier: the landed snprintf `%lld`/`%s` machinery routed through
  `runtime_error`'s two calls). -/
  SC : SnprintfContract g inp (0x80004428#64 : BitVec 64)
    s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
  /-- The entry-output pinning: the accumulated console output at the
  setjmp-continuation is `out` (`ExitPath.ChainPre`). -/
  hEntryOut : ∀ c, ChainPre c → output c.σ = out
  /-- The interp_run-continuation spill-frame geometry (`ExitPathSpans`);
  feeds the LANDED `interpContSeg_of`. -/
  frameIC : InterpContFrame out
  /-- **OPEN (M6 decode)** — main's error-path span `0x800045ec → 0x80000038`
  (through `fprintf(stderr,…)`, output-neutral). -/
  segMain : MainErrorSeg out
  /-- **OPEN (M6 decode)** — the crt0 `j exit` → `_exit` entry span
  `0x80000038 → 0x80000180` (through `__call_exitprocs`, output-neutral). -/
  segCrt0 : Crt0ExitSeg out
  /-- The `_exit`-prologue geometry (`_exit` code loaded +
  `htif_payload_writes = 0`); feeds the LANDED `exitPrologSeg`. -/
  geomEP : ExitPrologGeom out

/-- **`ErrShared` instantiated once** from its honest inputs: the exit tail is
assembled by `errorTailChain_of_segments` over the two landed segments (fed
their geometry residuals) and the two open ones, at `ra0 = 0x80004428`. -/
def ErrSharedInputs.toShared (I : ErrSharedInputs) : ErrShared where
  g := I.g
  inp := I.inp
  ra0 := (0x80004428#64 : BitVec 64)
  s0v := I.s0v
  s1v := I.s1v
  s2v := I.s2v
  s3v := I.s3v
  s4v := I.s4v
  s5v := I.s5v
  s6v := I.s6v
  s7v := I.s7v
  s8v := I.s8v
  s9v := I.s9v
  s10v := I.s10v
  s11v := I.s11v
  spv := I.spv
  m0 := I.m0
  SC := I.SC
  out := I.out
  HT := errorTailChain_of_segments I.out I.hEntryOut
    (interpContSeg_of I.out I.frameIC) I.segMain I.segCrt0
    (exitPrologSeg I.out I.geomEP)

/-! ## 2. The faithful leaf-only error work

Only executable leaf constructors need machine reachability.  Propagation
constructors reuse their recursive `ErrHalts` result inside `errFamilyClosed`.
The binary leaf is cause-indexed by `BinaryErrReach`; top-level abrupt
completion has its own direct `interp_run` path. -/

/- The complete remaining error-side work. -/
/- Obsolete constant-config work bundle.
structure ErrWork where
  /-- Shared `runtime_error` and exit-tail inputs. -/
  I : ErrSharedInputs
  /-- The ten named executable leaves plus cause-indexed binary failures. -/
  leaves : ErrLeafLinks I.toShared
  /-- A dangling closure is impossible for a store created by the executable;
  it remains a specification-side adequacy obligation. -/
  hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
    (vs : List Value), st.store.closures[a]? = none → ErrHalts c
  /-- Direct `interp_run` handling of top-level abrupt status; no error-site
  `jal` occurs on this path. -/
  hTopAbrupt : ∀ (p : Program) (c : Config), InterpRunAbruptPath p c

/-- Assemble the error family from exactly the faithful residual surface. -/
theorem errFamily_ofWork (Ly : Vsa.Refine.Layout) (W : ErrWork) :
    Vsa.Sim.InterpSimBundle.ErrFamily Ly :=
  errFamilyClosed_ofLinks Ly W.I.toShared W.leaves W.hBadClosure W.hTopAbrupt
-/

/-- Indexed error work for one actual loaded program/config pair.  The
`hCallTooMany` field of `cases` is fixed to the compiled child seam. -/
structure IndexedErrProgramInputs (p : Program) (c : Config) : Type where
  I : ErrSharedInputs
  hEval : ∀ st d env e st' v, EvalE st d env e st' v →
    EvalIH st d env e st' v
  hCallee : ∀ st d env f args
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64),
    CallCalleeStage I.toShared.g N A SL φf φc st d env f args
      sp r sret aEnv aExpr I.toShared.m0
  hGuard : ∀ st st' d env callNode f args fv,
    CallTooManyStage I.toShared st st' d env callNode f args fv
  cases : ErrorCasesI I.toShared.g I.toShared.m0
    (callTooManyCase_indexed I.toShared hEval hCallee hGuard)
  entry : ErrorProgramEntry I.toShared.g I.toShared.m0 p c
  topAbrupt : TopAbrupt p → ErrHalts c

def IndexedErrProgramInputs.toWork {p : Program} {c : Config}
    (W : IndexedErrProgramInputs p c) : ErrorProgramWork p c where
  g := W.I.toShared.g
  m0 := W.I.toShared.m0
  hCallTooMany := callTooManyCase_indexed W.I.toShared W.hEval W.hCallee W.hGuard
  cases := W.cases
  entry := W.entry
  topAbrupt := W.topAbrupt

/-- The complete indexed error work, selected after `Loaded` fixes the actual
program and machine entry. -/
structure ErrWork (L : Vsa.Refine.Layout) : Type where
  program : ∀ (p : Program) (c : Config), Vsa.Refine.Loaded L p c →
    IndexedErrProgramInputs p c

/-- Assemble the unchanged public error family from indexed work. -/
theorem errFamily_ofWork (L : Vsa.Refine.Layout) (W : ErrWork L) :
    Vsa.Sim.InterpSimBundle.ErrFamily L :=
  Vsa.Sim.InterpSimBundle.errFamily_of_sites L
    (fun p c hLoaded => (W.program p c hLoaded).toWork)

#print axioms ErrSharedInputs.toShared
#print axioms errFamily_ofWork

end Vsa.Sim
