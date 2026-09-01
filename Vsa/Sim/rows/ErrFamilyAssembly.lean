import Vsa.Sim.rows.ErrArmLinks
import Vsa.Sim.rows.ErrArmLinksB
import Vsa.Sim.ExitPathSpans
import Vsa.Sim.ExitPathSeg

/-!
# `ErrFamilyAssembly` — `ErrShared` instantiated + the 42 links fed to the family

Task #54 (wave 39).  Two pieces:

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

**2. `errFamily_ofArmLinks`.**  The 42 routed `hsite` residuals of
`errFamily_of_sites` are ALL discharged by the GENERATED link families
(`errLinkA_*` — 16 spill-arm premises, `errLinkB_*` — 26 setup-arm premises);
the two non-`jal` passthroughs (`hBadClosure`/`hTopAbrupt`) remain raw.  This
theorem performs the 44-slot feed once, so the error family's remaining work is
`ErrShared` (via `ErrSharedInputs`) + the two collectors' arm-linkage fields +
the 2 passthroughs — bundled as `ErrWork`, consumed by `Vsa/Sim/EndToEnd.lean`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps output)
open Vsa.Logic (Triple)
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

/-! ## 2. The 42 links fed to `errFamily_of_sites` -/

/-- **The error family from the two GENERATED link collectors.**  All 42 routed
`hsite` slots of `errFamily_of_sites` are discharged by `errLinkA_*` (16
spill-arm premises) / `errLinkB_*` (26 setup-arm premises); only the two
non-`jal` passthroughs remain raw.  The error-side remaining work is therefore
exactly: `S` (via `ErrSharedInputs`), the collectors' arm-linkage fields, and
the 2 passthroughs. -/
theorem errFamily_ofArmLinks (Ly : Vsa.Refine.Layout) (S : ErrShared)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (Lr : GRegs) (lds : List (List (BitVec 8)))
    (A : ErrArmLinks S m0 Lr lds) (B : ErrArmLinksB S m0 Lr lds)
    (hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Vsa.While.Addr)
      (vs : List Vsa.While.Value), st.store.closures[a]? = none → ErrHalts c)
    (hTopAbrupt : ∀ (p : Vsa.While.Program) (c : Config),
      Vsa.While.TopAbrupt p → ErrHalts c) :
    Vsa.Sim.InterpSimBundle.ErrFamily Ly :=
  Vsa.Sim.InterpSimBundle.errFamily_of_sites Ly
    (errLinkA_hVarUndef S m0 Lr lds A)
    (errLinkB_hAssignE S m0 Lr lds B)
    (errLinkA_hAssignUnbound S m0 Lr lds A)
    (errLinkB_hBinaryL S m0 Lr lds B)
    (errLinkB_hBinaryR S m0 Lr lds B)
    (errLinkB_hBinaryOp S m0 Lr lds B)
    (errLinkA_hOrL S m0 Lr lds A)
    (errLinkA_hOrR S m0 Lr lds A)
    (errLinkB_hAndL S m0 Lr lds B)
    (errLinkB_hAndR S m0 Lr lds B)
    (errLinkA_hUnaryE S m0 Lr lds A)
    (errLinkA_hNegType S m0 Lr lds A)
    (errLinkB_hCallF S m0 Lr lds B)
    (errLinkB_hCallArgs S m0 Lr lds B)
    (errLinkB_hCallC S m0 Lr lds B)
    (errLinkA_hArgsHead S m0 Lr lds A)
    (errLinkA_hArgsTail S m0 Lr lds A)
    (errLinkB_hNotCallable S m0 Lr lds B)
    hBadClosure
    (errLinkB_hArity S m0 Lr lds B)
    (errLinkB_hDepth S m0 Lr lds B)
    (errLinkB_hBody S m0 Lr lds B)
    (errLinkB_hEscape S m0 Lr lds B)
    (errLinkB_hAssertFail S m0 Lr lds B)
    (errLinkB_hAssertArity S m0 Lr lds B)
    (errLinkA_hExpr S m0 Lr lds A)
    (errLinkB_hVarInit S m0 Lr lds B)
    (errLinkA_hBlock S m0 Lr lds A)
    (errLinkB_hIfCond S m0 Lr lds B)
    (errLinkB_hIfThen S m0 Lr lds B)
    (errLinkB_hIfElse S m0 Lr lds B)
    (errLinkA_hWhileCond S m0 Lr lds A)
    (errLinkA_hWhileBody S m0 Lr lds A)
    (errLinkB_hWhileLoop S m0 Lr lds B)
    (errLinkB_hForInit S m0 Lr lds B)
    (errLinkA_hForLoop S m0 Lr lds A)
    (errLinkA_hRet S m0 Lr lds A)
    (errLinkB_hFlCond S m0 Lr lds B)
    (errLinkB_hFlBody S m0 Lr lds B)
    (errLinkB_hFlStep S m0 Lr lds B)
    (errLinkA_hFlLoop S m0 Lr lds A)
    (errLinkA_hSeqHead S m0 Lr lds A)
    (errLinkB_hSeqTail S m0 Lr lds B)
    hTopAbrupt

/-! ## 3. `ErrWork` — the whole error-side residual, one named record -/

/-- **The error-side remaining work.**  Named fields only: the shared-bundle
inputs `I`, the spill-seg reflection parameters `m0A`/`Lr`/`lds`, the two
GENERATED arm-linkage collectors (whose fields are the per-premise M4
`SpillArmPre`/`SetupArmPre` reachability residuals), and the two non-`jal`
passthroughs. -/
structure ErrWork where
  /-- The shared-bundle inputs (`SnprintfContract` + exit-tail segments). -/
  I : ErrSharedInputs
  /-- The spill/setup seg reflection memory. -/
  m0A : Std.ExtHashMap Nat (BitVec 8)
  /-- The spill/setup seg register pin list. -/
  Lr : GRegs
  /-- The spill/setup seg load byte-lists. -/
  lds : List (List (BitVec 8))
  /-- **OPEN (M4)** — the 16 Family-A (spill-arm) arm-linkage residuals. -/
  A : ErrArmLinks I.toShared m0A Lr lds
  /-- **OPEN (M4)** — the 26 Family-B (setup-arm) arm-linkage residuals. -/
  B : ErrArmLinksB I.toShared m0A Lr lds
  /-- **OPEN** — the 43rd site: dangling closure address (no `jal` site decoded;
  `CallErr.badClosure`). -/
  hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Vsa.While.Addr)
    (vs : List Vsa.While.Value), st.store.closures[a]? = none → ErrHalts c
  /-- **OPEN** — the top-level abrupt route (`TopAbrupt p` → exit 70). -/
  hTopAbrupt : ∀ (p : Vsa.While.Program) (c : Config),
    Vsa.While.TopAbrupt p → ErrHalts c

/-- The error family from the one `ErrWork` record. -/
theorem errFamily_ofWork (Ly : Vsa.Refine.Layout) (W : ErrWork) :
    Vsa.Sim.InterpSimBundle.ErrFamily Ly :=
  errFamily_ofArmLinks Ly W.I.toShared W.m0A W.Lr W.lds W.A W.B
    W.hBadClosure W.hTopAbrupt

#print axioms ErrSharedInputs.toShared
#print axioms errFamily_ofArmLinks
#print axioms errFamily_ofWork

end Vsa.Sim
