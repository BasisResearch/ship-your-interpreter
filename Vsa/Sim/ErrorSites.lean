import Vsa.Sim.ExitPath
import Vsa.Sim.SegEvalSound

/-!
# `ErrorSites` — the per-error-site discharge combinator (L6)

`errorSim_of_sites` (`ErrorSimFull`) takes 42 per-error-site residuals, each of
the form "reaching this error node's compiled code reaches a `jal runtime_error`
site ⇒ `∃ out, Halts c out 70`". Every one of those proofs has the SAME tail:

1. a machine segment (straight-line + resolved branches) from the site entry to
   the site's `jal runtime_error` instruction — a `#derive_case` chain +
   `name_seg` row (L1/L3);
2. ONE `stepObs_jal` step to `runtime_error`'s entry `0x80002da8` (each site's
   own `(pc, word)` data, but the SAME step lemma);
3. `errorTailHalts_exit` — the runtime_error → longjmp → exit(70) chain
   (already discharged, conditional on the `SnprintfContract SC` and the
   `ErrorTailChain HT` M6 facts).

This file packages steps 2–3 ONCE:

* `RuntimeErrorAt g inp m0 c` — the runtime_error-entry facts, i.e. exactly
  `errorTailHalts_exit`'s `hre` precondition bundle (loaded images, PC/x10
  pins, the `g` ghost frame, tick budget);
* `errHalts_of_reach` — `RuntimeErrorAt` + `SC` + `HT` ⇒ `Halts c out 70`
  (the repackaged capstone);
* `errHalts_of_site` — the row shape: a `Triple SitePre (RuntimeErrorAt …)`
  (the site segment INCLUDING its `jal`, already marshalled) ⇒
  `∃ out', Halts c out' 70` for every `SitePre`-entry config — one
  application per Wave-D error row, with `out` threaded through `HT`.

The per-site marshalling from a bare `name_seg` conclusion (which lands at the
`jal`'s own pc with computed regs/log) to `RuntimeErrorAt` (which pins
`x10 = inp`, the `g` frame, `mem = m0`) stays per-row work — it is where the
site's entry ghosts meet the computed outcome — but it consumes only
projections (`writeLog` survival via `BlockAdapter`, `gholds_lookup`,
`FrameCalc.pin8`) per the spine rules.

Timing witness (2026-08-26): see the build gate on this file's commit; the
combinator adds no reflection of its own.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps Halts)
open Vsa.Logic (Triple)
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)

namespace Vsa.Sim

/-! ## The runtime_error-entry bundle -/

/-- The runtime_error-entry facts — `errorTailHalts_exit`'s `hre`, packaged as
one predicate so an error-site row states its post once. `inp` is the
`struct ErrorIn` pointer in `a0`; `m0` the entry memory. -/
def RuntimeErrorAt (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
    c.σ.mem = m0 ∧
    c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
    c.σ.regs.get? Register.x10 = some inp ∧
    WinRAM (inp + 16#64) ∧
    (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
    (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- Unpack `RuntimeErrorAt` into `errorTailHalts_exit`'s `hre` shape. -/
theorem runtimeErrorAt_iff (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) :
    RuntimeErrorAt g inp m0 c ↔
      GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
      c.σ.mem = m0 ∧
      c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
      c.σ.regs.get? Register.x10 = some inp ∧
      WinRAM (inp + 16#64) ∧
      (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
      (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R) := Iff.rfl

/-! ## The reachability capstone -/

/-- From a config AT the runtime_error entry (packaged by `RuntimeErrorAt`),
the machine halts with code `70` printing the error message `out` — the
`errorTailHalts_exit` capstone, conditional only on the M6-side `SC`/`HT`
facts (supplied once at assembly time by L7/L8, shared by all 42 rows). -/
theorem errHalts_of_reach (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    (c : Config) (h : RuntimeErrorAt g inp m0 c) :
    Halts c out 70 :=
  errorTailHalts_exit g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    spv m0 SC out HT c h

/-! ## The site combinator — the Wave-D error-row shape -/

/-- **One error site, discharged.** Given a `Triple` from the site's entry
predicate `SitePre` (the site segment including its `jal runtime_error`,
already marshalled) to the runtime_error entry (`RuntimeErrorAt`), every
`SitePre` config halts with code `70` printing the `out` determined by `HT`.
This is the ONE lemma every `#derive_case` error row composes with; `ErrHalts`
is the `∃`-wrapper of it. -/
theorem errHalts_of_site (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    Halts c out 70 := by
  obtain ⟨c', hsteps, hreach⟩ := T c hsite
  obtain ⟨c'', σf, hsteps', hhalted, hout⟩ :=
    errHalts_of_reach g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
      spv m0 SC out HT c' hreach
  exact halts_of_steps_halted (hsteps.trans hsteps') hhalted hout

/-- The `ErrHalts c` (`∃ out, Halts c out 70`) form of `errHalts_of_site` —
the exact conclusion the `errorSim_of_sites` minor premises demand. -/
theorem errHalts_exists_of_site (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    ∃ out', Halts c out' 70 :=
  ⟨out, errHalts_of_site g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v
    s11v spv m0 SC out HT T c hsite⟩

/-! ## Sanity — the combinator composes -/

section Sanity

variable (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
  (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
  (m0 : Std.ExtHashMap Nat (BitVec 8))
  (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
  (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)

example {SitePre : Config → Prop}
    (T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c'))
    (c : Config) (hsite : SitePre c) :
    Halts c out 70 :=
  errHalts_of_site g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    spv m0 SC out HT T c hsite

end Sanity

#print axioms errHalts_of_site
#print axioms errHalts_exists_of_site

end Vsa.Sim
