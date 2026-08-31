import Vsa.Sim.JmpSpec
import Vsa.While.ErrorSem
import Vsa.Refinement

/-!
# Layer 5 — the error forward-simulation: `BigStepErr p → ∃ out, Halts c out 70`

This is the error half of `stuck_sim` (`Vsa/Refinement.lean`), the analog of M4's
`term_sim`.  It has two parts, both assembled here:

**Part A — `errorTailHalts` (the runtime_error → exit(70) chain).**  From a machine
configuration parked at a `jal runtime_error` site (interp_run/main frames set up,
`GoodState`, the setjmp cell populated), the machine transfers control all the way
to a clean HTIF halt with exit code `70`.  The decoded path (see
`memory/m5-stuck-sim.md`):

```
runtime_error @0x80002da8  ──runtime_error_spec──▶  interp_run setjmp-cont 0x80004428, a0=1
  ──bnez a0──▶ 0x80004508 (li s5,1; epilogue; ret a0=1)
  ──main bnez a0──▶ 0x80004600 (fprintf; li a0,70; ret)
  ──crt0 j exit──▶ _exit 0x80000180 (slli/srli/ori = (70<<<1)|1; sd a5,tohost)
  ──htif_store_exit──▶ Halted _ 70
```

`errorTailHalts` performs the reusable *composition*: it runs `runtime_error_spec`
(the big reusable transfer piece) to `0x80004428`, threads the interp_run-cont /
main / crt0 / exit spans as a single **`ErrorTailChain`** `Triple` residual (control
`0x80004428 → exit-store site`, a decode battery to be discharged), then applies the
**`ExitStoreHalts`** bridge (the exit `sd a5,tohost` → `htif_store_exit` →
`Halted _ 70` machine step — the one genuine plumbing residual) and assembles a
`Halts c out 70`.  The two big pieces it reuses by name are `runtime_error_spec`
(`Vsa/Sim/JmpSpec.lean`) and `htif_store_exit` (`Vsa/Sim/Htif.lean`, reached through
`ExitStoreHalts`).

**Part B — `errorSim` (the error forward-simulation skeleton).**  A mutual recursion
over `EvalErr`/`ExecErr`/… (mirroring `TermSimAssembly.term_sim_of_cases`'s
`@EvalE.rec` structure) whose per-constructor motive is "the compiled code reaches a
`jal runtime_error` site" — taken as per-error-site residual hypotheses, exactly as
`term_sim_of_cases` takes the case Triples.  Composed with `errorTailHalts` and
discharged into `stuck_sim`'s second disjunct via `stuck_of_halts_70`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.While
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The WHILE spec state (`Vsa.While.St`), qualified to avoid the clash with the
`Vsa.Sim.St` register-bundle structure in scope from `Muldi3Spec`. -/
local notation "SpecSt" => Vsa.While.St

/-! ## Part A — the runtime_error → exit(70) chain

### A `Halts` introduction helper

`Halts c out e` unfolds to `∃ c' σf, Steps c c' ∧ Halted c' e σf ∧ output σf = out`.
Building it from a `Steps` prefix reaching a config that halts is pure `Steps`
plumbing; we package it once so the chain assembly is a one-liner. -/

/-- Prepend a finite run to a halt: if the machine `Steps` from `c` to `c'` and `c'`
halts with code `e` printing `out`, then `c` halts with code `e` printing `out`. -/
theorem halts_of_steps_halted {c c' : Config} {σf : MState} {out : String} {e : Nat}
    (hs : Steps c c') (hh : Halted c' e σf) (ho : output σf = out) :
    Halts c out e :=
  ⟨c', σf, hs, hh, ho⟩

/-! ### The exit-store site predicate and the two residuals

`ExitStorePre` abstracts the configuration at the `_exit` HTIF store `sd a5,tohost`
(`0x80000180`), after `crt0` has driven `a0 = 70` into `_exit` and the
`slli/srli/ori` have formed the syscall-exit word `(70<<<1)|1` in `a5`.  We keep it
opaque: the two residuals below say exactly what the chain needs of it, and a future
decode pass will instantiate it with the concrete PC/register facts. -/

/-- **The interp_run-cont / main / crt0 / exit span**, as a `Triple` residual.  From
the `runtime_error_spec` postcondition state (`PC = ra0 = 0x80004428`, `a0 = 1`,
`GoodState`, tick invariant), the machine runs (finitely) to a configuration
satisfying `ExitStorePre out` — the `_exit` store site, with the console output
accumulated so far equal to `out`.  Discharged by decoding the interp_run-cont
(0x80004428→0x80004514 ret), main (0x800045e8→0x80004600 li a0,70; ret), crt0
(j exit) and `_exit` prologue (0x80000180 slli/srli/ori) spans. -/
structure ErrorTailChain (ra0 : BitVec 64) (ExitStorePre : String → Config → Prop)
    (out : String) : Prop where
  chain :
    Triple
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra0 ∧
        c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64))
      (ExitStorePre out)

/-- **The exit-store → halt bridge**, as a residual.  From an `ExitStorePre out`
configuration (`_exit`'s `sd a5,tohost` with `a5 = (70<<<1)|1`), the machine takes
one architectural `Step` whose post-state, on the *next* `stepOnce`, signals HTIF
exit with code `70` (via `htif_store_exit`, reached through `mem_write_value_tohost_exit`) —
packaged as a reached `Halted _ 70 σf` with `output σf = out`.  This is the one
genuine machine-plumbing obligation of Part A (the exit-store instruction step +
the `htif_done`-after-`try_step` check of `stepOnce`, `Vsa/Elf.lean:80`). -/
def ExitStoreHalts (ExitStorePre : String → Config → Prop) (out : String) : Prop :=
  ∀ c, ExitStorePre out c → ∃ c' σf, Steps c c' ∧ Halted c' 70 σf ∧ output σf = out

/-! ### `errorTailHalts` — the assembled chain

The reusable runtime_error→halt-70 composition.  Conditional on: the
`runtime_error_spec` frame geometry (its precondition, taken as a hypothesis `hre`),
the `SnprintfContract` `SC`, the `ErrorTailChain` span `HT`, and the `ExitStoreHalts`
bridge `HX`. -/

/-- **Part A capstone.**  From a config at the `jal runtime_error` entry
(`runtime_error_spec`'s precondition `hre`), threading `runtime_error_spec` (→ the
interp_run setjmp-continuation `ra0`, `a0 = 1`), the interp_run-cont/main/crt0/exit
span (`HT`), and the exit-store→halt bridge (`HX`), the machine halts with exit code
`70` printing `out`: `Halts c out 70`. -/
theorem errorTailHalts
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (ExitStorePre : String → Config → Prop) (out : String)
    (HT : ErrorTailChain ra0 ExitStorePre out)
    (HX : ExitStoreHalts ExitStorePre out)
    (c : Config)
    (hre : GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
      c.σ.mem = m0 ∧
      c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
      c.σ.regs.get? Register.x10 = some inp ∧
      WinRAM (inp + 16#64) ∧
      (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
      (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)) :
    Halts c out 70 := by
  -- 1. runtime_error → longjmp → interp_run setjmp-continuation `ra0`, with `a0 = 1`.
  obtain ⟨c1, hs1, hq1⟩ :=
    runtime_error_spec g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0 SC c hre
  obtain ⟨hG1, htick1, hpc1, _hx1, _hx8, _hx9, _hx18, _hx19, _hx20, _hx21, _hx22, _hx23,
    _hx24, _hx25, _hx26, _hx27, _hx2, hx10, _hmi1, _hframe1⟩ := hq1
  -- normalize the materialized longjmp return value `a0` to the literal `1`.
  have hx10' : c1.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) := by
    rw [hx10]; decide
  -- 2. interp_run-cont / main / crt0 / exit span → the `_exit` store site.
  obtain ⟨c2, hs2, hpre2⟩ := HT.chain c1 ⟨hG1, htick1, hpc1, hx10'⟩
  -- 3. exit store → `htif_store_exit` → Halted _ 70.
  obtain ⟨c3, σf, hs3, hh3, ho3⟩ := HX c2 hpre2
  -- compose the three finite runs and assemble the halt.
  exact halts_of_steps_halted (hs1.trans (hs2.trans hs3)) hh3 ho3

/-! ## Part B — the error forward-simulation skeleton

The mutual recursion over the error judgment, mirroring
`TermSimAssembly.term_sim_of_cases`'s `@EvalE.rec` structure, but with error
motives.  Each error constructor's motive is "the compiled code, from the interp
entry, reaches a `jal runtime_error` site" — packaged as a `Triple` into a
`RuntimeErrorEntry` predicate (the `runtime_error_spec` precondition family).  These
per-error-site facts are taken as residual hypotheses, exactly as
`term_sim_of_cases` takes the per-case Triples.

Below is the skeleton for the `ExecSeqErr` relation (`BigStepErr = ExecSeqErr initSt
0 0 p`, `Vsa/While/ErrorSem.lean`): its two constructors (`head`: the first statement
errors; `tail`: the head runs normally and the tail errors) recursed with an
error-motive that concludes `∃ out, Halts c out 70`.  The full six-relation mutual
recursor (`@ExecSeqErr.rec` with `EvalErr`/`EvalArgsErr`/`CallErr`/`ExecErr`/
`ForLoopErr` co-motives) is the same assembly widened to all six error relations;
the `errorSim` entry composes it with `errorTailHalts`. -/

/-- The Part-B forward-simulation target: reaching a `runtime_error` site and thus,
by `errorTailHalts`, a `Halts _ 70`.  We phrase it directly as the conclusion
`∃ out, Halts c out 70` the `stuck_sim` disjunct consumes; the machine
configuration `c` is the fixed loaded interpreter config (the ghost of the
per-relation motive).  -/
def ErrHalts (c : Config) : Prop := ∃ out, Halts c out 70

/-- **Part B skeleton (`ExecSeqErr` relation).**  Given, for the fixed interpreter
config `c`, that either error case of an `ExecSeqErr`-node's compiled code reaches a
`runtime_error` site and hence a `Halts c out 70` — the `head` case (the first
statement errors, residual `hHead`) and the `tail` case (the head ran normally and
the tail errors, residual `hTail`) — the top-level program error reaches
`∃ out, Halts c out 70`.

This is the assembly for one error relation (`cases` on the two `ExecSeqErr`
constructors), mirroring `term_sim_of_cases`: it COMPOSES the per-constructor site
facts.  The `tail`-case recursion into the sub-`ExecSeqErr` (and the full six-relation
mutual recursor `@ExecSeqErr.rec`) is exposed as `hTail`'s `ExecSeqErr … → ErrHalts c`
residual, to be tied off by the same recursor assembly widened to all six error
relations; discharging each site (decode of each `jal runtime_error`) + composing with
`errorTailHalts` is the remaining forward-sim work. -/
theorem errorSim_execSeq (c : Config)
    (hHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c)
    (hTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c)
    {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt}
    (h : ExecSeqErr st d env ss) : ErrHalts c := by
  cases h with
  | head st d env s ss he => exact hHead st d env s ss he
  | tail st d env s ss st' hnorm herr => exact hTail st d env s ss st' hnorm herr

/-- **Part B entry (`BigStepErr`).**  Specializing `errorSim_execSeq` to the
top-level `ExecSeqErr initSt 0 0 p` yields the program-level error simulation.  The
two residuals are the whole-program instantiation of the per-`ExecSeqErr`-node
reachability facts.  Composed with `stuck_of_halts_70`, this discharges the
error disjunct of `stuck_sim`. -/
theorem errorSim (c : Config) (p : Program)
    (hHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c)
    (hTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c)
    -- Top-level abrupt route (the new `BigStepErr` disjunct `TopAbrupt p`,
    -- `interp_run` → exit 70); same exit-70 shape as the site residuals.
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) : ∃ out, Halts c out 70 := by
  rcases h with hseq | habrupt
  · exact errorSim_execSeq c hHead hTail hseq
  · exact hTopAbrupt habrupt

/-- **Discharging `stuck_sim`'s error disjunct.**  From the error simulation
(`∃ out, Halts c out 70`) and `stuck_of_halts_70` (`Vsa/While/ErrorSem.lean`), a
program that hits a runtime error lands in `stuck_sim`'s second disjunct. -/
theorem stuck_of_bigStepErr (c : Config) (p : Program)
    (hHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c)
    (hTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c)
    -- Top-level abrupt route (the new `BigStepErr` disjunct); see `errorSim`.
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  obtain ⟨out, hh⟩ := errorSim c p hHead hTail hTopAbrupt h
  exact stuck_of_halts_70 hh

end Vsa.Sim
