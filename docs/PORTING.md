# Porting the toolkit to another interpreter

This guide is for an interpreter binary (Lua, OCaml bytecode, …) that runs on
the same machine layer: `Vsa/Machine.lean` (Sail RV64D as `Step`, `Halts`,
`Diverges`), `Vsa/Densify`, and `VsaIris/` (`vsaModel`, `MachWP`, `SWP`,
adequacy). It lists what can be reused as is, what must be instantiated, and
which parameters are still hard-wired to `c/while-riscv-htif.elf`.

## 1. The refinement statement: `Vsa/Lang`, `VsaIris/Lang`

These modules import only the machine layer. You can import them unchanged.

| Declaration | Meaning |
| --- | --- |
| `Vsa.Lang.Lang` | `Prog`, `Spec p e out` (halts with exit `e`, printing `out`), `Obs e` (exit codes the spec observes; `spec_obs`), `Fits p` (fragment and budget) |
| `Lang.Sim L Loaded` | forward simulation: `term` (spec ⇒ `Halts`), `stuck` (no spec ⇒ `Diverges` or an unobservable halt) |
| `Lang.Sim.refinement` | `Loaded p c → Fits p → L.Refines p c`: `Spec p e out ↔ Halts c out e` for observable `e`, and divergence excludes every spec result |
| `Lang.Total`, `Lang.SimTotal`, `SimTotal.refinement` | languages with a divergence semantics `Div` and trichotomy. Forward `term` and `div` give `RefinesTotal` (halts exactly, and `Div p ↔ Diverges c`) |
| `Refines.of_fillZero`, `RefinesTotal.of_fillZero` | restate the conclusion when loading is stated on `Vsa.Densify.fillZero c` |
| `Vsa.Lang.ofOutput P S`, `OutSim`, `OutSim.refinement`, `OutSim.refinement_fillZero` | output-only languages (`e = 0` is the only observable code), with the classic `term_sim`/`stuck_sim` fields. WHILE's instance is `Vsa.Refine.InterpSim L := OutSim BigStep (Loaded L)` |
| `Vsa.Lang.SmallStep` | `init`, `Next`, `Final p s e out`. It supplies `StepsN`, `Reach`, `Halts`, `Diverges`, `Progress`, and `halts_or_diverges` |
| `SmallStep.toLang Fits hp` | the small-step language (every exit code observable, `hp : Fits p → Progress p`), with an instance of `Lang.Total` |
| `SmallStep.ArmSim Fits Loaded Repr p` | per-step obligations: `entry` (loaded ⇒ at least one machine step to `Repr p (init p)`), `next` (each `Next` is matched by at least one machine step), `halt` (each `Final` state halts the machine) |
| `ArmSim.simTotal` | `(∀ p, ArmSim …) → (toLang Fits hp).SimTotal Loaded` |
| `Vsa.Lang.{Plus, steps_trans, stepsN_append, stepsN_prefix, stepsN_toSteps, halts_of_steps}` | machine run algebra |
| `VsaIris.Lang.RouteAt GF L live p c` | Iris obligations at one configuration: resources `mr`/`mm` agreeing with `c` (`RegAgree`, `MemAgree`, `VsaOk`), a total counted WP (`AdequacyHyp`, `twpW`) to `(e, out)` for each spec result, and a partial WP (`AdequacyHypP`, `wpW`) to an unobservable exit when there is none |
| `VsaIris.Lang.IrisRoute.sim` | `(∀ p c, Loaded p c → Fits p → Nonempty (RouteAt …)) → L.Sim Loaded` |

Instantiation recipes:

- **A bytecode VM (small step).** Present the bytecode semantics as a
  `SmallStep` (`Next p s s' := step p s = .next s'`, and
  `Final p s e out := ∃ w, step p s = .halt e w ∧ console w = out`). Prove
  `Good p → Progress p`. Discharge `ArmSim` one interpreter dispatch arm at a
  time, then read off `(ArmSim.simTotal A).refinement`.
- **A big-step source language.** Use `ofOutput` and `OutSim` as WHILE does,
  or a custom `Lang` with `Obs` when nonzero exits are specified.
- **Through Iris.** Supply `RouteAt` from your boot data. The WHILE instance is
  `VsaIris.Interp.routeAt_of_boot` in `VsaIris/Interp/EndToEnd.lean`:
  `interpSim_iris := OutSim.of_sim (IrisRoute.sim …)`.

## 2. Decode facts: `#simp_nf`, `decodeW`

`#simp_nf F binders : t using [lemmas]` (`Vsa/Meta/SimpNF.lean`) partially
evaluates `t` once, under hypotheses. It emits `def F` (the simp normal form)
and `F.eq`. `Vsa.Sim.decodeN` in `Vsa/Sim/DecodeNF.lean` is the Sail decoder
with `misa`, `cur_privilege` and `mseccfg` pinned. `Vsa.Sim.decodeW σ hmisa
hpriv hsec` then gives `(ext_decode w).run σ = .ok i σ` for any concrete word
`w`, where `i` is found by `rfl`. No per-word lemma is needed. A port whose
reset `misa` differs changes `Vsa.Sim.initMisa`, and `decodeN` follows.

## 3. Code pins from the image: `TextPiece`, `CodeAt`

- `CodeAt T img rT` (`VsaIris/Vsa/SymExec.lean`) states that every byte of the
  ranges `rT` is pinned to the image function `img` by `TextLoaded T`.
- `codeAt_of_pieces` proves it from the `TextPiece` footprints inside `T`
  (`Vsa/Sim/TextImage.lean`, `VsaIris/Vsa/TextPieces.lean`), range by range,
  with one `decide +kernel`.

The model is `codeAt_interp` in `VsaIris/Interp/SymInterp.lean`, where
`binByte` combines `fixedTextByte`/`fixedRodataByte` from
`Vsa/Sim/Code/FixedImageData.lean` and `interpRanges` lists the code and
constant-table ranges. A port supplies its own image function and pieces.

## 4. Symbolic execution: `symRun_cont`, `obCheck`, `sym_run`

- `symRun C n s` (`SymExec.lean`) executes a run as one closed computation over
  symbolic values `SE`, a symbolic store and a residual obligation list, from
  any symbolic state `s`. The configuration `Cfg` holds the image and code
  ranges, the tracked registers, the stop PCs and the per-program load kinds:
  `dpcs` (loads that read the data view), `hv` (loads of bytes nobody owns:
  the value is quantified, `Tree.hv`), `rawpcs` (owned loads kept unreduced,
  `Tree.raw`), `kv`/`kvM` (known words of the data view and of the entry
  memory) and `known` (entry registers with a literal value).
- Obligations sit on the tree node where they arise (`Tree.br` carries those
  since the last fork), so a prefix is discharged once. With `forkStop` the run
  ends at a branch the operands do not decide; the consumer prunes a side or
  continues it with another `symRun_cont`, so an infeasible side is never
  executed.
- `sltu`/`sltiu` are stepped by `aluStep_sltu`/`aluStep_sltiu`
  (`SymObsStep.lean`), generic in the registers; `SE.ltu` is their value.
- `symRun_swp` turns the residual WP into `SWP` at the state. `symRun_cont`
  takes the run-independent premises as one `RunCtx` and prunes with the
  reflective checker `obCheck Γ` (sound by `obCheck_sound` under
  `Geom.holds`). `symRun_auto` is the entry form. `geom_auto [facts]` proves
  `Geom.holds`.
- `sym_run [fuel] hlive using [facts] at pc…` and `sym_run1`
  (`VsaIris/Interp/SymInterp.lean`) are the tactic surface for goals
  `IW live Dt DA S Q pc R Mt`. A run is cut into segments at the branches its
  operands do not decide; each segment is one `symRun_cont`. The leftover
  goals are in step-lemma form, the form the pieces' statements are written
  against: a branch premise reads a written register from the fact-rewritten
  register chain of its step, an undecided access check or jump alignment is
  the side goal of that instruction's step lemma (`hea`, `hLDS`, `hLDD`,
  `hS`, `hal`), and a branch side that takes no step keeps its premise
  unnormalised. `sym_run1` stops at the first branch it cannot prune.
  `SYM_TRACE=1` reports each run in a build.
- The interpreter has no per-instruction step table. Its table value
  `StepGen.interpTbl` supplies the load kinds (`variants`), the sites where a
  step-by-step run would step (`interpHasStep`) and the call lemmas, which a
  proof names as `step% jalx <pc>`.

To port: copy `cfgI`, `binByte`, `interpRanges`, `iRegs` and the load-kind
lists (`interpDataPCs`, `interpHavocPCs`) with your binary's image, code
ranges, tracked registers and table variants. The executor and
`symRun_cont` stay the same.

## 5. Boot witnesses: `boot_witness`

In a namespace that defines `script`, `log` (a `PackedLog`), `gprs`,
`entrySteps` and `prog`, the command `boot_witness`
(`Vsa/Sim/Boot/WitnessCmd.lean`) does the following:

1. It runs the untrusted generator `Derive.data` natively (`Derive.lean`)
   and adds the derived data as literal definitions.
2. It builds the witness `W : Witness` (`Witness.lean`) and proves each field
   of `Witness.Ok` with one `decide +kernel` (checks in `FastCheck.lean`).
3. It emits `loadedEntry`, `loadedEntry_fill`, `loadedAt` and `loaded`.

Examples are in `Vsa/Sim/Boot/Gen/*.lean`. You can reuse the generic parts:

- the packed store log and `LogOk`
- the byte runs (`runs`, `pagesOk`, `runOkF`)
- the image view (`ImageView`)
- `EntryRegs` (`Entry.lean`)
- the `fillZero` entry theorems

The rest is WHILE-specific and must be restated for a new interpreter:

- `Witness.Ok`'s ownership and heap fields (`own`, `OwnOk`, `FrameOk`,
  `HeapFactsOk`, `BootRegs`, `stmts`/`count`)
- the fixed reference words `memRef`
- `aboveOk`'s address `0x8001acf0`
- the target `Vsa.Refine.Loaded interpRunLayout`

## 6. Per-rule arms: descriptors and modes

Arms are proved once for any `Wp : MachWP (vsaModel live)`. The two modes are
the total `twpW` (counted, for `term`) and the partial `wpW` (uncounted, for
`stuck`).

- `VsaIris/Interp/ArmCore.lean` defines `ArmAt Wp Φ F pc R S Mt` (frame plus
  machine state). `ArmAt.seg`/`ArmAt.run` run one reflected segment (`MRun`).
  `JalAt`/`jal_site% 0x…` describe a generated call site, and
  `ArmAt.callHelper*` calls through it. `ExitK`/`ArmAt.finish` close at the
  return.
- `VsaIris/Interp/ArmEval.lean` provides the mode-specific entries
  `evalEntryT`/`evalEntryP` and the recursive child calls
  `ArmAt.callEvalT`/`ArmAt.callEvalP`.
- In the descriptor pattern, one structure per rule family holds the
  semantics, the side condition, the call sites and the reflected paths, and
  one generic tail consumes it in both modes:
  - `IntOpDesc` + `intOpTail`/`intOpT`/`intOpP`
    (`IntOpRuns.lean`, `IntOpArm.lean`)
  - `CmpOp` with `IntRun`/`StrRun3`/`StrRun4` (`CmpRuns*.lean`)
  - `EqRuns.lean`
  - `LogRuns.lean`

  Adding an operator adds one descriptor value. A port writes new
  descriptors for its own dispatch arms and reuses `ArmCore`.

## 7. Parameters still hard-wired

These must be lifted, or edited per binary, before the machine layer is
shared by import rather than by copy:

- `Vsa.Sim.tohostAddr` (`Vsa/Sim/InitValues.lean`: `0x8001ad00` here,
  `0x8005c6c0` in Lua, `0x800668c0` in OCaml). It is used in
  `LdOK`/`StOK`/`StOKb` (`VsaIris/Vsa/SymRun.lean`), `TermWF`
  (`Vsa/Sim/BlockTerm.lean`), `obCheck`'s HTIF gap and `Geom.holds`
  (`SymExec.lean`), and `Htif`, `HtifStepObs`, `TermEntry`, `GoodState` and
  the memory-load files under `Vsa/Sim/`.
- `initMisa`, `initMstatus` and `initPmaRegions` (`InitValues.lean`) and the
  RAM window `[0x80000000, 0x100000000)` literal in `LdOK`/`StOK`/`obCheck`.
- The global pointer: `gp = 3` with the value `gpV = 0x8001b510`
  (`VsaIris/Vsa/Newlib.lean`, `MallocFastSegs.lean`), used by
  `SymExec.rdR`/`rdS`/`finReg_gp`.
- The image and ranges: `fixedTextByte`/`fixedRodataByte`, `interpText`,
  `interpRanges` and `binByte`'s `0x80018be0` split (`SymInterp.lean`).
- The console site `putcSite` (`VsaIris/Vsa/Console.lean`) and the newlib
  entry addresses in `VsaIris/Vsa/Newlib*.lean`.
- The WHILE layout: `interpRunLayout` and `interpRunEntry = 0x800043ec`
  (`Vsa/Sim/LayoutInstance.lean`), `topRegs`/`Boot`/`bootRes`
  (`VsaIris/Interp/World.lean`, `TopBoundary.lean`), and everything under
  `Vsa/Sim/Boot/`.
