# Abstraction-discovery round 11: the interpreter's runtime-function proofs (2026-10-02)

Branch `exp-R11`, from `exponentiate-next` 8f4bb737 (PR #14 snapshot 9, after ROUND-10). Target: the
runtime-function proofs of the interpreter in `VsaIris/Interp`: `Proof*.lean` (20 files), `Env*.lean`
(16), `Call*.lean` (22), `Loop*.lean` (4): 62 modules, 19,955 non-blank lines. Raw material (census
spy and tables, per-declaration profiles, kernel re-check, briefs, ontologist answers, timings) is in
`~/syi-r11/`. Run tactics in `Vsa/Stdout/Tac.lean`, `StepGen.lean`, `AllocTac.lean`, `Interp/ITac.lean`
and `Vsa/Stderr/*` belong to another agent this round and were not edited.

## 0. Primary measure (stated before any candidate)

Two suites, because the census puts the lines and the seconds in different places (section 1):

* **Suite L (agent effort; primary for vocabulary candidates):** non-blank lines of statement-identical
  re-proofs of held-out declarations, plus failed compiles.
* **Suite T (time; primary for decision candidates):** single-file user CPU of held-out modules
  (`LEAN_NUM_THREADS=1`, the module copied outside the repo and compiled against the branch's build,
  contenders interleaved in one window, min of 3).

A candidate is compared on the suite of the cluster it targets and measured on the other for
regressions. Bound for every contender and for the rollout: no file more than 10% (and 0.2 s) slower
(E49). Headline: the 62 modules' CPU and lines before/after; full `lake build` green.

## 1. Census

### 1a. Gate, reachability

The gate (`syi-gate/scripts/abstraction_gate.py --root`, run by hand; the branch still has no
`scripts/` and no CLAUDE.md, C1) fails with the same 12 clusters as after round 10. Two are in the
target: `Call run` (10 hand proofs, 13 → 13 lines, `CallClosure.lean` `CallK_run*`) and `Clo run`
(11, 13 → 9, `CallCloRuns.lean` `CloE_run*`). Both are `#ix_seg` machine-run pieces whose bodies are
one `sym_run` line; the lines are their hypotheses (stack window, pointer windows, register and slot
bindings).

Reachability cut first (constant closure of the headline and executable modules, round 9's
`Census.lean`, 10 s): of 1,856 target declarations, 323 are off the path but they hold **39 lines**:
unused structure-field projections (`NpCtx.h13`, `CloAr.s7m`, …), three 1–2-line equation lemmas
(`valsImg_cons`, `statusRet_cont`, `regsOf_nil`) and one tactic syntax declaration. Nothing to cut
(E38 again).

### 1b. Lines by conclusion head (round 4's census script, units of the 62 modules)

| kind (conclusion head) | units | non-blank lines | declaration seconds |
|---|---:|---:|---:|
| Iris `⊢ Wp.W Φ` (spec/arm/call proofs) | 136 | 8,393 | 77.1 |
| other theorems (spec bodies, helper and record lemmas) | 454 | 6,583 | 49.6 |
| machine runs: `#ix_seg` pieces (`sym_run`) | 74 | 910 | 75.0 |
| machine runs: `Span` (`sx_run`, the env functions) | 36 | 940 | 68.4 |
| machine runs: `#ix_piece` chains | 13 | 563 | 16.9 |
| machine runs: `IW` theorems (`sym_run`/`sym_run1`) | 12 | 453 | 13.3 |
| structures, defs, abbrevs | 188 | 1,271 | 2.5 |
| total | 913 | 19,113 | 302.8 (+16.6 unattributed) |

Declaration seconds come from `trace.profiler` (threshold 20 ms, `Elab.async false`) over every
module, joined to the units. **Machine runs are 15% of the lines and 57% of the declaration
seconds; the Iris and helper proofs are 78% of the lines and 42% of the seconds.**

Per-function kits. Each runtime function re-makes the same kit under its own names: an entry
context record (`NpCtx`, `NplCtx`, `NaCtx`, `SgCtx`, `VeqCtx`, `VpCtx`: register bindings, a stack
window `hs1..hs4` spelled out field by field (only `VeqCtx` uses the existing `StackGeom`), argument
geometries, frame/object disjointness), a continuation (`NpK`, `NaK`, `SgK`, `VpK`, `NplK`), a rest
bundle (`NpRest`, `NaRest`, `SgRest`), a footprint (`npS`, `sgF`, `veqS`, `getS`, `growS`), and a
saved-register stack record (`DefStack`, `GetStack`, `NewStack`, `CloSpills`, `CallSaved`). Two
files add their own `macro_rules` for `sx_side` to unfold their footprint.

Idioms in the Iris/helper proofs (grep over the 62 files): stack geometry derived by hand
(`hsg.lo`/`toNat_sub_frame`/`evalSP_off`/`evalSP_eq`: 68 lines in 12–15 files; the literal
`18446744073709550528#64` = −1088 appears on 255 lines in 17 files), store read-back chains
(`imgM_store_miss`/`ldv_store_miss`/`ldv_eqOn`: 124 lines, 19 files), run brackets (`wp_swpF Wp` 63,
`swp_closeRM` 34, `wp_span` 25), register-keep enumerations (`rcases … rfl | … <;> ix_reg`, 6 sites).
In the 177 theorem units of ≥ 25 lines, 72 contain none of these idioms.

Existing layers and their use in the target (lines in the 62 files / files there / files repo-wide):
`iframe` 627/47/168, `$$ [$]` 165/37/79, `icombine` 43/18/42, `wp_swpF` 69/20/48, `swp_close*`
115/20/50, `sym_run` 121/19/54, `sym_run1` 75/9/10, `sx_run` 50/6/17, `ix_fwd` 44/8/30,
`helperSpec`/`ms_callHelper` 12/9/22, `ms_callRegs` 9/4/8, `wp_callW` 4/4/11, `wp_localRunW` 5/5/14,
`evalEntryP` 8/4/21, `StackGeom` 51/15/39, `SlotWin` 5/4/9, `keep_split` 4/3/9; **0 uses**:
`ArmAt`/`ArmCore`/`ChildCall`/`evalEntryT`, `wp_segW`, `xrun`, `nx_run`, `carry_close` (51 files
elsewhere), `HostRun`, `HeapWin`, `RegKeep` (`keep3/4/6`, `upd_norm`), `omega_dc`/`dbm` as written
tactics, `rgn_side`/`key_or` (RegionTac), `Win.` keys, `simp_set` as written tactic.

### 1c. Seconds (E18, E24, E51)

Single-file one-thread user CPU of the 62 modules (base 8f4bb737, min of 2, 8 in parallel, load
7–12): **368.7 s** (Proof 151.5, Env 98.9, Call 81.6, Loop 36.7). Import floor (each module's
imports alone): 42.8 s. Heaviest: ProofStringify 43.7, EnvDefineSpans 35.3, ProofNativeAssert 17.8,
ProofNativePrint 17.1, ProofValuePrint 16.2, ProofValueEqual 16.1, LoopFor 15.7, EnvGetSpans 12.8,
EnvSetSpans 10.2, CallCloRuns 9.7.

Profiler totals (innermost attribution, all 62): type checking 65.7 s, `omega` 62.3, `rw` 28.2,
`simp` 24.7 (+7.2 `simp_set`), elaboration 11.4, `refine` 8.0, `cases` 5.0, every Iris proof-mode
tactic together ≈ 6.5. Kernel re-check of every target theorem (`addDeclCore`, 3,571 declarations
above 1 ms): 59.9 s, of which `omega` certificates 26.7 s; spread thin (largest parent `def_pro`
1.8 s).

### 1d. The decision calls, by the tactic that issued them (E52, E58)

Census spy (round 10's, `@[no_fallback]`, calling the project's `omega` front end; one thread,
`Elab.async false`; census user total 365.7 s):

| issued by | `omega` calls | `omega` s (tactic + own kernel) | failing | `simp` calls | `simp` s | failing simp |
|---|---:|---:|---:|---:|---:|---:|
| written `omega` (2,283 sites) | 2,691 | 47.3 | 77 | – | – | – |
| `sx_run` (env Span runs) | 360 | 28.8 | 211 | 1,394 | 8.8 | 16 |
| `sym_run1` | 680 | 13.2 | 301 | 4,607 | 19.1 | 1,231 |
| `sym_run` | 366 | 8.3 | 111 | 1,385 | 5.6 | 261 |
| `ix_fwd` | 113 | 1.3 | 63 | 328 | 19.2 | 0 |
| written `simp` | – | – | – | 1,999 | 10.4 | 44 |
| `ix_reg` | – | – | – | 738 | 3.5 | 36 |

By goal shape (successful `omega` calls; "or" = disjunctive goal, "mod" = `%` in the goal, "hmod" =
`%` in some hypothesis): **`sx_run` footprint-membership side goals `hS` (35 calls, 13.4 s, 380 ms
each) and `hLDS` (42 calls, 12.8 s, 300 ms each)** are the heaviest single family. Profiled instance
(E19, `def_pro`, the most expensive declaration, 12.2 s): the store address reaches `omega` as
`(((R 2).toNat + 18446744073709551552 % 2^64) % 2^64 + 24 % 2^64) % 2^64` and the goal is the
footprint `getS s out G` unfolded to five disjuncts (`s-64 ≤ b ∧ b < s ∨ out ≤ b ∧ b < out+24 ∨ G.sblk
… ∨ G.cap ≠ 0 ∧ (…)`); `omega` case-splits the nested `%` and the negated disjunction (700 ms per
call), although with `(R 2).toNat = s` and `80 ≤ s` the address is `s - 40` and the first disjunct
holds by literals. Written `omega` is 47 s over 2,691 calls (17.6 ms average; 1,307 calls with a `%`
hypothesis in context, 24.1 s).

`rw` (28.2 s profiler) is concentrated in ProofStringify 4.5, EnvDefineSpans 4.2, CallPrefix 4.0,
LoopWhile 2.2, CallCloHead 2.2, LoopFor 2.1.

### 1e. Clone check on the artefact (E46)

`env_get` (0x80002cdc) and `env_set` (0x80002c10) share 42 of 51 instruction words: prologue, scan
loop and epilogue are identical; the `jal strcmp` words differ only by their pc-relative offset (same
absolute target); the 9 hit-path words differ (copy vs write). EnvGetSpans/EnvSetSpans (164 lines
each, 12.8 / 10.2 s) re-prove the shared 42 words twice at different addresses; EnvGetHit/EnvSetHit
(67/65 lines) are not clones.

**Where the cost is.** Seconds: the machine runs (57% of declaration seconds), and inside them the
run tactics' side goals (`sx_run` footprint membership and address arithmetic with `%`; `sym_run1`'s
failing simp passes). Lines: the Iris/helper proofs (78%), spread over per-function kits and the
idioms above; ROUND-4 found no proof-mode abstraction that pays here, and M1 migrated the cheap part.

## 2. Laws

| law | statement | status / check |
|---|---|---|
| L-foot | an access at `base + c` (base an atom with a value fact, `c` a literal) lies in the footprint component keyed by the same atom; membership is decided by literals on that component, with no search over the footprint's disjuncts | true on the profiled `def_pro` goals by hand (address `s - 40`, first disjunct `s-64 ≤ b < s`); decided by keys for the allocator (round 10 `rgnKeyed`/`key_or` in `RegionTac`) and for newlib (round 3 `Win`); unused in Interp |
| L-wrap | `(x + (2^64 − c)) % 2^64 = x − c` for `c ≤ x < 2^64`; a frame base plus a literal offset is a literal offset of the frame top | proved: `toNat_sub_frame`, `evalSP_off`, a local copy `evalSP_off'` (LoopArgs), `key_toNat_add`/`lin_modneg` (RegionTac); applied by hand (68 lines) |
| L-geom | every address side condition of a run inside a frame of `n` bytes (stack window, pointer windows, `tohost` separation, alignment) follows from `StackGeom s n` and one geometry record per object; statements need only the records | records exist (`StackGeom`, `SlotGeom`, `ArgsGeom`, `SlotWin`, `RamWin`, `EvalFrameG`); five of six Ctx records and every `#ix_seg` statement spell the fields out (`Call run`, `Clo run`) |
| L-readback | after stores at keys `kᵢ` (width `wᵢ`), a read at key `k` outside every `[kᵢ, kᵢ+wᵢ)` returns the old value; same-atom keys are compared by literals | proved: `imgM_store_miss`, `ldv_store_miss`, `ldv_eqOn`, simp sets `sx_mem_set`/`ix_mem_set`; the Iris proofs chain them by hand (124 lines) |
| L-kit | a runtime-function proof is entry context → prologue spill of the saved set → body inside a footprint → epilogue restore → continuation applied to the post; spill/restore, the context's window facts and the exit register file are one generic lemma over (frame size, saved list, footprint) | instances re-made per function (6 Ctx, 5 K, 3 Rest, 5 stack records); generic pieces: `helperSpec`/`ms_callHelper` (newlib helpers), `regsOf_exit`, round 4's SEAM (not adopted) |
| L-translate | two copies of the same position-independent code at different bases have the same runs up to the pc offset | holds on `env_get`/`env_set` for 42 of 51 words (section 1e); no translation lemma exists at the `SWP` level, and the step drivers need literal pcs |

All laws but L-translate are already lemmas or tactic behaviour somewhere in the project; the stall
is in applying them at this layer (E4, E41).

## 3. Held-out suites (drawn before any candidate)

`abstractions/ROUND-11-heldout.json`, seed 20261002.

Suite T (modules; population: the 25 target modules of ≥ 4 s, stratified by the share of their
declaration seconds in machine runs):

| stratum | population | primary | fresh |
|---|---:|---|---|
| Rs: `Span`/`sx_run` runs | 5 | EnvGetHit | EnvSetSpans |
| Ri: `IW`/`#ix_seg`/`sym_run` runs | 9 | ProofValueKindName, ProofNativeAssert | CallPrefix, ProofStringify |
| W: Iris/helper dominated | 11 | LoopArgs, CallCloP | LoopWhile, ProofValuePrint |

Suite L (declarations re-proved with identical statements; population: the 177 theorem units of
≥ 25 lines with head `Wp.W` or "other theorem", 11,086 lines; three size strata):

| stratum (lines) | primary | fresh |
|---|---|---|
| 25–38 | `dispResL_of_argVals` (CallNative, 27), `regsOf_entry` (EnvSpan, 33) | `whileStage` (LoopWhile, 26), `vp_native` (ProofValuePrint, 36) |
| 38–60 | `wp_call_reallocOpt` (EnvDefineCalls, 60), `cloErrDepth` (CallCloP, 48) | `wp_call_reallocNull` (EnvDefineCalls, 43), `roOwn_clod` (ProofValuePrint, 44) |
| 60–400 | `sg_memcpy` (ProofStringify, 132), `frame_write_close` (ProofEnvSet, 82) | `def_grow` (EnvDefineGrow, 400), `sg_filled` (ProofStringify, 64) |

Law-precondition classes of the drawn L cases (E54, by regex over each body): `cloErrDepth` geom +
bracket, `whileStage` keep + bracket, `def_grow` bracket; the other nine contain none of the idioms
of L-geom/L-readback/L-keep. Of the 177 units, 72 contain none.

## 4. Blind ontologists

Four agents (three random 256-character seeds, one random dictionary sentence; seeds pasted as
literal text and echoed back by every agent, E53) got only `~/syi-r11/fanout/brief.md`: the semantics,
the census, the laws, the existing abstractions the target can import (with use counts, import
position and per-call cost), the real restrictions of the decision procedures, the forbidden
vocabulary and three held-out statements. Each returned five candidates in 128–177 s.

| candidate | agents | rules = laws | rank given | decided by |
|---|---:|---|---|---|
| F. charted footprints / atlas / cadastre: a footprint is a list of atom-keyed charts; an address normalised to atom + literal is looked up by atom and checked by a closed `Nat.ble`; one bridge lemma per footprint definition; delivered as a `sx_side` alternative reusing RegionTac's `linNF`/`key_or` | 4/4 | L-foot, L-wrap | 1st by 4/4 | syntactic lookup + closed computation; fallback to the existing path |
| G. frame/object certificates (FrameCert/ObjCert, datum, epoch/passport): one stack certificate and one per object, every window and no-wrap fact a projection; `ofFields` adapters for frozen statements; statement compression for the gate clusters | 4/4 | L-geom, L-wrap | 2nd by 4/4 | projections; literal checks; one small `omega`/`dbm` when n is symbolic |
| W. keyed write ledger: memory after a run as base ⊕ log of keyed entries, reads evaluated by a reflective `readK` | 4/4 | L-readback | 3rd–4th | closed computation; stuck on symbolic offsets |
| K. calling-convention envelope / ABI functor / spill-restore liturgy: prologue/epilogue proved once by induction over the saved list, one bracket lemma per function | 4/4 | L-kit | 3rd–5th | `decide` on instruction words vs generated text; flagged: irregular prologues stay by hand |
| T. translation-equivariant runs (relocation, transposition) | 4/4 | L-translate | 4th–5th | `decide` on PIC words; needs a step-commutation lemma against Sail (the expensive part) |

Every agent ranked the same five in nearly the same order and recommended F first (fused with the
minimal floor-fact part of G). Theories cited: manifold atlases (Lee), base+offset alias analysis
and value-set analysis (Wilson & Lam 1995; Balakrishnan & Reps 2004), CHERI capability bounds
(Woodruff et al. 2014), Torrens title registration, region calculus (Tofte & Talpin 1997), DBMs
(Miné 2001), proof-carrying code (Necula 1997), CompCert block/offset memory and Stacking (Leroy &
Blazy 2008; Leroy 2009), crystallographic unit cells, calendrical day numbers (Dershowitz & Reingold),
McCarthy arrays, ARIES/LSM logs, event sourcing, double-entry bookkeeping, XCAP, STAL, effect handlers
and `bracket`, relocation (Levine 2000), Noether/equivariance, transformational music theory (Lewin).

## 5. Retrieval by law

All five are **known**, and four already exist at another layer of this project:

* F: base+offset / value-set analysis; here round 10's `RegionTac` keys decide L-foot for the
  allocator's `Rgn`/`ARgn` regions (1–9 ms per obligation) and round 3's `Win` for newlib. `RegionTac`
  is already in the import closure of the heavy target modules and registers `rgn_side` as an
  `sx_side` alternative, which returns at once on footprints (no `Rgn` facts).
* G: proof-carrying certificates; the records exist (`StackGeom`, `SlotGeom`, `ArgsGeom`, `EvalFrameG`,
  `SlotWin`, `RamWin`); only `VeqCtx` and 15 files use `StackGeom`.
* W: McCarthy arrays; the run tactics already read memory through `writeLog` chains with the
  `sx_mem_set`/`ix_mem_set` simp sets; `carry_close` (round 8) consumes the same chains.
* K: CompCert callee-save invariants; round 4's SEAM candidate (family call seams) was this law at
  the call side and was not adopted.
* T: relocation; round 8's `HostRun` is the text-parametric analogue (same code, other host text),
  not translation.

## 6. Variation

`/ideonomy` draw: organon construction × substitution, organon *map*, prompts scope / decomposability
/ longevity, applied to F and G. Map (x: when the key is computed, y: what carries it):

```
                 | per side goal          | per run (hoisted)         | per footprint definition | per frame (certificate)
-----------------+------------------------+---------------------------+--------------------------+------------------------
the address      | linNF + key_or (PA)    | normalise R 2 -> s once   | -                        | G's .off projection
the footprint    | unfold disjuncts, pick | footprint pre-unfolded    | bridge lemma (F, PB)     | frame chart = projection
                 | by atom (PA)           | once into ordered InExt   |                          | of the certificate (F x G)
the register     | "R 2 is the stack atom": key by register index, no normalisation (substitution: address -> register)
```

Substitutions read off the map: scope one goal → the meet (key the unfolded `InExt` disjunction by
the address atom with the existing `key_or`, no datatype, PA); longevity per definition → F's bridge
lemmas (PB); decomposability fused → the frame chart is a projection of the stack certificate (F × G);
address → register (key by `R 2` syntactically) is cheap but brittle (writes through other base
registers) and stays a precheck inside PA. Following E25/E32/E41/E47 the meets are piloted for every
cluster, and the unanimous first pick is also piloted as a new datatype:

* **PA** (F as the meet, time): the existing key route made to reach footprint goals (`sx_side`
  alternative / `rgn_side` extension, `sym_run`/`sym_run1` side goals), no new datatype.
* **PB** (F as the ontologists built it): `Atlas`/chart datatype, bridge lemmas per footprint
  definition, `chart_mem`.
* **PC** (G as the meet, lines): projections on the existing geometry records, used in the held-out
  re-proofs and to restate one gate cluster.
* **PD** (W + K as the meet, lines): read-back and register-keep/exit rules over the existing
  `writeLog`/`imgM` terms and register lemmas, no ledger type.

T (translation) is not piloted: its saving is bounded by one duplicated pair (≈ 160 lines, ≈ 11 s)
and its setup needs a step-commutation lemma against the Sail model.

## 7. Bake-off (one timing script for all contenders, `~/syi-r11/bake/bake.sh`)

Pilot branches from 78f9fb97, each in its own worktree (E56), each built (`lake build VsaIris`, 0
errors, 0 `sorry`): PA `exp-R11-PA` 013a2ab0, PB `exp-R11-PB` 0db4a774, PC `exp-R11-PC` a6b34d2c,
PD `exp-R11-PD` ad907eb7.

### Suite T (time): single-file one-thread user CPU, s, min of 3 rounds, contenders back to back per file, three rounds in parallel (load 9–14)

| module | base | PA keys (meet) | PB atlas | PC geometry | PD read-back |
|---|---:|---:|---:|---:|---:|
| EnvGetHit (Rs) | 4.02 | **1.92** | 2.36 | 3.95 | 3.98 |
| ProofValueKindName (Ri) | 3.91 | **3.24** | 3.89 | 3.93 | 3.92 |
| ProofNativeAssert (Ri) | 16.44 | **11.97** | 16.26 | 16.65 | 16.73 |
| LoopArgs (W) | 8.65 | **7.87** | 8.71 | 8.55 | 8.52 |
| CallCloP (W) | 6.71 | 6.77 | 6.72 | 6.74 | 6.73 |
| **primary total** | 39.73 | **31.77 (−20.0%)** | 37.94 (−4.5%) | 39.82 | 39.88 |
| fresh: EnvSetSpans (Rs) | 10.33 | **4.55** | 6.51 | 10.43 | 10.51 |
| fresh: CallPrefix (Ri) | 8.63 | **8.19** | 8.61 | 8.61 | 8.54 |
| fresh: ProofStringify (Ri) | 43.57 | **33.16** | 43.97 | 44.17 | 44.52 |
| fresh: LoopWhile (W) | 9.31 | **7.67** | 9.32 | 9.36 | 9.67 |
| fresh: ProofValuePrint (W) | 15.09 | **13.82** | 15.40 | 15.19 | 14.93 |
| **fresh total (forecast)** | 86.93 | **67.39 (−22.5%)** | 83.81 (−3.6%) | 87.76 | 88.17 |
| diagnostic: EnvDefineSpans | 36.40 | 19.62 | **17.09** | 36.27 | 36.25 |
| changed by PC/PD: CallCloRuns | 9.99 | 7.34 | 9.81 | 9.96 | 10.20 |
| CallCloExit / CallCloBind / CallCloHead | 3.03 / 5.01 / 8.23 | 2.97 / 4.94 / 8.35 | 3.02 / 4.94 / 8.29 | 3.24 / 5.19 / 8.34 | 2.97 / 5.11 / 8.19 |
| CallNative / EnvDefineCalls / EnvSpan / ProofEnvSet | 2.38 / 2.38 / 1.28 / 2.28 | 2.08 / 2.22 / 1.28 / 2.42 | 2.41 / 2.40 / 1.30 / 2.41 | 2.44 / 2.32 / 1.27 / 2.31 | 2.39 / 2.34 / 1.31 / 2.30 |
| setup (non-blank) | | 271 new (`FootKey`) + 490 moved (`KeyNF` ← RegionTac/Region) | 280 generic + 14 bridges | 41 | 36 |

What each pilot found:

- **PA (keys reach the footprint, the meet).** `foot_key` decides a side goal whose footprint unfolds
  to `∨`/`∧` of comparisons, alignments, `≠` and literal constants (also under `∀ b ∈ accAddrs a w`) by
  `linNF` keys and literal checks only, never `omega`; hooked as a new `sx_addr` alternative (every
  `sx_side` alternative, including the per-file ones, ends in `sx_addr`, and `ix_fwd`'s discharger
  reaches it too) and as the first stage of `sym_run`/`sym_run1`'s geometry tactic. To make the key
  route importable below SymInterp/EnvTac, the region-free half of RegionTac (key lemmas, `KeyFacts`,
  `linNF`, `relNF`, difference facts, `alignOf`, `key_toNat_add`) moved unchanged into `KeyNF`
  (imports only RegionCore). Per call 0.7–2.0 ms (success), 0.05–1.5 ms (failure), against 300–700 ms
  for the old `hS`/`hLDS` route and 10–100 ms for the `sym_run` geometry goals. No proof file changed.
  Defects found: (1) a stronger discharger changes which goals a run leaves to the proof (reading
  BitVec register equations closed an alignment goal ProofArith closes by hand: wrong goal count), so
  run-tactic strength is part of every proof's interface; (2) `keyFacts` read floors only from
  top-level literal sums, not from conjuncts or bounds written with constants (`tohostAddr + 16 ≤
  p.toNat`); (3) the per-file `sx_side` alternatives are each tried and failed before the next (169
  failing `omega` calls in EnvDefineSpans, now ≈ 3.7 ms each).
- **PB (atlas datatype).** `Atlas.den` over guarded charts, a generic `InExt.atlas` bridge plus three
  footprint bridges, `chart_mem` as an `sx_side` alternative (1.1 ms success, 0.008 ms failure). It
  only reaches the env modules (it imports RegionTac, which is not below SymInterp), so it moved no
  `sym_run` module. It also reads local chart hypotheses `∀ x, lo ≤ x → x < hi → S x`, which closed
  goals EnvDefineSpans had discharged by hand (14 stale lines removed): that is why it beats PA on that
  one module. Found the same `keyFacts` floor defect and the rule-ordering hazard (per-file global
  `sx_side` rules outrank earlier generic ones; the generic rule must be registered again after them).
- **PC (geometry records).** One L-wrap projection `toNat_frame`/`toNat_frame_off`, `EvalFrameG.off`,
  `RamWin.ofEnds`, and `geom_open`/`with_geom` (open every geometry record in context as hypotheses,
  0.3 ms). Gate cluster `Clo run` restated with records: 11 pieces 138 → 104 lines, users in four files
  updated. Defect: `#ix_seg` turns every hypothesis left in a piece's context into a premise of its
  continuation goals, so hypotheses a piece body adds must be cleared (`with_geom`); `htifLo` and
  `tohostAddr` are one literal under two names and `omega` treats them as different atoms.
- **PD (read-back and register keep over the existing terms).** `ldv_win`, `rd_back [lemmas] using
  [defs]` (one call for a `imgM_store_miss` chain), `reg_keep [h]` (keep over a literal register list by
  one `decide +kernel`). Per call 0.2–0.6 s against ≈ 18–45 ms for the hand steps it replaces; two
  uses reverted for time. Defects: `maxRecDepth` escapes `first`; a failing simp-discharger alternative
  rolls back the unfolding the next alternative needed. Found a dead 9-line block in the base.

### Suite L (agent effort): statement-identical re-proofs of the six primary declarations

| case | base | PC lines (fails) | PD lines (fails) |
|---|---:|---:|---:|
| `dispResL_of_argVals` | 27 | 27 (0) | 14 (3) |
| `regsOf_entry` | 33 | 29 (0) | 22 (1) |
| `wp_call_reallocOpt` | 60 | 60 (0) | 44 (1) |
| `cloErrDepth` | 48 | 47 (3) | 44 (1) |
| `sg_memcpy` | 132 | 128 (1) | 95 (6) |
| `frame_write_close` | 82 | 79 (1) | 57 (3) |
| total | 382 | 370 (5) | 276 (15) |
| of which attributable to the round-11 layer | | −4 | ≈ −20 (one case, `sg_memcpy`) |
| older layers | | 0 | −7 |
| plain cleanup (no layer) | | −8 | ≈ −79 |

All twelve statement hashes match the base. The two pilots drew very different amounts of plain
cleanup from the same cases (8 vs 79 lines): that number measures the agent's thoroughness, not the
layer, and is credited to neither (E42). Layer-attributable: PC −4 on the suite plus −34 on the gate
cluster for 41 setup lines; PD ≈ −20 on the suite plus −13 on two CallCloHead chains for 36 setup
lines, at 0.2–0.6 s per call.

Reading. On suite T, PA beats the ontologists' datatype version PB on every module but one, primary
−20.0% vs −4.5%, fresh −22.5% vs −3.6%; the difference is reach (PA's key route sits under
`sx_addr` and inside `sym_run`, PB's only under the env modules' `sx_side`), and PB's one extra idea
(local chart hypotheses) is worth 2.5 s on EnvDefineSpans. PC and PD are time-neutral (CallCloExit
+7%, CallCloBind +3.6% under PC, within the bound). The line candidates are small: the census
already said 9 of the 12 L cases contain no idiom they target (E54), and the pilots confirm it.
Combination for the next step: PA + PC + PD (merged as `exp-R11-C` 933e8337, conflicts only in the
held-out re-proofs, PD's versions kept; full `lake build` green, 1,562 jobs), measured on the whole
scope and on the fresh L cases.

## 8. The combination: whole scope and fresh cases

**Whole scope** (all 62 target modules, single file, one thread, base 78f9fb97 and `exp-R11-C`
933e8337 interleaved per file, 8 shards, min of 2, load 10–20; `~/syi-r11/scope/`): **360.6 → 286.0 s
(−20.7%)**, no file over the bound. Largest: EnvDefineSpans 36.2 → 19.1, ProofStringify 43.4 → 32.0,
EnvGetSpans 11.2 → 4.8, EnvSetSpans 9.6 → 4.1, ProofNativeAssert 17.6 → 12.4, ProofNativePrint 17.3 →
12.3, ProofValueEqual 15.2 → 11.6, EnvSetHit 4.5 → 2.1, EnvGetHit 4.3 → 2.1, CallCloRuns 9.8 → 7.5.
The fresh T modules forecast −22.5%; the scope came in at −20.7%.

**Fresh L cases** (re-proved on the combination by one agent, no layer code allowed; `exp-R11-F`
5d55dfaf; statement hashes identical):

| case | base | after | round-11 layer | older layer | plain cleanup |
|---|---:|---:|---:|---:|---:|
| `whileStage` | 26 | 25 | 0 | 0 | −1 |
| `vp_native` | 36 | 26 | 0 | 0 | −10 |
| `wp_call_reallocNull` | 43 | 41 | 0 | −1 | −1 |
| `roOwn_clod` | 44 | 42 | 0 | 0 | −2 |
| `def_grow` | 400 | 374 | 0 (three `rd_back` uses −4 lines reverted: +10–15% file CPU) | 0 | −26 |
| `sg_filled` | 64 | 44 | −9 (PD `rd_back`; a near-clone of the tuned `sg_memcpy`) | 0 | −11 |
| total | 613 | 552 (−10%) | −9 (1.5%) | −1 | −51 |

PC's records bought nothing on the fresh cases (`def_grow`'s window record `EnvWin` is outside them;
`vp_native`'s facts are projections of a context field already); PA made no hand line dead there;
`reg_keep` applied to no fresh goal (the keep goals are about an abstract `R'` with a keep hypothesis,
not an `upd` chain). **Forecast for the line layers: 1.5% of the lines of fresh cases**, against 36
(PD) and 41 (PC) setup lines. The lines of these proofs are spec-specific glue and record bookkeeping;
an agent's cleanup pass removes 8–20% of them without any layer.

## 9. Rollout (own worktrees from 933e8337, one owner per layer, per-file +10% bound)

Brief: `~/syi-r11/rollout-brief.md` (layers, per-call costs of every reused tactic (E57), owners of
the shared functions (E62), the bound). Merged by the coordinator into `exp-R11-R3` together with
the fresh-case branch `exp-R11-F` and `origin/exponentiate-next` (e4efc1f1, snapshot 10): no
conflicts; full `lake build` green (1,562 jobs) at cc110310.

| agent | territory | what did the work | files (+/− non-blank) | measured (base 78f9fb97 → agent) |
|---|---|---|---|---|
| R1 keys (owned FootKey/KeyNF, every `sx_side`/`sx_addr` alternative) | the key route | PB's local-chart idea ported into `foot_key` without a datatype: a footprint leaf `S t` closed by any hypothesis `∀ x, P₁ x → … → S x` with premises decided by keys (covers chart hypotheses and disjunctive `hS`); list-membership leaves (`accAddrs`, `++`), literal multipliers, literal powers, reducible `+`/`−` abbrevs (`evalSP`); seven per-file `sx_side` alternatives deleted (every goal they solved, `foot_key` solves; measured per alternative with a spy; BinArm's kept, it solves 2 goals uniquely); new `foot_or t` (prove by keys, refute same-atom false goals at once, else `t`) as `ix_fwd`'s and `ix_mem`'s discharger: the false miss-lemma probes `a+8 ≤ a ∨ a+8 ≤ a` and `evalSP` addresses had cost 65–180 ms each on the `sx_addr` route; 20 hand lines in EnvDefineSpans became dead | FootKey +181/−12, Arm +3/−2, SymInterp +3, EnvDefineSpans −20, EnvTac −7, five files −3 each | 62 modules 364.1 → 260.9 s (−28.3%); EnvDefineSpans 39.3 → 11.2, CallPrefix 9.5 → 3.4, LoopFor 14.5 → 10.5, LoopWhile 9.3 → 6.4; `foot_key` 2.1 ms median success, 0.1 ms median failure; `foot_or` 1–2 ms |
| R2 geometry (owned the PC layer) | run-piece statements, stack geometry | `#ix_seg` pieces take `EvalFrameG s`/`RamWin a n`/`InpGeom` instead of spelled-out windows (Call_run*, CallX/CallN, CallK_runA–D, ArgsLoop_runA/B, three more Clo pieces), users in 12 files updated; `with_frame` (frame-slot loads stated at `s.toNat − 1088 + N`, ≈ 30 `rw [hoff N]` bullets gone); `StackGeom.evalFrame` replaces a 7–8-line derivation in 9 places; `StackGeom.lowerEval` merges two duplicate lemmas; 42 two-line `hsf` proofs → `toNat_frame rfl (by omega)`; `RamWin` moved down to Repr (statement identical) | 24 files, target −199, net −168; setup +31 | layer-attributable ≈ −190 lines, plain cleanup ≈ −10; all changed files within the bound (largest CallCloExit +7.5% in its sweep) |
| (PD) read-back | – | not rolled out (section 11) | – | – |

Defects the rollout found: (1) `macro_rules` alternatives are ordered by import order, so per-file
alternatives (EnvScanCore, EnvTac, ITac's `intro b hb; simp … at *; sx_addr`) ran before the generic
key route at ≈ 9 ms per success, and EnvTac's re-ran the whole `omega` route on every unsolvable goal;
(2) the same false miss-lemma probes also hit AllocTac's `sx_mem` and ITac's `ix_mem` (do-not-edit
files: they keep paying); (3) a tactic that replaces a hypothesis inside an `#ix_seg` piece
(`replaceLocalDecl`) introduces new locals that the continuation is abstracted over, and a later
`clear` silently fails: such tactics must add copies and clear them; (4) passing a general rewrite
(`evalSP_off' hfg`) to `sym_run … using` hit the heartbeat limit in simp on one piece and left the
post-state unnormalised (a changed generated statement) on another; (5) name clashes
(`StackGeom.lower` already exists for the 176-byte frame) and namespace shadowing (`RtErr.InpGeom`
under `open Vsa.RuntimeRepr`).

## 10. Measurements (base 8f4bb737 = 78f9fb97 sources → final cc110310; `exp-R11` a887b3ba+ adds only this document)

**Module CPU** (single file, one thread, base and final interleaved per file, 10 shards, min of 2, load
9–24; flagged files re-timed 5 rounds interleaved, E64; `~/syi-r11/final/`):

| | base | final | change |
|---|---:|---:|---:|
| the 62 target modules | 371.3 | 265.8 | **−28.4%** |
| Proof (20) / Env (16) / Call (22) / Loop (4) | 154.1 / 97.7 / 83.2 / 36.3 | 120.9 / 50.1 / 67.6 / 27.2 | −22% / −49% / −19% / −25% |
| primary held-out T (5) | 41.25 | 31.60 | −23.4% |
| fresh held-out T (5) | 96.84 | 66.64 | −31.2% |
| 251 affected modules outside the target (importers of SymInterp/KeyNF/FootKey/…) | 1,675.7 | 1,574.0 | −6.1% |
| new layer modules (FootKey, KeyNF, RegRead) | – | ≈ 4 | |

Largest: EnvDefineSpans 36.5 → 10.3, ProofStringify 50.3 → 38.2, EnvSetSpans 11.8 → 4.2, ProofNativePrint
18.9 → 11.4, CallPrefix 10.0 → 3.4, EnvGetSpans 9.9 → 3.7, LoopFor 15.2 → 10.7, ProofNativeAssert 16.7 →
12.2, ProofValueEqual 14.1 → 10.0; outside: SnpPrint 39.8 → 25.6, LeafArms 18.0 → 10.5, UnArm 16.5 → 10.8,
SnpSvf 59.8 → 53.4. **Per-file bound:** 5 files flagged in the two-round sweep (MallocPro, CallCloExit,
ExecExpr, SpecStringify, Case/CallArmP); re-timed five rounds interleaved: +0.0%, +3.9% (+0.11 s),
−2.6%, −1.3%, +0.0%. In the earlier outside sweep only `VsaIris/Stack.lean` stayed above +10% (1.06 →
1.19 s, +0.13 s: it gained the two `toNat_frame` lemmas); no file is over +10% and +0.2 s.

**Full clean build** (`rm -rf .lake/build` of the project's own modules, dependencies kept; all default
targets including executables; `LEAN_NUM_THREADS=10`; base and final alternated in two worktrees;
every run 0 errors, 0 `declaration uses 'sorry'`):

| commit | run | wall s | user s | load (1-min, start → end) |
|---|---|---:|---:|---|
| base 8f4bb737 (1,559 jobs) | 1 | 489.2 | 4,136 | 7.0 → 14.8 |
| | 2 | 671.7 | 4,803 | 15.0 → 23.3 |
| | 3 | 483.2 | 4,104 | 15.4 → 14.9 |
| final cc110310 (1,562 jobs) | 1 | 450.0 | 3,832 | 14.8 → 15.0 |
| | 2 | 482.8 | 4,000 | 23.3 → 15.4 |
| | 3 | 448.8 | 3,810 | 14.9 → 13.5 |
| **median** | | **489.2 → 450.0 (−8.0%)** | **4,136 → 3,832 (−7.4%)** | |
| min | | 483.2 → 448.8 (−7.1%) | 4,104 → 3,810 (−7.2%) | |

(The final also contains snapshot 10 of `exponentiate-next`, e4efc1f1, which changed only stdout/stderr
run tactics and ITac budget helpers.)

**Decision calls by issuer, census mode** (same spy as §1d, final tree): census user 365.7 → 259.3 s;
tactic-issued `omega` 52.5 → 4.1 s (`sx_run` 28.8 → 0.1, `sym_run1` 13.2 → 0.9, `sym_run` 8.3 → 0.9,
`ix_fwd` 1.3 → 0.3); `simp` issued by `sym_run1` 19.1 → 13.2, by `ix_fwd` 19.2 → 2.0, by `sx_run` 8.8 →
3.6; written `omega` 47.3 → 44.4 s (now the largest single item).

**Lines** (non-blank): the 62 target files 19,955 → 19,491 (−464, −2.3%; Proof 8,132 → 7,982, Env
4,041 → 3,957, Call 5,198 → 4,979, Loop 2,584 → 2,573). Layer code: `VsaIris/Vsa/FootKey.lean` 440 (new),
`VsaIris/Vsa/KeyNF.lean` 502 (≈ 490 moved unchanged from RegionTac/Region; RegionTac −509),
`VsaIris/Interp/RegRead.lean` 36, geometry lemmas and tactics +62 (Stack, SeqLoopClosure, SymInterp,
Repr ↔ SpecEnv move net 0). `git diff --shortstat e4efc1f1 cc110310 -- Vsa VsaIris`: 42 files, +1,469 /
−1,315.

**Axioms** (`lake env lean ~/syi-exp-logs/Ax.lean`, 14 lines): 12 theorems `[propext, Classical.choice,
Quot.sound]`, the two WhileLogic adequacy theorems `[propext, Quot.sound]`. Diff scan of this round's
changes (e4efc1f1..cc110310): no `sorry`, `axiom`, `native_decide`, `bv_decide`, `ofReduceBool`,
`maxHeartbeats`, `maxRecDepth` or `set_option`; no edit to Stdout/Tac, StepGen, AllocTac, ITac or
Stderr/*. `declaration uses 'sorry'`: 0 in every build log.

**Statements** (type hash of every constant of the `Vsa*` modules, base 8f4bb737 vs final, auxiliary
constants excluded; `~/syi-r11/hash/`): 43 changed types, 14 gone, 88 new, 137 moved. The 43: 42
interpreter run pieces and their run-chain lemmas restated with geometry records (`CallK_runA–D`,
`Call_run1/2`, `Call_runTM`, `CallN_run1/2`, `CallX_run1`, `ArgsLoop_runA/B`, `CloB_*`, `CloX_*`,
`CloE_runA/D`, `callCloHead_*`, `callPrefixT_*`, `callPrefixP_*`, `callNativeOut_p1–3`), every user in
the changed files (the full build checks it), none a headline or tool theorem; plus `nxRunCore` from
snapshot 10. Gone: `hoff'`, `StackGeom.lowerE`, `stackGeom_evalSP` (duplicates merged into
`StackGeom.lowerEval`), three auto-generated `congr_simp`, and snapshot 10's removed stdout tactic
syntaxes. Moved: the key normaliser (RegionTac/Region → KeyNF) and `RamWin` (SpecEnv → Repr), types
unchanged. All 12 held-out declarations keep their hashes.

**Gate** (`--root`): 12 → 12 firing clusters. The two target clusters shrank but still fire: `Call run`
13 → 8 lines per proof (both quarters), `Clo run` 13 → 9 first quarter, 10 → 7 last; the rule needs the
last quarter a third below the first, and a uniform restatement shrinks both (E70).

## 11. Decision

**Adopted:**

1. **Footprint keys (PA, rolled out by R1)** — the existing key normaliser made to reach the run
   tactics' side goals: `foot_key` as an `sx_addr`/`sx_side` alternative and first stage of `sym_run`
   geometry, `foot_or` as `ix_fwd`/`ix_mem`'s discharger, the region-free half of RegionTac moved down
   into `KeyNF`. Reasons by §0 (suite T, time): primary −20.0% and fresh −22.5% in the bake-off against
   −4.5%/−3.6% for the ontologists' datatype version (PB); whole target −20.7% for the combination and
   −28.4% after the rollout; 251 outside importers −6.1%; every file within the bound; clean build −7 to
   −8%. Setup 440 new lines (+ 490 moved).
2. **Geometry records as certificates (PC, rolled out by R2)** — `toNat_frame`/`toNat_frame_off`,
   `EvalFrameG.off`, `StackGeom.evalFrame`/`.lowerEval`, `RamWin.ofEnds`, `geom_open`/`with_geom`,
   `with_frame`; run-piece statements take records. Reasons: on its own cluster (the gate's two run
   clusters and the hand stack-geometry idiom) it removed ≈ 190 lines in the rollout plus 34 in the
   pilot for 72 setup lines, time-neutral. On the random held-out suite it bought −4 lines (fresh: 0):
   it is adopted for the run-piece statements and frame arithmetic, not as a general line saver.

**Not adopted:** PD's read-back/keep rules (`rd_back`, `reg_keep`) as a required route: −20 lines on
the primary suite, −9 (1.5%) on the fresh suite, 36 setup lines, 0.15–0.6 s per call against ≈ 20 ms
for the hand steps (two uses reverted for time in the pilot, three in the fresh cases). `RegRead.lean`
stays because six existing call sites use it at no measured file cost; new proofs should use the hand
`imgM_store_miss` chain or `rd_back` only where the file stays inside the bound. PB's atlas datatype
(its local-chart idea lives on inside `foot_key`). Translation-equivariant runs (not piloted).

Required route (to be written into CLAUDE.md / the discipline rules when the branch carries them, C1):

| task | use |
|---|---|
| a footprint / address side goal in a run tactic (`sx_side`, `sx_addr`, `sym_run` geometry, `ix_fwd`) | `foot_key` (automatic); never a per-file `sx_side` macro that unfolds the footprint |
| a stack-frame offset `(s + 2^64−c).toNat` | `toNat_frame rfl (…)` / `EvalFrameG.off` / `StackGeom.evalFrame`; never `rw [BitVec.toNat_add]; simp; omega` |
| a run piece's stack and pointer windows | `(hfg : EvalFrameG s)`, `RamWin a n`, `InpGeom`, with `with_geom`/`with_frame` in the body |

## 12. Where the cost is now, and round-12 targets

* **Written `omega`** (2,609 calls, 44.4 s of 259 s in census mode) is now the largest single item, as
  in round 10; most see a `%` hypothesis in context.
* **`sym_run1`'s own normalisation `simp`** (13.2 s, 764 failing calls) and `sx_run`'s (3.6 s): the
  successful passes, not the side goals.
* **The do-not-edit run tactics still pay the false-probe pattern** `foot_or` removed from `ix_fwd`:
  AllocTac's `sx_mem` and `sx_addr`/`bv1`/`bv2`, ITac's `ix_mem`/`ix_ro` (≈ 0.3–1.1 s per heavy file).
  When those files are free, routing their dischargers through `foot_or` is a one-line change each.
* **Lines**: the Iris/helper proofs' lines are spec-specific glue; agents' cleanup passes removed 8–20%
  of the drawn cases without any layer (incumbent debt, not an abstraction target); the per-function Ctx
  records' `hs1..hs4` windows did not pay to move to `StackGeom`.
* The gate's two run clusters need a baseline floor entry after this round (E70).
