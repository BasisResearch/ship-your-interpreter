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
