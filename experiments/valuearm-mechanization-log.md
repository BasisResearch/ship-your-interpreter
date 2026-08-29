# Value-arm mechanization — running progress log

Brief: `experiments/valuearm-mechanization-prompt.md`. Two hard gates at every phase
boundary: (1) `bash scripts/check_all.sh` = `check_all: OK`; (2) no elab regression
(every capstone ≤ its recorded baseline). Do NOT commit.

## STEP-0 baseline (verified green 2026-08-29)

- `check_all.sh` = **OK**, build **1086 jobs** (→ **1087** after Phase 0 adds
  `StackSlotGeom.lean`), **243/243** theorems axiom-clean
  `[propext, Classical.choice, Quot.sound]`. Tree green WITH all uncommitted changes.
- Elab baseline (from `experiments/valuearm-elab-baseline.md`, warm `.lake`,
  `set_option profiler true`, cumulative tactic-execution block):

  | decl        | file                          | tactic exec | type check | notes |
  |-------------|-------------------------------|-------------|------------|-------|
  | `blockC_mul`| `Vsa/Sim/rows/EvalMulRow.lean`| 71.6–84.2 s | 12.6 s     | ~200 omega @0.1–1.9 s each = the hog |
  | `blockC_div`| `Vsa/Sim/rows/EvalDivRow.lean`| 39.4 s      | 6.48 s     | same per-site geometry omega tax |
  | `evalMulSim`| `Vsa/Sim/rows/EvalMulRow.lean`| 284 ms      | 316 ms     | cheap composition wrapper |
  | `evalDivSim`| `Vsa/Sim/rows/EvalDivRow.lean`| 250 ms      | 296 ms     | cheap composition wrapper |

- State of the family: `blockC_div`/`blockC_mul` + `evalDivSim`/`evalMulSim` exist as
  hand-built INLINE tails (the shape Phase 4 must generate). Item-1 exists for **div only**
  (`EvalDivArm.lean`: `evalDivChain_run` + `evalDivChain_dispatch` + `divDispatchPost_of_chainEnd`).
  mod/eq/ne have dispatch segs (ModDispatchSeg/EqNeDispatchSeg) but NO item-1 and NO blockC.

## Phase 0 — kill the arm-tail omega hog (DONE ✅ 2026-08-29)

### Before/after elab (warm `.lake`, `set_option profiler true`, cumulative block)

Measured on a warm-olean single-file `lake env lean` (run-to-run band ~±15% on
`blockC_mul` per the baseline note; the drops here are ~6–8× so far outside noise):

| decl          | tactic exec BEFORE | tactic exec AFTER | speedup | omega calls (before→after) | omega time (before→after) | max omega >200ms after |
|---------------|--------------------|-------------------|---------|----------------------------|---------------------------|------------------------|
| `blockC_mul`  | **59.5 s**         | **7.8 s**         | **7.7×**| 76 → **0**                 | 46.4 s → **0 s**          | **NONE** (0 omega)     |
| `blockC_div`  | **35.8 s**         | **7.3 s**         | **4.9×**| 30 → 3                     | 28.5 s → 4.1 s            | 3 (2.15 s / 1.18 s / 0.78 s) |

(The `blockC_mul` baseline in the elab table above is the earlier 71.6 s/84.2 s
two-run band; re-measured immediately before the retrofit on this warm tree it was
**59.5 s** — that is the honest before-number for the 7.7× figure.)  `type checking`
also dropped: mul 9.96 s → 0.35 s, div 6.17 s → 0.81 s.  `evalMulSim`/`evalDivSim`
(the cheap composition wrappers) are untouched and still sub-second.

### Diagnosis

`set_option profiler true` on each decl + summing `omega took …` lines:
- **`blockC_mul`: 76 omega calls = 46.4 s of a 59.5 s tactic budget (78%).**
- **`blockC_div`: 30 omega calls = 28.5 s of 35.8 s (80%).**

Every one of them is a fixed-shape side-condition re-solved at a load/store site in
the row's ~50-hypothesis body (where each omega pays a large per-invocation +
context-scan cost — the elab-wall memo's mechanism).  The distinct fact classes:
1. **per-site geometry** `lo/hi/ht/win/al` of a spill slot `sp.toNat - K` (RAM bounds,
   htif-disjointness, 4/8-alignment) — the bulk;
2. **expr-relative geometry** of the two operand fetches `aExpr+8` / `aExpr+4`;
3. **store-vs-static-region disjointness** (code / value_int / __muldi3 images);
4. **per-`k` mem-frame disjointness** (`getElem_writeMap8_disjoint`/`read64_agreeP`
   window memberships in the StoreRepr / callee-saved-restore agreement proofs);
5. **scalar sp/SL arithmetic** (`1088 ≤ sp`, `sp-1088 = v2`, byte-shift reindexings,
   op-token byte splits, FrameBundle base geometry).

All are functions of `sp`/`SL`/`aExpr` + a constant against a FIXED small bundle of
stack-window bounds already present in the precondition.

### Fix — `Vsa/Sim/StackSlotGeom.lean` (NEW, axiom-clean, no maxHeartbeats/recDepth override)

Precompute each distinct fact ONCE in a **small-context lemma** (omega compiled into
the olean, or run against a ~7-field bundle), then have every site consume it by
`exact`/projection.  KEY discipline (learned the hard way — see below): keep the
number of *row-body* `have`s minimal, because every extra hypothesis re-slows every
remaining in-body omega (context bloat).  So facts are packed into **bundle
structures** built by ONE `have` each:

- `StackBounds sp SL` / `ExprBounds aExpr` — the input bound bundles (1 `have` each).
- `SlotGeom sp K` (+ `slotGeom8`) — `lo/hi4/hi8/ht4/ht8/win/al4/al8` for a slot
  `sp-K`; each site `(by rw [haddrK]; first | exact gK.lo | … | exact gK.al8)`
  (a cheap ≤8-way `exact`, no omega).  `exprGeom4` is the `aExpr+off` analogue.
- `SpArith sp SL` (+ `spArith`) — all scalar sp/SL facts (`sp1088`, `spLo`, `spHtif`,
  `SLlo40/32`, `e968`, `s3win`) in ONE bundle.
- `SlotWindows sp SL` (+ `slotWindows`) — the 12 store/s3 in-window + inter-slot
  disjointness facts for mul's five-store sequence, ONE bundle.
- `StoreRegionDis sp SL rlo rhi` (+ `storeRegionDis`) — the three store slots vs one
  static region, ONE `have` per region.
- Point helpers whose omega is baked into the olean (zero at callsite):
  `slotDisj_of_notInSL / notInStack / topWin / inRegion`, `notInSret_of_inRegion /
  window / frameWin / notInSL`, `notInDispWin_of_above`, `s3Disj_store`,
  `rpbShift`, `topSlotWin`, `armNorms`, `word32_split`, `frameBaseGeom`.
- Ground `K ≤ 1088` side-conditions switched `by omega` → `by decide`; monotone
  `sp-824 ≤ sp-40` via `Nat.sub_le_sub_left`, not omega.

`EvalMulRow` extracts `hSB/hEB/hAr` + the `gK`/`hSW`/`h*D` bundles once up front and
routes ~76 omega sites to projections → **0 omega**.  `EvalDivRow` does the same
(it reuses `evalDivChain_dispatch`, so it has a smaller store footprint) → **3 omega**.

### The one hog not fully removed (with the number + why)

`blockC_div` retains **3 omega** (2.15 s / 1.18 s / 0.78 s = 4.1 s total): the per-`k`
disjointness of the **static code/libgcc image regions** (`[0x80003164,0x80003fe0)`
etc.) from the stack window, in the `loaded_eval_expr_agreeP` / `loaded_*_agreeP`
closures (`(fun k hk => (hframeA k (by rcases hXStk with h|h <;> omega)).symm)`).
These are slow because the disjointness is *arithmetically near-false*: the
`sp ≤ regionLo` disjunct of `hXStk` cannot be ruled out from the bundle-level bounds
alone (verified: the same `rcases … <;> omega` FAILS in an isolated lemma given
`StackBounds` + all region hyps — omega finds a near-counterexample), so it is only
provable inside the **full row context** where some further hypothesis makes that
disjunct vacuous.  Extracting it to a small-context lemma is therefore impossible
without pinning down that hypothesis, and omega pays for the large case-split.  These
3 are the *only* remaining >200 ms omegas; `blockC_div` is still **4.9× faster** than
baseline and `blockC_mul` is **omega-free**.

### Gate

- `bash scripts/check_all.sh` → **`check_all: OK`** (build 1087 jobs; grep gate OK;
  **243/243 theorems axiom-audited**, allowed = `[Classical.choice, Quot.sound, propext]`).
- `#print axioms` on `blockC_mul`, `blockC_div`, `evalMulSim`, `evalDivSim` = all
  `[propext, Classical.choice, Quot.sound]`.

### Files touched
- NEW `Vsa/Sim/StackSlotGeom.lean` (the geometry-fact bundle library).
- `Vsa/Sim/rows/EvalMulRow.lean` — import + front-loaded bundles + site routing
  (frame/geometry discharge only; callee-seam + epilogue logic untouched).
- `Vsa/Sim/rows/EvalDivRow.lean` — same treatment.

## Phase 3 — `#derive_binop_item1`: entry-linkage + dispatch bridge (DONE ✅ 2026-08-29)

### The generator: `evalBinopChain_run` (`Vsa/Sim/BinopChainGen.lean`)

Chosen form: a SINGLE generic parameterised theorem (not a syntactic
metaprogram emitting 250-line tactic clones). `evalBinopChain_run` is a faithful
generalisation of `evalDivChain_run` reusing the arm-independent prefix blocks
`gtChainB1`/`gtChainB2a`/`gtChainB2b` VERBATIM (16 steps), with the FOUR data
points lifted to parameters and their per-op `decide`s to hypotheses:

- **Params**: `token idx slotAddr armPC : BitVec 64`, `t0..t3` (op-token bytes),
  `s0..s3` (jump-table slot bytes).
- **The four self-checking `decide` hypotheses** (a wrong byte makes the `decide`
  fail — self-checking, exactly as `divSlot_routes`):
  * `hTokVal  : bytesVal MKind.lw [t0..t3] = token`
  * `hIndexVal: sign_extend (extractLsb (bytesVal lw [t0..t3] + sext 0xff5) 31 0) = idx`
  * `hSlotAddr: (idx≪2 + (auipc+addi base)) = slotAddr`   (`= opTableBase + 4*idx`)
  * `hRoutes  : BitVec.update ((bytesVal lw [s0..s3] + 0x80019f84) + sext 0) 0 0 = armPC`
  plus `hBltu` (token bounds guard NOT taken), `sLo/sHi/sHt/sAl` (slot-addr RAM/
  htif/align bounds), `hRoutesAl` (routed target 4-aligned).
- **Generic helpers** `SlotPinned slotAddr s0 s1 s2 s3 m` / `binopLds1` /
  `binopLds2` generalise `DivSlotPinned` / `divLds1` / `divLds2`.
- **Routing `decide` parameterisation**: the terminator end-PC `rw` uses `hRoutes`
  (the `jr`-target); the slot `lw x15,0(x15)` effective address `slotAddr + sext 0`
  is bridged to `slotAddr` by `hsa0` (`sext 0#12 = 0`), so the slot pin/bounds are
  stated over `slotAddr` directly.
- **seg_frame_facts glue parameterisation** (the dispatch half): each op's
  `<op>DispatchPost_of_chainEnd` builds `SegFramePre <op>DispL` from the raw pins
  (GHolds by anon-constructor, `KeysOK` via `show KeysOK [..]; decide`) and runs the
  op's `<op>DispatchRow_frame` (fed by `<op>Dispatch_facts` = `seg_frame_facts …
  using fb`), exactly the `divDispatchPost_of_chainEnd`/`divDispatchRow_frame`
  pattern, parameterised per op.

### The div/mod vs eq/ne SHAPE SPLIT (handled per the brief's caveat)

- **div/mod family** (`Wr`/`Wl` operands, divisor `beqz` guard): the generic
  `evalBinopChain_run` covers the entry linkage; the strong post is
  `DivDispatchPost`/`ModDispatchPostS` (both carry `∃x12/x13`, `tick<2`,
  `sailOutput=out0`, callee-saved frame). mod's strong machinery
  (`ModDispatchPostS`/`modDispatchRowS`/`modDispatch_facts`/`modDispatchRow_frame`,
  `Vsa/Sim/ModDispatchStrong.lean`) is a verbatim clone of div's, swapping PCs
  (`0x800037dc→0x80003784`, `0x8000381c→0x800037c4`) + seg (`divDispatch→modDispatch`);
  a strong pin list `modDispLS` adds the `(12, 15)` op-token pin the `∃x12` reads.
  The divisor-nonzero residual is `Wr ≠ 0` (supplied by caller).
- **eq/ne family** (`sp`/`bufa`/`bufb`, single block, no guard): hand-instantiated
  against `eqDispatchRow`/`neDispatchRow` following the same `_frame` recipe
  (`Vsa/Sim/EqNeDispatchStrong.lean`: `EqDispatchPostS`/`NeDispatchPostS` +
  `eqDispatchRowS`/`neDispatchRowS` + `eqDispatchRow_frameS`/`neDispatchRow_frameS`,
  `neDispatch_facts`). Strong post = `x10=bufa=sp+0x40`, `x11=bufb=sp+0x20`,
  `x2=sp`, `tick<2`, `sailOutput=out0`, callee-saved frame; NO `∃x12/x13`, NO
  divisor guard. The generic entry linkage lands the div/mod-flavoured pins
  (`x16=2/x10=2/x17=Wr/x19=Wl`) but eq/ne's arm reads only `x2=sp`; extras unused.

### Per-op data table (authored from the binary)

Source: tokens `Vsa/MemRepr.lean:63` (`binOpTok`); `opTableBase = 0x80019f84`
(`EvalBinSim2.lean:77`); arm PCs `experiments/binop-value-tail-wiring.md` + each
dispatch seg header. index = token−11, slotAddr = opTableBase + 4*index, slot bytes
= little-endian `(armPC − opTableBase)` as Int32 (self-checked by the `hRoutes`
`decide`).

| op  | token | index | slotAddr    | slot bytes    | armPC (arm exit) |
|-----|-------|-------|-------------|---------------|------------------|
| div | 14    | 3     | 0x80019f90  | 58 98 fe ff   | 0x800037dc (→0x8000381c) |
| mod | 15    | 4     | 0x80019f94  | 00 98 fe ff   | 0x80003784 (→0x800037c4) |
| eq  | 19    | 8     | 0x80019fa4  | 60 97 fe ff   | 0x800036e4 (→0x8000371c) |
| ne  | 17    | 6     | 0x80019f9c  | b0 97 fe ff   | 0x80003734 (→0x8000376c) |

### Item-1 bridges landed (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

| op  | full-span bridge         | file               | generated vs hand |
|-----|--------------------------|--------------------|-------------------|
| div | `evalDivChain_dispatch`  | `EvalDivArm.lean`  | HAND (reference, unchanged); ALSO reproduced by `evalDivChain_run_gen` (BinopChainInstances) — generator validated |
| mod | `evalModChain_dispatch`  | `EvalModArm.lean`  | GENERATED (entry via `evalBinopChain_run`) |
| eq  | `evalEqChain_dispatch`   | `EvalEqNeArm.lean` | GENERATED |
| ne  | `evalNeChain_dispatch`   | `EvalEqNeArm.lean` | GENERATED |
| mul | `evalMulChain_run` (embedded in `blockC_mul`) | `EvalMulChain.lean` | ALREADY PRESENT (hand, token 13/idx 2/slot opTableBase+8/bytes b0 98 fe ff/arm 0x800037dc→0x80003834); NOT duplicated |

The generator (`evalBinopChain_run`) + strong dispatch machinery for mod/eq/ne are
all new; the div item-1 (`EvalDivArm.lean`) is kept as the untouched reference and
independently reproduced by `evalDivChain_run_gen` (same statement, proved via the
generator) to prove generator reproduction.

### Elab table (warm `.lake`, `set_option profiler true`, single-file)

| decl                       | tactic exec | notes |
|----------------------------|-------------|-------|
| `evalDivChain_run` (HAND baseline) | **692 ms** (+60 ms type check) | the div item-1 entry linkage, hand |
| `evalDivChain_dispatch` (HAND baseline) | ~18 ms | pure composition on top of the entry linkage |
| `evalBinopChain_run` (GENERATOR) | **669 ms** | the SHARED heavy proof; elaborates ONCE for all ops |
| `evalDivChain_run_gen` (div instance) | **~20 ms** total | 34× cheaper than the hand entry linkage |
| `evalModChain_dispatch` | **~43 ms** | full-span; ≤ div baseline |
| `evalEqChain_dispatch`  | **~35 ms** | full-span; ≤ div baseline |
| `evalNeChain_dispatch`  | **~35 ms** | full-span; ≤ div baseline |

Every generated item-1 bridge (mod/eq/ne, ~35–43 ms) is FAR under the div item-1
baseline (692 ms entry linkage). The generator amortises the 16-step block-soundness
proof: pay ~670 ms once in `BinopChainGen`, then each op costs one composition.

### Gate

- `bash scripts/check_all.sh` → **`check_all: OK`** (build **1093 jobs**, up from
  1087; stage-b grep gate OK, 977 files; **stage-c 259/259 theorems audited**,
  allowed = `[Classical.choice, Quot.sound, propext]` — up from 243/243, +16 new
  Phase-3 capstones).
- All new capstones registered in `scripts/check_all.sh` THEOREMS with provenance
  (the PHASE-3 block).

### Files added
- `Vsa/Sim/BinopChainGen.lean` — the generator `evalBinopChain_run` + `SlotPinned`/
  `binopLds1`/`binopLds2`.
- `Vsa/Sim/BinopChainInstances.lean` — `evalDivChain_run_gen` (div validation).
- `Vsa/Sim/ModDispatchStrong.lean` — strong mod post/row/frame (`modDispLS`,
  `ModDispatchPostS`, `modDispatchRowS`, `modDispatch_facts`, `modDispatchRow_frame`).
- `Vsa/Sim/EvalModArm.lean` — `modDispatchPost_of_chainEnd` + `evalModChain_dispatch`.
- `Vsa/Sim/EqNeDispatchStrong.lean` — strong eq/ne posts/rows/frames.
- `Vsa/Sim/EvalEqNeArm.lean` — eq/ne `_of_chainEnd` glue + `evalEqChain_dispatch`/
  `evalNeChain_dispatch`.
- `Vsa.lean`: imports added; `scripts/check_all.sh`: 16 THEOREMS entries added.

### Note on the API shape
The brief's requested `#derive_binop_item1 <op> <token> <jtSlotAddr> <armPC>`
command is realised as the parameterised theorem `evalBinopChain_run` + per-op
`_of_chainEnd`/`_dispatch` instantiations rather than a `#command` macro: since the
four data points enter as ordinary term arguments and the per-op `decide`s are
`by decide`, a Lean elaborator command would add no leverage over direct
instantiation while risking the "emit plain terms, not deep tactic blocks" law.
The instantiation IS the generator invocation (one `evalBinopChain_run` application
+ four `by decide`s per op), which is exactly the "swap the 4 data points" contract.

## Phase 4a — `derive_binop_all` tail generator (`intBoxEpilogue`), validated on div + mul (DONE ✅ 2026-08-29)

### The generator: `intBoxEpilogue` (`Vsa/Sim/BinopTailGen.lean`)

Chosen form (per the Phase-3 precedent + the VERDICT): a SINGLE parameterised
generic theorem, NOT a `#command` macro. It reproduces the maximal SHARED,
op-independent SUFFIX of every int-box binop value tail — the segment that is
byte-for-structure-identical between `blockC_mul` and `blockC_div`:

    value_int (call) ; ld s3,0x418(sp) ; j 0x800033ec   →   PreEpilogueVD

i.e. everything from the `value_int` ENTRY config `τ0` (PC=0x8000280c) through
`value_int_spec`, the `s3` restore, the exit jump, and the full `PreEpilogueVD`
transport packaging. Each arm's op-specific FRONT (entry linkage + dispatch +
strong callee spec `muldi3_spec`/`divdi3_spec` + the pre-`value_int` `mv` shuffles +
the `jal value_int` site itself) STAYS INLINE at the call site — that front is where
div/mul genuinely diverge (different callee, different memory reach-back: mul threads
through m5's 5 `writeMap8`, div through `divDispatch_mem_frame`; the VERDICT's
"assemble inline like blockC_mul"). The generator hoists only the ~120-line tail
marshalling both arms did IDENTICALLY into ONE proof, elaborated once.

### Descriptor schema (the theorem's parameters — a plain Lean signature, no DSL)

`intBoxEpilogue` takes:
- **ghosts/layout**: `g` (arm-entry/epilogue-restore ghost), `N A SL φf φc φfm φcm
  φf' φc' st' st''`, `sp r sret v8 v9 v18 v19 w19`, `pay` (boxed payload), `boxed :
  Int` (source value), `out0 m0`.
- **the box entry config** `τ0 : Config` + `boxLink : BitVec 64` (value_int's return
  link = the ld PC).
- **suffix descriptor** (the op-varying data): `ldPC jPC : BitVec 64`, `jImm : BitVec
  21`, and the TWO suffix site lemmas passed as ordinary term args of named
  abbrev-signatures `LdS3Site ldPC` / `JExitSite jPC jImm` (so their heavy per-site
  `decide`s live in `DivTailSites`/`MulTailSites`, elaborated ONCE there, never re-run
  in the generic proof); plus the small self-checking bridges `hboxLink : boxLink =
  ldPC`, `hldPCupdate` (int_post PC-clear = ldPC, `by decide` at callsite),
  `hldAfter`/`hjTgt`/`hjTgtAl`/`hldPCeq` (PC arithmetic, `by decide`/existing addr
  lemmas).
- **int_pre pieces at τ0** (register/mem/tick/output pins) + `hval_bridge :
  (BitVec.ofNat 64 pay.toNat).toInt = boxed` (the op's produced-value lemma:
  `div_wrap_bridge` / `mul_wrap_bridge`).
- **the arm's transport of `τ0.mem` back to `c`/`m0`/store** (`hSurvSL0`, `hs3τ0`,
  four spill reads, `hMemExt0`, `hmemframe0`) + the **frame collapse** `hframeGτ0 : ∀
  R≠x19, AbiPreservedNoise → τ0.regs = g R` (the caller threads its op-specific front
  + callee frames up to τ0; the value_int frame + the x19 restore are handled
  INTERNALLY).
- **geometry** consumed from Phase-0's `StackSlotGeom` bundles (`hSLlo40/32`,
  `hsp*`, the four ld-slot bounds = `g40.lo/hi8/ht8/al8`).

### The VERDICT's key move (how `int_pre`'s ghost is built inline)

`int_pre`'s frame `∀ R, NotWrittenV R → regs = g R` is provable ONLY for `g` = the
value_int-ENTRY register snapshot. `intBoxEpilogue` builds `int_pre` INTERNALLY with
`gbox := fun R => τ0.σ.regs.get? R`, closing its frame by `fun R _ => rfl` — the box
ghost is bound to the runtime entry config, NEVER a universally-quantified shared
premise. That is exactly why the fixed-ghost `divValueTail` combinator could not host
`stage`/`suf` but this parameterised theorem can. `intPostToEpilogue` (Phase-0's
shared epilogue packager) is consumed at the end with the arm's `g`.

### The div + mul descriptors (concrete instantiations)

| op  | τ0 (box entry)            | ldPC/jPC/jImm                    | ld/j site lemmas          | boxed value             | bridge |
|-----|---------------------------|----------------------------------|---------------------------|-------------------------|--------|
| div | `⟨τ3,j3,…⟩` @0x8000280c    | 0x8000382c/0x80003830/0x1ffbbc   | `site_8000382c/30_ee` (DivTailSites) | `wrap64 (a.tdiv b)` | `div_wrap_bridge` |
| mul | `⟨τ19,j19,…⟩` @0x8000280c  | 0x80003880/0x80003884/0x1ffb68   | `site_80003880/84_ee` (MulTailSites) | `wrap64 (a*b)`      | `mul_wrap_bridge` |

Both arms now END with one `intBoxEpilogue` application (replacing their prior
~120-line hand `value_int_spec … intPostToEpilogue` tail); the front (dispatch +
callee seam) is unchanged.

### Before/after elab (warm `.lake`, `set_option profiler true`, cumulative block)

| decl        | POST-PHASE-0 hand baseline | GENERATED (intBoxEpilogue) | Δ |
|-------------|----------------------------|----------------------------|---|
| `blockC_div`| **7.25 s** tactic exec (0.84 s tc) | **5.33 s** (0.80 s tc) | −1.92 s (**−26%**) |
| `blockC_mul`| **7.83 s** tactic exec (0.20 s tc) | **7.07 s** (0.17 s tc) | −0.76 s (**−10%**) |

Both generated arms are UNDER the post-Phase-0 hand baseline — no regression; the
shared marshalling now elaborates once in `intBoxEpilogue` (its own elab, single
file, ~constant) instead of twice inline. `evalDivSim`/`evalMulSim` unchanged
(cheap composition wrappers).

### Gate

- `bash scripts/check_all.sh` → **`check_all: OK`** (build **1094 jobs**, up from
  1093 for the new `BinopTailGen.lean`; stage-b grep gate OK, 978 files; **stage-c
  260/260 theorems audited**, allowed = `[Classical.choice, Quot.sound, propext]` —
  up from 259/259, +1 for `intBoxEpilogue`).
- `#print axioms` on `blockC_div`, `blockC_mul`, `evalDivSim`, `evalMulSim`,
  `intBoxEpilogue` = all `[propext, Classical.choice, Quot.sound]`.
- New capstone `Vsa.Sim.intBoxEpilogue` registered in `scripts/check_all.sh`
  THEOREMS with provenance (PHASE-4a note).

### Files added / touched
- NEW `Vsa/Sim/BinopTailGen.lean` — `intBoxEpilogue` + the `LdS3Site`/`JExitSite`
  suffix-site abbrev-signatures.
- `Vsa/Sim/rows/EvalDivRow.lean` — tail (lines ~550–757 of the hand body) replaced
  by the τ3-level transport derivations + one `intBoxEpilogue` call; import added.
- `Vsa/Sim/rows/EvalMulRow.lean` — same treatment at τ19; import added.
- `Vsa.lean`: `import Vsa.Sim.BinopTailGen`. `scripts/check_all.sh`: +1 THEOREMS entry.

### For the fan-out stage (mod/eq/ne) — divergences noted

- **int box (mod)** reuses `intBoxEpilogue` VERBATIM: mod's box is also `value_int`,
  its tail is `value_int_spec ; ld s3 ; j 0x800033ec` with a `mod` produced-value
  (`binOpSem_mod_int`, `wrap64 (a.tmod b)`); only the descriptor (ldPC/jPC/jImm +
  ModTailSites site lemmas + the mod front) changes. NO generator change needed.
- **bool box (eq/ne)** needs a SIBLING `boolBoxEpilogue`: the box is `value_bool`
  (not `value_int`), so `int_pre`/`value_int_spec`/`intPostToEpilogue` become
  `boxBool_pre`/`value_bool_spec_full`/`boolPostToEpilogue` (the last must be built —
  the `value_bool` analogue of `intPostToEpilogue`). ne additionally inserts a `seqz
  a1,a1` before the box `jal`; that extra site lands in the arm's FRONT (before τ0),
  so `boolBoxEpilogue` stays seqz-agnostic — same clean cut as here. The
  `LdS3Site`/`JExitSite` abbrevs + the whole suffix-transport skeleton port
  unchanged; only the box-spec triple differs.
- One shared param subtlety to preserve: the ld immediate is HARD-CODED `0x418` in
  `LdS3Site` (both div and mul restore s3 from `0x418(sp)`); if a future op uses a
  different s3-restore offset, `LdS3Site` must be parameterised by the imm too.
