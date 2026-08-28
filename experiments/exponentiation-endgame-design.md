# Exponentiation design — collapsing the M4/M5 endgame to a mechanical fan-out (2026-08-28)

**Premise (from `M4-M5-endgame-plan.md` + grounded audit).** The whole L0–L8 stack is assembled;
`InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam : InterpSim L` is a complete
theorem, `LayoutInstance` pins the concrete `Layout`+`GeomFacts`. "Completion" = discharging four
residual bundles (`hterm`, `htri`, `hdivFam`, `herrFam`). The naive reading is "dozens of bespoke
~200-line RISC-V machine proofs = multi-week". This document shows why that is **wrong**: every leaf
is one of **four machine-code shapes**, three of which are already ~90 % covered by existing reflection
tooling that simply wasn't applied uniformly. The exponentiation is to finish the v2 metaprogram layer
and standardise all leaves onto it.

## The four shapes (every remaining leaf is one of these)

| Shape | What | Leaves | Existing tool | Residual |
|-------|------|--------|---------------|----------|
| **A** straight-line→terminator segment | ALU/load/store body + fixed-polarity branch/jump | eval/exec case bodies, exit spans | `#derive_case`→`name_seg` (`DeriveCase.lean`) + `block_facts` | data byte-pins, store windows, branch guards (per-site data); marshal into case pre/post `Triple` |
| **B** error-site → `runtime_error` → exit(70) | Shape-A body + one `jal runtime_error` | **all 42 error sites** (13 done as rows, 29 left) | `#derive_case` body + `errHalts_exists_of_site` capstone (`ErrorSites.lean`, shared SC/HT/exit proven ONCE) | the per-site `T : Triple SitePre (RuntimeErrorAt …)` + reachability `hsite` |
| **C** scan loop | `Triple.loop` over one back-edge basic block | env_define scan, env_get scan, exec/for loops | `bblock_sound_bt` with `tgtPC=head` IS the loop body (`BlockTerm.lean:78`) | one loop-invariant+measure **per loop shape**, not per site |
| **D** call/marshal w/ callee contract | `jal rd` splice: `prefix ≫ callee ≫ suffix` | closure body-IH, native calls, env_new/env_define/realloc compose | `Triple.seq` (structural); `callClosureSim` already does exactly this | name the callee contract; the seq is free |

Key measured facts behind the table:
- **`#derive_case name chain [blk] ;; [blk] …`** (`DeriveCase.lean:83`) emits `def name : List BBlock` +
  `theorem name_seg` in `SegEvalState` normal form (canonical write-log, computed regs, computed end PC).
  Residual obligations: `ChainFacts` (code pins, decode, guards, store windows) + ONE `decide` (`ChainOK`).
  Reach: straight-line ALU/load/store bodies + all 6 conditional branches / `j` / `jr` terminators, multi-block
  chains with contiguity checked by one `decide`. **No** loops, **no** `jal rd` (by design).
- **`block_facts h with "<prefix>"`** (`BlockTactics.lean:88`) already auto-closes the *mechanical* half of
  a block's facts (code byte pins + decode) from ONE loaded-image hypothesis (e.g. `Eval_exprLoaded σ.mem`).
  Used throughout `EvalAddChain.lean`. This is the tool that kills the dominant per-site threading tax.
- **All 42 error sites are isomorphic** (confirmed): each is `RuntimeErrorAt g inp m0` = "machine parked at
  `runtime_error` entry `0x80002da8` with `x10=inp`, memory pinned, callee-saved captured", reached by a short
  straight-line prefix ending in `jal runtime_error`. They differ ONLY in (site PC, prefix bytes, routing
  precondition). `errHalts_exists_of_site` (`ErrorSites.lean:118`) already reduces "site reached → `Halts c _ 70`"
  to just `T`+`hsite`, with the whole runtime_error→longjmp→exit(70) tail proven once as `SC`/`HT`/`ExitStoreHalts`.
- **The DONE eval rows predate full `#derive_case` adoption** — they hand-thread `bblock_sound_bt` chains
  (~1000-line chain file + ~800-line row file, ~2–2.5× manual overhead). i.e. the lever largely EXISTS; the
  rows just weren't rebuilt on it. `DeriveCase.lean:33-36` explicitly names the missing piece:
  > "The pre/post/value-fn `Triple`-closing layer (marshalling the computed outcome into the case's
  > `SubEvalReturn`/`PreEpilogueV` shapes) is composed per row from `name_seg` + `FrameCalc`/`geom`;
  > **folding it into this command is the v2 extension once real rows exist.**"

## The exponentiation — four metaprograms (build order)

1. **`#derive_error_site name [body pairs] jal_pc`** (Shape B; unlocks the 29-site fan-out — biggest single chunk).
   Extends the `#derive_case` elaborator to append the terminating `jal runtime_error` and wrap the emitted
   `name_seg` outcome into `T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c')`. Per site becomes:
   paste disassembly block table (script-generatable from `objdump`) + one command + instantiate. ~1000 lines → ~5.
   The only genuinely-semantic residual is `hsite` (routing: "dispatch arm at PC with flag set"), itself a
   uniform shape across sites.

2. **`chain_facts` tactic** (lift `block_facts` from `BBlockFacts` to the whole `ChainFacts` bundle).
   One tactic closing `ChainFacts σ.mem σ.mem L lds name` from `Eval_exprLoaded`(image) + `GeomFacts`(geometry) +
   the computed pin list. Removes the ~400–600-line per-block threading tax that dominates the current chain files.

3. **`#derive_case` v2 (fold marshalling)** — emit `name_row : Triple (pre) (post)` directly, composing
   `name_seg` + `FrameCalc.of_writeLog` + `geom` internally. Collapses each eval/exec case (and the remaining
   mechanical binary ops eq/ne/mul/div/mod) from ~1800 lines to one command + block table.

4. **`#derive_loop` / `#derive_call_seg`** (Shapes C/D) — `Triple.loop` wrapper over a back-edge block, and a
   `jal rd` splice that seq-composes a named callee contract. Needed for env_define scan + closure body-IH +
   env_new/realloc. A handful of invariants/contracts, not dozens of proofs.

## Why this is "a single easy, manageable task"

Once (1)–(3) exist, discharging a leaf = **paste disassembly table → one command → `decide`**. The 29 error
sites and the remaining eval/exec cases become a mechanical, script-driven fan-out (per the coordination
protocol: bounded worktree agents, one leaf each). The genuinely-novel residuals shrink to a **bounded,
enumerable set**: ~4 loop invariants (Shape C), ~3 callee contracts (env_new/env_define/realloc, Shape D),
the reachability links (`hsite` per site + `hEntryHalts` once), and the two classical facts (`Trichotomy`,
`DivFamily`). That is a finite, dividable to-do list — not an open-ended multi-week grind.

## Proof-of-concept — LANDED (2026-08-28)

The reusable **core** of metaprogram (1) is landed as a plain higher-order lemma (the command is a thin
wrapper over it, exactly as `errRow` wraps `errHalts_exists_of_site`): **`Vsa/Sim/ErrorSiteJal.lean`**,
green + axiom-clean (`{propext, Classical.choice, Quot.sound}`), integrated into `Vsa.lean`.

- `JalErrPre g inp m0 pcJal b0 b1 b2 b3 c` — the "parked at the site's `jal runtime_error`" precondition
  (ErrorIn ptr in `x10`, memory `m0`, callee-saved ghost frame `g`, tick/minstret budget, jal byte-pins).
- `jalStep_to_runtimeError … : Triple (JalErrPre …) (fun c' => RuntimeErrorAt g inp m0 c')` — the single
  `jal runtime_error` step, marshalled to ALL TEN `RuntimeErrorAt` conjuncts ONCE (PC=`0x80002da8` via
  `obs_jal_pc`+target identity; `x10`/`mem`/loaded-images preserved; the `g` frame transported across the
  jal via `post_jal_other` over every `NotWrittenJmp` register). Per-site inputs are only the jal's own
  decode data + the target identity — uniform across all 42 sites.
- The bundled `example` proves the payoff: each row's assumed `T` is now literally
  `Triple.seq prefix_seg jalStep_to_runtimeError`. **The bespoke ~200-line per-site marshalling (which NO
  site had ever executed — every row took `T` as a hypothesis) collapses to one `Triple.seq`.**

This validates Shape B's exponentiation on the largest isomorphic chunk (42 sites). Remaining for a full
error-site fan-out: each site's `#derive_case` *prefix* `Triple SitePre (JalErrPre …)` (L3 elaborator +
`block_facts`, mechanical) and the reachability `hsite` (uniform "dispatch arm at PC with routing flag").

### Bonus fix (pre-existing integration bug, unrelated to the above)
`Vsa/Sim/rows/EvalLtRow.lean` (defining `blockC_lt`/`evalLtSim`, the `.lt` eval case) was **orphaned —
imported nowhere** after its relocation out of `EvalBinSim4`, while siblings `EvalLeRow`/`EvalGtRow` were
wired in. So the `.lt` case was absent from the built tree and `check_all` stage (c) had been failing on
`Vsa.Sim.blockC_lt`/`evalLtSim`. Added the missing `import Vsa.Sim.rows.EvalLtRow` to `Vsa.lean`. Now:
`lake build Vsa` = **1054 jobs** green; `check_all` OK, **192/192** theorems axiom-clean.

## v2 metaprogram layer — build progress

- **(1) `chain_facts` — LANDED (2026-08-28), `Vsa/Sim/ChainFactsTac.lean`.** The `block_facts` walker lifted
  from a single block's `BBlockFacts` to the whole `ChainFacts σ.mem σ.mem L lds name` bundle a
  `#derive_case`-emitted `name_seg` carries: `chain_facts h with "<prefix>"` closes every mechanical
  byte-pin/decode leaf across the chain from ONE loaded-image hypothesis, leaving only the data-dependent
  MemFacts/guards as goals. Demo `chainFactsDemo_facts`/`chainFactsDemo_row` (real eval_expr ALU segment)
  green + axiom-clean. This kills the dominant per-block threading tax. Callers must import the DecodeTable
  batches covering their words (as `block_facts` callers already do).
- **(2) `#derive_error_site` — LANDED (2026-08-28), `Vsa/Sim/DeriveErrorSite.lean`.** Command
  `#derive_error_site name (pc,word,imm) (b0,b1,b2,b3) decodeLemma` emits
  `theorem name : ∀ g inp m0, Triple (JalErrPre …) (RuntimeErrorAt g inp m0)` by instantiating
  `jalStep_to_runtimeError` — all `by decide`/`hword`/`htgtEq`/`hdec` args filled from the table. Demo on the
  REAL `0x800034e4` site (`decode_8c5ff0ef`) green + axiom-clean. Per-site jal-step boilerplate (~15 lines)
  → one command line. Scope: emits the uniform jal-step tail only; the prefix→`JalErrPre` bridge stays
  per-site (x10=inp is set by the node dispatch *before* the prefix, not recoverable from a generic
  `SegEvalState`). A row's `T` = `Triple.seq <prefix_seg> (name g inp m0)`.

Both integrated into `Vsa.lean`; full build **1056 jobs** green, `check_all` OK, **192/192** axiom-clean.

- **(3) `segToTriple` marshalling fold — LANDED (2026-08-28), `Vsa/Sim/DeriveCaseRow.lean`.** Bridges a
  `#derive_case` seg outcome into `Triple (SegPre bs L lds pc0 m0) Q`: `SegPre` is the parked-at-entry
  `Config` precondition (GoodState/PC/minstret/GHolds/ChainFacts/mem=m0/tick<2), and `hpost` reads the
  computed end-PC / `out.regs` (via `gholds_lookup`) / `writeLog m0 out.log` off the outcome. `hwf : ChainOK`
  stays the row's one kernel `decide` (not decidable until concrete — the intended row pattern). Demo
  `demoChainRow` on `demoChain` (reads `x7=3`, end-PC, mem) green + axiom-clean. This folds the seg→Triple
  marshalling DeriveCase.lean:33-36 named.
- **(4a) `loopFromBody` — LANDED (2026-08-28), `Vsa/Sim/DeriveLoop.lean`.** Shape C: thin over `Triple.loop`
  in the machine dialect — invariant `I`, guard `B`, measure `μ : Config → Nat`, per-iteration body Triple
  `∀ n, Triple (I∧B∧μ=n) (I∧μ<n)` → whole-loop `Triple I (I∧¬B)`. Plus `loopFromStepBody` (front door for a
  raw `Step`-shaped body, the `stepObs_*` output shape) and `regMeasure` (counter-GPR countdown). Demos
  `countdownLoop`/`regCountdownLoop` green + axiom-clean. Per-loop residual = the body oracle (one
  `bblock_sound_bt` back-edge run + measure-decrease arithmetic), which `LoopStep.loopStep` already produces.

All four integrated into `Vsa.lean`; full build **1058 jobs** green, `check_all` OK, **192/192** axiom-clean.

- **(4b) `callSeg` — LANDED (2026-08-28), `Vsa/Sim/DeriveCallSeg.lean`.** Shape D: the `prefix ≫ callee ≫
  suffix` call-splice extracted from `callClosureSim`'s hand-rolled `Triple.seq (Triple.seq pre callee) suf`
  into a reusable combinator, plus `callSegConseq` (seam-massaging variant threading the callee contract
  over its own boundary predicates via `Triple.conseq` — the real case where the body IH's SegEntry/SegExit
  are only propositionally equal to the prefix post / suffix pre). Demo `callClosureSimShape` reproduces the
  closure crux's exact composition over placeholder predicates. Green + axiom-clean. Pure `Triple` algebra,
  no reflection. Substituting the concrete CallEntryP/SegEntry/SegExit/CallExitP gives back `callClosureSim`.

All five integrated into `Vsa.lean`; full build **1059 jobs** green, `check_all` OK, **192/192** axiom-clean.

## v2 layer status — COMPLETE (all five combinators exist and fire, one per shape + facts + marshalling)
`chain_facts` (facts) · `segToTriple` (seg→Triple marshalling) · `#derive_error_site` (Shape B) ·
`loopFromBody` (Shape C) · `callSeg` (Shape D). Each is green, axiom-clean, and demonstrated firing
end-to-end. What each leaf
now needs, per shape: paste its objdump block table → `#derive_case`/`#derive_error_site` → `chain_facts`
closes the mechanical facts → `segToTriple`/`loopFromBody` marshals into the case Triple → one `ChainOK`
`decide`. The genuinely per-leaf residuals shrink to: the routing precondition (`hsite`/`SitePre`), the
loop invariant+measure+body-oracle per distinct loop, and the concrete seam predicates.

## PROVEN ON A LIVE LEAF (2026-08-28) — `Vsa/Sim/ErrorSiteApplied.lean`
`row_hNegType_applied` is the `EvalErr.negType` error-site row (real `0x800034e4` jal site) with its
`(T : Triple SitePre (RuntimeErrorAt …))` hypothesis **ELIMINATED** — supplied internally by the generated
`errSite_800034e4 g inp m0` (which `#derive_error_site` proves unconditionally). Its conclusion is the exact
`errorSimFull` minor-premise `∀`-closure, byte-identical to `row_hNegType`, but the ~200-line bespoke
jal→`RuntimeErrorAt` machine marshalling that every prior row merely ASSUMED is now a proved term. Green +
axiom-clean, integrated in `Vsa.lean` (build **1060 jobs**, `check_all` OK, **192/192**). This is the
multiplier demonstrated on live code, not a demo: one real conditional residual converted to discharged.
Residuals unchanged and shared: `SC`/`HT` (the same two L7/L8 facts for all 42 rows) + `hsite` (the M4-side
caller linkage that `c` is parked at this node's jal).

## FAN-OUT EXECUTED — all 18 remaining sites (2026-08-28), `Vsa/Sim/rows/ErrSitesBatch{0..3}.lean`
The objdump scout found **19 distinct `jal runtime_error` sites** (not 41 — the "42" are the minor
premises; the distinct jal PCs are 19), all `rd=x1`, all with `decode_<word>` lemmas present, spanning
`0x80002e90..0x80003fdc`. One (`0x800034e4`) was already done. The other **18** were generated by a
**massively-parallel COW-clone workflow** (`error-site-fanout`, 4 workers): each worker made an APFS
`cp -c` clone of the repo with warm `.lake` oleans, wrote its `#derive_error_site` batch, verified with
`lake env lean` (never `lake build` — no lock contention), staged the verified file to `/tmp`, and returned
structured status only (never touching the main repo — clear no-delete protocol). All 4 batches green
first try, all COW clones worked (no fallback). Coordinator joined serially: copied staged files into
`Vsa/Sim/rows/`, added imports, ran ONE full build. Result: **`errSite_<pc>` proved for ALL 19 sites**,
full build **1064 jobs** green, `check_all` OK, **192/192** axiom-clean. The complete library of proved
per-site jal→`RuntimeErrorAt` Triples now exists — every error row's assumed `T` is now a supplied term
(cf. `ErrorSiteApplied.row_hNegType_applied`).

## Binary-op eval-case fan-out — CALIBRATION VERDICT (2026-08-28): NOT a clean fan-out
Unlike the 19 isomorphic error sites, the open binary-op eval cases (eq/ne/mul/div/mod/ge) are
heterogeneous and mostly need bespoke work. Pilot findings:
- **ge** — the XORI base-infra blocker is now CLEARED (2026-08-28): `MKind.xori` added to the block-reflection
  decoder (BlockMem `MKind`/`astOfM`/`wvalM`/`MemFacts`/`KindOK`/`Decidable` + the soundness `cases` branch
  reusing the pre-existing `execute_itype_xori_char`; BlockDecode `decodeM` opcode 0x13/funct3=4; the three
  ALU-frame `cases` alternatives in BlockTerm + the one in LoopStep). Full build 1064 jobs green, check_all
  192/192 axiom-clean. So `ge` is now a genuine lt/le/gt clone (token 23, arm shares 0x80003628, dispatch
  takes the beq @0x80003648, fixup falls through to `not;srli`) — no longer blocked.
- **mul — LANDED (2026-08-28, commit 7a96b72).** The "arithmetic-with-libgcc-call" shape is now a proved
  leaf in the build path: `evalMulSim`/`blockC_mul` (`Vsa/Sim/rows/EvalMulRow.lean` + `EvalMulChain.lean` +
  `MulTailSites.lean`), the `EvalE.binary .mul` int case as `blockB_binary ≫ blockC_mul ≫ blockD_v_rec` in
  the EvalIH motive shape — sibling of gt/add/sub/lt/le. `blockC_mul` threads the `jal __muldi3` Shape-D
  callee seam via `muldi3_spec`; the `Muldi3Spec` base was extended with `sailOutput` tracking (`o` field)
  so the callee run marshals through, all downstream consumers rebuild green. This is the WIP the earlier
  pilot LOST before capture — recovered from the working tree, gated, committed. Gate: build 1067 jobs,
  check_all **194/194** axiom-clean. **mul is now the concrete template for div/mod** (same seam, swap
  `__muldi3`→`__divdi3`/`__moddi3` + the DivSpec callee contract).
- **div/mod** — fan out from mul: same Shape-D libgcc seam, clone `EvalMulRow` swapping the callee contract.
  Callee specs exist (DivSpec). Each ~a clone-effort now that the mul template is banked.
- **eq/ne** — need the eval-arm seam composing `value_equal_spec_full` (ValueEqualSpec4, COMPLETE +
  axiom-clean — value_equal is NOT the blocker). Same seam-shape as mul but through value_equal.

So the eval-case frontier is 3 sub-shapes, each ~a full-row effort, NOT a paste-table fan-out. The
error-site multiplier worked because those leaves were uniform; these aren't. Recommended order: (1) XORI
in the block decoder — DONE; (2) mul deliberately → template for div/mod — DONE (commit 7a96b72); (3) ge
as an lt/le/gt clone (now unblocked); (4) div/mod as EvalMulRow clones (swap callee contract); (5) eq/ne
via the value_equal seam. Remaining binary-op leaves: ge, div, mod, eq, ne.

## Next (M5 error family)
Downstream (semantic, not mechanical): map each `errorSimFull` minor premise to its site and instantiate
its row with the matching `errSite_<pc>` (the `SitePre`/`hsite` routing). Supply the shared `SC`/`HT` once
at L7/L8. Then the M5 error family is unconditional modulo those two shared facts. The same COW-clone
workflow pattern generalises to the eval/exec-case fan-out (`#derive_case` + `chain_facts` + `segToTriple`)
and the loop fan-out (`loopFromBody`).
