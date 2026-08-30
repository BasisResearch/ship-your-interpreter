# Elf / InitValues interface–implementation split (Axis 2 of build-speed plan)

Design for `build-speed-exponentiation-plan.md` Axis 2 item 1: make a typical edit
near the DAG root invalidate a small cone instead of the world. All numbers below
measured 2026-08-29 on main (986 Vsa modules; grep + python over import lines, no
builds run).

## 0. Why every edit rebuilds the world (invalidation mechanics)

Lake (Lean 4.29) invalidates by **trace hash chaining**, not by output content:
a module's build trace mixes the hash of its `.lean` source with the traces of
all its imports. Editing *anything* in a file — a proof body, a doc comment —
changes its source hash, hence its trace, hence the trace of every direct
importer, transitively. There is **no early cutoff** ("olean unchanged, stop"):
the entire reverse-import cone re-elaborates. `buildType` only affects C/native
compile flags and is irrelevant to this cascade. Observed: the A+B merge touched
14 files and cost ~30–40 min / 1100 jobs, exactly the cone prediction.

So the only lever at the DAG root is *where declarations live*: a volatile
declaration in a 975-cone module taxes every edit at ~35 min; the same
declaration in a 3-cone module taxes it at seconds.

## 1. The two files, measured

Surprise: both files are already tiny (129 / 130 lines) and have been edited
**exactly once each** (initial commit `b6cdbdf`); the 272 KB hex blob is already
split out into `Vsa/ElfBytes.lean`. The problem is not their weight — it is that
**volatile-by-role declarations (the fuel-bounded runner) and the giant binary
blob sit inside the 975-module cone**, so any future M5-runner edit or ELF
regeneration is a full-tree rebuild.

### Import-cone facts (python over `import Vsa.*` lines, 986 modules total)

| module | direct importers | transitive reverse cone |
|---|---:|---:|
| `Vsa.ElfBytes` | 1 (only `Vsa.Elf`) | **976** |
| `Vsa.Elf` | **575** (514 of them DecodeTable batches) | **975** |
| `Vsa.Sim.InitValues` | **524** | **913** |

Next fan-out tier (for context): `ValueSites` 48/294, `Batch01Part04` 31/343,
`Triple` 23/299, `Code.Eval_expr` 19, `ValueSpec`/`RegAccess`/`ExecuteAlu` 18.
Middle-band cones: `Machine` 370, `Attr` 367, `StateNF` 366, `Pmp` 363,
`GoodState` 362, `Hooks` 360, `MemRead` 357, `Fetch` 356 — the next targets
after this split, out of scope here.

**Critical path** (longest import chain): **46 modules**:
`ElfBytes → Elf → InitValues → Hooks → Fetch → Skeleton → StepAddi → StepBeq →
Frame → StepAlu → StepObs → Muldi3Sites → Muldi3Spec → DivSpec → DivLoops →
DivSites2 → RegPins → StepFrameOut → ChainFrameOut → StrcmpSpec → StrcmpSpecW
→ …W2 → …W3 → …W4 → EnvDefSpec → EnvDefSpec2 → ValueEqualSpec3 →
SnprintfSpec7 → …11 → …17 → …18 → …19 → …20 → …25 → WriteLogNF → SegEval →
SegEvalSound → FrameCalc → DeriveCase → DeriveCaseRow → EqNeDispatchSeg →
SegFrameFactsAuto → ModDispatchStrong → EvalModArm → rows.EvalModRow → Vsa`.
Elf/InitValues sit at positions 1–3 but contribute seconds; the wall time of the
path lives in the Strcmp/Snprintf/Seg segment — that is Axis 1 territory. The
split does not shorten the path; it stops edits from *entering* it at the root.

## 2. Declaration classification

### `Vsa/Elf.lean` (129 lines; imports `LeanRiscv`, `Vsa.ElfBytes`)

Use counts = number of `.lean` files under `Vsa/`+roots referencing the name
(word-grep, excluding the defining file):

| decl | kind | use-files | who | class | destination |
|---|---|---:|---|---|---|
| `hexVal` | def | 0 | (only `hexToBytes`) | impl helper | **move → ElfRun** |
| `hexToBytes` | def | 0 | (only `elfBytes`) | impl helper | **move → ElfRun** |
| `elfBytes` | def | 0 | (only `whileElf?`/`initState`) — pulls the 272 KB `elfHex` | impl | **move → ElfRun** |
| `whileElf?` | def | 1 | ElfMono | impl | **move → ElfRun** |
| `RunResult` | structure | 1 | ElfMono | impl | **move → ElfRun** |
| `setupElf` | def | 1 | ElfMono (+doc refs in Decode/InitValues; future `init_good` target) | interface | keep |
| `stepOnce` | def | **13** | Machine, StepObs, StepAlu/Addi/Jump/Beq/Store/Branch, Tick, TermEntry, ErrorSim, ErrorTail, ElfMono | **interface — THE step everything's Triples are about** | keep |
| `runSteps` | def | 1 | ElfMono (`runSteps_mono`) | impl | **move → ElfRun** |
| `initState` | def | 1 | ElfMono | impl | **move → ElfRun** |
| `runElf` | def | 1 | ElfMono | impl | **move → ElfRun** |
| `runWhileElf` | def | 2 | ElfMono, VsaRun (exe) | impl | **move → ElfRun** |

Key measurement: **the entire fuel-bounded runner + the ELF blob are consumed by
exactly two files** (`Vsa/ElfMono.lean`, `VsaRun.lean`). The 575 direct
importers import `Vsa.Elf` for (a) `stepOnce` (13 of them), (b) transitive
`LeanRiscv` (the DecodeTable/site templates `open LeanRV64DExecutable … Vsa`),
and nothing else. `elfHex`/`elfBytes` have **zero** use sites outside the file.

### `Vsa/Sim/InitValues.lean` (130 lines; imports `Vsa.Elf`, uses nothing from it — doc refs only)

| decl | kind | use-files | class |
|---|---|---:|---|
| `initMisa` | def (1 literal) | **562** | interface — the workhorse (every decode lemma's `hmisa`) |
| `initMstatus` | def | 15 | interface |
| `initMseccfg` | def | 0 | interface (sites pin `0#64` directly) |
| `initMie` | def | 0 | interface |
| `initZero64` | def | 0 | interface |
| `initPmpcfg` | def | 2 | interface |
| `initPmpaddr` | def | 14 | interface |
| `tohostAddr` | def (1 literal) | **227** | interface |
| `initPmaRegions` | def (63-line record literal) | 23 | the only non-trivial content |

Verdict: **InitValues is already a pure interface module.** There is no heavy
implementation to move; its 913-cone is *earned* (`initMisa` genuinely appears
in 562 files' statements). The correct action is a freeze policy, not a split.
Two optional refinements measured below both give little and are not part of the
core change.

## 3. The split

Principle (per the task constraint): the public module names `Vsa.Elf` and
`Vsa.Sim.InitValues` **stay and become the frozen interfaces**, so none of the
575/524 `import` lines change. The volatile content moves to a **new module
outside the cone**; only its 2 real consumers redirect.

### New file: `Vsa/ElfRun.lean`

```
import Vsa.Elf
import Vsa.ElfBytes

namespace Vsa
-- moved verbatim, in order:
-- hexVal, hexToBytes, elfBytes, whileElf?, RunResult,
-- initState, runSteps, runElf, runWhileElf
end Vsa
```

(`runSteps` calls `stepOnce` — imported from `Vsa.Elf`. `RunResult`'s
`deriving Repr, DecidableEq` moves with it; no downstream instances exist.)

### `Vsa/Elf.lean` after (the frozen interface, ~50 lines)

- Keeps `import LeanRiscv` — **load-bearing**: 575 files rely on it transitively.
- **Drops `import Vsa.ElfBytes`** (its only importer; `elfBytes` moves out).
- Keeps exactly: module doc (updated), `setupElf`, `stepOnce`.
- Header gains a freeze banner: "FROZEN INTERFACE — 575 direct importers; any
  edit is a full-tree (~35 min) rebuild. New definitions/lemmas go in
  `Vsa/ElfRun.lean` or a leaf. Interface changes require a full-build
  justification." Same banner (524 importers) added to `InitValues.lean`.

### `Vsa/Sim/InitValues.lean` after

Unchanged except the freeze banner. It keeps `import Vsa.Elf` (now importing
the thin interface; decoupling it to `import LeanRiscv` was simulated and wins
nothing — see §5 — because the DecodeTable batches import `Vsa.Elf` directly
anyway). Future init lemmas continue to land in leaves (`InitGood*` already do).

### Redirected consumers (the only other edits, 3 files)

1. `Vsa/ElfMono.lean`: `import Vsa.Elf` → `import Vsa.ElfRun`.
2. `VsaRun.lean` (the `vsa_run` exe root): `import Vsa.Elf` → `import Vsa.ElfRun`.
3. `Vsa.lean` (root aggregator): add `import Vsa.ElfRun` next to `Vsa.ElfMono`
   (also reachable transitively via ElfMono; explicit for clarity).

Nothing else references any moved name (verified by word-grep for all 9 moved
names over the whole tree, catching qualified `Vsa.runElf`-style uses too; also
no `Vsa.Elf.`-qualified references exist — everything is plain `Vsa.*`).
`experiments/*.lean` has 10 files importing `Vsa.Elf`; not lake-built, and none
uses a moved name in anger (scratch probes; fix on touch).

### Rejected alternative

Making `Vsa/Elf.lean` a re-exporter (`import Vsa.ElfRun` inside it) would keep
every import line *and* every name path working with zero consumer edits — but
it keeps ElfRun inside all 575 importers' transitive closure, so an ElfRun edit
still rebuilds the world. The volatile module must sit **outside** the cone;
that costs exactly the 2 consumer redirects, which is the right trade.

## 4. Ordered execution steps

1. Branch. Create `Vsa/ElfRun.lean` with the 9 moved decls (verbatim cut-paste,
   same `namespace Vsa`, same decl order).
2. Shrink `Vsa/Elf.lean` (drop `ElfBytes` import + 9 decls; update module doc;
   add freeze banner). Add freeze banner to `Vsa/Sim/InitValues.lean`.
3. Redirect the 3 consumers (ElfMono, VsaRun, Vsa root).
4. **Full-build gate**: `lake build` (expect ~1100 jobs / 30–40 min — this
   changeset itself edits `Elf.lean`, so it pays the full cone once; schedule
   when the serial profiler releases the toolchain) then
   `scripts/check_all.sh` (expect 269/269, axiom-clean). No stated theorem
   changes, so this is purely mechanical verification.
5. Cosmetic: `scripts/check_all.sh:263` comment cites `Elf.lean:86` for the
   `stepOnce` htif re-check; line number shifts — update the comment.
6. Commit as one atomic changeset (per plan §Risk: "wide, load-bearing edit …
   one atomic changeset with a full-build gate").

## 5. Estimated cone shrink (simulated on the real import graph)

| edit scenario | modules rebuilt BEFORE | AFTER |
|---|---:|---:|
| runner/fuel/RunResult work (M5 divergence-sim runner variants, new `runSteps` lemmas) — lands in `ElfRun` | **975** | **3** (`ElfRun`, `ElfMono`, `Vsa`; + `vsa_run` exe) |
| ELF binary regeneration (`ElfBytes.lean` rewritten after a C-side change) | **976** | **4** (`ElfRun`, `ElfMono`, `Vsa`, `VsaRun`) — mechanical cone only; the semantic re-proof burden of new bytes is separate and unchanged |
| fuel-monotonicity / whole-binary facts (`ElfMono`) | 1 (already a leaf) | 1 |
| `stepOnce`/`setupElf` semantics change | 975 | 975 — **by design**: these are the frozen interface; such a change means the machine semantics changed and the world *should* rebuild |
| `InitValues` register values | 913 | 913 — frozen; values only change if the emulator/ELF changes (world-rebuild events anyway) |

Simulated but **not recommended** (measured no/low value):
- Decoupling `InitValues` from `Vsa.Elf` (`import LeanRiscv` directly):
  cone(Elf) 975 → 975. The 530 DecodeTable batches import both directly, so the
  cones almost coincide; only 3 files (`ExecuteJump`, `GoodState`,
  `InitGoodPmp`) reach Elf solely through InitValues. Skip.
- Splitting `initPmaRegions` into a `Vsa/Sim/InitPma.lean` leaf imported by its
  23 users: PMA-edit cone 913 → **375** (the users include `Fetch`/`Hooks`/
  `GoodState`, which carry ~360-cones themselves). Touches 23 files for a
  scenario (PMA table change) that only occurs on emulator regeneration.
  Optional, low priority.

Net: after this split, **every plausible near-term edit at the DAG root costs
seconds instead of ~35 minutes**, and the two 500+-importer modules are
explicitly frozen with the policy written into their headers. The remaining
build-wall is Axis 1 (the Snprintf/Strcmp elaboration chain on the 46-module
critical path) and, later, the 350–370-cone middle band (`Machine`/`StateNF`/
`Pmp`/`GoodState`/`Hooks`/`Fetch`), which would benefit from the same
interface/impl discipline.
