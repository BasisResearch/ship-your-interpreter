# Lane V: adversarial soundness review of `endToEnd_refinement` (paper §9.3)

Reviewed: `hub/iris-main` at `286c2ad` (branch `lane-v`). The theorem:

```lean
theorem Vsa.Sim.EndToEnd.endToEnd_refinement (h : VsaIris.Interp.IrisHoles) :
    ∀ p c, Loaded interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out)
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (see §3).
The proof itself was not found wanting. What the review broke is the
**hypothesis**: `Loaded interpRunLayout p c` is not satisfied by any
configuration the binary actually reaches, for any program, so the theorem
as stated says nothing about a real run of `c/while-riscv-htif.elf`. The
three independent reasons are C1–C3 below; each has a concrete fix
proposal in §4. Everything else the hypothesis asks for was checked against
the real boot state and holds (§1.3).

Evidence tooling and results live in `experiments/review-v/`
(`check_loaded.py`, `patch_elf.py`, `minify.py`, the corpus in `wl/`, and
`check_loaded_results.txt`). The emulator is the repo's
`riscv-lean/lean_emulator` (`lean_riscv_emulator`, built from this tree);
"step N" below is that emulator's traced step counter from `_start`.

## 0. Findings, ranked

| # | severity | finding | evidence | fix |
|---|---|---|---|---|
| C1 | **critical (vacuity)** | `InterpRunPhysicalFacts.console : ConsoleStream` pins `stdout->_flags = 0x200a` (`flag1 = 0x20`), but at `interp_run`'s entry the real word is `0x000a`; `0x2000` (`__SORD`) is set only by the first console write, *after* entry. So `Loaded` is false at the entry state of **every** program, including the proof ELF. | proof-ELF trace: `sh` at step 1302 (pc `0x80005af4`, `setvbuf`) writes `_flags := 0x000a`; entry at step 85483; the first `__swbuf_r` write at step 104764 (pc `0x8000a914`: `lui a2,0x2000; or a5,a5,a2; sh a5,16(s4)`) sets `0x200a`. `check_loaded.py`: `console: failed: flags` for all 30 traced programs. | §4 P1 |
| C2 | **critical (vacuity, ∀ p)** | `InterpRunPhysicalFacts.rodata_image : FixedRodataLoaded` pins `[0x80018be0, 0x8001acf0)`, whose first 454 bytes are the embedded script (`_script_start = 0x80018be0`, `while.wl` + NUL). Any build of the binary with a different script fails the pin at the script bytes, so only the `while.wl` build can be `Loaded`; the "∀ p" is inhabited only by hand-built configurations whose rodata holds `while.wl`'s text next to some other program's AST, a state the binary cannot reach. No proof reads a byte in the script range. | `check_loaded.py`: `rodata_image: 423–441 mismatching bytes, all inside [0x80018be0,0x80018da5)` for 29/30 programs; `grep` of every hex literal in `Vsa/`, `VsaIris/` finds 0 references in `[0x80018be0, 0x80018da6)`. | §4 P2 |
| C3 | **high (vacuity)** | `stack_bytes : ∀ k ∈ [0x87800000, 0x88000000), ∃ b, mem[k]? = some b` and adequacy's `VsaOk.live topLive` demand all 8 MiB of stack be *present* in Sail's sparse memory map. The loader (`initializeMemory`) inserts only the ELF's `p_filesz` bytes (`.bss` excluded; ELFSage `segment_body`), and the run to entry writes a few KB of stack. The model reads absent bytes as 0 (`readByte = getD 0`), so this is not a soundness issue for the machine, but `Loaded` can only be met by a densified configuration, which is not what the loader produces. | `check_loaded.py`: `stack_bytes: 1781–4597 of 8388608 stack bytes present`; `.bss` fully present at entry (2008/2008) only because CRT/`__sinit`/`malloc` wrote it. | §4 P3 |
| H1 | high (no witness from the loader) | Task 1 as posed is infeasible today: the only kernel-checked `Loaded` witness is the control's hand-assembled dense snapshot (`OutputAliasSnapshot.snapshotWords`, `ControlHeapMemory.heapLog`: a fabricated chunk list, AST at `0x82000000`); the real parser puts the AST in the dlmalloc heap right after `_end` (`0x8001c330…` for `while.wl`, 154 chunks). Reaching `interp_run` takes 85,483 architectural steps (`_start` → CRT → `__sinit` → parser); no reflection tool exists for that boot path, and no `Loaded` witness exists for any `c/tests/*.wl` (the design doc says so). | `INTERP_DESIGN.md` "lane BG": *No checked `Loaded` configuration has been built for those programs, for any field.* Entry steps per program: 9,901 (empty) … 120,300 (`for.wl`). | §4 P4 |
| M1 | medium (assumption strength) | `Loaded` is not a property of the loaded configuration alone. `InitialAllocatorAt.capacity` requires `2·n + 8256 ≤ heapEnd − top` for the cost `n` of **every terminating derivation** of `p` (`ExecSeqCost`), and `stack_admissible` requires the syntactic `ProgramStackFits`. A terminating program whose modeled allocation exceeds ~120 MB has a `BigStep` but the binary prints `out of memory` and exits 1; it is simply outside the theorem. `README.md` describes `Loaded` as "sits at the interpreter phase with `p`'s memory representation", which understates ~110 atomic conditions. | `adv_oom_term.wl` (`s = s+s` 26 times, then `println(1)`): `BigStep` gives `"1\n"`; the emulator prints `out of memory` and exits 1 (§2); the 23-doubling variant `adv_big_ok` completes with `2`. | §4 P5 |
| M2 | medium (spec absorbed implementation quirks) | Two source-language behaviours are reverse-engineered from the binary: (Q8) `Value.catDisplay` cuts a named closure's rendering to 63 bytes, and `stringify` renders any native as `"<native fn>"` while `print` renders `"<native fn print>"`. They are faithful (confirmed empirically, §2) but they mean the "language's" semantics now encodes a `snprintf(buf, 64, …)` buffer size and a `strcpy(buf, "<native fn>")` shortcut. | `adv_longname`, `adv_name58/59`, `adv_native` in §2. | user decision (already Q8); document in README |
| M3 | medium (meaning) | The observable trace `output σ = String.join σ.sailOutput` is the HTIF console **plus** any Sail `print_effect` text; the proven path prints nothing extra, and stderr and stdout are the same console (`_write` ignores `fd`), so a runtime error's diagnostic is part of `out` (with `e = 70`). Not weaker than intended, but worth stating in README. | `htif.c:_write`, `plat_term_write`, `ConcurrencyInterfaceV1.print_effect`. | doc |
| L1 | low (scope) | `CStr` requires every byte `< 128`, so a program with a non-ASCII byte in a string literal or identifier (the lexer accepts them) has no `ProgramRepr`, hence is outside the theorem; the machine's `output` for such bytes is `Char.ofNat b` per byte (mojibake), so the ASCII restriction is also what keeps `output` = the C string. | `adv_nonascii`: `ProgramRepr decodes: bad CString`; emulator prints `hÃ©llo`. | doc |
| L2 | low (hygiene) | `scripts/check_all.sh` stage b scanned only `Vsa/`; `VsaIris/` was never checked for `native_decide`/`bv_decide` (`check_iris_holes.py` covers only `sorry`/`admit`/`axiom`). Stage c (`import Vsa`) cannot see the final theorem; `VsaIris/Audit.lean` prints its axioms but nothing asserts them. Stage a4 (discipline) failed at `hub/iris-main` on 20 legacy files (all added 2026-08-24..09-05, before the 2026-09-11 rule revision). README still said the theorem is conditional on `RemainingWork`. | `scripts/check_all.sh --static-only` at `286c2ad`: `stage a4: discipline violation` (29 hits, 20 files). | fixed in this lane (§3) |
| L3 | low (hygiene) | Raised elaboration limits: none in `VsaIris/`; 1,000 files under `Vsa/` set `maxHeartbeats` (968 also `maxRecDepth`), including `Vsa/Sim/LayoutInstance.lean` (`400000`), all reachable from the theorem. Not a soundness concern (limits do not affect the kernel), but CLAUDE.md Law 1 is violated by the legacy tree wholesale. | token scan (§3). | none proposed |
| L4 | low (dead code) | 88 modules were unreachable from every root or were `RemainingWork`-tower leftovers wired only through `Vsa.lean`'s umbrella import; 35 stale `THEOREMS` entries in `check_all.sh` pointed at them (one, `demoRowGen`, was macro-declared). The tower core (`TermAssembly`, `InterpSimFinal`, `rows/AssemblySkeleton`, `While/StmtDispatchClose`) is still imported by `rows/Field_hStr.lean` and read by `scripts/residual_coverage_ledger.py`/its tests, so it stays. | census in §3. | deleted in this lane (§3) |

Nothing in the proof route (`term_sim_of`, `stuck_sim_of`, `Vsa.Refine.refinement`) was found to be trivially true: both directions of `BigStep p out ↔ Halts c out 0` are load-bearing (`Halts` has no "stuck" escape, `Diverges` is `∀ n, ∃ c', StepsN n c c'`, exit code `e = tohost.payload >> 1` so `exit(70)`/`exit(1)`/`exit(65)` are all `≠ 0`).

## 1. Vacuity

### 1.1 What was checked, and how

The control witness `Control.loaded : Loaded interpRunLayout nativeNameProgram heapConfig` (`Vsa/Sim/NativeNameAudit/ControlLoaded.lean`) is kernel-checked and axiom-clean, but `heapConfig` is `physicalConfigS0 (writeLog snapshotMem fullLog)`: a dense function-backed memory (`ramMemory`, every RAM byte `some`) built from the fixed text/rodata images, a hand-listed word table (`snapshotWords`) and a hand-written dlmalloc log (`heapLog`, chunk headers at `0x80fffff8`, `0x81fffff8`, …). It is not derived from the ELF loader or from any run.

To test `Loaded` against the **real** boot state, this lane:

1. built one ELF per program by overwriting the 453-byte script blob of the proof ELF in place (`patch_elf.py`; the image is byte-identical outside the blob, exactly `scripts/difftest.py corpus`'s padding rule, without the missing cross-compiler; `c/tests/{for,functions,recursion}.wl` exceed 453 bytes and were minified whitespace/comment-only, `functions.wl` split in two);
2. ran each under the Lean emulator with `--trace-all` up to the first step at `pc = 0x800043ec`;
3. reconstructed the entry memory as `initializeMemory` (PT_LOAD `p_filesz` bytes) plus every traced store (the text has no AMO/LR/SC/CSR instructions, so stores are the only memory writes), and took the registers from the entry row;
4. evaluated every `InterpRunPhysicalFacts`/`InterpRunReadyFacts`/`BootHeap` field that is a first-order fact about that state (`check_loaded.py`), in the sparse (actual) view and a zero-filled (dense) view.

### 1.2 What fails at the real boundary (all 30 traced programs, proof ELF included)

- `console` (`ConsoleStream.flags`, `flag1`): real `0x000a`, pinned `0x200a` (C1).
- `rodata_image`: the script bytes (C2) — 29/30; the proof ELF passes this one.
- `stack_bytes` (sparse view only): 0.03–0.05 % of the stack present (C3).
- `ProgramRepr` for `adv_nonascii` only (L1).

### 1.3 What holds at the real boundary (all traced programs)

Registers (`pc`, `a0 = 0x87fffe10`, `a1`, `a2`, `a3 = 0`, `ra = 0x800045ec`,
`sp = 0x87fffd00`, `gp = 0x8001b510`, `s0 = 0x8001b970`), `main_ra`,
`text_image`, `statics` (all eight `img*` pins), every `ExitRuntimeData`
field (both idle `FILE`s), `BootHeapFacts.stderr`, `globals`/`call_depth`,
`interp_geom`, `setjmp_geom`, `stack_ok`, `stmts_*`, the initial store
(`FrameRepr initSt`: `count = 3`, the three natives with the right entry
addresses and copied names), `cap_canon` (`cap = 8`), the whole
`DlHeap.HeapAt` shape (chunk walk `_end → top`, top header, page-aligned
break, `top + 16 ≤ brk`, `sbrk_base`, `top_pad = 0`, bins as rings,
`bin_free`/`free_binned`, `binblocks` bits and `< 2^32`; `adv_toomany`
reaches entry with two free chunks in bins 1 and 4 and still satisfies all
of it), `BootFrameChunks` (three whole, distinct, unshared in-use payloads),
binding keys as whole payloads, `ProgramRepr` (the decoded AST matches the
source), AST bytes off the writable ELF/stack/frame arrays and inside in-use
chunk payloads, `SharedGeom`, and `OutRepr` (no output before entry).

So the two per-field vacuity failures are exactly the console flags and the
script pin; every other boundary fact, including the delicate heap-shape
ones (Q5, Q5b, Q6, `cap_canon`), is true of the binary.

### 1.4 `IrisHoles` satisfiability (spot check)

The ten `newlib.*`/`out.*` holes are safety/functional specs of newlib code
under `ConsoleStream`/`StdioOK`. Their preconditions therefore inherit C1:
as stated they describe the FILE *after* the first write (`__SORD` set),
which is the state every call except the first runs in; the first
`fputc`/`fputs`/`fwrite`/`fprintf` call of a run starts from `0x000a` and
sets `0x2000` itself (step 104764 above). The spot-checked behaviours the
holes promise hold on the emulator: `exit(0)` prints nothing further
(`newlib.exitHandlers` quiet), `fputs`/`fputc` print exactly the string
(every `*.expected`), `snprintfFn` renders `"<fn " ++ name ++ ">"` cut to
63 bytes (`adv_name58`: 63 characters uncut, `adv_name59`: cut, no `>`),
`snprintfInt` renders `%lld` including `-9223372036854775808`, and the
error-path `fprintf` prints the diagnostic and exits 70. No hole was found
unsatisfiable, but P1 should be applied to their preconditions as well.

## 2. Empirical cross-check (Lean emulator, this tree's `lean_riscv_emulator`)

`c/tests` (minified where needed; `functions.wl` as two halves):

| program | output | exit | theorem's prediction |
|---|---|---|---|
| while (proof ELF and minified) | `55 2500 36` | 0 | `BigStep` (`Validation.whileWl_valid`) ✓ |
| arithmetic, for, scope, strings, recursion, functions1+2 | `= *.expected` | 0 | `BigStep` (`Validation.*_valid`) ✓ |
| err_divzero | `runtime error [line 1]: division by zero` | 70 | no `BigStep` ⇒ exit ≠ 0 ✓ |
| err_undefined | `runtime error [line 1]: undefined variable 'nope'` | 70 | ✓ |
| err_parse | `parse error [line 1]: …` | 65 | outside the theorem (no AST, never reaches `interp_run`) |

Adversarial programs (`experiments/review-v/wl/adv_*.wl`):

| program | behaviour | matches semantics? |
|---|---|---|
| `adv_depth999` (`f(999)`, 1000 nested calls) | `999`, exit 0 | ✓ `Call.closure` needs `d < 1000` |
| `adv_depth1000` | `stack overflow (call depth > 1000)`, exit 70 | ✓ |
| `adv_longname` (70-char name) | `""+f` → `<fn aaa…` (63 bytes, no `>`); `println(f)` → full name with `>`; the cut string `≠ "x<fn …>"` | ✓ Q8 (`fnCatRender`), `Value.display` uncut |
| `adv_name58` / `adv_name59` | 63 chars with `>` / 63 chars without | ✓ boundary of the cut |
| `adv_native` | `""+println` → `<native fn>`; `println(println)` → `<native fn println>`; `""+fn(){}` → `<fn>`; `print==print` true; two literals `false` | ✓ |
| `adv_intmin` | `-2^63`, `(-2^63)/(-1) = -2^63`, `% = 0`, `10^24` wraps to `2003764205206896640`, `-7/2=-3 -7%2=-1 7/-2=-3` | ✓ `wrap64`, `tdiv`/`tmod` |
| `adv_strcmp`, `adv_truthy`, `adv_loopvar`, `adv_nest` (440 nested `-`), `adv_nest_odd` | as the semantics | ✓ (`""` is truthy, as `Value.truthy`) |
| `adv_assert2`, `adv_notcallable`, `adv_arity`, `adv_modzero`, `adv_break`, `adv_toomany` (33 args) | diagnostic, exit 70 | ✓ all are stuck in the semantics |
| `adv_empty` | no output, exit 0 | ✓ `BigStep [] ""` |
| `adv_nonascii` (`"héllo"`) | prints `hÃ©llo`, exit 0 | outside the theorem (L1) |
| `adv_big_ok` (`s=s+s` ×23, 8 MB final string) | `2`, exit 0 | ✓ (fits the heap; a large allocation succeeds) |
| `adv_oom_term` (×26, 64 MB, then `println(1)`) | `out of memory`, exit 1 | has `BigStep` with `"1\n"`, yet exits 1: not a counterexample only because `capacity` makes it un-`Loaded` (M1) |
| `adv_oom_div` (`while(true){s=s+s;}`) | `out of memory`, exit 1 | ✓ no `BigStep`; `stuck_sim`'s nonzero exit (the uncounted regime's NULL arm) |

(`recursion.wl` exceeded the traced run's 60M-step cap; the uncapped run printed `3628800 6765 true false 9`, exit 0.)

## 3. Hygiene

- `scripts/check_all.sh --static-only` at `286c2ad`: stage a3 (drift) clean, stage b clean, stage a4 **failed** on 20 legacy files (R1/R5/R7). This lane grandfathered them (they predate the rule revision; listed under a dated comment in `scripts/discipline_grandfather.txt`); the gate passes again.
- Token scan of `Vsa/` and `VsaIris/` (comments and strings stripped): 0 `sorry`/`admit`/`native_decide`/`bv_decide`/`axiom`. Raised limits: 0 files in `VsaIris/`, 1,000 in `Vsa/` (L3).
- `python3 scripts/check_iris_holes.py`: `ok: 10 ledgered holes`.
- Axioms (`scripts/check_final_axioms.sh`, new): `endToEnd_refinement`, `interpSim_iris`, `term_sim_of`, `stuck_sim_of`, `supplies_of`, `Vsa.Refine.refinement`, `Control.loaded`, `all_stackFits`, `ctl_world_{counted,uncounted}` all depend on `[propext, Classical.choice, Quot.sound]` only. `check_all.sh` gained stage c2 (runs this script when a `VsaIris` build is present) and stage b now scans `VsaIris/`, `VsaIris.lean`, `VsaRun.lean`.
- Dead code (import-graph census, roots = `Vsa.lean`, `VsaIris.lean`, `VsaRun.lean`, every `check_all.sh` theorem, every `.lean` referenced from `scripts/` or `experiments/`): 2372 modules, 2296 reachable, 76 unreachable from every root; `EndToEnd.lean`'s own closure is 1384 modules. 29 tower leftovers were reachable only through `Vsa.lean`'s umbrella imports. Deleted in this lane: 88 modules (the unreachable ones minus the grandfathered `Vsa/Sim/Code/Main.lean`, plus the tower leftovers closed under reverse dependency, minus the generator targets `rows/LayoutGround.lean`, `rows/ErrorRoutingClasses.lean` and the test fixture `rows/NativeBodyAssert.lean` with its dependency), their 35 `THEOREMS` entries, their `Vsa.lean` imports, and their grandfather/`abs_inventory.sh` lines. `lake build Vsa VsaIris` is green after the deletion. Still deletable with a follow-up: `Vsa/Sim/TermAssembly.lean`, `InterpSimFinal.lean`, `rows/AssemblySkeleton.lean`, `While/StmtDispatchClose.lean`, `rows/Field_hStr.lean` (+ `scripts/residual_coverage_ledger.py`, `scripts/tests/test_{residual_coverage_ledger,assembly_skeleton}.py`), and the two stale `THEOREMS` entries `InterpSimFinal.refinement_conditional`, `TermAssembly.refinement_of_residuals`.
- Stale docs: `README.md` (fixed); `TOOLING.md:231` (example checkpoint naming `RemainingWork`); `experiments/smt/PROOF_CLOSURE_PLAN.md` (frames `RemainingWork`/`DivWork`/`ErrWork` as open; an entry for this review was added); `VsaIris/DESIGN.md:149`, `INTERP_DESIGN.md` §0/§11 (describe the migration as a plan).

## 4. Proposals (statement changes; the user's call)

- **P1 (C1) `ConsoleStream.flags` at the boundary.** State the boundary as `_flags = 0x000a` (`__SWR | __SNBF`), or `flags ∈ {0x000a, 0x200a}`, and prove once that the first console write sets `__SORD` (the `lui/or/sh` at `0x8000a904–0x8000a914`) and every later one preserves it. The holes' preconditions (`stdioOwn`/`StdioOK`) should take the same disjunction, or a `first : Bool` index. Without this, no run of the binary is in the theorem's domain.
- **P2 (C2) exclude the script from the rodata pin.** Split `FixedRodataLoaded` into `[0x80018da6, 0x8001acf0)` (everything after the script blob and its NUL), or subtract `[_script_start, _script_start + 454)`. No proof references a byte in that range; the 26 consumers of `FixedRodataLoaded` only project pinned slots above it. With P1 and P2, every `c/tests/*.wl` build reaches an entry state that passes every first-order field of `Loaded` (this lane's checker), which is the precondition for building loader-derived witnesses (P4).
- **P3 (C3) presence versus zero reads.** Either (a) prove a densification lemma for the machine, `Halts c out e ↔ Halts (fillZero c) out e` and likewise for `Diverges`, from `readByte = getD 0` and the fact that `stepOnce` never inspects presence, and state the theorem for `Loaded … (fillZero c)`; or (b) weaken `stack_bytes`/`VsaOk.live` to "reads as some value or is absent", which touches adequacy's byte points-to. (a) is cleaner and keeps `Loaded` unchanged.
- **P4 (H1) loader-derived witnesses.** After P1–P3, build `Loaded` for each `c/tests/*.wl` from a reflected boot trace: the write log up to entry (≈ 9k–15k stores) applied to the ELF image, with `heapConfig`-style `decide`s over the reflected memory. The existing `writeLog` machinery (`ControlHeapMemory`) is the model; the missing piece is a generator that turns the emulator's entry write log into a `snapshotWords`/`fullLog` term and re-runs the control's field proofs generically. This does not need to reflect the 85k steps, only their write log, and it would make the control witness itself loader-derived.
- **P5 (M1) say what `Loaded` assumes.** README's statement should name the two program-dependent hypotheses (`capacity`: every terminating derivation's modeled allocation fits below `__heap_end` with slack; `stack_admissible`: `ProgramStackFits`), the ASCII restriction, and that a program can be `Loaded` only if its script is the one linked into the image (until P2). Alternatively, make the semantics OOM-aware (an `outOfMemory` outcome) so `capacity` can go.
- **P6 (L4 follow-up).** Remove the residual-ledger tooling and the tower core in one commit, or re-seat `rows/Field_hStr.lean` on the layer so the core becomes unreachable.

## 5. What this review did not do

- No kernel-checked `Loaded` for the loader's configurations (H1). The
  first-order field checks are machine-checked by a Python checker over
  the emulator's trace, not by Lean.
- The Lean build under the shared lock was used only for the axiom audit
  and to confirm the deletions compile; no proof was re-elaborated by hand.
- `scripts/tests` (pytest) was not run; LANE.md (lane A) reports
  environment-path failures there predating this lane.
