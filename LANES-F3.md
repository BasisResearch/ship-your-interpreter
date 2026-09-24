# Lane H3 — string and memory helpers (`strlen`, `memcpy`, `strcmp`, `snprintf %lld`)

Branch `lane-h3`, from `hub/iris-main` (merged at `b2dcf79`, F3's loop rule).
Design: `VsaIris/INTERP_DESIGN.md` §9, package H3.

## Done

### `strlen` — complete, both WPs, standard axioms

`VsaIris/Vsa/StrlenSpec.lean` `strlen_specW` is the continuation-style spec
over `MachWP`, with `strlen_spec` (total) and `strlen_specP` (partial) from the
same proof. `#print axioms`: `propext, Classical.choice, Quot.sound`.

Shape: the WHOLE function — the alignment test, the byte-peel loop, the
word-at-a-time scan, the seven-way byte tail and the seven return arms — is ONE
`LocalRun` (`VsaIris/LocalRun.lean`), so the Iris layer is a single
`wp_localRunW` application and everything else is pure Lean.

Files:
- `VsaIris/Vsa/SegRun.lean` (176) — shared: `segFrom_of_seg` (one reflected
  read-only segment as one local-run step), `localRun_le`, and `AluStep` /
  `runFact_of_aluStep` for instructions outside the reflected block model.
- `VsaIris/Vsa/StrlenSeg.lean` (412) — the code bytes, the read region, `Reads`,
  `CStr` from the region's bytes, one pin list, `strlenStep`, `strlenAluStep`.
- `VsaIris/Vsa/Strlen.lean` (995) — the run: `retArm`, `tail0..tail6`,
  `wordRun`, `alignRun`, `peelRun`, `strlenRun`.
- `VsaIris/Vsa/StrlenSpec.lean` (186) — the Iris spec.

Ownership follows INTERP_DESIGN §3: the code and the string's bytes are
persistent (`text`); the ≤ 7 bytes past the NUL that the word load over-reads
belong to the caller's block, so they are owned and handed back unchanged.

### Measurement: the Iris route against VSA's strlen cone

Serial `lake env lean` per file on this machine; "net" subtracts the measured
import-only baseline (0.93–1.21 s per file).

| | files | lines | wall | net |
|---|---|---|---|---|
| VSA cone, retired by the Iris proof | 11 | 9,163 | 20.7 s | ~9.1 s |
| Iris route, `strlen`-specific | 3 | 1,593 | 9.0 s | ~5.4 s |
| Iris route, shared infrastructure | 1 | 176 | 1.2 s | ~0.2 s |

**Lines 9,163 → 1,593, about 5.8×. Net elaboration ~9.1 s → ~5.4 s, about
1.7×.** The elaboration gap is much smaller than the line gap because most of
VSA's cone is generated `site_*` batteries that elaborate cheaply; the cost
that disappears is human, not machine.

Retired: `StrlenSpec`, `StrlenSpecU`, `StrlenSites`, `StrlenReadState`,
`StrlenHeadRun`, `StrlenWordRun`, `StrlenTailRun`, `StrlenTailComplete`,
`StrlenLastRun`, `StrlenCompleteRun`, `StrlenSupply`.

Reused unchanged (and counted on neither side of the table above):
`StrlenSegments.lean` (141, the `#derive_case` blocks — a producer, kept by
INTERP_DESIGN §7), `StrlenMagic.lean` (225, `detect_all_ones`, the zero-byte
arithmetic), about 200 lines of BitVec arithmetic scattered through
`StrlenSpec`/`StrlenSpecU` (`ptrN`, `sext0_add`, `ofNat_sub`, `zext_beqz`,
`andi7_aligned`/`_unaligned`, `magic_build`, `allOnes_build`, `a4_incrG`,
`detect_takenG`/`detect_nottakenG`, `snez_finalG`, `sub_a4_a0_val`), and one
generated site (`StrlenSites.site_80006d64`).

The Iris statement is also strictly more reusable: ONE proof serves both the
total and the partial WP, which the `Triple`-based cone cannot do.

### Finding: `sltu` is not in the reflected block model

`snez rd,rs` is `sltu rd,x0,rs`, and `MKind` (`Vsa/Sim/BlockMem.lean:549`) has
`slt` but no `sltu`. `#derive_case` accepts the word — it decodes to the
nearest kind — but the block's `DecodeFactM` then cannot be closed, because
`DecodeTable.decode_00f03533` concludes `rop.SLTU` while `astOfM` of the
reflected line does not. That is the model's safety net working, and it is why
`Vsa/Sim/StrlenLastRun.lean` proves that one instruction observationally. The
Iris route reuses the same generated site through `Inst.runFact_of_aluStep`
(the `jalExec_of_site` analogue for a register-writing step). **Adding `sltu`
to `MKind` would retire both that bridge and `StrlenLastRun`.**

### On the two loop rules

F1's `wp_localRunW` (`VsaIris/LocalRun.lean:266`) and F3's `MachWP.loopSeg`
(`VsaIris/Loop.lean:79`) are both mode-generic and both fuel-bounded; both cite
xv6iris `ProofMemset.v:1-9`. They differ in where the invariant lives:
- `loopSeg` keeps it as an `IProp` with an opener/closer around ONE segment's
  footprint, and an additive exit resource `K`. That is the right rule for a
  loop whose body is one segment and whose invariant mentions Iris resources.
- `wp_localRunW` keeps it as a pure predicate over `(registers, bytes)` for a
  fixed owned footprint, and a whole *function* — loops, branches, tails and
  all — is one instance.

`strlen` has two loops, a seven-way branch tail and seven exits over one fixed
footprint, so `wp_localRunW` covers it end to end in one application and the
branch structure costs nothing extra. `memcpy` writes memory but over a fixed
byte set, so the same shape applies. Both rules are used by name; neither was
reimplemented.

### What xv6iris does for the same loops, and where this lane agrees

Read from the Rocq sources at `github.com/mit-pdos/xv6iris` (fetched; line
numbers as they appear there).

- **`iris/ProofMemset.v:141-144`, `:168-169` — `wp_memset_loop_free_sconf`.**
  Fuel induction on the remaining byte count, `induction rem as [|rem' IH]`.
  The file header states the rule this lane follows verbatim: "Fuel induction
  over the remaining byte count … bounded loop, not iLöb." `wp_localRunW`'s
  and `MachWP.loop`'s doc comments already cite it; `strlen`'s `wordRun` and
  `peelRun` are the same shape, with the measure being bytes left before the
  NUL and before the eight-byte boundary.
- **`iris/ProofMemmove.v:331-370` — `mm_loop`.** The invariant carries the
  source bytes FRACTIONALLY (`↦ₘ[kts]{dqs}`) over a sliding window, the
  destination bytes EXCLUSIVELY (`↦ₘ[ktw]`, at old values `dst_olds`), and
  three register pins for the two cursors and the source end. The
  postcondition hands back the source unchanged and the destination holding
  the source's bytes. Induction is again on `rem`, peeling one byte per
  iteration.
  **Consequence for `memcpy` here:** put BOTH windows in the run's owned byte
  set `S` and let the end condition say "source unchanged, destination equals
  source" — that is `mm_loop` at `dqs = 1`, and `wp_localRunW` supports it
  directly through `segFrom_of_segW`. If a genuinely FRACTIONAL source is ever
  needed, `wp_localRunW` cannot express it (its cells are persistent `text` or
  exclusive `S`), and F3's `MachWP.loopSeg` is the rule to use instead,
  because its invariant is an arbitrary `IProp` and can hold `↦ₘ{q}`.
- **`iris/ProofCopyinstr.v` `cs_inner`** (the NUL scan, the closest analogue
  of `strlen`). Its invariant tracks "no NUL appears before `done + i`"
  (`bb_nonul`) and advances the cursor one byte per iteration, by plain `nat`
  induction. This lane's `StrBytes` (`nonzero`, `ascii`, `nul`) plus `byteBeq`
  ("the byte at offset `a ≤ len` is NUL exactly at `a = len`") is the same
  fact, stated once and used by every byte test in the tail and the peel.

### The reusable layer the other three instantiate

`VsaIris/Vsa/SegRun.lean` (263 lines) is now function-independent:

| piece | what it does |
|---|---|
| `segFrom_of_segW` | a reflected segment that WRITES owned bytes, as one `SegFrom` step (this is what `memcpy`'s copy loops need) |
| `segFrom_of_seg` | its empty-write-set specialization |
| `leafL` / `leafStep` | ONE pin list for a leaf function; `hwf`/`hkeys`/`hwr` become one `decide` each on the literal register list, and a segment contributes only its `ChainFacts` and the successor's register values |
| `localRun_le` | fuel as a bound, not an exact count |
| `AluStep` / `runFact_of_aluStep` | an observational VSA site as one local-run step, for instructions outside `MKind` |

`strlenStep` is `leafStep` at `strlenRegs`, not a second proof.

### `strcmp`: reflected blocks landed and decode-checked

`VsaIris/Vsa/StrcmpSeg.lean` — `gen_fn.py --fn strcmp --entry 0x80006ea0`
verbatim: 40 `#derive_case` blocks over the 24 CFG blocks, both polarities.
`Vsa/Sim/` had only a site battery (`StrcmpSites.lean`, 3,557 lines) for this
function. A scratchpad probe (outside the repo) ran `chain_facts` on all 40
and confirmed every decode and fetch leaf closes, leaving only data-dependent
goals: **`strcmp` needs no observational site** — every instruction it uses is
inside `MKind`/`bop`.

## In flight
Nothing half-landed. `memcpy`, `strcmp` and `snprintf` `%lld` are not started
as chains; the plan below is mechanical from here.

## Holes
None opened. No `sorry`, `axiom`, `native_decide`, `bv_decide` or raised limit
anywhere in this lane's files; `scripts/check_iris_holes.py` passes.

## Next — the remaining three, with what is already in place

**`strcmp`** (entry `0x80006ea0`, 24 blocks). Segments: landed and checked
(above). Needed: the `Ctx`/`Reads`/pin-list module (the `StrlenSeg.lean`
template at `strcmpRegs = [1, 5, 6, 7, 10, 11, 12, 13, 14, 15]`), then the
chain. Three things a reader should know before starting it:

- **Two read regions, and a `.rodata` word.** The magic mask is loaded from
  `0x8001ac80` by the `auipc`/`ld` pair at `0x80006eb0`; it holds eight `0x7f`
  bytes, so the loaded word is `StrlenMagic.magic7f` and the NUL detection is
  the SAME `detect_all_ones` arithmetic `strlen` uses. `Code.StrcmpLoaded`
  does NOT cover those eight bytes (they are outside `[0x80006ea0,
  0x80006fcc)`), so they enter the run's persistent `text` explicitly — VSA's
  own word-path precondition carries them as eight byte pins
  (`Vsa/Sim/StrcmpSpecW.lean:35-40`).
- **The return value is a SIGN CLASS, not a byte difference.** The lane-compare
  tail (`0x80006f20 … 0x80006f80`) narrows by 16-bit halves: at
  `0x80006f5c`/`0x80006f44` it computes `lo16(a2) - lo16(a3)` (resp. the high
  half) and only falls through to the byte subtraction at `0x80006f74` when
  the low byte of that difference is nonzero. So when the first differing byte
  is the ODD one of its 16-bit half, the function returns `256 ×` the byte
  difference. Only the sign is the contract. VSA states it that way
  (`strcmp_spec`'s "sign-class `Q` form", `Vsa/Sim/StrcmpSpecW.lean:5-10`);
  the Iris spec must too. Writing the post as `a0 = byte₁ - byte₂` is WRONG
  and will only fail at the very end of the tail.
- **The NUL exits re-enter the byte loop.** `0x80006fa4`/`0x80006fac`/
  `0x80006fb8` return 0 when the words are equal, but otherwise jump to the
  byte loop at `0x80006f84` with the cursors advanced, so the byte path is
  reachable from the aligned path and is not just the misaligned case.

Estimate: larger than `strlen`'s chain — two cursors, the unrolled
three-word body, and the lane-compare tail's bit reasoning.

**`memcpy`** (entry `0x80006bc8`, 17 blocks). Segments: `Vsa/Sim/`
`MemcpyCopySegments.lean` already has 21 of them, covering every block EXCEPT
`0x80006bd8` (the `sltiu` length test — the `MKind` gap, take it through
`runFact_of_aluStep` at the generated `site_80006bd8`) and the three
unaligned-destination head-peel blocks `0x80006cbc`/`0x80006cd4`/`0x80006cec`
(regenerate with `gen_fn.py` if the unaligned case is wanted; `env_define`'s
destinations are `malloc`ed, hence aligned). This is the first consumer of
`segFrom_of_segW`: the owned byte set is the destination window, and the run's
end condition says it holds the source bytes.

**`snprintf` `%lld`** (VSA M3). The success path is proved in
`Vsa/Sim/SnprintfSpec*.lean`; the Iris job is the digit loop plus the format
parser segments, and the `%s`/`%d` error paths stay as the `newlib.snprintf`
hole (INTERP_DESIGN Q4). Start from `SnprintfSites*.lean` and the M3 digit
loop rather than re-reflecting.

**Model fix that would help all of them.** Adding `sltu`/`sltiu` to `MKind`
retires `Vsa/Sim/StrlenLastRun.lean`, the `site_80006d64`/`site_80006bd8`
batteries and the `AluStep` bridge; recorded with its evidence and discharge
plan in `experiments/smt/PROOF_CLOSURE_PLAN.md`.
