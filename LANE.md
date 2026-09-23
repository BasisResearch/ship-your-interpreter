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

## In flight
- `memcpy`, `strcmp`, `snprintf` `%lld`: statements and straight-line parts.

## Holes
- none opened.

## Next
1. `memcpy` spec over `MachWP` (dispatch, 72-byte bulk, word loop, byte tail).
2. `strcmp` spec.
3. `snprintf` `%lld` digit loop.
