# Abstraction-discovery round 2: the exit path (2026-09-30)

Branch `exp-F2` (from `exponentiate`), commits 1ebcd209, f5774078, c38d362c, 37671596.
Target: `VsaIris/Vsa/ExitH/Run{Idle,IdleU,Written,WrittenU}.lean`, the machine run of newlib's
`exit` → `__call_exitprocs` → `stdio_exit_handler` → `_fwalk_sglue(_fclose_r)` over stdin, the
console stream and stderr, consumed by `exit_run` (`ExitH/Iris.lean`).

## 1. Census

| file | pieces | lines | clean-build module seconds (census) | CPU, `lake env lean`, 8 threads |
|---|---:|---:|---:|---:|
| `RunIdle.lean` | 23 × 20 instructions | 90 | 638 | 322 s (second run 305 s) |
| `RunIdleU.lean` | 23 | 90 | 622 | 328 s |
| `RunWritten.lean` | 46 × 10 instructions | 159 | 688 | 379 s |
| `RunWrittenU.lean` | 46 | 159 | 708 | 323 s |
| total | 138 | 498 | 2,656 (19% of the 13,937 s build) | 1,352 s |

All numbers below are user CPU of `lake env lean <file>` with `LEAN_NUM_THREADS=8`, one file at
a time. The machine was shared (load average 25–55), so single measurements carry about ±10%.

Four runs, two differences:

* U vs non-U: the console stream's flags word, `CloseMt 0x200a#64 Mt` vs `CloseMt 0x000a#64 Mt`
  (`consoleFlagsV o`, bit 13). The two files are textually identical otherwise.
* Idle vs Written: stderr's FILE (`ErrIdleMt`, flags `0x12`; `ErrWrittenMt`, flags `0x201a`).
  The piece start addresses of the two chains coincide after 300 instructions
  (`exitIdle_16` and `exitWritten_31` both start at `0x8000e3f4`, the return of the second
  `_fclose_r` into `_fwalk_sglue`); no stderr field is read before that point.

Profile of one piece (`exitIdle_10`, 20 instructions, 15.6 s under the profiler):

| part | seconds | what it does |
|---|---:|---|
| `xh_forget_sp` | 2.7 | pushes one `fillR` through every store of the log, one `omega` per store |
| `xh_compactR` | 1.5 | 30-way case split, one `simp` per register |
| `nx_run` (20 steps) | 11.4 | per step: normalise, discharge side goals |
| — of which `omega` | 8.3 | 1,584 calls from 502 address side conditions (`nx_addr`) |
| — of which `simp only [upd_apply, …]` | 2.3 | register reads |
| kernel (other threads) | 7.2 | 132 auxiliary `omega` proofs |

Two structural findings from the statements: each piece's statement carried every branch
hypothesis of the whole history (2.6k → 81k expression nodes over the idle chain; the next piece
clears them first thing), and each piece added one `fillR` layer under the store log, so a load
from static memory passed one layer per earlier piece (18 side conditions for one `ld` in the
18th piece).

## 2. Laws

| law | statement | check |
|---|---|---|
| L-bit | the exit path's branches on the console flags word `fl` depend only on `fl ≠ 0`, `fl > 1`, `fl & 0x200 = 0`, `fl & 8 = 8`, `fl & 3 = 2`, `fl & 0x80 = 0`; bit 13 is never tested | read off the disassembly (`_fwalk_sglue` `bgeu`; `_fclose_r` `andi 0x200`, `bnez`, `andi 0x80`; `__sflush_r` `andi 8`, `andi 3`); confirmed by the run: every branch is decided from these six facts |
| L-prefix | two runs that agree up to a state share the proof up to that state | the 300-instruction head is proved once and both tails start from its leftover |
| L-dead | a decided branch hypothesis is not needed after its piece | the pieces already cleared them on entry (`xh_clean`) |
| L-key | every address of the run is a literal in the static window `[0x8001b520, 0x8001c168)` or `s + c` with a literal `c` in the stack window `[s − 256, s)`; disjointness, forgotten-region membership, access permission and footprint membership are functions of the literals and of where `ExitSp s` places the two windows | five + five lemmas proved once (below); ROUND-1's cluster K for a two-region world |
| L-layer | forgetting `[lo, lo+n')` under a forgotten `[lo, lo+n)` is one forgotten region of size `max n n'` | `fillR_fillR_ge`, `fillR_fillR_le` |
| L-reg | a register file is determined by the newest update of each register | `updL_dedup` |

## 3. Candidates

**A. Flag-parametric chain.** State the run for a symbolic `fl` with `ConFlags fl` (the six
facts of L-bit, named fields, `ExitH/Loads.lean`) and `CloseMt fl Mt`; `conFlags_of o` supplies
both values. `exit_run` no longer splits on `o`. The local precedent is
`consoleFlagsV_and512` in `Stdout/Fputc.lean`.

**B. Shared head.** `RunHead.lean`: the first 300 instructions (15 pieces), no stderr
hypothesis. `#ix_branch name (hE : ErrIdleMt Mt) from exitHead_15 by …` starts a chain at
another chain's leftover under extra hypotheses; `RunIdle.lean` (7 pieces) and
`RunWritten.lean` (8 pieces) are the two tails. `exitIdle_chain`/`exitWritten_chain` compose
head and tail in three lines.

**C. Reflective executor (`sym_run`).** Not built. It does not apply to this path yet; the
blocks, in the order they would be hit:

1. No linking jump: `symStep` decodes body lines (`decodeM`), `decB`, `decJ` (`jal x0`) and
   `decJR` (`jalr x0`). The exit path has about twenty `jal ra`/`jalr ra` calls (including the
   `jalr a5` to the FILE's close callback), and each would end the run as `.stop`.
2. `symLoad` forwards only an 8-byte `ld` over an 8-byte store at the identical key; a same-base
   overlapping access of any other width returns `none`. The path stores and reloads 16-bit
   flags (`sh`/`lh`/`lhu` at `+0x10`) and 32-bit counts (`sw`/`lw`).
3. Entry memory is opaque: a load from owned memory that misses the log is the atom
   `.ld k a`; the known-value table `Cfg.kv` is consulted only for data-view bases (`dbase`).
   Every branch on a FILE field would be a two-way `Tree.br`, and the callback target a
   symbolic `Tree.jr`. The 27 `CloseMt` fields and 11 `Err*Mt` fields need a `kv` for owned
   memory (sound while no store overlaps the key).
4. The front end (`VsaIris/Interp/SymInterp.lean`) is fixed to `cfgI`, `binByte`,
   `interpRanges` and `IW` goals; `NW` over `stdioText` needs its own `CodeAt` instance.
5. Its memory obligations are still closed one at a time by `norm <;> sx_side`; the measured
   cost here was exactly that (address side conditions), so moving to `sym_run` without L-key
   inside `obCheck` would not remove it.

**Cheap waste (from the profile).**

* W1 (L-dead): `xh_run` clears the branch hypotheses before the leftover is abstracted, and
  `xh_one` fails the piece if a branch was left undecided.
* W2 (L-reg): `xh_compactK` proves register compaction by `updL_dedup`; the kernel evaluates
  `dedupL` on the literal keys.
* W3 (L-layer): `xh_forget` merges the new `fillR` layer into the old one and tries the
  outside-region lemma first.
* W4 (L-key): `xh_addr` (discharger of the load/store and forget lemmas) and the `XH`-scoped
  `sx_side` close address side conditions by `sepC_sound` (two stack accesses, reused from
  `SymExec.lean`), `xh_static_stack`/`xh_stack_static`, `xh_static_out`/`xh_stack_out`/
  `xh_stack_in`, `xh_stOK_stack`/`xh_ldOK_stack`, `xh_own_stack`/`xh_own_static`/`xh_own_errno`,
  or `decide` on two literals; `nx_addr` (`omega`) remains the fallback.

## 4. Measurements

| stage | RunHead | RunIdle | RunWritten | U twins | total CPU | vs baseline |
|---|---:|---:|---:|---:|---:|---:|
| baseline | — | 322 | 379 | 328 + 323 | 1,352 s | 1.0× |
| A + B + W1 (1ebcd209) | 190 | 115 | 150 | deleted | 455 s | 3.0× |
| + W2 + W3 (f5774078) | 136 | 76 | 83 | | 295 s | 4.6× |
| + W4, written tail 8 × 20 (37671596) | 57.5 | 36.1 | 41.4 | | 135 s | 10.0× |

`lake build` reports 57 s, 27 s and 31 s for the three modules (census: 638, 622, 688, 708);
the two tails build in parallel after the head.

The same piece after W1–W4 (`exitHead_12`, the heaviest head piece): 11.6 s → 4.2 s under the
profiler (forget 1.45 → 0.28 s, 20 steps 10.2 → 3.9 s), auxiliary kernel proofs 122 → 9.

| | before | after |
|---|---:|---:|
| Run files | 498 lines, 4 files, 138 pieces | 128 lines, 3 files, 32 pieces |
| `ExitH/Tac.lean` | 96 | 342 (window lemmas, compaction, layer merge, `#ix_branch`, step macros; the case-split compaction removed) |
| `ExitH/Loads.lean` | 135 | 153 (`ConFlags`, `conFlags_of`) |
| `ExitH/` total | 1,049 | 939 |

Held-out check: `exit_run` and `exitHandlers_spec` keep their statements (only the proof body
of `exit_run` and the imports changed); full `lake build` green (1,098 jobs);
`Vsa.Sim.EndToEnd.endToEnd_refinement`, `Vsa.Sim.Boot.proofElf_halts`, `exit_run`,
`exitHandlers_spec` and the three chains depend on `[propext, Classical.choice, Quot.sound]`.
No `maxHeartbeats`, `sorry`, `axiom`, `native_decide` or `bv_decide` added.

Failed attempts (9 failed compiles):

1. An empty `$fs,*` splice in the middle of the fact list produced a malformed list; every
   `simp only` failed under `try` and the first piece timed out (5 compiles to find). The fact
   list is now built as an array (`xhFacts ++ fs`).
2. `bnez` on the whole flags word was not decided with `fl` symbolic (`Ne` is not unfolded by
   the normaliser), so the run explored both sides: twice the work, two leftovers, and a
   heartbeat timeout at head piece 11. The scratch run of the same chain had passed with the
   spurious second leftover unnoticed. Fix: `ne_eq`, `not_false_eq_true` in the fact list;
   `xh_one` now rejects a piece with more than one leftover.
3. `by decide` on `¬ (consoleFlagsV o).toNat ≤ 1` timed out at `whnf`; reduced with
   `BitVec.reduceToNat` first.
4. Written tail at 20 instructions per piece overflowed the heartbeat budget at piece 7 before
   W4; it fits after W4.
5. Two lemma proofs (`rw` instance counts in `fillR_fillR_*`, a `▸`).

## 5. Decision

**Adopted: A and B, with W1–W4.** A removes two of four runs outright; B removes the 300
shared instructions from one of the remaining two; W1–W4 cut the per-piece cost 2.8×. Each was
kept on its own measurement (table above), statements downstream unchanged.

**Not adopted: C**, blocked as listed; items 1–3 are the concrete work list for the executor.

Required route for a newlib path run on the `nx_run` route:

| task shape | use |
|---|---|
| the same path at two values of a flags/config word | a named structure of the tested bits (`ConFlags` is the model) and one chain over the symbolic word; never a twin file |
| two paths with a common prefix | the prefix as its own chain and `#ix_branch` for each continuation |
| a piece's leftover | the reached state only (`xh_run`: clear decided branches, `xh_one`) |
| register-file compaction | `xh_compactK` (`updL_dedup`); never a per-register case split |
| dead stack | one merged `fillR` layer (`fillR_fillR_ge/le`) |
| address side condition with literal offsets | the window lemmas through `xh_addr` / the scoped `sx_side`; `omega` only as fallback |

Proposed gate rules (for the tree that carries `scripts/discipline_rules.tsv`):
a file under `VsaIris/Vsa/**` whose name is another file's name plus `U`; a `macro "…step…"`
whose body repeats a fact list of more than ten `h?.field` terms present in another file of the
same directory.

## 6. What remains

* Per instruction the run now costs about 0.19 s: the register-read normalisation
  (`simp only [upd_apply, …]`, 1.2 s per piece) and two passes of the 49-fact `simp only` per
  step (0.7 s per piece).
* The window lemmas are stated for `ExitSp`/`exitS`. The same law holds for the `outS s need`
  runs (`Stderr/FwriteRun.lean` 33 pieces, `SnpSvf.lean`, `Stderr/SprintErr.lean`,
  `Fprintf/SConv.lean`, `Stdout/*`); the next step is one window structure (`lo`, `hi`, `align`,
  `place` with the window size as a parameter) and `xh_addr` over it.
* `#ix_branch`, `xh_compactK`, the `fillR` merge and `xh_one` sit in `ExitH/Tac.lean` so this
  round did not rebuild the dependents of `Interp/ITac.lean` and `Vsa/SymCompact.lean`. They
  belong there; `SymCompactTac.lean`'s `nx_compactR`/`nx_regEq` is the same 30-way proof that
  `xh_compactK` replaces.
* `Stdout/Swbuf.lean` has the same twin (`#swbuf_seg swbuf_A 0x200a#64`, `swbufU_A 0x000a#64`).
* Residual `omega`: the two layer-merge conditions per piece and stack accesses at offset 0.
* Candidate C's work list (section 3).
