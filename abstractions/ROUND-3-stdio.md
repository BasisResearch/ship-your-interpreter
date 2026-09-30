# Abstraction-discovery round 3: the newlib runs (2026-09-30)

Branch `exp-F2`, from `exponentiate` after ROUND-2 (505dab1b), merged with `exponentiate`
118e5f3c (step lemmas on demand, allocator paths on the region layer). Commits 62c8c985 …
dc881a7e. Target: the `nx_run` / `snp_run` machine runs of `VsaIris/Vsa/{Stdout,Stderr,Fprintf}`
and `VsaIris/Vsa/Snp*` (about 2,735 module-seconds in the last clean build before this round).

## 1. Census

Measured at the merged tip (118e5f3c, in the verification worktree, read-only) and at this
round's last commit: user CPU of `lake env lean <file>`, `LEAN_NUM_THREADS=8`, one file at a time,
all 89 modules of the four directories and `ExitH`. The machine was shared (load 8–30), so single
numbers carry about ±10%.

Profile of the runs before the round (FwriteRun, Flush, Fwrite, SnpSvf pieces): 40–65% of the time
is arithmetic side conditions, `omega` with every hypothesis of a large context (FwriteRun: 2,520
`omega` calls; SnpSvf: 4,923 calls ingesting 11,494 facts, and each of its 210 step side goals cost
0.24 s). The rest is the per-step register normalisation (`simp only [upd_apply, …]` over the
whole goal, 10–15 ms per step), a 30-way `simp_all` in `ret_keep` at every summary return
(Fwrite: 18.8 s of 69 s), and failing discharges (a miss lemma tried on a hit, 100–220 ms each,
because every macro alternative of `nx_addr` fails in turn).

## 2. Laws

| law | statement |
|---|---|
| L-key (ROUND-2, generalised) | every address of a run is a static literal or a literal offset from the top `T` of a stack frame (`sp + c` with a `BitVec` stack pointer, `s - K + k` with a `Nat` one); with the frame's window in context, each address side condition is a comparison of literals |
| L-region | access permitted and owned for an address inside an access region is one law (`ARgn.ldOK`/`.stOK`/`.acc`), whoever mints the region |
| L-refute | two accesses of one window whose literal intervals overlap are not disjoint; two distinct positions are not equal. Such a side condition needs no arithmetic to fail |
| L-reg (ROUND-2) | a register file is determined by the newest update of each register |
| L-keep | at a summary return, a register is either clobbered (a literal contradiction) or kept (a read through the update chain) |
| L-bit (ROUND-2) | holds for the exit path only: `__swbuf_r` tests bit 13 of the console flags word (`slli a3,a5,0x32; bgez` at `0x8000f108`, the `ORIENT` check), so the `swbuf_A 0x200a` / `swbufU_A 0x000a` pair (and the same pairs in `Fwrite`, `Fputs`) are two paths, not one path twice |

## 3. What was built

**Windows (`Stdout/Win.lean`, `SnpWin.lean`, `RegionCore.lean`).** `Win S T n m` is the access
region `ARgn S (T - n) (n + m)` below and above a `Nat` top `T`, 8-aligned, off the static data
window; `StackWin S sp n m := Win S sp.toNat n m`. The key of an address is its position
`A + d = T + u` with literal `d`, `u`, produced per address form (`StackWin.posN`/`.posP`,
`pos0`, `Win.posK`/`.posKT`). One consumer set closes every shape by one `decide`: `Win.ldOK`,
`.stOK`, `.stOKb`, `.own`, `.lt64`, `.sep`, `.pos_eq`, `.static_win`, `.win_static`, two windows
`.sepW`/`.sepW'`, and the forget-region lemmas of ROUND-2 (`StackWin.static_out`, …). The
dominant form (a negative `BitVec` offset) has one-step variants (`StackWin.ldOKN`, …,
`SymExec.sepC_sound`).

`win_key` and `win_side` read the goal's shape and the addresses' forms and emit the one matching
lemma; nothing is tried blind (three attempts that did were recursion-depth failures, see §5).
When the literals show the condition false, `win_key` throws the internal exception
`winRefuted` (`WinRefute.lean`), which the macro alternatives behind `nx_addr` do not intercept.
`open scoped VsaIris.Sym.Win` routes `nx_addr`, `nx_fdisch`, `sx_addr`, `sx_side` through them and
turns on register compaction during a run (`nx_tidy`). A run states its window once:
`nx_win sp n m` (with the separation from windows already in context), `snp_win s n`,
`SnpGeom.win`, `ExitSp.win`. 44 files opt in with 114 such lines; no theorem statement used
by another module changed.

**Region.** ROUND-1's region layer and the windows are the same law for access permission and
ownership: `ARgn` and its three laws moved to `RegionCore.lean`; `Win.rgn` is an `ARgn`, and
the allocator's own stack window (`WOK.stackRgn`, merged in from `exponentiate`) is the `rgn` of
a `Win` at `(C.S, C.s, 256, 0)`. The layers differ in how the key check is closed (linear
arithmetic over symbolic chunk bases vs. `decide` over literal offsets) and in their disjointness
laws (`Rgn.offStack`/`frame_log` vs. `Win.sep`/`sepW`/`static_win`), which is why they stay two
consumers of one core rather than one layer.

**Shared tactics, relocated as asked.** `#ix_branch` → `Interp/ITac.lean`; register compaction
by kernel evaluation (`updL_dedup`, `nx_compactR`, `nx_compactIf`, replacing `nx_compactR`'s
30-case proof) and the `fillR` layer merge → `SymCompact.lean`; `nx_forget` (outside-first,
merged layers) and `nx_forget_sp` → `SymCompactTac.lean`; `nx_clean`, `nx_one`, the `nx_tidy`
hook and a `ret_keep` without `simp_all` (substitute, then contradiction or one read) →
`Stdout/Tac.lean`. `ExitH/Tac.lean` keeps only the exit path's fact list and step macros
(342 → 57 lines).

## 4. Measurements

User CPU, seconds, same method before and after:

| cluster | modules | before | after | speed-up |
|---|---:|---:|---:|---:|
| Stdout | 19 | 308.8 | 187.9 | 1.64× |
| Stderr | 17 | 249.9 | 154.7 | 1.62× |
| Fprintf | 28 | 380.2 | 291.7 | 1.30× |
| Snp | 18 | 433.4 | 282.7 | 1.53× |
| ExitH | 7 | 116.9 | 118.5 | 0.99× |
| all 89 | | 1,489.2 | 1,035.3 | 1.44× |
| the ten named targets | | 590.4 | 301.7 | 1.96× |

| target | before | after | | target | before | after |
|---|---:|---:|---|---|---:|---:|
| Stderr/FwriteRun | 108.8 | 38.5 | | Stdout/Fputc | 39.8 | 23.9 |
| SnpSvf | 116.1 | 60.6 | | Stdout/Sfvwrite | 35.2 | 20.1 |
| Fprintf/Flush | 77.2 | 30.9 | | Stdout/Sflush | 25.5 | 12.5 |
| Stdout/Fwrite | 69.5 | 39.7 | | Stderr/SprintErr | 35.3 | 14.5 |
| Stdout/Swbuf | 40.7 | 24.9 | | Fprintf/SConv | 42.3 | 36.0 |

Lake module seconds in the last full build of this branch (parallel, 8 threads per job):
Stdout 143, Stderr 123, Fprintf 236, Snp 127, ExitH 111 (rebuilt modules only).

Lines: 54 files, +1,185 / −491 against `exponentiate`; new shared files `Stdout/Win.lean` 619
(of which 39 lines of shape checks), `SnpWin.lean` 65, `RegionCore.lean` 68, `WinRefute.lean` 23.
Run files change by one to three lines each.

Held-out check: full `lake build` green (1,085 jobs); `endToEnd_refinement`, `proofElf_halts`,
`exit_run`, `fwriteErr_run`, `snp_pro` on `[propext, Classical.choice, Quot.sound]`; no `sorry`,
`axiom`, `native_decide`, `bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth` added.

Failed attempts (about 15 failed compiles):

1. The last alternative of `first` elaborates with error recovery: a false `(by decide)` there
   is logged and replaced by `sorry` instead of failing (twice: in `win_side`, then in the `win_key`
   elaborator). Key lemmas now run under `withoutRecover`, and a trailing `fail` closes each chain.
2. Shape parsing: the collection is not the last argument of `Membership.mem`; a `∀ b, b ∈ … → S b`
   binder is not an arrow. Both only made the dispatcher fall back (slower, not wrong); found by
   unit examples, which now sit at the end of `Win.lean` and `SnpWin.lean`.
3. Three maximum-recursion failures, each a key lemma unified against a term it does not fit
   (`(s + c + c').toNat` against `(sp + c).toNat`; `outS` against `snpS`; a `Nat` window against
   `(BitVec.ofNat 64 s).toNat` by `assumption`). Runtime exceptions pass through `first`, so each
   killed a whole module. Fix: dispatch by shape and form, footprint guards (`win_foot`), reducible
   hypothesis lookup.
4. `nx_win` read the footprint only from an `SWP` goal, not from under binders.
5. `ret_keep`: the `rfl` patterns inside its quotation are hygienic identifiers, so no case was
   substituted and every one reached `simp_all`.
6. The first shape dispatcher measured slower than the chain of `exact`s it replaced, until the
   ownership shape was parsed correctly.

## 5. Decision

**Adopted:** the window layer as the one key abstraction for the newlib runs (instance of the
region laws), keyed refutation, kernel register compaction in the shared files, `ret_keep`
without `simp_all`. Measured on all 89 modules: 1.44× overall, 1.96× on the ten targets, ExitH at
parity with its round-2 form.

**Not adopted:** the `ConFlags` treatment of the `Swbuf`/`Fwrite`/`Fputs` flag pairs (L-bit fails:
bit 13 is tested). The pairs share their suffix after the orientation block, where both states
hold flags `0x200a`; a join summary at that point would share it, at the cost of stating the join
state. Not done this round.

## 6. What remains

* The per-step normalisation traverses the whole goal (`simp only [upd_apply, …]`, 10–15 ms per
  step in every run); a normaliser that touches only the new register value would remove it, and
  this is what the reflective executor does for interpreter runs.
* `snp_run` pays on-demand step elaboration inside its own time (SnpStrlen: 44 of 48 s in the
  driver itself).
* Unkeyed address forms fall back to `omega`: symbolic buffers (`ptr + i`, `dst + i`), a FILE
  pointer known only through `f.toNat = 0x8001bb20`, symbolic positive offsets
  (`sp + ofNat (352 + 16 * iovs.length)` in `SConv`), and `(BitVec.ofNat 64 s + c)` before a run
  folds it. Each needs one more position producer.
* Not opted in: `SnpStrlen`, `SnpMove`, `SnpPuts`, most of `SnpPrint`, `VfpEntry`, `FprintfHead`
  (their stack hypotheses have other shapes).
* Kernel checking of two large structures in `SnpPrint` (`PrintOut`, `PrintSt`) costs 20 s.
