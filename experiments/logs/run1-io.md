# RUN 1 — io lane log (clone /tmp/vsa-io-lane)

One entry per function AS EACH LANDS (green + axioms + wall + path).
Mission: output-DAG whole-function summaries bottom-up via the gen_fn layer.
Pilots (models): rows/FnWriteFold.lean (P1), FnWriteRFold.lean (P2 call-splice),
FnSwriteFold.lean (P3 tail-j). swrite_summary/write_r_summary/write_summary LANDED.

## DAG survey (from experiments/disasm.txt, 2026-09-01)

Reachable print-path call graph (bottom-up), stdout UNBUFFERED (__SNBF, 1-byte
_nbuf, per main's setvbuf(_IONBF) — empirically confirmed):

- fputs shim 0x80006500 (5i, tail-j) → _fputs_r 0x800063b8 (82i; strlen jal seam
  + lock stubs + __sfvwrite_r) → __sfvwrite_r UNBUFFERED arm → jalr fp->_write
  (= __swrite 0x8000efd4, LANDED) — NO flush chain on this route.
- fwrite shim 0x80005260? (check) → _fwrite_r 0x80005078 (122i; __muldi3 seam +
  __sfvwrite_r + udivdi3 tail math).
- fputc shim 0x800062e0 → _fputc_r 0x80006210 → _putc_r 0x8000e6a4 →
  __swbuf_r 0x8000f0c8 → _fflush_r 0x8000edcc → __sflush_r 0x8000eb70 (jalr
  fp->_write seam ×1 under write pins) → __swrite. The fputc route NEEDS the
  flush chain (unbuffered putc always takes __swbuf_r).
- lock stubs __retarget_lock_{acquire,release}_recursive 0x80006fe0/0x80006ff8:
  single-`ret` stubs — trivial FnSummaries, consumed by every _X_r fn.
- __sbprintf 0x8000dda8 (57i) — synthetic FILE builder; fold conditional on a
  named _vfprintf_r summary premise (vfprintf itself OFF-LIMITS this run).

FILE-flags statefulness note: _fputs_r/_fwrite_r/__swbuf_r each do ORIENT
(set __SORD 0x2000 in _flags on first use). Summaries therefore take the flags
halfword SYMBOLIC with named bit facts (&8≠0 __SWR, &2≠0 __SNBF, &512=0 ¬__SSTR,
_flags2 bits 0/13 = 0) and post flags' = flags ||| 0x2000 — one summary covers
first + steady-state calls. Guards close by the seg-guard-close-symbolic-pins
recipe.

## Landings

(entries appended below)

### 2026-09-01 AMENDMENT: s-reg keeps threaded through all three pilots (PRE-REQ)
- Landed `SRegs` (s1..s11 named-field bundle) + `sKeepL : SRegs → GRegs` in
  Vsa/Sim/SegToTripleFramed.lean (green 1.6s, segRowFramed axioms unchanged).
- WG/WRG/SWG += `sv : SRegs`; every Pre/Post/join structure += `sregs :
  GHolds c.σ (sKeepL g.sv)`; every segRowFramed keep list `++ sKeepL g.sv`
  (FrameOK still ONE decide, keys literal); putchar seam transported via new
  `sregs_putchar_frame`; jal seam via 11 `obs_jal_other_env` components.
- FnWriteFold 2.4s / FnWriteRFold 3.1s / FnSwriteFold 5.8s — all GREEN,
  axioms exactly {propext, Classical.choice, Quot.sound}. Oleans regenerated.
- Template counted_loop_fold.lean.tmpl updated; `gen_fn --fold --fn _write`
  regenerates the amended FnWriteFold BYTE-IDENTICALLY (verified by diff).
- Observation logged: fn-summary-posts-lack-callee-saved-keeps.
- Why: every io-DAG caller holds s-regs live across its callee seams
  (__sfvwrite_r s1-s6 across jalr __swrite; __sflush_r s0-s3; _fputs_r/
  _fwrite_r s0-s3) — the un-amended posts were unconsumable there.

### 2026-09-01 LANDED: lock stubs (DAG item 2 side-quest, consumed everywhere)
- Vsa/Sim/rows/FnLockStubsFold.lean: `lockAcquire_summary` + `lockRelease_summary`
  (FnSummary 0x80006fe0 / 0x80006ff8, RetStubPre→RetStubPost: pure ret, nothing
  changes, GENERIC caller keep list + FrameOK-by-decide at the call site).
  GREEN 1.5s, axioms {propext, Classical.choice, Quot.sound}, discipline OK.
- Support: Code/__retarget_lock_{acquire,release}_recursive.lean (gen_code_lemmas),
  rows/FnRetarget_lock_{acquire,release}_recursive.lean (gen_fn, self-verified).
  All oleans built.

### 2026-09-02 HARVEST: previous io-lane clone work landed in MAIN
- /tmp/vsa-io-lane (base 2865529) held the SRegs amendment + lock stubs +
  the __sfvwrite_r partial (gen arms/Code/transport green, fold MID-FLIGHT)
  but main had only the LOG entries.  Copied all 17 files, regenerated
  oleans serially: PtrArith 1.5s, SegToTripleFramed +SRegs/sKeepL, lock
  stubs 1.5s, FnWriteFold 1.6s / FnWriteRFold 2.8s / FnSwriteFold 5.6s
  (all amended, axioms clean), Code/__sfvwrite_r 2.3s,
  rows/FnSfvwrite_r 3.6s, rows/TransportSfvwrite_r 2.5s.

### 2026-09-02 LANDED: __sfvwrite_r UNBUFFERED arm — sfvwrite_unbuf_summary
- Vsa/Sim/rows/FnSfvwriteFold.lean (2782 lines) GREEN 6.6s, axioms exactly
  {propext, Classical.choice, Quot.sound}.  `sfvwrite_unbuf_summary (g) :
  FnSummary 0x8000de8c (SfvFnPre g) (SfvFnPost g)` — the io-DAG crux:
  15-arm Triple.seq chain (14 segRowFramed arms + the `jalr fp->_write`
  INDIRECT seam via stepObs_jalr/decode_000780e7/rX_bits_x15, first jalr
  fn-seam in a fold) splicing the landed P3 `swrite_summary` at the
  ghost bundle `sfvSWG g` (ra0 := 0x8000df20, m0 := sfvM1, sv := sfvLiveSV).
  Post: a0 = 0, s-regs restored (full sKeepL), mem = sfvM3 (8 spills +
  callee footprint + resid slot zeroed), out = pushBytes out0 bytes.
- TWO elaborator/kernel pathologies fixed on the way (both logged in
  observations.md at the moment of noticing):
  1. chainfacts-inblock-store-then-load-whnf-bomb: dec8F's `ld` after 4
     spills gets a stepMemM TOWER pins goal; the mid-flight `show LPins8
     (sfvM1a g)` was a silent STACK OVERFLOW (this is where the previous
     session died).  Fix: `pin8_peel_sd` (peel one disjoint sd image off a
     Pin8) + `show LPins8 _ (addr)` keeping the memory a metavar.
  2. Kernel deep recursion in the `sfvM3_spill_pin8 … rfl` hsplit args
     (list-append defeq at a non-boundary split delta-unfolds the image
     towers) — replaced all 8 `rfl`s with `simp only [sfvLog1, sfvLog2,
     sfvE_*, List.cons_append, List.nil_append]`.  Same class for no-store
     arm mem posts: `writeLog X [] = <image>` rfl head-congruence-unfolds
     both towers — added per-seg `*_log_nil` lemmas + `writeLog_nil`
     (the P2 wrBeqArm idiom, now MANDATORY for every no-store arm).
- Fold anatomy: 14 ChainFacts lemmas (landed by the previous session,
  2 repaired), 13 named-field join structures, sHiKeepL partial keep
  bundle (spilled s1..s6 leave sKeepL piecewise), 4 code-image transports
  (sfvM1a/M1/MC/M3), sailOutput_sigmaPost_jalr (rfl).
