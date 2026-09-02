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
