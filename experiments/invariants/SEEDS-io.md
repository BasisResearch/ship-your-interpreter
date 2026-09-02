# Invariant seeds for the mining-silent io cases (coordinator-authored)

Status triage FIRST — 9 of the 17 need NO seed (invariant already proven):

| case | status |
|---|---|
| io_write / io_write_r / io_swrite | LANDED — `write_summary`/`write_r_summary`/`swrite_summary` (FnWrite*Fold); WInv/WRGOk/SWGOk ARE their invariants |
| io_snprintf / io_svfprintf_r | LANDED — the snprintf campaign (SnprintfSpec3 `decimalLoop_spec` = the digit loop; Spec40-42 wrapper) |
| io_sfvwrite_r | unbuffered arm LANDED (`sfvwrite_unbuf_summary`, rows/FnSfvwriteFold); buffered arm see S4 |
| io_value_print | dispatch, no loop — arms landed (ValuePrintArms); needs contracts spliced, not invariants |
| io_fputs_r / io_fwrite_r | wrapper shells over __sfvwrite_r — no loop of their own; call-splice folds (WRGOk mirror), seed S5 |

Seeds for the 8 genuinely-unlanded, by shape:

## S1 — flush write-back loop (`_fflush_r`@0x8000edcc, `__sflush_r`@0x8000eb70)
Model: WInv (FnWriteFold) + the swrite splice. Shape: drain `[base, p)`:
`FlushInv`: fields `base p end : BitVec 64`, `written : Nat`, with
`base ≤ p ≤ end` (guard), `written = (p - base).toNat` (progress),
`FILE fields (_bf._base, _p) pinned at their slots` (T5 window facts),
`out = out0 ++ bytes[base, p)` after the __swrite splice (post via
swrite_summary), stack window untouched (`memFrame` at `[SL.lo, sp)`).
sflush additionally: `_w := 0` reset write-back at exit (slot fact).

## S2 — single-byte put (`_putc_r`@?, `_fputc_r`@0x80006210)
No loop: straight span + conditional flush call. Seed = call-splice
post (WRGOk mirror): `out' = out0 ++ [c]` when unbuffered (__SNBF, our
stdout), FILE `_w` decrement/reset per branch, sret/frame per abiFrame.
These are gen_fn folds, not mined invariants — seed the PRE (arg regs
a0=reent a1=char a2=FILE) + the two-branch post.

## S3 — vfprintf fmt loops (`_vfprintf_r`@0x8000a884 pinned paths)
%lld digit loop: SAME SHAPE as landed `decimalLoop_spec` (SnprintfSpec3)
— seed verbatim from it: `val_k = digits-emitted-so-far interpretation,
cursor decrements from buf+len, val' = val / 10, digit = val % 10 stored
at cursor`. %s copy loop: byte-copy shape = memcpy iterW precedent
(MemcpySpec2): `copied prefix = source prefix, cursor pair advances in
lock-step, NUL-terminator check as guard`.

## S4 — __sbprintf buffered arm (`__sbprintf`@0x8000dda8 + __sfvwrite_r buffered)
Synthetic FILE on stack: ALL fields concrete (the 47c route map). Seed:
`fake._bf._base = sp+K (concrete), _bf._size = 400, _flags = __SWR|__SSTR-like`,
buffered-arm copy loop = memcpy shape into the fake buffer (S3's copy seed),
final `_fflush_r` splice drains via S1. The invariant is mostly T1 constants
(every FILE field concrete) — highest mechanical-mining yield once loop-head
probes are wired; LLM only for the cross-call composition statement.

## S5 — wrapper shells (`_fputs_r`, `_fwrite_r`)
No loop (newlib delegates to __sfvwrite_r): seed = the uio/iov setup posts:
`iov.base = buf, iov.len = n (fwrite: size*nmemb via __muldi3 — splice
muldi3_spec), uio fields at sp-slots (T5 window facts), then
sfvwrite_unbuf_summary splice, out' = out0 ++ buf[0,n)`. WRGOk mirror for
frame/spill.

USAGE: per-case `.lean` candidates should be the hermetic-struct idiom
(KindBridge precedent) instantiating these shapes with corpus PCs/regs;
fuzz each (`statement_fuzz.py --file`). The S1/S3/S4 loop conjuncts are
mechanically minable once `invgen.py` wires loop-head probes for these PCs
(the batch's gap) — mine first, seed only the quantifier structure.
