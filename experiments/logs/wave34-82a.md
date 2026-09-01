# Wave 34 Task #82a log — amend stringifyStrdupTailContract for the s0-reseat frame ghost + close the memcpy bridge

## Diagnosis (confirmed against observations 2026-08-31 strdup-memcpy-s0-reseat-frameghost)
- Contract `stringifyStrdupTailContract` (StringifyStrdupTail.lean) threads ONE frame
  ghost `gm` through both the malloc frame (pre-`mv s0,a0`, s0 = old) AND the memcpy
  target `EnvDefFrame ... gm` (post-`mv s0,a0`, s0 = dst). `EnvDefFrame.hAbi` +
  `AbiPreserved x8 = true` pins s0 = gm x8 at BOTH ⇒ forces sOld = dst (false).
  Machine-checked obstruction: `strdupMemcpy_frame_obstruction` (kept as regression guard).

## Amendment option chosen: (a) thread the reseated ghost `gm[x8 := dst]`
- Cleaner than (b): needs NO change to `EnvDefFrame` (which hardcodes `AbiPreserved`).
  With `gmReseat := ghostReseatS0 gm dst`, at memcpy entry `get? x8 = some dst = gmReseat x8`
  and for R≠x8 `get? R = gm R = gmReseat R`. So `EnvDefFrame ... gmReseat` is HONEST.
- `RegisterType Register.x8 = BitVec 64` (by rfl); ghost update
  `fun R => if h : R = x8 then some (h ▸ dst) else gm R` elaborates cleanly.
  Helper `ghostReseatS0` + lemmas `ghostReseatS0_x8`/`ghostReseatS0_ne` land in StringifyStrdupTail.lean.

## Consumers (grep audit)
- ONLY code caller of `stringifyStrdupTailContract` = `stringifyStrdupTailContract_closed`
  (StrdupTailContractClose.lean). All other mentions (ConcatHeapCore/StrdupMemcpyArg/
  StrdupTailBridges/StrdupTailJalSeams) are doc-comment prose. Fan-out = 2 files. OK.
- `stringifyStrdupTailContract_closed` has NO consumers yet.

## Decisions / tempted-pragmatic
- (log continues below as work proceeds)
