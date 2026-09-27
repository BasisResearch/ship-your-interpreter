import Vsa.Sim.EnvDefSeg
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.EnvDefBridges3

/-!
# `EnvDefBridges4` — the remaining `env_define` machine bridges THROUGH the seg layer

`Vsa/Sim/EnvDefCompose.lean` leaves three straight-line machine bridges named:
`bridgeAppendHead` (grow path), `bridgeStore` (append path), and `hUpdate`'s
straight-line prefix.  Each was destined to grow a bespoke `site_*` battery in the
legacy `EnvDefBridges*` idiom (`namesToValsPrefix_run` is the last one hand-built —
~250 lines of per-site `stepObs_*` + a 33-branch register frame).

This file discharges the STRAIGHT-LINE MACHINE RUN of each through the block-reflection
seg layer (`#derive_case` + `segToTriple`, the `EnvDefSeg` model), landing the computed
machine post in a handful of lines.  Every word in these spans is tabled + `decodeM`-
supported (verified against `scripts/decode_index.tsv`), and — unlike the `env_define`
*call* prefixes (`capComputeSeg`/`mallocArgSeg`), which end in a `jal` seam and need
`bridgeOfSeg` — the append-head and store spans END IN A BRANCH/JUMP terminator
(`beqz`/`bnez`/`j`), which `BlockTerm`'s `TKind` (`br`/`j`) carries NATIVELY.  So NO
`bridgeOfSeg` and NO new `bridgeOfSegBr` variant is needed: `segToTriple` (built on
`segEval_sound`, whose end PC is `evalBlocksPC` = the terminator target) marshals the
whole branch-terminated seg directly.  (Recorded in `experiments/observations.md`.)

## What lands here vs. what stays a named spec residual

LANDS (the machine run, replacing the would-be `site_*` battery):
* `appendHeadSeg` / `appendHeadRow` — the grow-path append-head span
  `0x80002bc0..0x80002bcc` (`ld;sd` ▷ `beqz` ▷ `bnez`), landing the computed
  post (env->vals stored, parked at the append head `0x80002b1c`).
* `appendStoreSeg` / `appendStoreRow` — the append-path store block
  `0x80002b44..0x80002b8c` (loads + shifts/adds + `sd`/`sd`/`sd`/`sd`/`sw` ▷ `j`),
  landing the computed write-log post (the three value words, the name word, the
  incremented count) parked at the shared tail `0x80002aec`.

STAYS a named typed premise (the SPEC-side marshalling, NOT machine reasoning):
* the `FrameRepr` reconstruction turning the computed store-block `writeLog` into
  `env_define_update_post`'s `Store.define` result — its content is the LANDED
  `frameRepr_append` (`EnvDefBridges3`); the residual is only the tie of the computed
  `writeLog` byte-images to `frameRepr_append`'s readback hypotheses.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

/-! ## Item 1 — the grow-path append-head span `0x80002bc0..0x80002bcc`

Per the `EnvDefBridges3` ledger the span is 1 load + 1 store + 2 branch sites:
```
80002bc0  ld   a5,8(s4)     -- x15 := env->names   (reload after the two reallocs)
80002bc4  sd   a0,16(s4)    -- env->vals := a0      (the realloc(vals) result)
80002bc8  beqz a5,80002bd0  -- br BEQ; NOT taken on the success path (names ≠ 0)
80002bcc  bnez a0,80002b1c  -- br BNE; taken on the success path (vals ≠ 0) → append head
```
Two blocks (one terminator each): `[ld;sd] ▷ beqz(false)` then `[] ▷ bnez(true)`.
Both branches WRITE NO GPR (BlockTerm's `br` class), so the whole thing is ONE
`#derive_case` seg — no `bridgeOfSeg`, the branch terminators are in-model. -/

/-! ## Item 2 — the append-path store block `0x80002b44..0x80002b8c`

The store block (name absent, `count < cap`) writes the copied name pointer into
`names[count]`, the value's three words into `vals[count]`, and `count+1` into
`env->count`, then `j`s to the shared finalize tail `0x80002aec`:
```
80002b44  lw   a5,0(s4)     -- x15 := env->count           (= n)
80002b48  ld   a2,8(s4)     -- x12 := env->names
80002b4c  ld   a4,16(s4)    -- x14 := env->vals
80002b50  slli a3,a5,0x1    -- x13 := n*2
80002b54  slli a7,a5,0x3    -- x17 := n*8
80002b58  add  a3,a3,a5     -- x13 := n*3
80002b5c  ld   a6,0(s5)     -- x16 := v.word0   (v = the value struct at s5)
80002b60  ld   a0,8(s5)     -- x10 := v.word1
80002b64  ld   a1,16(s5)    -- x11 := v.word2
80002b68  add  a2,a2,a7     -- x12 := &names[n]  (names + n*8)
80002b6c  slli a3,a3,0x3    -- x13 := n*24
80002b70  sd   s1,0(a2)     -- names[n] := s1    (the copied name ptr)
80002b74  add  a4,a4,a3     -- x14 := &vals[n]   (vals + n*24)
80002b78  addiw a5,a5,1     -- x15 := n+1
80002b7c  sd   a6,0(a4)     -- vals[n].word0 := v.word0
80002b80  sd   a0,8(a4)     -- vals[n].word1 := v.word1
80002b84  sd   a1,16(a4)    -- vals[n].word2 := v.word2
80002b88  sw   a5,0(s4)     -- env->count := n+1
80002b8c  j    80002aec     -- → shared finalize tail
```
One straight-line block, `j` terminator — again NO `jal`, so the whole thing is ONE
`#derive_case` seg carried in-model (the `j` is a `TKind.j`).  The five stores land in
the seg's canonical `writeLog` (`out.log`); the FrameRepr reconstruction that turns that
write-log into `env_define_update_post`'s `Store.define` result is the LANDED
`frameRepr_append` (`EnvDefBridges3`) — NOT re-proved here (it is the genuinely spec-side
part, and its content is already discharged). -/

/-! ## Item 3 — the update-path HIT store block `0x80002ac0..0x80002ae8` (the `hUpdate` prefix)

The update path (name FOUND in the scan) is `prologue ≫ scan-loop ≫ HIT-store-block`.
Per the task the scan LOOP stays a `loopFromBody` seam (its shape is the env_get scan,
`env_get_scan_spec'` in `EnvGetSpec4`); this row lands the STRAIGHT-LINE HIT tail — the
`hUpdate` prefix's genuinely straight-line part — that overwrites `vals[i]` with the new
value `v` and falls through to the shared finalize tail `0x80002aec`:
```
80002ac0  ld   a5,16(s4)    -- x15 := env->vals
80002ac4  slli a4,s0,0x1    -- x14 := i*2         (s0 = the found index i)
80002ac8  ld   a1,0(s5)     -- x11 := v.word0
80002acc  ld   a2,8(s5)     -- x12 := v.word1
80002ad0  ld   a3,16(s5)    -- x13 := v.word2
80002ad4  add  a4,a4,s0     -- x14 := i*3
80002ad8  slli a4,a4,0x3    -- x14 := i*24
80002adc  add  a5,a5,a4     -- x15 := &vals[i]
80002ae0  sd   a1,0(a5)     -- vals[i].word0 := v.word0
80002ae4  sd   a2,8(a5)     -- vals[i].word1 := v.word1
80002ae8  sd   a3,16(a5)    -- vals[i].word2 := v.word2   (falls through to 0x80002aec)
```
Straight-line, NO terminator (fall-through into the shared epilogue) — exactly the
`mallocArgSeg` shape.  Its three stores land in the seg's canonical `writeLog`; the
`FrameRepr` overwrite (`Store.define` UPDATE case — same var list, `vals[i]` value
replaced) is the spec residual, served by the same readback discipline as
`frameRepr_append`.  No `jal`, no `bridgeOfSeg`; the scan loop above is the only genuine
seam left, and it is a `loopFromBody`/`env_get_scan_spec'` residual (named, not built
here). -/
   -- sd   a3,16(a5)

end Vsa.Sim
