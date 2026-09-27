import Vsa.Sim.StrcpySites
import Vsa.Sim.MemcpySpec
import Vsa.Sim.StrlenSpec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcpy` byte-head-path total-correctness spec (`strcpy_bytehead_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/StrcpySites.lean`) into a total-correctness triple for the **byte-head
copy path** of newlib `strcpy` — the path taken when the source/destination
alignment fast-path does not apply (`(dst ||| src) & 7 ≠ 0`).

This mirrors `memcpy`'s byte-copy path (`MemcpySpec.lean`) but the length is
**discovered**, not given: the loop is a bottom-tested do-while whose exit is the
`bnez a4` on the just-loaded byte — it copies `s.length` characters *plus* the NUL
terminator, `s.length + 1` bytes total, into `[dst, dst + s.length]`.

## The byte-head loop (`[0x80006e7c, 0x80006e94)`, back-edge `0x90 → 0x80`)

* `0xe7c`: `mv a5,a0`      — `a5 := dst` (preamble, once)
* `0xe80`: `lbu a4,0(a1)`  — loop head: `a4 := zext (byte at a1 = src+i)`
* `0xe84`: `addi a5,a5,1`  — `a5 := dst + (i+1)`
* `0xe88`: `addi a1,a1,1`  — `a1 := src + (i+1)`
* `0xe8c`: `sb a4,-1(a5)`  — store the byte at `a5-1 = dst+i`
* `0xe90`: `bnez a4,0xe80` — loop back iff the stored byte ≠ 0 (more to copy)
* `0xe94`: `ret`           — the just-stored byte was the NUL (`i = s.length`)

So at loop head `0xe80` iteration `i` (`0 ≤ i ≤ len`): `a0 = dst`, `a1 = src+i`,
`a5 = dst+i`; the copied prefix `[dst, dst+i)` holds the source bytes; and byte
`i` is `bs i` (the string char for `i < len`, `0` at `i = len`). The `bnez` exits
exactly when `bs i = 0`, i.e. `i = len`, after storing the NUL at `dst+len`.

## TRUE dst footprint

The byte-head path writes **exactly `len + 1` bytes** `[dst, dst+len]` — the `len`
characters and the terminating NUL. (The `sb zero,7(a2)` finisher at `0x80006e98`
belongs to the *word-loop* byte tail, NOT this path; the byte-head loop's `sb`
writes the NUL itself as its final iteration.)

## Ghost parameters

`dst` (x10 in), `src` (x11 in), `s : String` (`CString m0 src s`), `r` (x1, return
addr, 4-aligned), `m0` (pinned memory), `bs : Nat → BitVec 8` (the offset→byte
function, `bs k = char k` for `k < len`, `bs len = 0`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr (CStr CString Mem)
open Vsa.Sim.Code (StrcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `StrcpyLoaded` preserved by a single byte insert outside the code region

The `strcpy` code lives in `[0x80006dc4, 0x80006ea0)`. A byte store outside that
range preserves every code-byte read (each concrete code address differs from the
out-of-range key by `omega`). -/

/-! ## The string byte-function ghost

`StrBytes m0 src len bs` packages what `CString` gives us about the source bytes,
in the offset→byte form the copy consumes:
* `chars`: byte `k < len` reads `bs k` (nonzero) from `src + k`;
* `nul`: byte `len` reads `bs len = 0` (the NUL) from `src + len`.

`bs len = 0` is recorded separately (`bs_nul`) so the `bnez` exit can fire. -/

/-! ## Region / no-wrap side conditions for the byte-head path

`CpyRegions dst src len` bundles the disjointness / no-wrap facts.  The written
region is `[dst, dst+len]` (`len+1` bytes); the read region is `[src, src+len]`.
Both live in RAM above the HTIF window and disjoint from the `strcpy` code
`[0x80006dc4, 0x80006ea0)`; the two regions are mutually disjoint. -/

/-! ## The copied-prefix memory invariant

`CpyInv dst src len bs i m0 mem` describes `mem` at byte-head iteration `i`
(`0 ≤ i ≤ len`):
* `copied`: `[dst, dst+i)` holds the copied bytes `bs`;
* `outside`: every address outside `[dst, dst+len]` still reads `m0`;
* `src_intact`: the source bytes `[src+i, src+len]` still read from `m0` (the
  copy never touches the source: disjoint regions). -/

/-! ## Blanket ghost-frame predicate (`NotWrittenCpy`) + generic per-class helpers

The byte-head path writes GPRs `x15` (`a5`), `x14` (`a4`), `x11` (`a1`).  `x10`
(`a0 = dst`) and `x1` (`ra`) are preserved.  `NotWrittenCpy R` is the disequality
conjunction over `{x11, x14, x15}` and the per-step noise write-set
`{PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip}`.  The STORE writes
only memory (no `rd`), covered by the noise disequalities alone. -/

/-! ## Store-byte identity: `stData 1 (zext b) = b` -/

/-! ## The config-level state predicate at the loop head `0x80006e80`

`StCpy g pc i r dst src len m0 bs c` bundles the standing observation at byte-head
iteration `i` (`0 ≤ i ≤ len`): `GoodState`, code loaded, PC, `a0 = dst`,
`a1 = src+i`, `a5 = dst+i`, `x1 = r`, `minstret` defined, `tick < 2`, `CpyRegions`,
`StrBytes`, `i ≤ len`, the copied-prefix invariant `CpyInv … i`, and the blanket
ghost frame.  `a4 = x14` is the scratch loaded byte (not tracked across the head). -/

/-! ## Pointer/window bounds for iteration `i`

The `lbu` reads at `src + i` (`i ≤ len`, so `src+i` is in RAM/above HTIF); the `sb`
writes at `a5 - 1 = dst + i`.  `ptr_toNat` bridges `.toNat`. -/

/-! ## State at `0x80006e90` (pre-`bnez`) for iteration `i`

After one loop body (lbu/addi a5/addi a1/sb) for iteration `i ≤ len`: `a1 = src+(i+1)`,
`a5 = dst+(i+1)`, `a4 = zext (bs i)`, and the copied prefix has advanced to `i+1`. -/

/-! ## One loop body iteration (`0x80006e80 → 0x80006e90`)

Chains `lbu a4 → addi a5 → addi a1 → sb a4,-1(a5)`.  The `lbu` reads `bs i` from
`src+i`; the two `addi`s advance `a5`/`a1`; the `sb` writes `bs i` at `dst+i`
(`sbAddr_succ_raw`), and `cpyinv_store` re-establishes `CpyInv … (i+1)`. -/

/-! ## The `bnez a4` at `0x80006e90` (loop back-edge / exit to ret)

`a4 = zext (bs i)`.  Taken iff `bs i ≠ 0` iff `i < len` (loop back to iteration
`i+1`); not-taken iff `bs i = 0` iff `i = len` (fall through to `ret` at `0xe94`
with the full described update `CpyInv … (len+1)`). -/

/-! ## The "done" configuration at `0x80006e94` (ret entry)

`a0 = dst` (strcpy returns dst), `x1 = r`, and the full described memory update
`CpyInv … (len+1)` — the copied prefix `[dst, dst+len]` (chars + NUL). -/

/-! ## Loop invariant, guard, measure

`LoopICpy = AtHeadCpy ∨ StCpyDone`: either at `0xe80` iteration `i ≤ len` (copied
prefix `[dst,dst+i)`), or done at `0xe94` (ret) with the full update.  `LoopBCpy`
= "at `0xe80` with `i < len`".  Measure `LoopMuCpy = 2^64 - a5.toNat`
(`a5 = dst+i`), strictly decreasing as `i` grows (`a5` increments by 1, no wrap). -/

/-! ## `ret` (`0x80006e94 → r`) and the described-update postcondition -/

/-! ## Preamble `mv a5,a0` (`0x80006e7c → 0x80006e80`)

Sets `a5 := dst` (`a0`), establishing `StCpy` at iteration `0` (nothing copied yet,
`mem = m0` outside, source fully intact). -/

/-! ## The byte-head-path total-correctness spec (from the byte-head entry `0xe7c`) -/

/-! ## Entry dispatch (`0x80006dc4 → 0x80006e7c`, misaligned → byte head)

* `0xdc4`: `or a5,a0,a1`   — `a5 := dst ||| src`
* `0xdc8`: `andi a5,a5,7`  — `a5 := (dst ||| src) &&& 7`
* `0xdcc`: `bnez a5,0xe7c` — taken iff `(dst ||| src) &&& 7 ≠ 0` (misaligned)

The byte-head path is the misaligned case: `(dst.toNat ||| src.toNat) % 8 ≠ 0`. -/

/-! ## The byte-head-path total-correctness spec (from the strcpy entry `0xdc4`)

The complete misaligned-path spec: from the `strcpy` entry `0x80006dc4` with
`x10 = dst`, `x11 = src`, a `StrBytes` source-byte description, `(dst|src)%8 ≠ 0`,
`x1 = r` 4-aligned, and `mem = m0`, the machine runs to `r` with `x10 = dst`,
`GoodState`, and the `len` chars + NUL copied into `[dst, dst+len]`. -/

/-! ## `CString`-phrased corollary

Packaging the source-byte description as `CString m0 src s`: the copy realizes
`s.length + 1` byte writes into `[dst, dst + s.length]` (`s.length` chars + NUL). -/

end Vsa.Sim
