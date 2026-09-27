import Vsa.Sim.StrcmpSpecW3
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec, part 4 (NUL exits, `strcmp_word_spec`, `strcmp_full_spec`)

Finishes the aligned word path. `StrcmpSpecW2` widened `WordExit`'s NUL arm to the full
register state `WNulExit`; here we discharge the three NUL-word blocks
(`0xfac`/`0xfa4`/`0xfb8`) to `BDone`, assemble the word-path spec `strcmp_word_spec`, and
unify with the byte path in `strcmp_full_spec`.

**NUL-exit control flow** (from `StrcmpSpecW3`'s verified disasm notes). At a NUL exit for
offset `n = 24j + off(pc)`, A's word at `n` holds the NUL (`la < n+8`). The block advances
`a0/a1` to `pa+n`/`pb+n` (`fa4` by 8, `fb8` by 16, `fac` by 0) then `bne a2,a3` re-tests the
cached words:

* **equal** ⇒ both strings' NULs coincide (`la = lb`), so the strings are EQUAL and
  `li a0,0; ret` returns `0` = `strcmpSpecSign` (via `strcmpSpecSign_eq`);
* **differ** ⇒ jump to the byte loop `0xf84` at the advanced pointer `pa+n` over the
  suffixes `csa.drop n` / `csb.drop n`; `byte_loop_to_done` + `byte_f9c_ret` finds the
  tail difference, and `strcmpSpecSign_drop` lifts the suffix sign to the whole strings.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Region-suffix bridge (word region → byte region at the advanced pointer)

The byte-loop re-entry runs `BSt` (a `StrcmpRegion`, byte width-1 reads up to `p+len`) at
base `pa+n` with the suffix string `csa.drop n` (length `la - n`). We derive a
`StrcmpRegion (pa + ofNat n) (la - n)` from the word `StrcmpWRegion pa la`, using `n ≤ la`
(so `pa.toNat + n + (la - n) + 1 = pa.toNat + la + 1 ≤ pa.toNat + la + 8`). -/

/-! ## NUL-exit equal case: `la = lb`, spec sign `0`

When the cached words are EQUAL at the NUL offset `n` and A's word holds the NUL
(`n ≤ la < n+8`), the two strings terminate at the same place. From `BytePrefix csa csb n`
plus byte-for-byte word agreement on `[n, n+8)`, we get `BytePrefix csa csb la` and
`byteVal csb la = 0`, hence `lb = la` and `strcmpSpecSign csa csb = 0`. -/

/-! ## Byte-loop suffix run: `BSt (drop n) 0` → `BDone` for the WHOLE strings

From the byte-loop head at `0xf84`, base `pa+n`/`pb+n`, suffix strings `csa.drop n` /
`csb.drop n`, the byte loop finds the tail difference and returns to `r` with the SUFFIX
spec sign; `strcmpSpecSign_drop` (under `[0,n)` agreement) rewrites it to the whole-string
sign. -/

/-! ## Shared byte-loop head builder at a NUL `bne`-taken target (`0xf84`)

Both NUL `bne a2,a3` sites (`0xfac`, `0xfc0`) branch to `0xf84` with `a0 = pa+n`,
`a1 = pb+n`, the words differing. This produces the byte-loop head `BSt` over the suffix
strings so `bst_suffix_to_done` closes it. -/

/-! ## The NUL `bne a2,a3` sites (`0xfac`, `0xfc0`)

At the bne site the pointers are already advanced to `pa+n`/`pb+n`, `a2/a3` hold the cached
words. Equal ⇒ `li a0,0; ret` (result 0, via `nul_eq_spec_zero`); differ ⇒ byte loop at
`pa+n` (via `mk_suffix_bst` + `bst_suffix_to_done`). Two near-identical instances differing
only in the ret-path site names (`fb0/fb4` vs `fc4/fc8`). -/

/-! ## The NUL-word exit `WNulExit → BDone`

Case on the three NUL-block PCs: `fac` reaches its `bne` directly (`nulOff 0`); `fa4`
does `addi a0,8; addi a1,8` (via `word_off8`) then falls into `fac`; `fb8` does
`addi a0,16; addi a1,16` (via `word_off16`) then `bne` at `fc0`. Each closes with
`nul_bne_fac`/`nul_bne_fc0`. -/

/-! ## The aligned word-path `strcmp` spec (`PreWCmp → BDone`)

Composes `strcmp_word_reaches_exit` (entry `0xea0` → `WordExit`) with the exit dispatch:
the lane arm goes to `BDone` via `wlane_to_done`, the NUL arm via `wnul_to_done`. -/

/-! ## Top-level `strcmp` full spec (byte path ∪ word path)

`strcmp_full_pre` widens `strcmp_pre`'s misalignment disjunct to `True` (either alignment
is admissible), keeping all shared side conditions and adding the word-path witnesses
(`StrcmpWRegion`, `MaskPinned`). `strcmp_full_post` is `strcmp_post` verbatim. The proof
`Triple.cases` on the entry alignment test `(pa|pb) & 7 = 0`: aligned → `strcmp_word_spec`,
misaligned → `strcmp_byte_path`. -/

end Vsa.Sim
