import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvDefBridges2

/-!
# `EnvDefSeg` — the `env_define` straight-line prefixes as `#derive_case` segs

The `env_define` code region `[0x80002a5c, 0x80002c10)` has a bespoke byte-pin
battery (`Env_defineLoaded` + the hand `site_*_ed` lemmas in
`EnvDefBridges.lean`/`EnvDefSpec*`) that predates the block-reflection decode
table.  Every Shape-A bridge prefix there pays 5-15 hand `stepObs_alu`/`stepObs_jal`
site lemmas — each one a ~30-line invocation naming the concrete decode lemma
(`Vsa.Sim.DecodeTable.decode_<word>`), the `execute_*_char` characterization, the
four byte pins, and a dozen `by decide` side conditions.

This file demonstrates the payoff of putting the region ON the block-reflection
decode table: since **all 106 unique instruction words in the region are already
tabled** (verified by `scripts/decode_index.tsv`) and all 85 straight-line words
are supported by `decodeM`/`mkLine` (`BlockDecode.lean`), the straight-line body
of any bridge prefix is ONE `#derive_case`/`segToTriple` seg — the whole `Steps`
chain, computed end-PC, computed registers, and write log auto-threaded, the only
kernel obligation the single `ChainOK` `decide`.

## Why the `jal` stays a seam

The block terminator model (`TKind` in `BlockTerm.lean`) covers `br`/`j`/`jr` but
DELIBERATELY excludes `jal rd` (a *call*, which links `x1`) — see
`BlockTerm.lean:56`.  Each env_define prefix ends in `jal strlen`/`jal malloc`/…
(rd = x1), so the call-linkage stays the Shape-D `callSeg` seam (exactly as
`CmpDispatchSeg` keeps its `jal value_bool` a seam).  The `#derive_case` seg is
therefore the *straight-line argument-marshalling body* up to (not including) the
`jal`; that body is what the hand `site_*_ed` battery spends its bulk on.

The malloc prefix `0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal
malloc` has a genuine two-instruction straight-line body (`addi`/`addi`) — the
hand `site_80002b24_ed` + `site_80002b28_ed` pair (~60 lines).  Here it is ONE seg
`mallocArgSeg` (3 lines of block table) + ONE `segToTriple` row.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- The malloc-prefix straight-line body `0x80002b24 → 0x80002b2c`, two blocks
(fall-through, no terminator until the `jal` seam that follows):
  `addi x8,x10,1`  (`addi s0,a0,1` — the malloc size = strlen(name)+1) then
  `addi x10,x8,0`  (`mv a0,s0` — marshal the size into a0 for the call).
Both words (`00150413`, `00040513`) are tabled and `decodeM`-supported; `mkLine`
produces the concrete `MInstr` by `rfl`. -/
   -- mv   a0,s0  (= addi a0,s0,0)

/-! ## The `strlen` prefix's straight-line body — ONE instruction seg

The strlen prefix `0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen` has only a
one-instruction straight-line body (`mv a0,s2 = addi a0,s2,0`), the `jal` being
the seam.  Even this single-instruction case is a `#derive_case` seg (replacing
the hand `site_80002b1c_ed`, ~30 lines). -/

   -- mv a0,s2 (= addi a0,s2,0)

/- ## DEMO — the grow-path cap-compute prefix as a seg, via `bridgeOfSeg`

`EnvDefBridges2` builds the SAME `slliw;slli;sw;mv;jal realloc` cap-compute prefix
by hand: 5 per-site `stepObs_*` lemmas (`site_80002b90_ed .. site_80002ba0_ed`,
~165 lines) + `capComputePrefix_run` (~175 lines of run + per-register frame
threading) + `bridgeCapCompute_closed` (~90 lines of `ReallocPre` marshalling).

Here the whole straight-line body `0x80002b90..0x80002b9c` (`slliw;slli;sw;mv`) is
ONE `#derive_case` seg `capComputeSeg` (4 lines of block table), the jal seam is
the SAME existing `site_80002ba0_ed` repackaged into a `JalStep` by
`jalStep_of_obs` (one call), and `capComputeSeg_run` derives the full landed run
via `bridgeOfSeg` — replacing the ~340 lines of hand `site_*`+`*Prefix_run` with
the seg def + ~35 lines.  The `bridgeCapCompute_closed` `ReallocPre` marshalling
stays identical (it is the genuinely per-callee part) and is NOT re-proved here —
`capComputeSeg_run` is a drop-in for the `capComputePrefix_run` it consumes.

The `slliw` word `0x0017979b` at `0x80002b90` is the decode kind added in part (A);
the seg needs it on the block-reflection table, so this demo is only possible AFTER
the `MKind.slliw` add. -/

/- The cap-compute straight-line body `0x80002b90 → 0x80002b9c` (four blocks, the
body up to the `jal realloc` seam):
  `slliw a5,a5,1` (`x15 := 2*cap`), `slli a1,a5,3` (`x11 := newcap*8`),
  `sw a5,4(s4)` (`env->cap := newcap`), `mv a0,s6` (`x10 := env->names`).
All four words tabled + `decodeM`-supported; `mkLine` gives the concrete `MInstr`
by `rfl`. -/
   -- mv    a0,s6  (= addi a0,s6,0)

end Vsa.Sim
