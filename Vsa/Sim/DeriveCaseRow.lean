import Vsa.Sim.SegEvalSound
import Vsa.Sim.FrameCalc
import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

/-!
# `DeriveCaseRow` — the seg→`Triple` marshalling combinator (L3, v2 step 3)

`#derive_case` (`Vsa/Sim/DeriveCase.lean`) emits `theorem name_seg` in
`SegEvalState` normal form: from the entry pins it produces
`∃ σ' i', Steps ⟨σ,i,u⟩ ⟨σ',i',…⟩ ∧ … ∧ σ'.mem = writeLog σ.mem out.log ∧
σ'.regs.PC = evalBlocksPC … ∧ GHolds σ' out.regs ∧ frame`, conditional on a
`ChainFacts`+`ChainOK` bundle.  `DeriveCase.lean:33-36` flags the missing v2
piece: the `pre`/`post` `Triple`-closing layer marshalling that computed
outcome into the shape a real row's caller wants.

This file builds that marshalling as a **reusable combinator** `segToTriple`,
mirroring `Vsa/Sim/ErrorSiteJal.lean`'s `jalStep_to_runtimeError` (pre-predicate
over `Config`, run the `Steps`, project the structured post out of the outcome).

* `SegPre bs L lds pc0 m0 c` — the "parked at the case's entry `pc0`" precondition:
  exactly the hypotheses `name_seg` demands (`GoodState`, `PC = pc0`, a `minstret`
  witness, `GHolds`, `KeysOK`, `ChainFacts`), plus the entry memory pinned to `m0`
  and the tick budget `< 2`.  This is the concrete shape of a real row's entry —
  the `SubEvalReturn`/`PreEpilogueV` pre once its ghosts are named.
* `segToTriple` — from `SegPre`, the row's ONE kernel `decide` (`hwf : ChainOK
  pc0 (keysG L) bs`), and a caller-supplied post `Q` that reads the **computed**
  outcome (end PC `evalBlocksPC pc0 (SegEvalState.init L lds) bs`, the computed
  registers `out.regs`, the write-log-updated memory `writeLog m0 out.log`) off
  the seg conclusion, produces `Triple (SegPre …) Q`.  The caller proves `Q` from
  the outcome once (`hpost`); everything else — running the `name_seg` `Steps` and
  packaging it into the `∃ c', Steps c c' ∧ Q c'` a `Triple` wants — is here.

The demo `demoChainRow` applies it to `demoChain`/`demoChain_seg` (DeriveCase.lean),
reading the computed end PC + a computed register (`x7 = 3`, the last `addi`) +
memory off the outcome into a concrete `Triple`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-! ## Demo — applying `segToTriple` to `demoChain`/`demoChain_seg`

`demoChain` (DeriveCase.lean) is the three-`addi` chain `x5:=1; x6:=2; x7:=3`.
We instantiate `segToTriple` at the concrete entry `pc0 = 0x80000000` and empty
pin list, reading the computed end PC and the computed `x7 = 3` register (and the
mem/frame) off the outcome into a concrete post `DemoPost`.  The `ChainOK`
argument closes by ONE kernel `decide`; the outcome projections (`evalBlocksPC`,
`GHolds … out.regs`) reduce by `decide`/`rfl` on the concrete chain. -/

end Vsa.Sim
