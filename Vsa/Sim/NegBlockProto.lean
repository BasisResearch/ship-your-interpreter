import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockTactics
import Vsa.Sim.NegTailSites

/-!
# `NegBlockProto` — prototype: the neg-tail load/store run via ONE block lemma

Proof-of-concept for migrating the hand-threaded `blockC_neg` (EvalNegSim2) to
the basic-block reflection lemma. The segment `0x800039ac – 0x800039c0`
(σ5–σ10 in the hand proof, **180 lines**): three loads that extract the
sub-value's payload / dead / kind words, then three error-arg staging stores.

Here it is ONE `bblock_sound_bt` application (fall-through terminator). The
loads' values (`bytesVal`), the three stores (`writeLog`), the PC, the `Steps`
chain, the minstret/tick/output invariants, and the callee-saved frame all come
out computed. Compare the line counts at the bottom of the file.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (Eval_exprLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

