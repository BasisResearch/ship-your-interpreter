import Vsa.Sim.NegBlockProto
import Vsa.Sim.EvalNegSim
import Vsa.Sim.BlockAdapter
import Vsa.Triple

/-!
# Stage A0 — neg block lemmas as `Triple`s + a `seq`/`conseq` compose demo

Layer 1 (`Vsa/Triple.lean`) already gives the program logic
`Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'` over `Config = ⟨σ, tick,
steps⟩`, with `seq`, `conseq`, … proven. `value_int_spec` is already a `Triple`
(its `int_pre`/`int_post` are the template used here).

This file restates the three neg block lemmas from `NegBlockProto.lean` —
`neg_prologue_block`, `neg_loadstore_full`, `neg_tail_block` — as `Triple`s.
Each block's entry pins/tick/memory become a `…Pre : … → Config → Prop`; its
exit pins/tick/memory/frame become a `…Post`. Following the Layer-1 design
(doc-comment at the top of `Vsa/Triple.lean`), framing is **not** a rule: the
register frame and memory survival ride *inside* the postcondition, exactly as
`int_post` does. `conseq` threads them at seams.

The wrapper proofs are near-mechanical: `intro c hpre; obtain … := hpre; obtain
… := <block lemma> …; exact ⟨…⟩`. The `Steps` witness is the block lemma's own
`Steps` (with `c' := ⟨σ', i', c.steps + blen⟩`).

The compose demo `neg_prologue_loadstore_triple` chains the prologue and
load/store triples via `Triple.seq`, with a `Triple.conseq` at the seam
absorbing the marshalling (the prologue's post PC/regs/mem entail the
load/store's pre — the `x13` kind-dword bridge and code-survival across the
memory-unchanged prologue). This validates that `seq`+`conseq` compose block
triples end-to-end.

NO Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (Eval_exprLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Block 1 — the neg PROLOGUE (`neg_prologue_block`, σ0→σ4)

Entry PC `0x800035ec`, exit PC `0x800039ac`. Loads the op token, `li a5,12`,
loads the kind dword, and takes `beq a4,a5`. Memory is unchanged; the frame is
carried in the post. `m0` threads the entry memory so a downstream seam can
recover the load/store side-conditions about it. -/

/-! ## Block 2 — the neg LOAD/STORE run (`neg_loadstore_full`, σ4→σ10)

Entry PC `0x800039ac`, exit PC `0x800039c4`. Three loads (payload/dead/kind) +
three error-arg staging stores. Memory ends in `writeLog` form; the frame rides
in the post. -/

/-! ## Block 3 — the neg TAIL (`neg_tail_block`, σ10→σ15)

Entry PC `0x800039c4`, exit PC `0x800039d8`. `li a2,2; lw s0,4(s0); bne a0,a2
not-taken; neg a1,a1; mv a0,s1`. Memory unchanged; frame in the post. -/

/-! ## Compose demo — `seq` + `conseq` chain two block triples

Chains the prologue triple to the load/store triple. The seam `conseq` marshals
the prologue's post into the load/store's pre:
* PC `0x800039ac` matches on the nose;
* the `x13` **kind-dword bridge** — prologue post fixes `x13 = bytesVal .ld
  [kb…]`, so the load/store's ghost `v13` is instantiated to that value;
* **code-survival** — prologue keeps `mem = m0`, so `Eval_exprLoaded` and the
  load/store side-conditions (`LdOK`/`StOK` on `m0`) carry across unchanged.

The composed precondition therefore additionally asserts, about the *entry*
memory `m0`, the load/store's memory side-conditions (they are ghost facts about
`m0` that the prologue does not itself supply, but which survive its
memory-preserving run). This is the sound assertion-carried framing the plan
calls for. -/

/-! ## Full 3-block spine — `neg_blocks_triple` (σ0→σ15, PC 0x800035ec→0x800039d8)

The core **A1** result: the whole straight-line neg spine `0x800035ec → 0x800039d8`
as ONE composed `Triple`, chaining `negPrologue_triple`, `negLoadStore_triple`,
`negTail_triple` via `Triple.seq`+`Triple.conseq` at the two seams.

The prologue→loadstore seam is the `neg_prologue_loadstore_triple` demo above.
The new **loadstore→tail seam** absorbs:
* the kind-int bridge `x10 = bytesVal .lw [kb…] = 2#64` (side-condition `hkind2`);
* the payload bridge `x11 = bytesVal .ld [pb…]` → the tail ghost `p11`;
* the carried callee-saved `x9`/`x2`/`x8`;
* **code-survival across the three error stores**: the loadstore Post fixes
  `mem = writeLog m0 (wlogM …)`, three 8-byte stores at `v2+0xf0/0xf8/0x100`; the
  tail wants `Eval_exprLoaded mem` and the e→line `LdOK4 mem (v8+4) [lb…]`, both
  recovered from the `m0`-versions via `writeLog_getElem_disjoint` on the three
  store windows (carried as the disjointness side-conditions below).

The tail `minstret` witness is obtained from the loadstore Post's `∃ w`. -/

