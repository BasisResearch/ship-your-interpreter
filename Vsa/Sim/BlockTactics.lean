import Vsa.Sim.BlockTerm

/-!
# `block_facts` — auto-discharge the mechanical half of `BBlockFacts`

The `BBlockFacts` bundle a `bblock_sound_bt` application needs is half
mechanical and half data-dependent. The mechanical half is a pure function of
each instruction's `pc`/`word`: the four code-byte pins come from
`Code.<fn>_at_<pc> h`, the decode from `DecodeTable.decode_<word>`.

`block_facts h with "<prefix>"` walks the goal, closes every
`BytePinsM`/`DecodeFactM`/`BytePinsT`/`DecodeFactT`/`True` leaf by generating and
applying those lemmas from the instruction literal, and leaves the
data-dependent leaves (`MemFacts`, terminator guards) as fresh goals in program
order. No search: each closed leaf is one named `exact`.
-/

open Lean Elab Tactic Meta

namespace Vsa.Sim

/-! ## Stage C2 — register projection (`block_reg`)

`block_reg h n` projects the `n`-th GPR out of a block-output
`h : GHolds σ' (runGM …)` (or any `GHolds σ' L` whose association list is
concrete). It expands to `gholds_lookup (n := n) _ h rfl`, where the trailing
`rfl` computes `lookupG n (runGM …) = some v` and fixes `v` to the block's
computed result; the result type `gprGet σ' n = some v` is *definitionally*
`σ'.regs.get? (gprReg n) = some v`, i.e. `σ'.regs.get? Register.x⟨n⟩ = some v`, so
it drops straight into the positional-projection slots (`hGH.2.2.1`, …) that the
block lemmas used to hand-thread. The index `n` is given explicitly — it cannot
be recovered by unifying against the `gprGet`-defeq goal. -/

end Vsa.Sim
