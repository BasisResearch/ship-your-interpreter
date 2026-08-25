import Vsa.Sim.NegBlockProto
import Vsa.Alloc
import Vsa.Sim.InterpEntry
import Vsa.Sim.RegPins
import Lean

/-!
# Stage C — block-frame discharge helpers (`BlockTactics2`)

Reusable helpers for the register-frame side-conditions the block frame lemmas
(`hframePro`/`hframeBlk`/`hframeTail`, i.e. the `∀ R … → σ'.R = σ.R` outputs of
`neg_prologue_block`/`neg_loadstore_full`/`neg_tail_block`) demand at each call
site. Each such application needs two arguments for a universally-quantified
register `R`:

1. `(∀ rr ∈ noiseRegs, (rr == R) = false)` — closed by `abiNoise_noiseRegs hR`.
2. `(∀ n ∈ wrRegsM b.body, (gprReg n == R) = false)` — closed by the
   `block_frame_wr` tactic given the block's concrete written-reg index list.

`abiPreserved_ne` is the standalone form of the local `abi_ne'` those proofs
carried inline (the callee-saved exceptions like `he8 : (Register.x8 == R) =
false` are picked up by an `assumption` arm).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. Only Lean 4 core + Std tactics.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Alloc
open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Vsa.Sim

/-- `AbiPreserved R` and `¬ AbiPreserved X` give `(X == R) = false`: two distinct
callee-saved-vs-not registers can never be equal. The standalone form of the
inline `abi_ne'` that `blockC_neg`'s `hframeG` carried. -/
theorem abiPreserved_ne {R X : Register} (hR : AbiPreserved R = true)
    (hX : AbiPreserved X = false) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

/-- `AbiPreservedNoise R` discharges the first frame side-condition,
`∀ rr ∈ noiseRegs, (rr == R) = false`, by unpacking its seven noise-register
disequalities. -/
theorem abiNoise_noiseRegs {R : Register} (hR : AbiPreservedNoise R) :
    ∀ rr ∈ noiseRegs, (rr == R) = false := by
  obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
  intro rr hrr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil,
    or_false] at hrr
  rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `block_frame_wr [i₀, …, iₖ]` closes a goal
`∀ n ∈ wrRegsM b.body, (gprReg n == R) = false` (or the `wrChain` variant) where
`[i₀, …, iₖ]` is the block's concrete list of written GPR indices (as it reduces
under `wrRegsM`/`wrChain`). It reduces the membership to a `k+1`-way disjunction
of `n = iⱼ` equalities, substitutes each, and closes every resulting
`(gprReg iⱼ == R) = false` by `abiPreserved_ne` (an anonymous `AbiPreserved R =
true` reached by `assumption`, `AbiPreserved (gprReg iⱼ) = false` by `decide`)
with an `assumption` fallback that picks up any callee-saved exception hyp in
context (e.g. `he8 : (Register.x8 == R) = false` for the callee-saved `x8`). The
`rcases` alternative count is derived from the list length so the substitutions
actually fire. -/
elab "block_frame_wr" "[" ids:num,* "]" : tactic => do
  let n := ids.getElems.size
  -- length-`n` `rcases … with rfl | rfl | … | rfl`, then close all goals.
  let listStx ← `(([$[$(ids.getElems)],*] : List Nat))
  evalTactic (← `(tactic| intro n hn))
  evalTactic (← `(tactic| have hn' : n ∈ $listStx := hn))
  evalTactic (← `(tactic| clear hn))
  evalTactic (← `(tactic|
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn'))
  -- `rfl | rfl | … | rfl` with `n` alternatives, assembled as an `rcasesPatMed`
  -- (`sepBy1(rcasesPat, " | ")`) so the `rcases` substitutions actually fire.
  -- an UNHYGIENIC `rfl` ident: `rcases` recognises the subst pattern by matching
  -- the raw name `` `rfl ``, so macro scopes must not be attached.
  let rflPat ← `(rcasesPat| $(mkIdent `rfl):ident)
  let alts : Array (TSyntax `rcasesPat) := Array.replicate n rflPat
  let med ← `(rcasesPatMed| $alts|*)
  evalTactic (← `(tactic| rcases hn' with $med:rcasesPatMed))
  evalTactic (← `(tactic|
    all_goals first
      | exact abiPreserved_ne (by assumption) (by decide)
      | assumption))

/-! ## C3 — load/store side-condition bundle discharge (`ld_ok` / `st_ok`)

The block Pres (`NegBlockProto.LdOK8`/`LdOK4`/`StOK8`) each bundle the RAM-bound /
HTIF-window / alignment sub-facts (and, for loads, the byte pins). Call sites used
to spell out the anonymous constructor with a per-field `by rw [haddr…]; omega`.
These tactics assemble the bundle from ONE address-normaliser `haddr : ea.toNat =
k` (the RAM/window/alignment facts then follow by `omega` off the ambient `sp`/
`tohost` bounds) plus the caller's byte pins.

`tohostAddr` is a `def`; `omega` can't see through it, so each tactic first
rewrites it to its literal value (`rfl`) before the `omega`. -/

/-- Discharge an `StOK8 ea` from `haddr : ea.toNat = k`: RAM bounds + above-HTIF
window + 8-alignment, all by `omega` off the ambient `sp`/tohost bounds. -/
macro "st_ok" haddr:term : tactic =>
  `(tactic|
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      first
        | (rw [show tohostAddr = (0x8001ad00 : Nat) from rfl, $haddr:term]; omega)
        | (rw [$haddr:term]; omega))

/-- Discharge an `LdOK8 m ea bs` from `haddr : ea.toNat = k` and the eight byte
pins `[p0,…,p7]` (each `m[k+i]? = some bᵢ`). The RAM/window/alignment tuple goes
by `omega`; each pin rewrites `ea.toNat` by `haddr` and closes by the supplied
proof. -/
macro "ld_ok8" haddr:term:max " [" ps:term,* "]" : tactic =>
  `(tactic|
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (rw [show tohostAddr = (0x8001ad00 : Nat) from rfl, $haddr:term]; omega)
        | (rw [$haddr:term]; omega)
        | (rw [$haddr:term]; first $[| exact $ps]*))

/-- `LdOK4` variant of `ld_ok8` — four byte pins. -/
macro "ld_ok4" haddr:term:max " [" ps:term,* "]" : tactic =>
  `(tactic|
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (rw [show tohostAddr = (0x8001ad00 : Nat) from rfl, $haddr:term]; omega)
        | (rw [$haddr:term]; omega)
        | (rw [$haddr:term]; first $[| exact $ps]*))

end Vsa.Sim
