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

/-- **The parked-at-entry precondition for a `#derive_case` segment.**  A config
sitting at the case's entry PC `pc0` with everything `name_seg` demands staged:
`GoodState`, the entry PC, a `minstret` witness, the `GHolds` pin list `L`, its
`KeysOK`, the `ChainFacts` bundle for the chain `bs`, the entry memory pinned to
`m0`, and the tick budget `< 2`.  This is the post of the node dispatch that
routes into the case (the row's `SubEvalReturn`/`PreEpilogueV` pre); `segToTriple`
runs the whole `bs` segment from here. -/
def SegPre (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some pc0 ∧
  (∃ vm, c.σ.regs.get? Register.minstret = some vm) ∧
  GHolds c.σ L ∧
  KeysOK (keysG L) ∧
  ChainFacts c.σ.mem c.σ.mem L lds bs ∧
  c.tick < 2

/-- **The reusable seg→`Triple` marshalling.**  From `SegPre` (parked at the
case's entry `pc0`) plus the row's one kernel `decide` `hwf`, the whole `bs`
segment runs to a config whose computed outcome — end PC `evalBlocksPC pc0
(SegEvalState.init L lds) bs`, registers `(evalBlocks bs (SegEvalState.init L
lds)).regs`, memory `writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log`
— the caller has proven satisfies `Q` (via `hpost`, uniform in the post state's
step counters).  Everything the `Triple` wants (running the `name_seg` `Steps`
and packaging the existential) is done here ONCE; a real row supplies only `hwf`
(`by decide`) and `hpost`, the `SubEvalReturn`/`PreEpilogueV` projection of its
own outcome off `out.regs`/`writeLog`.  Mirror of `jalStep_to_runtimeError` for
the straight-line/branch case bodies (Shape A). -/
theorem segToTriple (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      Q ⟨σ', i', u'⟩) :
    Triple (SegPre bs L lds pc0 m0) Q := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  -- Run the `#derive_case`-emitted `name_seg` on this config (via `segEval_sound`).
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, _hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  -- Rewrite the seg outcome's `writeLog c.σ.mem …` under the pinned entry memory.
  rw [hmem] at hmem'
  -- Package into the `∃ c', Steps c c' ∧ Q c'` a `Triple` wants; `Q` off `hpost`.
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, ?_, ?_⟩
  · exact hs
  · exact hpost σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hpc' hmi' hregs

#print axioms segToTriple

/-! ## Demo — applying `segToTriple` to `demoChain`/`demoChain_seg`

`demoChain` (DeriveCase.lean) is the three-`addi` chain `x5:=1; x6:=2; x7:=3`.
We instantiate `segToTriple` at the concrete entry `pc0 = 0x80000000` and empty
pin list, reading the computed end PC and the computed `x7 = 3` register (and the
mem/frame) off the outcome into a concrete post `DemoPost`.  The `ChainOK`
argument closes by ONE kernel `decide`; the outcome projections (`evalBlocksPC`,
`GHolds … out.regs`) reduce by `decide`/`rfl` on the concrete chain. -/

/-- A concrete row post read off the `demoChain` outcome: parked at the computed
end PC with `x7 = 3` (the last `addi`) and memory unchanged (the chain has no
stores, so `out.log = []` and `writeLog m0 [] = m0`). -/
def DemoPost (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x8000000c#64 ∧
  gprGet c.σ 7 = some 3#64

/-- The demo row: `Triple (SegPre demoChain [] [] 0x80000000 m0) (DemoPost m0)`,
built by `segToTriple` — the seg→`Triple` marshalling folded into one application.
The `hwf` argument is the row's one kernel `decide`; `hpost` projects the concrete
end PC / `x7 = 3` / unchanged memory off the computed outcome. -/
theorem demoChainRow (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre demoChain [] [] 0x80000000#64 m0) (DemoPost m0) := by
  apply segToTriple demoChain [] [] 0x80000000#64 m0 (DemoPost m0) (by decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_⟩
  · -- memory unchanged: `out.log = []`, `writeLog m0 [] = m0`.
    rw [hmem']; rfl
  · -- end PC: `evalBlocksPC 0x80000000 (init) demoChain` reduces to `0x8000000c`.
    rw [hpc']; rfl
  · -- `x7 = 3`: read off `GHolds σ' out.regs` via `gholds_lookup`.
    exact gholds_lookup (v := 3#64) _ hregs (by decide)

#print axioms demoChainRow

end Vsa.Sim
