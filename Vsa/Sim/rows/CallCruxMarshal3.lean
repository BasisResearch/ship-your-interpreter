import Vsa.Sim.rows.CallCruxMarshal2

/-!
# `CallCruxMarshal3` — the fold-exit falsity (wave 43, lane cruxdefine)

**The 8th statement falsity** (ledger `callparamfold-carrier-n-unreachable`,
Law 4).  The params-fold is a DO-WHILE: the loop head `callParamFoldPC =
0x800032dc` is entered exactly `n` times (`k = 0..n-1`), and after the LAST
`env_define` the back-edge `bne s6,a5 @0x8000331c` compares the bound `8·n`
with the bumped index `8·n` and FALLS THROUGH — `callParamFoldCarrier … n`
(PC pinned at the head) is never reached.  So the wave-37
`callClosureEntrySplice` premises `hFoldSeam` (at `k = n-1`) and
`hFoldToHandoff` (sourced at `carrier n`) were machine-undischargeable.

The machine-checked obstruction, in the two landed discharge vehicles:

* `foldBackLoop_facts_last_false` — the wave-40 loop-polarity row's
  `ChainFacts` (2-pin `callClosureFoldBackL`) is UNINHABITED at the last
  param: its bne-TAKEN guard reduces to `8·(k+1) != 8·(k+1) = true`.
* `foldBackLoop5_facts_last_false` — the same for this wave's 5-pin
  `callClosureFoldBackL5`, hence `foldDefineReturn_last_false`: the
  `FoldDefineReturn` pin bundle (CallCruxMarshal2 §3) is uninhabited at
  `k + 1 = n` — `callParamFoldSeamStep` correctly covers ONLY `k + 1 < n`.

The amendment (same wave, `rows/CallClosureSplice.lean`): `hFoldSeam` ranges
over `k + 1 < n`, `hFoldToHandoff` is sourced at `carrier (n-1)` — the last
iteration (staging ≫ env_define ≫ EXIT-polarity back-edge ≫ value_null ≫ body
entry) belongs to the handoff leg, which is the machine truth.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## The obstruction — the loop back-edge cannot fire at the last param -/

/-- **The wave-40 loop row is unusable at the last param**: with the fold bound
pinned to `8·(k+1)` (i.e. `n = k+1`, the LAST iteration's return) the
loop-polarity `ChainFacts` is uninhabited — its bne-TAKEN guard demands
`8·(k+1) != 8·k + 8`, false by `mul8_ofNat_succ`. -/
theorem foldBackLoop_facts_last_false (sp : BitVec 64) (k : Nat)
    (ib : List (BitVec 8)) (m m2 : Std.ExtHashMap Nat (BitVec 8))
    (hib : bytesVal MKind.ld ib = 8#64 * BitVec.ofNat 64 k)
    (hfacts : ChainFacts m m2
      (callClosureFoldBackL sp (8#64 * BitVec.ofNat 64 (k + 1))) [ib]
      callClosureFoldBackLoopSeg) :
    False := by
  obtain ⟨⟨_hprog, _hpins, hterm⟩, -⟩ := hfacts
  -- the bne-TAKEN guard, reduced on the concrete seg + pin structure:
  have hg : ((8#64 * BitVec.ofNat 64 (k + 1))
      != (bytesVal MKind.ld ib + sign_extend (m := 64) (0x008#12))) = true := hterm
  rw [hib] at hg
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide
  rw [h8, ← mul8_ofNat_succ] at hg
  simp at hg

#print axioms foldBackLoop_facts_last_false

/-- The same obstruction on this wave's 5-pin list (`callClosureFoldBackL5`). -/
theorem foldBackLoop5_facts_last_false (sp cur fp clp : BitVec 64) (k : Nat)
    (ib : List (BitVec 8)) (m m2 : Std.ExtHashMap Nat (BitVec 8))
    (hib : bytesVal MKind.ld ib = 8#64 * BitVec.ofNat 64 k)
    (hfacts : ChainFacts m m2
      (callClosureFoldBackL5 sp cur fp clp (8#64 * BitVec.ofNat 64 (k + 1)))
      [ib] callClosureFoldBackLoopSeg) :
    False := by
  obtain ⟨⟨_hprog, _hpins, hterm⟩, -⟩ := hfacts
  have hg : ((8#64 * BitVec.ofNat 64 (k + 1))
      != (bytesVal MKind.ld ib + sign_extend (m := 64) (0x008#12))) = true := hterm
  rw [hib] at hg
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide
  rw [h8, ← mul8_ofNat_succ] at hg
  simp at hg

#print axioms foldBackLoop5_facts_last_false

/-- **`FoldDefineReturn` is uninhabited at the last param** (`k + 1 = n`):
its `spill` field carries the loop-polarity `ChainFacts`, impossible there.
`callParamFoldSeamStep` therefore covers exactly the amended `k + 1 < n`
range; the last iteration is the `hFoldToHandoff` leg. -/
theorem foldDefineReturn_last_false
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp fp clp : BitVec 64} {m0 : Std.ExtHashMap Nat (BitVec 8)}
    {k : Nat} {hk : k < (cd.params.zip vs).length} {c : Config}
    (hlast : (cd.params.zip vs).length = k + 1)
    (h : FoldDefineReturn N A SL φf' φc st store' cd vs frame sp fp clp m0 k
      hk c) :
    False := by
  obtain ⟨ib, hib, hfacts⟩ := h.spill
  rw [hlast] at hfacts
  exact foldBackLoop5_facts_last_false sp
    (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp k ib
    c.σ.mem c.σ.mem hib hfacts

#print axioms foldDefineReturn_last_false

end Vsa.Sim
