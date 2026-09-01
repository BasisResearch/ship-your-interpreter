import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ReprSurvival
import Vsa.Sim.SegReadback
import Vsa.Sim.rows.CallClosureFoldBack
import Vsa.Sim.rows.CallClosureNormalRet
import Vsa.Sim.rows.CallClosureRow

/-!
# `CallCruxMarshal` — the carrier re-assembly bricks between the crux span rows
(wave 42, lane cruxmarsh, plan queue item 4)

The wave-40 crux spans landed as `#derive_case`/`segToTriple` rows
(`callClosureFoldBackLoopRow`/`…ExitRow`, `callClosureRetClassRow`,
`callClosureNormalJoinRow`, `callClosureBodyExit{Ret,Normal}Row`).  Each
concludes a `Post` of the uniform shape

```
GoodState c.σ ∧ c.σ.mem = writeLog m0 log ∧ c.σ.regs.get? PC = some q ∧
  GHolds c.σ (evalBlocks seg …).regs
```

To thread these into the NAMED carriers the next stage consumes
(`CallParamFoldInv`, `BodyHandoff`, `SegExit`) the marshalling must re-establish
`OutRepr` — the console-output correspondence — at the reached config.

## The obstruction that shaped this file (ledger `rowpost-drops-sailoutput-blocks-outrepr`)

`OutRepr σ st = (Machine.output σ = st.out)` depends ONLY on `σ.sailOutput`, so a
memory-only span (every crux span is one) preserves it — `segEval_sound` DOES
prove `σ'.sailOutput = σ.sailOutput`.  But `segToTriple`'s `hpost`
(`DeriveCaseRow.lean`) DROPS that fact, so the landed row `Post` defs cannot
carry `sailOutput`, and `OutRepr` is underivable at any row-Post.

The freeze-safe fix (no edit to `DeriveCaseRow`): `segToTripleOut`, a sailOutput
-carrying `segToTriple` built on `segEval_sound` DIRECTLY (reachable through the
`DeriveCaseRow → SegEvalSound` import).  Its precondition `SegPreO` additionally
pins the entry `sailOutput` to a ghost `s0`, and its `hpost` receives
`σ'.sailOutput = s0` — so a marshalling row lands `OutRepr` via
`outRepr_of_sailOutput_eq`.  This is the reusable brick every span→carrier
re-assembly needs — factored ONCE (CLAUDE.md law 3: two similar marshals ⇒
factor before the third).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

namespace Vsa.Sim

set_option linter.unusedVariables false

/-! ## §1. The sailOutput-carrying seg→`Triple` marshalling brick -/

/-- **The parked-at-entry precondition carrying the entry `sailOutput`.**  Same
as `SegPre` plus a pin of the entry state's `sailOutput` to a ghost `s0` — the
minimal extension that lets the marshalling combinator surface the memory-only
span's output preservation.  A row that already holds `SegPre bs L lds pc0 m0`
plus `c.σ.sailOutput = s0` (any config with an `OutRepr` witness has this by
`rfl` at `s0 := c.σ.sailOutput`) satisfies `SegPreO`. -/
def SegPreO (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (s0 : Array String) (c : Config) : Prop :=
  SegPre bs L lds pc0 m0 c ∧ c.σ.sailOutput = s0

/-- **`segToTripleOut`** — `segToTriple` with the `σ'.sailOutput = s0` fact
threaded into `hpost`.  Built on `segEval_sound` directly (which proves the
sailOutput equation) rather than on `segToTriple`, so the reached config's
`OutRepr` is derivable in the marshalling `hpost` — the fact `segToTriple`
discards.  Everything else is identical to `segToTriple`. -/
theorem segToTripleOut (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (s0 : Array String)
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.sailOutput = s0 →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      Q ⟨σ', i', u'⟩) :
    Triple (SegPreO bs L lds pc0 m0 s0) Q := by
  intro c hpre
  obtain ⟨⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩, hso⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, _hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  rw [hso] at hout
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  exact hpost σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hout hpc' hmi' hregs

#print axioms segToTripleOut

/-! ## §2. `OutRepr` transport off a sailOutput carry

Given the entry `OutRepr σ0 st` (`Machine.output σ0 = st.out`) and the reached
state's `sailOutput = σ0.sailOutput` (what `segToTripleOut` surfaces),
`OutRepr σ' st` follows.  This is `outRepr_of_sailOutput_eq` (`ReprSurvival.lean`)
packaged against a ghost sailOutput `s0`: the marshalling row carries the entry
`OutRepr` and pins `s0 := σ0.sailOutput`, and this brick lands the exit `OutRepr`.
It is the field every span→`SegExit`/`CallParamFoldInv`/`BodyHandoff`
re-assembly was missing. -/

/-- **`outRepr_transport`** — the usable form.  From the marshalling row's
`σ'.sailOutput = s0` (segToTripleOut's `hpost` fact) and the entry-config
`OutRepr` witness re-expressed as `Machine.output σ0 = st.out` with
`σ0.sailOutput = s0`, land `OutRepr σ' st`. -/
theorem outRepr_transport {σ' σ0 : MState} {st : Vsa.While.St}
    (hso : σ'.sailOutput = σ0.sailOutput)
    (hOut0 : OutRepr σ0 st) :
    OutRepr σ' st :=
  outRepr_of_sailOutput_eq hso hOut0

#print axioms outRepr_transport

/-! ## §3. The register-pin marshalling brick (GHolds → `regs.get?`)

`gholds_lookup` (`BlockPilot.lean`) reads a pin off `GHolds σ L` as
`gprGet σ n = some v`; `gprGet σ n = σ.regs.get? Register.xN` by `rfl` at every
concrete GPR index.  `gholds_reg` chains the two so a carrier's register field
(`c.σ.regs.get? Register.xN = some v`) is one application off a row-Post's
`GHolds` — the shape every carrier re-assembly repeats per pinned register. -/

/-- Read a concrete GPR pin off `GHolds` straight into the `gprGet` form.
`hread` is the seg-outcome readback of index `n` (`by rfl` for a load-free
pass-through, `lookupG_runGM_snoc`+`srcVal_runGM_ne` for a load-bearing one —
`SegReadback.gholds_lookup_ld`).  At every concrete GPR index `n`,
`gprGet σ n = σ.regs.get? Register.xN` DEFINITIONALLY (`by rfl`), so the caller
casts the conclusion into the carrier's `regs.get? Register.xN = some v` field
by `rfl` — no coercion (`gprGet` and `regs.get? Register.xN` share the type
`Option (BitVec 64)` only at a concrete GPR, which is why the bridge is a
per-index `rfl` at the call site, not a generic hypothesis). -/
theorem gholds_reg {σ : MState} {L : GRegs} {n : Nat} {v : BitVec 64}
    (hregs : GHolds σ L)
    (hread : lookupG n L = some v) :
    gprGet σ n = some v :=
  gholds_lookup L hregs hread

#print axioms gholds_reg

/-- The `gprGet`/`regs.get?` bridge at the crux's pinned GPR indices, as a
`decide`-free `rfl` battery — the per-index casts `gholds_reg` conclusions need.
(One entry per register a `CallParamFoldInv`/`SegExit` field reads.) -/
theorem gprGet_x2  (σ : MState) : gprGet σ 2  = σ.regs.get? Register.x2  := rfl
theorem gprGet_x8  (σ : MState) : gprGet σ 8  = σ.regs.get? Register.x8  := rfl
theorem gprGet_x10 (σ : MState) : gprGet σ 10 = σ.regs.get? Register.x10 := rfl
theorem gprGet_x15 (σ : MState) : gprGet σ 15 = σ.regs.get? Register.x15 := rfl
theorem gprGet_x18 (σ : MState) : gprGet σ 18 = σ.regs.get? Register.x18 := rfl
theorem gprGet_x19 (σ : MState) : gprGet σ 19 = σ.regs.get? Register.x19 := rfl
theorem gprGet_x21 (σ : MState) : gprGet σ 21 = σ.regs.get? Register.x21 := rfl
theorem gprGet_x22 (σ : MState) : gprGet σ 22 = σ.regs.get? Register.x22 := rfl
theorem gprGet_x23 (σ : MState) : gprGet σ 23 = σ.regs.get? Register.x23 := rfl

#print axioms gprGet_x2

/-! ## §4. Named destructurers for the crux row Posts (CLAUDE.md R7)

The row `Post` defs (`rows/CallClosure{FoldBack,RetClass,NormalRet,BodyExit}`)
are anonymous `∧`-towers.  Rather than positional `.2.2.2` navigation at every
consumer, each is destructured ONCE here into the shape the carrier re-assembly
consumes: `GoodState`, the memory equation, the exit PC, and the pass-through
register pins read off `GHolds` via `gholds_reg` + the `gprGet_*` cast battery.
These are the concrete instantiations of §1–§3 that show the marshalling bricks
compose on the landed rows (the pass-through pins reduce by `rfl`; the
load-bearing restore reads are supplied by the callers via
`SegReadback.gholds_lookup_ld`, threaded through `gholds_reg`). -/

/-- The FoldBack loop row's pass-through register pins as `regs.get?` facts —
the fold carrier's `spReg`/`bound` fields at the loop head.  `x15` (a5, the
bumped index) is load-bearing (`ld a5,0(sp)`); its readback is left to the
caller's `gholds_lookup_ld` (the row exposes it via `GHolds`), so this
destructurer yields the two structural passthroughs the invariant needs
unconditionally (sp anchors the slots, s6 the loop bound). -/
theorem foldBackLoop_passthrough {sp s6v : BitVec 64}
    {lds : List (List (BitVec 8))} {m0 : Std.ExtHashMap Nat (BitVec 8)}
    {c : Config}
    (h : CallClosureFoldBackLoopPost sp s6v lds m0 c) :
    GoodState c.σ ∧
    c.σ.mem = m0 ∧
    c.σ.regs.get? Register.PC = some 0x800032dc#64 ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    c.σ.regs.get? Register.x22 = some s6v := by
  obtain ⟨hG, hmem, hpc, hregs⟩ := h
  refine ⟨hG, ?_, hpc, ?_, ?_⟩
  · -- memory-pure span: log = [] ⇒ writeLog m0 [] = m0
    rw [hmem]; rfl
  · rw [← gprGet_x2]
    exact gholds_reg hregs (by rfl)
  · rw [← gprGet_x22]
    exact gholds_reg hregs (by rfl)

#print axioms foldBackLoop_passthrough

/-- The `.normal` join row's exit facts — parked at `callJoinPC = 0x800033ec`,
memory-pure (the restore seg stores nothing), sp preserved.  The three restored
callee-saveds (`s3`/`s5`/`s7` = x19/x21/x23) are load-bearing readbacks the
caller reassembles against `CallerSpillSlots`/`s7ImageAtBody` via
`gholds_lookup_ld`; this destructurer yields the structural exit shape and the
sp anchor. -/
theorem normalJoin_exit {sp : BitVec 64}
    {lds : List (List (BitVec 8))} {m0 : Std.ExtHashMap Nat (BitVec 8)}
    {c : Config}
    (h : CallClosureNormalJoinPost sp lds m0 c) :
    GoodState c.σ ∧
    c.σ.mem = m0 ∧
    c.σ.regs.get? Register.PC = some 0x800033ec#64 ∧
    c.σ.regs.get? Register.x2 = some sp := by
  obtain ⟨hG, hmem, hpc, hregs⟩ := h
  refine ⟨hG, ?_, hpc, ?_⟩
  · rw [hmem]; rfl
  · rw [← gprGet_x2]
    exact gholds_reg hregs (by rfl)

#print axioms normalJoin_exit

/-! ## §5. The env_define fold-step spec bridge (item 2 spec side)

The per-param seam (`callParamFoldSeam_of`, `rows/CallClosureSplice.lean`)
advances the fold carrier `CallParamFoldInv … k → … (k+1)`.  Its `store` field
moves `StoreRepr … (foldStore … k)` to `StoreRepr … (foldStore … (k+1))` — and
`foldStore … (k+1)` is EXACTLY `(foldStore … k).define frame xₖ vₖ` (this
lemma), so the env_define contract's post (`Store.define`-shaped) marshals into
the next carrier's `store` field without re-running the fold.  This is the
`take`-succ decomposition of the `List.foldl` carrier the `storeChainList`
composition steps along — the `foldStore … n = closureBoundStore` companion
(`foldStore_full`, `rows/CallClosureRow.lean`) at the SUCCESSOR step. -/
theorem foldStore_succ (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (k : Nat) (hk : k < (cd.params.zip vs).length) :
    foldStore store' cd vs frame (k + 1)
      = (foldStore store' cd vs frame k).define frame
          ((cd.params.zip vs)[k]'hk).1 ((cd.params.zip vs)[k]'hk).2 := by
  unfold foldStore
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

#print axioms foldStore_succ

end Vsa.Sim
