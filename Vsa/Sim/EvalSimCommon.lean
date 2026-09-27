import Vsa.Sim.EvalIntSim
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — shared, case-INDEPENDENT `eval_expr` prologue/epilogue lemmas

The `EvalE.int` simulation Triple (`evalIntSim`, `EvalIntSim4.lean`) is a
composition `blockA_ee ≫ blockC_ee ≫ blockD_ee`. Of these, `blockA_ee` (the
prologue + jump-table dispatch) and `blockD_ee` (the shared epilogue: four `ld`
restores + `mv a0,s1` + `addi sp,sp,1088` + `ret`) do NOT inspect the produced
`Value` or the `.int`-specific callee `value_int` — they are shared across every
sibling `EvalE` leaf case (`null`/`bool`/`str`/`var`).

This file extracts the **epilogue** in its case-independent form:

* **`PreEpilogueV`** — the machine state at the shared epilogue entry
  `0x800033ec`, parameterized over an arbitrary produced `Value v` (the sret
  buffer holds `ValueRepr … v` — the epilogue never reads the buffer contents,
  it only threads them into `EvalExit.result`). `EvalIntSim3.lean`'s
  `PreEpilogue … n` is the instance `PreEpilogueV … (.int n)`.
* **`blockD_v`** — the epilogue Triple `PreEpilogueV … v → EvalExit … v`, the
  seven-instruction restore/return sequence. Value-agnostic: `EvalIntSim4.lean`'s
  `blockD_ee` is `blockD_v` at `v := .int n`.
* The four `ld`-restore address offsets (`epi_off438/430/420/428`) and the
  sd-then-ld `spill_roundtrip_ee` bridge — all value-independent, reusable by
  every leaf case's epilogue.

A future `null`/`bool`/`str`/`var` case instantiates `blockD_v` at its own `v`
(e.g. `.null`, `.bool b`, `.str s`) once its own `blockC_*` arm reaches
`PreEpilogueV … v`; only the arm (block C, the payload load + which `value_*`
callee runs) is case-specific.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `MemExtends` — presence monotonicity -/

/-- Every address populated in `m0` is still populated in `m`. All real machine
memory deltas are `writeMap4/8` chains (inserts), so every verified walk
preserves this; it is the fact `EvalExit` forgets and recursive callers need
(the post-call `ld`s of the unconstrained sub-result padding bytes). -/
def MemExtends (m0 m : Mem) : Prop :=
  ∀ (a : Nat) (b : BitVec 8), m0[a]? = some b → ∃ b', m[a]? = some b'

/-- A `writeMap8` (an 8-byte insert) preserves presence: nothing is deleted, and
the 8 written bytes are present. -/
theorem memExtends_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8)) :
    MemExtends mem (writeMap8 mem a8 d) := by
  intro k b hk
  by_cases hin : a8 ≤ k ∧ k < a8 + 8
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a8 ∨ k = a8 + 1 ∨ k = a8 + 2 ∨ k = a8 + 3 ∨ k = a8 + 4 ∨
        k = a8 + 5 ∨ k = a8 + 6 ∨ k = a8 + 7 from by omega)
      with h | h | h | h | h | h | h | h
    · exact ⟨_, by rw [show k = a8 + 0 from by omega]; exact getElem_writeMap8_0 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_1 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_2 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_3 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_4 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_5 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_6 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_7 mem a8 d⟩
  · exact ⟨b, by rw [getElem_writeMap8_disjoint mem a8 k d (by omega)]; exact hk⟩

theorem MemExtends.trans {m0 m1 m2 : Mem}
    (h1 : MemExtends m0 m1) (h2 : MemExtends m1 m2) : MemExtends m0 m2 := by
  intro a b h
  obtain ⟨b', hb'⟩ := h1 a b h
  exact h2 a b' hb'

/-- Presence extension preserves the readability of one complete machine
word.  The value may change because the intervening execution may overwrite
the word. -/
theorem read64_total_of_memExtends {m0 m : Mem} {a : Nat}
    (hExt : MemExtends m0 m)
    (h : ∃ d : BitVec 64, read64 m0 a = some d.toNat) :
    ∃ d : BitVec 64, read64 m a = some d.toNat := by
  obtain ⟨d, hd⟩ := h
  simp only [read64, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
  obtain ⟨b0, hb0, r0, hr0, _⟩ := hd
  obtain ⟨b1, hb1, r1, hr1, _⟩ := hr0
  obtain ⟨b2, hb2, r2, hr2, _⟩ := hr1
  obtain ⟨b3, hb3, r3, hr3, _⟩ := hr2
  obtain ⟨b4, hb4, r4, hr4, _⟩ := hr3
  obtain ⟨b5, hb5, r5, hr5, _⟩ := hr4
  obtain ⟨b6, hb6, r6, hr6, _⟩ := hr5
  obtain ⟨b7, hb7, _, _, _⟩ := hr6
  obtain ⟨b0', hb0'⟩ := hExt a b0 hb0
  obtain ⟨b1', hb1'⟩ := hExt (a + 1) b1 hb1
  obtain ⟨b2', hb2'⟩ := hExt (a + 2) b2 hb2
  obtain ⟨b3', hb3'⟩ := hExt (a + 3) b3 hb3
  obtain ⟨b4', hb4'⟩ := hExt (a + 4) b4 hb4
  obtain ⟨b5', hb5'⟩ := hExt (a + 5) b5 hb5
  obtain ⟨b6', hb6'⟩ := hExt (a + 6) b6 hb6
  obtain ⟨b7', hb7'⟩ := hExt (a + 7) b7 hb7
  let d' : BitVec 64 := sign_extend (m := 64)
    (((((((b7'.append b6').append b5').append b4').append b3').append b2').append b1').append b0')
  refine ⟨d', ?_⟩
  simp only [read64, readLE, bind, Option.bind, pure, hb0', hb1', hb2', hb3', hb4', hb5',
    hb6', hb7', Nat.mul_zero, Nat.add_zero, d']
  rw [sext_full]
  apply congrArg some
  exact (word8_toNat_recon b0' b1' b2' b3' b4' b5' b6' b7').symm

/-- A populated finite interval suffices for a `Value` slot wholly inside it.
This is the usable form for sparse machine memories and concrete stack slots. -/
theorem valueWordsTotal_of_interval {m : Mem} {lo hi a : Nat}
    (hPop : ∀ k : Nat, lo ≤ k → k < hi → ∃ b : BitVec 8, m[k]? = some b)
    (hlo : lo ≤ a) (hhi : a + 24 ≤ hi) :
    ValueWordsTotal m a := by
  have word (x : Nat) (hxlo : lo ≤ x) (hxhi : x + 8 ≤ hi) :
      ∃ d : BitVec 64, read64 m x = some d.toNat := by
    obtain ⟨b0, hb0⟩ := hPop x (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hPop (x + 1) (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hPop (x + 2) (by omega) (by omega)
    obtain ⟨b3, hb3⟩ := hPop (x + 3) (by omega) (by omega)
    obtain ⟨b4, hb4⟩ := hPop (x + 4) (by omega) (by omega)
    obtain ⟨b5, hb5⟩ := hPop (x + 5) (by omega) (by omega)
    obtain ⟨b6, hb6⟩ := hPop (x + 6) (by omega) (by omega)
    obtain ⟨b7, hb7⟩ := hPop (x + 7) (by omega) (by omega)
    let d : BitVec 64 := sign_extend (m := 64)
      (((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
    refine ⟨d, ?_⟩
    simp only [read64, readLE, bind, Option.bind, pure, hb0, hb1, hb2, hb3, hb4, hb5,
      hb6, hb7, Nat.mul_zero, Nat.add_zero, d]
    rw [sext_full]
    apply congrArg some
    exact (word8_toNat_recon b0 b1 b2 b3 b4 b5 b6 b7).symm
  obtain ⟨d0, h0⟩ := word a hlo (by omega)
  obtain ⟨d1, h1⟩ := word (a + 8) (by omega) (by omega)
  obtain ⟨d2, h2⟩ := word (a + 16) (by omega) (by omega)
  exact ⟨d0, d1, d2, h0, h1, h2⟩

theorem ValueWordsTotal.mono {m0 m : Mem} {a : Nat}
    (hExt : MemExtends m0 m) (h : ValueWordsTotal m0 a) :
    ValueWordsTotal m a := by
  obtain ⟨d0, d1, d2, h0, h1, h2⟩ := h
  obtain ⟨d0', h0'⟩ := read64_total_of_memExtends hExt ⟨d0, h0⟩
  obtain ⟨d1', h1'⟩ := read64_total_of_memExtends hExt ⟨d1, h1⟩
  obtain ⟨d2', h2'⟩ := read64_total_of_memExtends hExt ⟨d2, h2⟩
  exact ⟨d0', d1', d2', h0', h1', h2'⟩

-- (relocated block ends; wave 47e)

/-! ## `LeafMemPin` — the leaf exit memory pinned to its write chain (wave 47e)

The two facts a LEAF walk's exit memory satisfies but `EvalExit` forgets
(`LeafExitPin` of the re-seat verdict,
`experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean`): the whole
delta from the entry `m0` is the four prologue spills (in `[SL.lo, sp)`) plus
the `value_*` sret write — a presence-preserving `writeMap` chain confined to
`[SL.lo, sp) ∪ [sret, sret+24)`, with NO arena drift.  Threaded through the
leaf `blockC_*` posts and carried across the epilogue by `blockD_v`'s `Q`
parameter (memory-pure). -/

/-! ## Address arithmetic for the frame + spill windows (value-independent) -/

/-! ## The spill roundtrip — the sd-then-ld bridge (value-independent)

If `mem` reads back `v.toNat` at address `a` (i.e. an 8-byte `sd`-spill of `v`
survives at `a`), then the eight individual bytes `bi = mem[a+i]?` are `some`,
and the little-endian sign-extended reassembly the epilogue `ld` produces
(`sign_extend (b7 ++ … ++ b0)`) equals `v`. Consumed by the four `ld` restore
sites (`site_800033ec/f0/fc/f4_ee`). -/

/-! ### Offsets: the four `ld` restore addresses as `sp - k`. -/

-- `KindSlotPinned` RELOCATED to `InterpEntry.lean` (wave 47i: the `EvalGround`
-- entry bundle needs it below `EvalEntry`; same name/namespace — zero consumer
-- changes; the tag-0 bridge `int_slot_kindPinned` stays here).

/-! ## `ArmEntryK` — the machine state at a leaf arm's entry PC (dispatch target)

The case-INDEPENDENT half of the prologue + jump-table dispatch (`blockA_ee`,
`EvalIntSim2.lean`) lands at the per-case arm PC. `ArmEntryK` collects the machine
facts true there, generalized over exactly the three case-specific couplings of
the dispatch:

* **`armPC : BitVec 64`** — the jump-table landing PC (the arm's first
  instruction). For `.int` this is `0x80003408` (the `ld a1,8(a2); jal value_int`
  arm); each `EX_*` kind's slot points to its own arm.
* **`calleeLoaded : Mem → Prop`** — the "this arm's callee is loaded" predicate,
  carried through the spills alongside `Eval_exprLoaded`. For `.int` this is
  `Value_intLoaded`; `null`/`bool`/`str` use `Value_nullLoaded`/… .
* **`e : Expr`** — the evaluated expression (`ExprRepr ment aExpr.toNat e`). For
  the `.int` case `e = .int n`.

Everything else — the four spilled callee-saved slots, the lowered `sp`, the
`store_survives`/`StoreRepr`/`memFrame`/frame facts, and all the geometric
region facts — is identical across every leaf case. `EvalIntSim2.lean`'s
`ArmEntry … n` is the instance `ArmEntryK … (0x80003408) Value_intLoaded (.int n)`.

A future `null`/`bool`/`str`/`var` case reuses `blockA_ee`'s prologue+dispatch to
reach `ArmEntryK` at its own `armPC`/`calleeLoaded`/`e`, then runs only its own
arm (block C) to `PreEpilogueV … v`, closing with the shared `blockD_v`. -/
     -- s2 = interp* (mv s2,a1 @0x80003184)

/-! ## `PreEpilogueV` — the machine state at the shared epilogue `0x800033ec`

Generalizes `EvalIntSim3.lean`'s `PreEpilogue` over the produced `Value v` (the
sret buffer holds `ValueRepr … v`). After a leaf arm's block C: `value_*` has
filled the sret buffer with `ValueRepr v`, `s1 = sret`, `sp = sp-1088`
(all preserved by the callee's `NotWritten*` frame). The four spilled
callee-saved slots `[sp-8], [sp-16], [sp-24], [sp-32]` still hold their entry
values (disjoint from the sret write). `eval_expr` loaded. Output invariant
(`= out0`). -/

/-! ## `blockD_v` — the shared epilogue, generalized over the produced `Value`

`PreEpilogueV … v → EvalExit … v`. The seven epilogue instructions never inspect
the sret buffer's contents: `v` is only threaded into `EvalExit.result` (with the
identity `φc` extension) and `EvalExit.store` (identity `φf`/`φc`, `st'.store =
st.store` — true for every leaf case). Value-agnostic body: identical to the
`.int`-specialized `blockD_ee` with `n → v`. -/

/-! ## `jal`-observation consumers (local; mirror `DivSites2`'s `obs_jal_*`)

`obs_jal_*` proper live in `DivSites2` (imported later in the `EvalIntSim2`
chain), so `armTail_v` — which sits in this earlier file — recreates the four it
needs directly on `get?_sigmaPost_jal` (`StepJump`) + `readback` (`Muldi3Spec`),
under distinct names to avoid a clash when both files are imported. -/

/-! ## `armTail_v` — the shared `jal <callee>; j 0x800033ec` arm tail

Every leaf `EvalE` arm, after its (optional) payload load, ends with exactly two
instructions: `jal <value_*>` (the callee that fills the sret buffer) and
`j 0x800033ec` (into the shared epilogue). `armTail_v` captures this tail once,
parameterized over:

* **`armPC`** — the `jal`'s PC (the arm entry, for `null` `0x8000342c`).
* **`calleeEntry`** — the callee's entry PC (`= armPC + sext jalImm`; `value_null`
  is `0x800027ec`).
* **`calleeLoaded`** — the arm-callee code predicate, carried through the tail.
* **`v`** — the produced `Value` (`.null`/`.bool _`/`.str _`/`.int _`).

The `jal`/`j` machine steps are supplied as the two per-arm `stepObs`-form
hypotheses `hjalSite`/`hjSite` (mirroring `site_8000342c_ee`/`site_80003430_ee`);
the callee is supplied as `hcallee`, a config-level behavior implication whose
post is exactly the strengthened `value_*` post (ValueRepr `v`, output preserved,
memory framed outside `[sret,sret+24)`, `NotWrittenV` register frame). This is
callee-agnostic: `int`/`bool`/`str` reuse it with their own `value_*` spec.

Input: the arm-entry state satisfies (the relevant subset of) `ArmEntryK` at
`armPC`, plus the four spill slots / geometry it threads. Output: `PreEpilogueV`
at `v`, ready for `blockD_v`.

The `jal` target is `calleeEntry = armPC + sext jalImm`, its link `armPC + 4`;
the `j` target is `0x800033ec = (armPC+4) + sext jImm`. The `calleeLink` is
`armPC + 4` (a `BitVec 64`). -/

end Vsa.Sim
