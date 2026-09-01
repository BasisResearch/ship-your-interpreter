import Vsa.Sim.FrameMeta
import Vsa.Sim.CallSpec

/-!
# `CallFrameMeta` — the red-zone frame metatheorem (ONE shot per staging seam)

Every call splice's STAGING seg (arg marshalling between callees) so far paid
four hand-threaded hypothesis families per seam:

1. **ABI frame** — free since `bridgeOfSeg`/`FrameMeta`, but restated per site;
2. **`AInv` survival** — a bespoke `hAInvStable*` premise keyed to the seg's
   exact spill window (e.g. `hAInvStableSpill` over `[spM+8, spM+16)` in
   `rows/StrdupTailContractClose.lean` §1), plus a per-site `OutL`
   unfolding + `omega` to connect the window to the concrete log;
3. **code-pin survival** — a per-site `hjalmem : XLoaded (writeLog m0 seg.log)`
   premise (the code bytes survive the seg's spills);
4. **spill-window disjointness** — the same `OutL`/`omega` reasoning again for
   each downstream reader.

The observation: a staging seg only ever writes into the caller's stack **red
zone** (a `[lo, hi)` window below/at the frame).  Containment of the seg's
reflected write-log in that window (`LogInRZ` — one `simp only [LogInRZ];
omega` on the concrete log, the `OutL` recipe) implies ALL FOUR families at
once, given two ONCE-PER-OBJECT stability facts:

* `AInvStableOn AInv exts rz.foot` — the arena invariant doesn't care about
  the stack red zone (ONE premise per contract, monotone: subsumes every
  smaller-window `hAInvStable*` via `AInvStableOn.mono`);
* `MemPredStableOn CodeP rz.foot` — the code region is disjoint from the red
  zone (a Layout-level fact, provable once per `*Loaded` battery, never per
  splice).

`rzSeamFrame_of_run` packages the conclusion as the named-field `RZSeamFrame`;
`loaded_writeLog_of_rz` is the direct `hjalmem`-killer.

Note the gp-agreement `AInvStableOn` consumes needs NO extra premise: `x3` is
`AbiPreserved`, so the seam's own ABI frame supplies it.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

/-! ## The red zone and log containment -/

/-- **The caller's stack red zone** `[lo, hi)` — the byte window a staging seg
is allowed to scribble.  Explicit data (the falsity lesson): the window is a
visible literal at each use site, not an implicit ghost. -/
structure RedZone where
  lo : Nat
  hi : Nat

/-- The red zone as a footprint predicate (feeds `AInvStableOn`/
`MemPredStableOn`). -/
def RedZone.foot (rz : RedZone) : Nat → Prop :=
  fun a => rz.lo ≤ a ∧ a < rz.hi

/-- **Log containment in the red zone** — every write-log entry `[A, A+w)`
lands inside `[lo, hi)`.  Recursive, so a CONCRETE log (the seg layer's
`(evalBlocks …).log`, a literal list) unfolds to a conjunction of linear
facts closed by `simp only [LogInRZ]; omega` given the stack bounds — the
established `OutL` discharge recipe, ONE omega per seam instead of one per
(window × consumer). -/
def LogInRZ (rz : RedZone) : List WEntry → Prop
  | [] => True
  | e :: log => (rz.lo ≤ e.1 ∧ e.1 + e.2.1 ≤ rz.hi) ∧ LogInRZ rz log

/-- Addresses outside the red zone are outside every contained log entry. -/
theorem outL_of_logInRZ {rz : RedZone} {log : List WEntry} {a : Nat}
    (h : LogInRZ rz log) (ha : a < rz.lo ∨ rz.hi ≤ a) : OutL log a := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨by have := h.1; omega, ih h.2⟩

/-- **Reads outside the red zone pass through the whole write-log fold** —
the memory-transform clause of a red-zone-contained staging seg, free. -/
theorem writeLog_rz_out (rz : RedZone) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (hlog : LogInRZ rz log) :
    ∀ a : Nat, ¬ rz.foot a → (writeLog m0 log)[a]? = m0[a]? := by
  intro a ha
  refine writeLog_out m0 log a (outL_of_logInRZ hlog ?_)
  have ha' : ¬ (rz.lo ≤ a ∧ a < rz.hi) := ha
  omega

/-! ## Once-per-object stability of a memory predicate (the code-pin interface) -/

/-- A memory predicate (a `*Loaded` code-pin battery, a data-region pin, …) is
stable under changes confined to the footprint `F`.  For a code battery this is
provable ONCE from its pin range being disjoint from `F` (a Layout-level fact)
— never re-derived per splice. -/
def MemPredStableOn (P : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (F : Nat → Prop) : Prop :=
  ∀ m m' : Std.ExtHashMap Nat (BitVec 8),
    (∀ a : Nat, ¬ F a → m'[a]? = m[a]?) → P m → P m'

/-- Stability under a BIG footprint transfers to any smaller one. -/
theorem MemPredStableOn.mono {P : Std.ExtHashMap Nat (BitVec 8) → Prop}
    {F F' : Nat → Prop} (hsub : ∀ a, F' a → F a)
    (h : MemPredStableOn P F) : MemPredStableOn P F' :=
  fun m m' hmem => h m m' (fun a ha => hmem a (fun h' => ha (hsub a h')))

/-- **The `hjalmem`-killer.**  The per-splice premise
`XLoaded (writeLog m0 seg.log)` is FREE from log containment + the
once-per-object stability fact. -/
theorem loaded_writeLog_of_rz (rz : RedZone)
    (P : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (hstable : MemPredStableOn P rz.foot)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry)
    (hlog : LogInRZ rz log) (hP : P m0) : P (writeLog m0 log) :=
  hstable m0 (writeLog m0 log) (writeLog_rz_out rz m0 log hlog) hP

/-! ## The one-shot seam frame -/

/-- **The red-zone seam frame** — everything a splice seam needs beyond the
marshalled registers, as ONE named-field conclusion:
the ABI register frame, the memory transform (reads outside the red zone
unchanged — subsumes every spill-window disjointness fact), the arena
invariant's survival, and the code pins' survival. -/
structure RZSeamFrame (rz : RedZone)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (CodeP : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (σ σ2 : MState) : Prop where
  /-- ABI callee-saved frame across the seam. -/
  abi : ∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R
  /-- Reads outside the red zone are unchanged (all disjointness facts at once). -/
  memOut : ∀ a : Nat, ¬ rz.foot a → σ2.mem[a]? = m0[a]?
  /-- The arena invariant survives the seam. -/
  ainv : AInv σ2 exts
  /-- The code pins survive the seam. -/
  code : CodeP σ2.mem

/-- **The red-zone frame metatheorem.**  For a staging seg run (any
`bridgeOfSeg`/`segEval_sound`-produced seam: entry memory `m0`, exit memory
= the reflected write-log, ABI frame free from `WrChainAvoidAbi`), log
containment in the caller's red zone yields the WHOLE seam frame in one shot.
A splice seam now needs ONLY (the seg run, its log-containment `LogInRZ` —
one `omega` — and the two once-per-object stability facts); the per-splice
`hAInvStable*` / `hjalmem` / spill-window `OutL` threading families are dead. -/
theorem rzSeamFrame_of_run (rz : RedZone)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (CodeP : Std.ExtHashMap Nat (BitVec 8) → Prop)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (σ σ2 : MState)
    (hlog : LogInRZ rz log)
    (hmem0 : σ.mem = m0)
    (hmem2 : σ2.mem = writeLog m0 log)
    (habi : ∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R)
    (hAInvStable : AInvStableOn AInv exts rz.foot)
    (hAInv : AInv σ exts)
    (hCodeStable : MemPredStableOn CodeP rz.foot)
    (hCode : CodeP m0) :
    RZSeamFrame rz AInv exts CodeP m0 σ σ2 := by
  have hout : ∀ a : Nat, ¬ rz.foot a → σ2.mem[a]? = m0[a]? := by
    intro a ha; rw [hmem2]; exact writeLog_rz_out rz m0 log hlog a ha
  refine ⟨habi, hout, ?_, ?_⟩
  · -- AInv survival: gp-agree comes FREE from the seam's own ABI frame (x3 is
    -- AbiPreserved); mem-agree outside the red zone from the log containment.
    refine hAInvStable σ σ2 (habi Register.x3 (by decide)).symm ?_ hAInv
    intro a ha
    rw [hmem0, hout a ha]
  · -- code pins survive: reads outside the red zone unchanged, code disjoint.
    exact hCodeStable m0 σ2.mem hout hCode

#print axioms outL_of_logInRZ
#print axioms writeLog_rz_out
#print axioms MemPredStableOn.mono
#print axioms loaded_writeLog_of_rz
#print axioms rzSeamFrame_of_run

end Vsa.Sim
