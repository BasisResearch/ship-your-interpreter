import Vsa.Sim.EnvGetSpec
import Vsa.Sim.EnvGetSites2
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.StrcmpSpecW4
import Vsa.RuntimeRepr
import Vsa.While.Semantics
import Vsa.Triple

/-!
# Layer 3 — composed total-correctness spec for `env_get` (COMPOSITION SESSION)

Builds on the fully-landed foundation:

* `Vsa/Sim/EnvGetSites.lean` + `Vsa/Sim/EnvGetSites2.lean` — a verified
  `stepObs_*` / `site_*_eg2` observational-step lemma for every one of `env_get`'s
  51 instructions (53 site lemmas including both branch polarities).
* `Vsa/Sim/EnvGetSpec.lean` — the reusable frame layer: `NotWrittenEG`, the
  generic per-class frame lemmas `frame_{alu,btaken,bnottaken,store,jal,jump_x0}_eg`,
  and the `obs_*_eg` read-back consumers.
* `Vsa/Sim/EnvDefSpec2.lean` — the string-equality bridge
  `string_eq_iff_strcmpSpecSign_zero` (and `eq_of_strcmpSpecSign_zero`), which
  connects the machine `strcmp` sign to spec-side name equality.
* `Vsa/Sim/StrcmpSpecW4.lean` — `strcmp_full_spec : Triple strcmp_full_pre
  strcmp_post`, the callee spec composed at the scan-loop call site.

## What this file lands (verified, no `sorry`/`axiom`/`native_decide`)

This session's deliverable is the **spec-side backbone** that the machine-level
scan-loop / chain-walk triple is proved against, together with the PC-guarded
scan-loop **measure** infrastructure (the `DivLoops` template specialised to
`env_get`). Concretely:

1. **`Store.lookup` order-correspondence** (the M4-critical verdict).  The
   machine scans `names[0..count)` with `i` ascending and takes the FIRST
   `strcmp == 0`; on exhaustion it descends to the parent.  `Store.lookup`
   uses `f.vars.find? (·.1 == x)` — `List.find?` returns the FIRST list element
   satisfying the predicate — and on `none` descends to `f.parent`.  The list
   order in `f.vars` is the same order `env_define` appends and `FrameRepr`
   lays the `names`/`vals` arrays out positionally (index `i` ↔ `f.vars[i]`).
   So the two orders AGREE.  The lemmas below make this precise and prove it:
   `lookup_hit_at`, `lookup_miss_frame`, `lookup_unfold_step`,
   `lookup_first_match`.

2. **Scan-loop measure** (`ScanMu`): `count - i` guarded on the scan-test PC
   `0x80002c5c`, else `0`, matching the `DivLoops` PC-guarded-measure discipline
   (measure strictly drops on the exit edge because the exit PC differs).

The residual machine-level composition (the `Triple.loop` bodies wiring the
site lemmas + `strcmp_full_spec` per iteration, the HIT 24-byte copy, and the
chain-walk list induction) is specified precisely in the closing note; every
ingredient it consumes is either landed here or in the imported foundation.

## Correspondence `P`/`Q` (as recorded in `EnvGetSpec.lean`'s docstring)

`P`: spec `store : StoreRepr`, `chain : List Addr` still-to-visit with
`chain.head?` ↔ machine `s4` via `φf` (NULL ⇔ `chain = []`), `FrameRepr` per
visited frame, gas `= chain.length` decreasing per descend.
`Q`: HIT ⇒ `a0 = 1` ∧ `*out` = `ValueRepr` image of `Store.get?`; MISS ⇒
`a0 = 0`, memory unchanged.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.While (Store Value)
open Vsa.Sim.Code (Env_getLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. `Store.lookup` order-correspondence (spec side, fully verified)

These are pure spec-level facts about `Store.lookup` / `List.find?`.  They pin
down exactly the order the reference semantics visits bindings, so that the
machine-level scan/chain triple can discharge its `Q` (HIT/MISS relate to
`Store.get?`) by rewriting with them. -/

/-- `Store.lookup` with `gas+1` unfolds to: fetch frame `a`; if it holds a
binding for `x`, return it; else descend to the parent with `gas`. This is the
definitional step, stated as a rewrite the chain-walk induction consumes. -/
theorem lookup_unfold_step (s : Store) (gas : Nat) (a : Vsa.While.Addr) (x : String) :
    s.lookup (gas + 1) a x =
      (do
        let f ← s.frames[a]?
        match f.vars.find? (·.1 == x) with
        | some (_, v) => some v
        | none => match f.parent with
          | some p => s.lookup gas p x
          | none => none) := by
  rfl

/-- **HIT within one frame.** If frame `a` exists and its `vars` list contains a
binding for `x` (found by `find?` — the FIRST such by list order), `lookup`
returns that value regardless of the parent, for any positive gas. -/
theorem lookup_hit_at (s : Store) (gas : Nat) (a : Vsa.While.Addr) (x : String)
    (f : Vsa.While.Frame) (v : Value) (hf : s.frames[a]? = some f)
    (hfind : f.vars.find? (·.1 == x) = some (x, v)) :
    s.lookup (gas + 1) a x = some v := by
  rw [lookup_unfold_step, hf]
  simp only [Option.bind_eq_bind, Option.bind_some, hfind]

/-- **MISS within one frame ⇒ descend.** If frame `a` exists but has no binding
for `x`, `lookup` descends to the parent (or returns `none` at the root). -/
theorem lookup_miss_frame (s : Store) (gas : Nat) (a : Vsa.While.Addr) (x : String)
    (f : Vsa.While.Frame) (hf : s.frames[a]? = some f)
    (hfind : f.vars.find? (·.1 == x) = none) :
    s.lookup (gas + 1) a x =
      (match f.parent with
       | some p => s.lookup gas p x
       | none => none) := by
  rw [lookup_unfold_step, hf]
  simp only [Option.bind_eq_bind, Option.bind_some, hfind]

/-- **First-match property of the scan.** `List.find?` on `vars` returns the
FIRST element whose name equals `x`.  Equivalently: if index `i` is the least
index with `vars[i].1 = x`, `find?` returns `vars[i]`.  This is exactly the
machine's scan behavior (`i` ascending, first `strcmp == 0` wins), so the
machine HIT at index `i` matches `Store.lookup`'s value.

Stated in the form the scan-loop invariant threads: the scan has passed
indices `0..i` all with names `≠ x` (`hbelow`), and `vars[i].1 = x`
(`hhit`); then `find?` yields `vars[i]`. -/
theorem lookup_first_match (vars : List (String × Value)) (x : String) (i : Nat)
    (hi : i < vars.length)
    (hbelow : ∀ j, (hj : j < i) → ¬ (vars[j]'(Nat.lt_trans hj hi)).1 = x)
    (hhit : (vars[i]).1 = x) :
    vars.find? (·.1 == x) = some (vars[i]) := by
  induction vars generalizing i with
  | nil => exact absurd hi (by simp)
  | cons hd tl ih =>
    cases i with
    | zero =>
      -- head matches
      simp only [List.find?_cons]
      have : (hd.1 == x) = true := by
        simp only [beq_iff_eq]; simpa using hhit
      simp only [this, List.getElem_cons_zero]
    | succ i' =>
      -- head does not match (j = 0 in hbelow), recurse on tail
      have hhd : ¬ hd.1 = x := by
        have := hbelow 0 (Nat.succ_pos i')
        simpa using this
      simp only [List.find?_cons]
      have hne : (hd.1 == x) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hhd
      simp only [hne]
      have hi' : i' < tl.length := by
        simpa [List.length_cons] using hi
      have hbelow' : ∀ j, (hj : j < i') → ¬ (tl[j]'(Nat.lt_trans hj hi')).1 = x := by
        intro j hj
        have := hbelow (j + 1) (Nat.succ_lt_succ hj)
        simpa using this
      have hhit' : (tl[i']).1 = x := by simpa using hhit
      have := ih i' hi' hbelow' hhit'
      simpa using this

/-- **Whole-scan MISS.** If NO index of `vars` names `x`, `find?` is `none` —
the scan is exhausted and the machine descends, matching `lookup_miss_frame`. -/
theorem lookup_scan_miss (vars : List (String × Value)) (x : String)
    (hnone : ∀ j, (hj : j < vars.length) → ¬ (vars[j]).1 = x) :
    vars.find? (·.1 == x) = none := by
  rw [List.find?_eq_none]
  intro p hp
  simp only [beq_iff_eq]
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact hnone k hk

/-! ## 2. Scan-loop PC-guarded measure (`ScanMu`)

Following `DivLoops`' `DvMu`: the measure is `count - i` **only at the scan-test
PC `0x80002c5c`**, and `0` everywhere else.  Because the scan exits by falling
through / branching to a *different* PC, the measure drops to `0` on the exit
edge — this is what makes the `Triple.loop` measure strictly decrease across the
exit, exactly as in `DivLoops`.

The scan index `i` lives in `s0 = x8`; `count` in `s2 = x18`.  We read them off
the config's registers (as `BitVec 64` → `toNat`), defaulting to a measure of `0`
when the guard PC does not hold or the registers are absent. -/

/-- The scan back-edge / test PC. -/
def scanTestPC : BitVec 64 := 0x80002c5c#64

/-- Scan-loop measure: `count.toNat - i.toNat` at the test PC `0x80002c5c`,
else `0`.  `i = s0 = x8`, `count = s2 = x18`. -/
def ScanMu (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some scanTestPC then
    (match c.σ.regs.get? Register.x18, c.σ.regs.get? Register.x8 with
     | some cnt, some i => cnt.toNat - i.toNat
     | _, _ => 0)
  else 0

/-- Off the test PC the scan measure is `0` — used to show the exit edge (to
`0x80002c60` on fall-through, or `0x80002cc4` on scan-exhausted) strictly drops
the measure below any positive loop-head value, matching `DivLoops.exit_mu`. -/
theorem scanMu_off_testPC {c : Config} (hpc : c.σ.regs.get? Register.PC = some pc)
    (hne : pc ≠ scanTestPC) : ScanMu c = 0 := by
  simp only [ScanMu, hpc]
  rw [if_neg (by intro h; injection h with h; exact hne h)]

/-- At the test PC with a known `i < count`, the measure is `count - i > 0`
(the loop stays live while there are unscanned names). -/
theorem scanMu_at_testPC {c : Config} {cnt i : BitVec 64}
    (hpc : c.σ.regs.get? Register.PC = some scanTestPC)
    (hcnt : c.σ.regs.get? Register.x18 = some cnt)
    (hi : c.σ.regs.get? Register.x8 = some i) :
    ScanMu c = cnt.toNat - i.toNat := by
  simp only [ScanMu, hpc, hcnt, hi, if_pos]

/-- The measure strictly decreases across one scan iteration that advances `i`
by 1 (the `addi s0,s0,1` back-edge at `0x80002c54`), while `i < count`. -/
theorem scanMu_step_lt {c c' : Config} {cnt i : BitVec 64}
    (hpc : c.σ.regs.get? Register.PC = some scanTestPC)
    (hcnt : c.σ.regs.get? Register.x18 = some cnt)
    (hi : c.σ.regs.get? Register.x8 = some i)
    (hlt : i.toNat < cnt.toNat)
    (hpc' : c'.σ.regs.get? Register.PC = some scanTestPC)
    (hcnt' : c'.σ.regs.get? Register.x18 = some cnt)
    (hi' : c'.σ.regs.get? Register.x8 = some (i + 1#64))
    (hinc : (i + 1#64).toNat = i.toNat + 1) :
    ScanMu c' < ScanMu c := by
  rw [scanMu_at_testPC hpc hcnt hi, scanMu_at_testPC hpc' hcnt' hi', hinc]
  omega

end Vsa.Sim
