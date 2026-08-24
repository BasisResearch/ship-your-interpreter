import Vsa.Sim.GoodState
import Vsa.Sim.StateNF
import Vsa.Sim.StepAddi
import Vsa.Sim.StepBeq

/-!
# `GoodState`-preservation machinery (M2 framing)

Every per-instruction step lemma ends by re-establishing `GoodState σ'`, where
`σ'` is `σ` plus a short chain of register writes (`insert`s) to registers that
are *not* pinned by `GoodState`'s non-`∃` fields (`minstret_increment`, `nextPC`,
`PC`, `minstret`, an `rd` GPR, and on tick steps `mcycle`/`mtime`/`mip`).
`StepAddi.lean` / `StepBeq.lean` each spend ~250 lines of mechanical
field-by-field reconstruction on this. This file factors that into one reusable
single-insert preservation lemma (`GoodState.insert_nonpinned`) plus a chaining
tactic (`goodstate_frame`), so a step-lemma author writes one line.

## Design

`GoodState` has two kinds of fields (see `Vsa/Sim/GoodState.lean`):

* 21 **pinned** fields — `σ.regs.get? R = some c` at a *fixed* value `c`
  (`cur_privilege`, `misa`, `mstatus`, `mie`, `mseccfg`, `satp`, `mtvec`,
  `mideleg`, `medeleg`, `hart_state`, `htif_done`, `htif_tohost`,
  `htif_tohost_base`, `elp`, `pmpcfg_n`, `pmpaddr_n`, `pma_regions`, `menvcfg`,
  `mcountinhibit`, `mcyclecfg`, `minstretcfg`);
* 10 **`∃`-fields** — `∃ v, σ.regs.get? R = some v` (`mip`, `sig_meip`,
  `sig_seip`, `mtime`, `mtimecmp`, `minstret`, `minstret_increment`, `mcycle`,
  `nextPC`, `PC`).

`NonPinned r` (via the decidable `isNonPinned` Bool) holds exactly for registers
that are *not* one of the 21 pinned ones. Inserting to such an `r` preserves
every pinned field (the key differs, so the read reads through) and every
`∃`-field (either the key differs and reads through, or it matches and the newly
inserted value witnesses the `∃`).

### The dependent-cast trap

`Std.ExtDHashMap.get?_insert` reads

```
(m.insert k v).get? a = if h : (k == a) then some (cast ⋯ v) else m.get? a
```

The `dite` branch types depend on the condition, so `rw [hne]` on the
`(k == a)` discriminant fails with "motive is not type correct" (the `cast`
carries a proof of `k = a`). Two ways this file sidesteps it:

* pinned read-through (`get?_insert_pinned`): discharge the `dite` with
  `simp only [hne, …]` (simp handles the `Decidable`-dependent motive), never
  `rw`;
* `∃`-preservation (`exists_get?_insert`): case-split on `(r == A)`; in the
  `true` branch the goal `∃ w, some (cast ⋯ v) = some w` is closed by `⟨_, rfl⟩`
  — **the existential absorbs the cast entirely**, no transport needed.

`pin_of_isNonPinned` derives the disequality `(r == A) = false` from
`NonPinned r` and `A` pinned *without* any `cases` on `Register` (which would
blow up to ~160×160 goals): it uses `beq_eq_false_iff_ne` plus the fact that
`isNonPinned r = true ≠ false = isNonPinned A`.
-/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine (MState)

namespace Vsa.Sim

/-! ## `NonPinned` -/

/-- `true` iff `r` is **not** one of `GoodState`'s 21 pinned (non-`∃`) registers,
i.e. `r` is one of the machine-mutated registers a hot-path step may write
(GPRs, `PC`, `nextPC`, `minstret`, `minstret_increment`, `mcycle`, `mtime`,
`mip`, …). Decidable, so `NonPinned` side goals close by `decide`. -/
def isNonPinned (r : Register) : Bool :=
  match r with
  | .cur_privilege | .misa | .mstatus | .mie | .mseccfg | .satp | .mtvec
  | .mideleg | .medeleg | .hart_state | .htif_done | .htif_tohost
  | .htif_tohost_base | .elp | .pmpcfg_n | .pmpaddr_n | .pma_regions
  | .menvcfg | .mcountinhibit | .mcyclecfg | .minstretcfg => false
  | _ => true

/-- `r` is not pinned by `GoodState`'s non-`∃` fields. Definitionally
`isNonPinned r = true`, so `(by decide)` discharges it for concrete `r`. -/
abbrev NonPinned (r : Register) : Prop := isNonPinned r = true

/-- From `NonPinned r` and a pinned register `A` (`isNonPinned A = false`),
the two registers are distinct, so `(r == A) = false`. Proved without any
`cases` on `Register`: distinct `isNonPinned` values force `r ≠ A`. -/
theorem pin_of_isNonPinned {r A : Register}
    (hr : isNonPinned r = true) (hA : isNonPinned A = false) : (r == A) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h; subst h; rw [hr] at hA; exact absurd hA (by decide)

/-! ## Single-insert read-through primitives -/

/-- Reading a register `A` distinct from the inserted key `r` (`(r == A) = false`)
reads through the insert. Discharges the dependent `dite` of
`Std.ExtDHashMap.get?_insert` with `simp only` — `rw [hne]` fails here because the
branch types depend on the discriminant (the `cast`). -/
theorem get?_insert_pinned (regs : Std.ExtDHashMap Register RegisterType)
    (r : Register) (v : RegisterType r) (A : Register)
    (hne : (r == A) = false) :
    (regs.insert r v).get? A = regs.get? A := by
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne, dif_neg, Bool.false_eq_true, not_false_eq_true]

/-- Definedness (`∃`-shape) of a register is preserved by any single insert:
if `A = r` the freshly inserted value witnesses the `∃` (the goal
`∃ w, some (cast ⋯ v) = some w` closes by `⟨_, rfl⟩`, so the dependent `cast`
is absorbed by the existential); otherwise the old witness reads through. -/
theorem exists_get?_insert (regs : Std.ExtDHashMap Register RegisterType)
    (r : Register) (v : RegisterType r) (A : Register)
    (h : ∃ w, regs.get? A = some w) : ∃ w, (regs.insert r v).get? A = some w := by
  rw [Std.ExtDHashMap.get?_insert]
  by_cases hc : (r == A) = true
  · simp only [hc, dif_pos]; exact ⟨_, rfl⟩
  · simp only [hc, dif_neg, Bool.not_eq_true]; exact h

/-! ## The single-insert `GoodState` preservation lemma -/

/-- **The reusable frame lemma.** Inserting a value `v` into a non-pinned register
`r` preserves `GoodState`: every pinned field reads through (its key differs from
`r`), and every `∃`-field stays defined. Chain it once per write in a step's
insert-chain (see `goodstate_frame`). -/
theorem GoodState.insert_nonpinned {σ : MState} (hG : GoodState σ)
    {r : Register} (hr : NonPinned r) (v : RegisterType r) :
    GoodState {σ with regs := σ.regs.insert r v} := by
  have P : ∀ (A : Register), isNonPinned A = false →
      ({σ with regs := σ.regs.insert r v}).regs.get? A = σ.regs.get? A :=
    fun A hA => get?_insert_pinned σ.regs r v A (pin_of_isNonPinned hr hA)
  have E : ∀ (A : Register), (∃ w, σ.regs.get? A = some w) →
      ∃ w, ({σ with regs := σ.regs.insert r v}).regs.get? A = some w :=
    fun A h => exists_get?_insert σ.regs r v A h
  constructor
  case cur_privilege => rw [P _ (by decide)]; exact hG.cur_privilege
  case misa => rw [P _ (by decide)]; exact hG.misa
  case mstatus => rw [P _ (by decide)]; exact hG.mstatus
  case mie => rw [P _ (by decide)]; exact hG.mie
  case mseccfg => rw [P _ (by decide)]; exact hG.mseccfg
  case satp => rw [P _ (by decide)]; exact hG.satp
  case mtvec => rw [P _ (by decide)]; exact hG.mtvec
  case mideleg => rw [P _ (by decide)]; exact hG.mideleg
  case medeleg => rw [P _ (by decide)]; exact hG.medeleg
  case hart_state => rw [P _ (by decide)]; exact hG.hart_state
  case htif_done => rw [P _ (by decide)]; exact hG.htif_done
  case htif_tohost => rw [P _ (by decide)]; exact hG.htif_tohost
  case htif_tohost_base => rw [P _ (by decide)]; exact hG.htif_tohost_base
  case elp => rw [P _ (by decide)]; exact hG.elp
  case pmpcfg_n => rw [P _ (by decide)]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [P _ (by decide)]; exact hG.pmpaddr_n
  case pma_regions => rw [P _ (by decide)]; exact hG.pma_regions
  case menvcfg => rw [P _ (by decide)]; exact hG.menvcfg
  case mcountinhibit => rw [P _ (by decide)]; exact hG.mcountinhibit
  case mcyclecfg => rw [P _ (by decide)]; exact hG.mcyclecfg
  case minstretcfg => rw [P _ (by decide)]; exact hG.minstretcfg
  case mip => exact E _ hG.mip
  case sig_meip => exact E _ hG.sig_meip
  case sig_seip => exact E _ hG.sig_seip
  case mtime => exact E _ hG.mtime
  case mtimecmp => exact E _ hG.mtimecmp
  case minstret => exact E _ hG.minstret
  case minstret_increment => exact E _ hG.minstret_increment
  case mcycle => exact E _ hG.mcycle
  case nextPC => exact E _ hG.nextPC
  case PC => exact E _ hG.PC

/-! ## Orthogonal dimensions: memory and HTIF output

`GoodState` reads only `σ.regs`, so writes to `σ.mem` (stores) and pushes to
`σ.sailOutput` (HTIF console) preserve it definitionally. -/

/-- `GoodState` depends only on `σ.regs`: if two states share their register map,
one is `GoodState` iff the other is. Bridges the record-update states whose `.regs`
projection is defeq to `σ.regs` but not syntactically equal (so `exact hG` fails). -/
theorem GoodState.of_regs_eq {σ σ' : MState} (h : σ'.regs = σ.regs)
    (hG : GoodState σ) : GoodState σ' := by
  constructor
  case cur_privilege => rw [h]; exact hG.cur_privilege
  case misa => rw [h]; exact hG.misa
  case mstatus => rw [h]; exact hG.mstatus
  case mie => rw [h]; exact hG.mie
  case mseccfg => rw [h]; exact hG.mseccfg
  case satp => rw [h]; exact hG.satp
  case mtvec => rw [h]; exact hG.mtvec
  case mideleg => rw [h]; exact hG.mideleg
  case medeleg => rw [h]; exact hG.medeleg
  case hart_state => rw [h]; exact hG.hart_state
  case htif_done => rw [h]; exact hG.htif_done
  case htif_tohost => rw [h]; exact hG.htif_tohost
  case htif_tohost_base => rw [h]; exact hG.htif_tohost_base
  case elp => rw [h]; exact hG.elp
  case pmpcfg_n => rw [h]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [h]; exact hG.pmpaddr_n
  case pma_regions => rw [h]; exact hG.pma_regions
  case menvcfg => rw [h]; exact hG.menvcfg
  case mcountinhibit => rw [h]; exact hG.mcountinhibit
  case mcyclecfg => rw [h]; exact hG.mcyclecfg
  case minstretcfg => rw [h]; exact hG.minstretcfg
  case mip => rw [h]; exact hG.mip
  case sig_meip => rw [h]; exact hG.sig_meip
  case sig_seip => rw [h]; exact hG.sig_seip
  case mtime => rw [h]; exact hG.mtime
  case mtimecmp => rw [h]; exact hG.mtimecmp
  case minstret => rw [h]; exact hG.minstret
  case minstret_increment => rw [h]; exact hG.minstret_increment
  case mcycle => rw [h]; exact hG.mcycle
  case nextPC => rw [h]; exact hG.nextPC
  case PC => rw [h]; exact hG.PC

/-- A `GoodState` is preserved by replacing the byte memory (stores don't touch
registers). -/
theorem GoodState.set_mem {σ : MState} (hG : GoodState σ)
    (m' : Std.ExtHashMap Nat (BitVec 8)) : GoodState {σ with mem := m'} :=
  GoodState.of_regs_eq (σ := σ) (σ' := {σ with mem := m'}) rfl hG

/-- A `GoodState` is preserved by replacing the HTIF output buffer. -/
theorem GoodState.set_sailOutput {σ : MState} (hG : GoodState σ)
    (o' : Array String) : GoodState {σ with sailOutput := o'} :=
  GoodState.of_regs_eq (σ := σ) (σ' := {σ with sailOutput := o'}) rfl hG

/-! ## The chaining tactic

`goodstate_frame h` re-establishes `GoodState` of any state that is `h`'s state
plus a chain of non-pinned register inserts: it peels one `insert_nonpinned` per
write (each `NonPinned` side goal discharged by `decide`, each inserted value
`v` inferred by unification with the target insert-chain), then closes with `h`.

Usage in a step lemma:
```
example (hG : GoodState σ) : GoodState (sigmaPost σ pc vminstret) := by
  goodstate_frame hG
```
Equivalently, the plain iterated-application form (no tactic):
```
exact hG.insert_nonpinned (by decide) _ |>.insert_nonpinned (by decide) _ |> …
```
-/

/-- Re-establish `GoodState` of a non-pinned insert-chain over the state of `h`.
Peels `GoodState.insert_nonpinned` (discharging `NonPinned` by `decide`, inferring
each inserted value) until the goal is `h`'s `GoodState`. -/
syntax (name := goodstateFrame) "goodstate_frame " term : tactic

macro_rules
  | `(tactic| goodstate_frame $h:term) =>
    `(tactic|
      (repeat' first
        | exact $h
        | (apply GoodState.insert_nonpinned (hr := by decide))))

/-! ## Validation against `StepAddi` / `StepBeq` shapes

`sigmaPost σ pc vminstret` (`StepAddi.lean`) is the five-write chain
`minstret_increment := true`, `nextPC := pc+4`, `x10 := …`, `PC := pc+4`,
`minstret := v+1` — none pinned. The following `example`s confirm the machinery
reproduces `goodstate_sigmaPost` (and the `StepBeq` variants) in one line, so the
hand-written ~250-line reconstructions in those files could be replaced. (They are
left intact per the task; this is forward-looking validation only.) -/

/-- The ADDI five-write chain shape is handled by the chaining tactic. Matches
`Vsa.Sim.goodstate_sigmaPost` (`StepAddi.lean`). -/
example (σ : MState) (pc vminstret : BitVec 64) (hG : GoodState σ) :
    GoodState (sigmaPost σ pc vminstret) := by
  goodstate_frame hG

/-- The same, in the explicit iterated-application form (five inserts). -/
example (σ : MState) (pc vminstret : BitVec 64) (hG : GoodState σ) :
    GoodState (sigmaPost σ pc vminstret) :=
  ((((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _

/-- The taken-BGEU write chain (`StepBeq.lean`) — a five-write chain with two
`nextPC` writes and no GPR — is handled identically. Matches
`Vsa.Sim.goodstate_sigmaPost_taken`. -/
example (σ : MState) (pc vminstret : BitVec 64) (hG : GoodState σ) :
    GoodState (sigmaPost_taken σ pc vminstret) := by
  goodstate_frame hG

/-- The not-taken-BGEU write chain (`StepBeq.lean`). Matches
`Vsa.Sim.goodstate_sigmaPost_nottaken`. -/
example (σ : MState) (pc vminstret : BitVec 64) (hG : GoodState σ) :
    GoodState (sigmaPost_nottaken σ pc vminstret) := by
  goodstate_frame hG

/-- The ADDI **tick** write chain (`StepAddi.lean`'s `sigmaTick`): `sigmaPost`
followed by the `tick_clock` writes `mcycle`, `mtime`, `mip` — all non-pinned.
Confirms the tick dimension (`mcycle`/`mtime`/`mip`) frames the same way. Matches
the `GoodState` half of `Vsa.Sim.step_addi_tick`. -/
example (σ : MState) (pc vminstret vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) :
    GoodState (sigmaTick σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  have hpost : GoodState (sigmaPost σ pc vminstret) := by goodstate_frame hG
  exact ((hpost.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

end Vsa.Sim
