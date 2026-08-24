# M3 pilot design note — Layer-3 function specs over the Sail RV64 model

Deliverable of the M3 method pilot: the first Layer-3 total-correctness triple
(`Vsa.Sim.muldi3_spec`, libgcc `__muldi3` shift-add 64-bit multiply) **and** the
reusable method that produces it. This note records the spec-statement pattern,
the parity/noise design, what generalizes to the next specs (`strlen`, `env_*`),
and the per-site cost.

Files (all `sorry`/`axiom`/`native_decide`/`bv_decide`-free; `muldi3_spec`
depends only on `propext`, `Classical.choice`, `Quot.sound`):

- `Vsa/Sim/StepObs.lean` — parity-agnostic observational step wrappers (the
  reusable core).
- `Vsa/Sim/Muldi3Sites.lean` — the 9 per-site step lemmas.
- `Vsa/Sim/Muldi3Spec.lean` — config-level `Triple` composition: arithmetic
  invariant, transitions, loop, final spec.

## The Layer-3 design move: observational steps (`StepObs`)

`stepOnce` ticks the platform clock every `plat_insns_per_tick = 2` retired
instructions, so every Layer-0/2 step lemma comes in two variants
(`step_*_notick` / `step_*_tick`) whose post-states differ by `tick_clock`'s
`mcycle`/`mtime`/`mip` writes (`sigmaPost_*` vs `sigmaTick_*`). A Layer-3 spec
must be **parity-agnostic**: the caller does not know the tick counter's parity
at the entry PC.

`StepObs.lean` folds the two variants into **one** wrapper per instruction class:

```
stepObs_alu … (hi : i < 2) :
  ∃ σ' i', Step ⟨σ,i,u⟩ ⟨σ',i',u+1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
    σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_alu …)
```

The two moves that make this work:

1. **`i < 2` is the tick invariant.** `stepOnce` keeps the tick counter in
   `{0,1}` (resets to `0` on the boundary, otherwise `0 ↦ 1`). Carrying `i < 2`
   lets the loop re-enter with the counter unconstrained, and lets the wrapper
   `by_cases (i+1 = 2)` to pick the notick/tick lemma.

2. **`ReadsLikePost σ' spost` — observation via `get?`, not insert-chains.**
   `ReadsLikePost σ' spost := ∀ R ∉ {mcycle, mtime, mip}, σ'.regs.get? R =
   spost.regs.get? R`. Since GPRs and the PC are never in the tick write-set, the
   tick state reads *identically* to the notick `sigmaPost_*` on every observable
   register (`get?_sigmaTick_* : sigmaTick reads = sigmaPost reads` off the three
   tick inserts). So the observation is the **same term** whichever variant
   fired — the parity split disappears into the unmentioned noise registers.

This is the general Layer-3 turn: Layer-0 syntactic insert-chains stay internal;
Layer-3 speaks only through `get?` read-backs, and clock noise / instruction
counting are absorbed existentially (`∃ i'`, `∃ minstret`).

One wrapper per class used here: `stepObs_alu` (ITYPE/RTYPE/SHIFTIOP …),
`stepObs_branch_taken` / `stepObs_branch_nottaken` (BTYPE), `stepObs_jr` (the
`ret = jalr x0` pseudo form). They live in `StepObs.lean` for reuse by later
function specs.

## Spec statement pattern (`muldi3_spec`)

```
def muldi3_pre  x y r m0 c := (∃ a2 a3, St 0x…640 x y a2 a3 r m0 c) ∧ r.toNat % 4 = 0
def muldi3_post x y r m0 c := GoodState c.σ ∧ c.σ.mem = m0 ∧
                              PC = r ∧ x10 = x*y ∧ x1 = r
theorem muldi3_spec : Triple (muldi3_pre x y r m0) (muldi3_post x y r m0)
```

Ingredients of the pattern (reusable for the next specs):

- **Ghost parameters.** `x`, `y` (operands), `r` (return address), `m0` (the
  pinned memory) are ∀-bound parameters of the theorem, threaded through `P`/`Q`.
  Memory-unchanged is stated as `c.σ.mem = m0` in both `P` and `Q` (no stores ⇒
  `.mem` is `rfl`-preserved by every regs-only step).

- **A single config predicate `St`.** `St pc a0 a1 a2 a3 r m0 c` bundles the
  standing observation at a program point: `GoodState`, code-loaded, `mem = m0`,
  PC, the live GPRs, `x1 = r`, `minstret` defined (∃), and `c.tick < 2`. Every
  transition is a one-step `Triple` between two `St`s. Clobbered registers
  (a0–a3 = x10–x13) are tracked; everything else is unchanged and can be read
  back through the `post_*_other` frame lemmas if `Q` needs it.

- **Noise absorption.** `minstret` is `∃`-quantified in `St` (never pinned to a
  value); `mcycle`/`mtime`/`mip` never appear; the tick counter is `< 2` only.
  `Q` mentions no cycle/time/instret values — exactly the plan's requirement.

- **Fetch-side conditions as `P` hypotheses.** `r.toNat % 4 = 0` (return address
  4-aligned) is in `P`; the per-site fetch bounds (`0x80000000 ≤ pc`,
  `pc+4 ≤ tohostAddr`, `pc % 4 = 0`) are `by decide` at each concrete site pc.

## Loop handling (`Triple.loop`)

The shift-add loop (`0x48 … 0x5c`, back-edge `0x5c → 0x48`) is a **bottom-tested
do-while**: the exit branch (`bnez`) tests the *updated* `a1`, so the exit
happens mid-flow, not at a clean head. The clean encoding for `Triple.loop`:

- **Invariant** `LoopI = AtHead ∨ AtDone`: either at `0x48` with the shift-add
  invariant `a0 + a2*a1 = x*y`, or already done at `0x60` with `a0 = x*y`.
- **Guard** `LoopB` = "at `0x48` with `a1 ≠ 0`". Excluding `a1 = 0` from the
  guard is essential: it keeps the measure strictly decreasing on the exiting
  iteration (`a1 ≠ 0 ⇒ (a1>>>1).toNat < a1.toNat`, `shr_lt`), which the loop rule
  demands even for the iteration that leaves the loop.
- **Measure** `LoopMu c = x11.toNat` (total via `getD 0#64`).
- **Body** (`loop_body`): one iteration `iter_48_5c` (internally `by_cases` on
  the low bit for the conditional `add`), then `by_cases (a1>>>1 = 0)` for the
  `bnez` — loop back (`AtHead`, measure ↓) or fall through (`AtDone`).

`loop_to_done` runs `Triple.loop` then discharges the two `LoopI ∧ ¬LoopB`
exits: `AtDone` (already at `0x60`) or `AtHead ∧ a1 = 0` (run one last iteration
to `0x60`, `a0 = x*y` since `a2*0 = 0`).

### The arithmetic core (BitVec 64, wrap-around, no `bv_decide`)

The invariant preservation reduces to one identity, proved by `toNat` + mod-2^64
Nat reasoning with core lemmas only (no Mathlib, no `bv_decide`):

```
invmul_bv : a2 * a1 = (a2 <<< 1) * (a1 >>> 1) + (a1 &&& 1) * a2
```

`inv_even` / `inv_odd` specialize it (`a1&1 = 0` / `= 1`) to the even/odd
iteration. `shr_lt` (`a1 ≠ 0 ⇒ (a1>>>1).toNat < a1.toNat`) is the measure-decrease
fact. `ret_tgt` (bit-0 clear of a 4-aligned `r` is a no-op) closes the `ret`
target via a per-bit `testBit` argument. These are the only genuinely
"mathematical" lemmas; everything else is machine-stepping plumbing.

## Per-site cost

Each of the 9 sites (`Muldi3Sites.lean`) is: one `hexec` assembly (decode lemma
`Vsa.Sim.DecodeTable.decode_<word>` + one/two `rX_bits_*` read-backs through the
prelude frame + one `wX_bits_*`), byte-word + non-RVC `by decide` facts, and one
`stepObs_*` application. ~15 lines for a straight-line ALU site; branch sites
split taken/not-taken (~25 lines the pair); `ret` is the `stepObs_jr`
instantiation. This is the DemoStore/DemoLoad recipe, unchanged.

Each config-level transition (`Muldi3Spec.lean`) is a one-step `Triple.of_step`
whose successor `St` fields are read off `ReadsLikePost` through the `obs_*_*`
consumers (`obs_alu_pc/rd/other/minstret`, `obs_btaken_*`, `obs_bnottaken_*`,
`obs_jr_*`). ~12 lines each. The `obs_*` consumers are reusable across specs.

## What generalizes to `strlen`, `env_*`

- **`StepObs.lean` is spec-independent** — the observational wrappers cover the
  ALU/branch/jump classes any function uses. Load/store classes need one more
  `stepObs_load`/`stepObs_store` wrapper each (same shape, over the existing
  `step_store_*`/`step_load_*` lemmas), plus the mem-changed conjunct (`strlen`
  reads only; `env_*` may store — then `Q`'s `mem = m0` becomes a described
  update).
- **The `St` + `obs_*` + one-step-`Triple` composition pattern** transfers
  verbatim. Only the tracked register set and the per-function invariant change.
- **`Triple.loop` with the `AtHead ∨ AtDone` invariant and guard-excludes-exit
  measure** is the template for any counted loop; `strlen`'s loop (increment a
  pointer until a NUL byte) is measure = bytes-remaining, guard = "not at NUL".
- **Arithmetic cores are per-function** but small and `toNat`/`omega`-shaped;
  the discipline (reduce BitVec to `toNat` mod 2^64, close with core Nat lemmas,
  never `bv_decide`) is fixed.

## AMENDMENT (post-pilot, proven in the division cluster): ghost-frame threading

The pilot's `St` tracked only the live registers, and `muldi3_post` asserted
only x1/x10 — with the claim that untracked preservation "is a one-line
read-back if a future caller needs it". **That claim is wrong**: once a
transition is packaged as a `Triple` over a state predicate that omits
register R, R's value is unrecoverable downstream (per-step observations are
consumed eagerly; `Triple.conj` of two triples is unsound; machine
determinism does not rescue it). The `__umoddi3` wrapper needs t0/x5 to
survive the `jal` into the core — impossible against the untracked core spec.

**The rule (mandatory for every Layer-3 state predicate):** carry a blanket
ghost-frame conjunct from the start —

```
Ust (g : (R : Register) → Option (RegisterType R)) … where
  …
  hframe : ∀ R, NotWritten R → c.σ.regs.get? R = g R
```

`NotWritten R` is an `abbrev` (NOT `def` — `by decide` must synthesize
`Decidable`, and the frame helpers destructure it) for the Bool-disequality
conjunction over the function's written registers ∪
{PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip}. One generic
helper per instruction class (`frame_alu`, `frame_btaken`, `frame_bnottaken`,
`frame_jr`, …: `ReadsLikePost` + the `get?_sigmaPost_*` frame lemma ⇒
variable-R read-back) makes each transition's frame obligation one line:
`fun R hR => (frame_XXX hobs R … hR).trans (hSt.hframe R hR)`. `g` is
constant through the whole function and ties to the entry state in the pre.

Caller side: instantiate the callee's ghost at the call-site successor state
(`g := fun R => σ₂.regs.get? R` — the entry `hframe` becomes `rfl`), and the
callee's post-frame returns every untouched register (this is how
`umoddi3_spec` recovers t0 across the `jal`).

Also surface `c.tick < 2` in every function post (the caller must keep
stepping), and remember `GoodState` does NOT pin GPRs — a caller must supply
`∃ v, get? = some v` for every GPR the callee's `Ust` tracks.

Retrofit status: division core DONE (`DivSpec`/`DivLoops`). `Muldi3Spec`'s
`St`, `MemcpySpec`'s `StB`/`StW`, and `StrlenSpec` still lack the frame
conjunct and must be retrofitted before anything composes them as callees.
Cross-region calls additionally conjoin BOTH functions' `*Loaded` predicates
in P (per-function code predicates are independent byte-pins).

## AMENDMENT 2 (post-string-family): accumulated composition rules

Everything below was learned the hard way across the strlen/strcmp/strcpy/
memcpy/value_*/div specs; M4-tier work must follow these from the start.

- **Exit-bundle states carry FULL state.** Any disjunctive "exit" predicate
  a loop or dispatcher lands in (e.g. `WordExit`) must carry every live
  GPR, `x1 = r`, `minstret ∃`, `tick < 2`, `GoodState`, `mem` relation,
  region/`CStr` witnesses, and the ghost frame — a thin PC+facts tuple is
  un-composable downstream and forces a re-thread of the emitting proofs
  (the `WNulExit` widening).
- **Loop-invariant terminal PCs must be concrete literals** distinct from
  the guard PC. An exit disjunct at `PC = r` (generic) breaks the
  PC-guarded measure (`if PC = head then μ else 0`); run the `ret` *after*
  the loop from a literal-PC pre-ret state.
- **Measures against `2^64`:** when no length register exists, use
  `2^64 − ptrReg.toNat` (pointers increment without wrap); a
  `len + 1 − pos` measure saturates at 0 when `pos` is an absolute address.
- **Path crossovers instantiate fresh ghosts** (`g' := σ.regs.get?` at the
  crossover state); the unified spec exposes one top-level ghost and each
  branch's post-frame chains back through the dispatch frames.
- **Jump tables**: switch dispatch may compile to a `.rodata` jump table
  (auipc/slli/add/lw/add/jr). The table bytes are NOT in the function's
  `*Loaded` predicate — carry a separate byte-pin hypothesis; extract
  values with `objdump -s -j .rodata`. The computed `jr` composes via
  `stepObs_jr` with a generic rs1.
- **Stack-using functions** (spills): the post's memory clause is framed to
  exclude the stack window below entry `sp` (the `MallocContract`/env_new
  form: `∀ a, ¬priv a → ¬(SL.lo ≤ a < sp) → mem[a]? = m0[a]?`). A unified
  spec mixing stack-free and stack-using branches uses the weaker
  stack-window post. Spilled slots survive callee calls via the callee's
  own stack-window/mem-unchanged clause.
- **Total vs byte-present loads at call sites:** specs whose loads use the
  byte-present (`get? = some`) chains impose MAPPEDNESS preconditions
  (e.g. strcpy's `SrcWordMapped` for the aligned tail's over-read).
  Malloc'd buffers are only mapped where written — at M4 call sites either
  discharge mappedness from the allocation/write history or restate the
  relevant sites with the total (`getD`) chain.
- **Structure fields shadow structure parameters** of the same name for
  later fields — name observation fields distinctly (`pcget`).
- **Collision discipline:** before adding top-level names, sweep
  (`comm -12`) against all of `Vsa/Sim` + `Vsa`; the aggregate build is
  the only place duplicates surface, long after both files verified.

## Remaining / caveats

Nothing is left `sorry`'d — `muldi3_spec` is complete and kernel-checked. Two
modelling choices worth noting for the next specs:

- `muldi3_post` states `x1 = r` (return register intact) and the clobbers
  `x10 = x*y`; it does **not** re-assert the *other* callee-saved GPRs, because
  `St` only tracks x10–x13 and x1. Re-asserting an arbitrary preserved GPR is a
  one-line `obs_*_other` read-back if a future caller needs it — the information
  is present, just not surfaced in `Q`.
- The `ret` fetch-side window facts (`r` in RAM, below `tohost`) are **not**
  needed here because `ret` only *reads* `x1` and redirects the PC; the machine
  does not fetch at `r` within this triple. A caller that continues past `ret`
  supplies those as its own `P`.
