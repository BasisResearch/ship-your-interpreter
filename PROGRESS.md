# iris-machine progress

## Done

- **Multi-step segment rule** (`VsaIris/Step.lean`, `wp_run`, commit 356cb61).
  VSA's facts are segment facts: `n` instructions with only an end-state
  frame. The state interpretation now lets the ghost maps lag the machine by
  `j` steps. `j` sits in a third ghost map (`ctl`, key 0). `mTWP` hands its
  prover the key-0 cell at 0 (`cpuTok`), so clients always see `j = 0`.
  `wp_run` proves an `n+1`-step footprint rule from a `RunFact`: a uniform
  exact step count and an effect confined to the written cells. It never
  describes the states in between. `wp_local_step` is now its one-step case.
  `MachineModel` gains `ok : State → Prop` (default `True`), which the state
  interpretation carries and every step rule re-establishes.
- **VSA instance** (`VsaIris/Vsa/Instance.lean`, commit 074583c).
  - `vsaModel live` is the Iris machine over `Config` and `stepOnce`. The PC
    is at index 32, GPRs go through `gprGet`, and memory is the total read.
    `VsaOk live` bundles `GoodState`, tick < 2, GPR presence, and presence
    of a `live` byte set (for code fetch).
  - `vsa_adequacy` concludes `Vsa.Machine.Halts c out 0`, verbatim.
  - `seg_runFact` turns `segEval_sound` into a `RunFact`, and `wp_seg` is
    the Iris segment rule with named ownership (PC, pinned GPRs, written
    bytes, read-only bytes). It is one generic lemma, not per-site.
- **Tools** (`VsaIris/Vsa/Tools.lean`): code slicing (`instrAt_append`),
  blocks as byte lists (`blockOwn_range`), code presence (`code_present`),
  and a `jal` site as `JalExec` (`jalExec_of_site`, over VSA's `JalStep`).

## In flight

- Pilot: env_new (`VsaIris/Vsa/EnvNewPilot.lean`), in continuation style.
  The plan is the prefix segment (`wp_seg`), then `jal malloc`
  (`wp_call_malloc` + `jalExec_of_site`), then the existing
  `envNewSuccessSeg` (`wp_seg`).

## Holes

- `DlMallocImpl` (unchanged, pre-existing): malloc/free meet their specs.
- The pilot's NULL path, where `malloc` returns 0 and env_new reaches
  `fwrite`/`exit`, will be a caller-supplied continuation. The VSA proof
  assumes arena non-exhaustion instead.

## Next

- Finish the pilot, measure lines and elaboration time against the VSA cone
  of `envNewAllocator_run`, and write the report.

## QUESTIONS

- `live`: a points-to fixes the *total* read (`getD 0`). Fetch facts need
  `σ.mem[a]? = some b`, so byte presence for code comes from `VsaOk.live`, a
  fixed set that stores never shrink. The alternative is an `Option`-valued
  memory projection, where points-to implies presence. That is cleaner for
  code, but it makes never-written arena bytes unownable, which would break
  `isHeap`. I chose the total read plus `live`.
