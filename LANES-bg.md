# Lane BG: A0's `BootGap` moved into `Loaded` — DONE

User decision (2026-09-24): the boundary facts A0 took as the premise `BootGap` become
`InterpRunReadyFacts` fields, as S1 did with `stack_admissible`.
`lake build Vsa VsaIris VsaIris.Audit` is green; `check_iris_holes.py` passes. No holes added.
Axioms of every new theorem ⊆ {propext, Classical.choice, Quot.sound} (`VsaIris/Audit.lean`).
`Vsa/Refinement.lean` is unchanged.

## Statement change (`Vsa/Sim/LayoutInstance.lean`)

`InterpRunReadyFacts.ownership : ∃ D, InitialOwned … D` is replaced by

```lean
boot : ∃ D top brkv chunks bins F, BootHeap c.σ.mem A φf φc stmts count D top brkv chunks bins F
-- BootHeap = { owned : InitialOwned …, alloc : InitialAllocatorAt …, facts : BootHeapFacts … }
-- BootHeapFacts = { top_room, brk_page, binblocks, frame : BootFrameChunks, stderr }
```

The facts share one set of witnesses (the `shared` set and one allocator walk), which is why
they sit with `InitialOwned` in one field. `InterpRunReadyFacts.ownership` is now a theorem with
the old field's type, so its consumers compile unchanged. All definitions are in Vsa terms
(`BootFrame`, `BootFrameChunks`, `impureStderrAddr`), not Iris terms.

## Interface for A (`VsaIris/Interp/World.lean`)

```lean
theorem world_of_boundary (b : Boot c p) (ρ : Regime) (hρ : RegimeOK b.top ρ) :
    ([∗map] k ↦ v ∈ b.bytes b.G, k ↦ₘ v) ∗ consoleOwn (output c.σ) ⊢
      |==> ∃ γf γc, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes b ρ)
```

- `Boot` gained `frame : BootFrame` and `heapFacts : BootHeapFacts …`; `boot_of_loaded` fills
  them from `InterpRunReadyFacts.boot`.
- `Boot.G : FrameGeom` is the global frame's geometry; `Boot.gap : BootGap b b.G` is the
  projection of the old premise; `Boot.frameChunks` gives `FrameChunks … b.G`.
- The gap argument and `G` are gone from `boot_of_bytes` and `world_of_boundary`; adequacy's
  `mm` is `b.bytes b.G`.

## Witnesses

- Control: `Vsa/Sim/NativeNameAudit/ControlBootHeap.lean` (`Control.bootHeap`, kernel `decide`s
  and reads through the heap log, moved from A0's WorldVacuity), used by `Control.readyFacts`,
  hence `Control.loaded`. `ctl_bootGap := ctlBoot.gap`; `ctl_world_counted`/`_uncounted` still
  instantiate `world_of_boundary`.
- `c/tests/*.wl`: **not done, and not meaningful in S1's form.** `ProgramStackFits` is a
  predicate on the AST, so S1 could decide it per program. No new field mentions the program.
  They are facts about the loaded memory, and no checked `Loaded` configuration has been built
  for any `c/tests` program, for any field (the control is the only one). A per-program witness
  would need a loaded memory holding each program's AST, frame and heap walk. That means building
  the `NativeNameAudit/Control*` construction (about 1.9k lines) once per program, or making it
  generic over an AST encoder.

## Docs

INTERP_DESIGN.md: a "Decisions" bullet, "STATEMENT CHANGE (lane BG)", §5.1 updated, Q5/Q5b/Q6
marked resolved. PROOF_CLOSURE_PLAN.md §2: the A0 and H4 boundary entries now name the supplier.

## Next (user)

Whether to build per-program `Loaded` configurations for `c/tests/*.wl` (see above).
