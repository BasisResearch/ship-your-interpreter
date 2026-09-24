# Lane A0: the boundary world — DONE (one user decision pending)

Package A0 of `VsaIris/INTERP_DESIGN.md` §5.1/§9. Imported from `VsaIris.lean`;
`lake build Vsa VsaIris VsaIris.Audit` is green; `check_iris_holes.py` passes. No holes added.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound} (`VsaIris/Audit.lean`).

## Interface for A (`term_sim_iris`, `stuck_sim_iris`)

```lean
-- VsaIris/Interp/World.lean
theorem world_of_boundary (b : Boot c p) {G : FrameGeom} (gap : BootGap b G)
    (ρ : Regime) (hρ : RegimeOK b.top ρ) :
    ([∗map] k ↦ v ∈ b.bytes G, k ↦ₘ v) ∗ consoleOwn (output c.σ) ⊢
      |==> ∃ γf γc, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes b ρ)
```

- `boot_of_loaded : Loaded interpRunLayout p c → Nonempty (Boot c p)`.
- `Boot.bytes G` is adequacy's `mm`; `Boot.bytes_agree` gives `MemAgree`.
- `bootRes b ρ` = `worldPre … ρ initSt 0` (heap `heapRes vsaLayoutP vsaRoomB ρ`, store, console,
  `Stdio.stdioOwn`, `interpCtxPre`) ∗ `frameAt 0 (φf 0)` ∗ `astSs` ∗ `roOn CodeByte m` ∗
  `roOn shared m` ∗ stack below `spEntry` ∗ `main`'s frame outside `struct Interp` ∗ other statics.
  `setjmp` (H5) turns `worldPre` into `world`.
- Heap layout/room are H4's `vsaLayoutP`/`vsaRoomB` (what `IrisHoles.alloc` consumes).
  `Boot.regime_of_bigStep` gives `RegimeOK b.top (.counted n)` at the derivation's cost;
  `regimeOK_uncounted` for partial mode.
- `textOwn_of_roOn`: any `textOwn` a block lemma needs, from `roOn CodeByte m`.
- `freeStack_carve` splits the stack for `interp_run`'s 176-byte frame; F3's
  `stackScratch_boundary` + `Boot.fits` carve the rest.

## Vacuity (`VsaIris/Interp/WorldVacuity.lean`)
`ctlBoot`, `ctl_bootGap`, `ctl_world_counted` (2^20 credits), `ctl_world_uncounted`:
`world_of_boundary` applies at the control program in both regimes.

## Findings
- **`BootGap` (named premise, not derivable from `Loaded`)**: the global frame's three blocks are
  distinct whole unshared chunk payloads (`FrameChunks`), `top_room`, H4's Q5 page-aligned break and
  Q5b 32-bit `binblocks`, and Q6 `_impure_data._stderr = &__sf[2]`. Recorded in
  PROOF_CLOSURE_PLAN.md §2 ("MISSING BOUNDARY FACTS (lane A0)") and INTERP_DESIGN §5.1.
- **Control snapshot fix**: `Vsa/Sim/OutputAliasSnapshot.lean` zeroed `_impure_data._stdin`/`_stderr`,
  while the ELF's `.data` holds `&__sf[0]`/`&__sf[2]` (`decide` proved `BootGap.stderr` false at the
  old control). Added the two ELF words to `snapshotWords`; everything downstream rebuilds green.
- Kernel hang (previous session): `bootAddrs` was `(List.range (2^32)).filter …`, which the kernel
  unfolded. It is now sealed behind `Classical.choose`; World.lean checks in ~2 s.
- After the hub merge `struct Interp` is 480 bytes (jmp_buf 208, `err_msg` @224); VSA's
  `interp_geom : ObjGeom (inp, 384)` undercounts but is only a geometry bound.

## Pending (user)
Supply `BootGap` as `InterpRunReadyFacts` fields (a statement change like S1's
`stack_admissible`), or keep it as a premise of the Iris theorems?
