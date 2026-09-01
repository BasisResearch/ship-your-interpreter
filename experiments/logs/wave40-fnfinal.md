# Wave 40 — FnResid final: φc-entry rebase + off-path bundle suppliers

## Context read
- FnResidSupply.lean: `fnArmGeom_hArm_offdiag` takes `hEntryRebase : ∀ mm, StoreRepr mm N A φf φc st.store → StoreRepr mm N A φf φc' st.store` as a NAMED premise. `fnResid_of_pipeline` assembles FnArmSpec ∧ EvalRecWiden from it. Both green.
- FnArmSeams.lean: `AllocBuildStagingLink`/`AllocBuildTailFacts`/`AllocBuildReloadPost` are named-field bundles; `staging_of_link`/`allocBuildEntry_tail`/`fnArmSeamRun_of_seams` CLOSED modulo those bundles.
- StoreRepr (RuntimeRepr.lean:128): φc appears in `frames` (via FrameRepr→ValueRepr .closure), `closures`, `φc_inj`, `closures_arena`. All at indices `< s.closures.size` EXCEPT the frame-value `.closure ca` refs which have NO structural bound.
- PhiExtends φc φc' n = ∀ a<n, φc' a = φc a (InterpEntry.lean:101).

## Rebase analysis
- General `storeRepr_phic_mono` is FALSE without a side-condition: a frame value `.closure ca` with `ca ≥ s.closures.size` breaks it (φc' ca may ≠ φc ca).
- Honest route: define `StoreClosuresBounded s` (frame-value closure refs are in-bounds) as a named-field structure; prove `storeRepr_phic_mono` under it. This discharges `hEntryRebase` given the bound.

## Work log

### Item 1 DONE — φc-entry rebase LANDED
- `Vsa/Sim/rows/StoreReprPhicRebase.lean` GREEN + axiom-clean {propext, Classical.choice, Quot.sound}, 0.5s.
- `ValueClosuresBounded size v` (frame-value closure ref < size), `StoreClosuresBounded s` (named-field: all frame-value closure refs in-bounds).
- `valueRepr_phic_mono` / `frameRepr_phic_mono` / `storeRepr_phic_mono`.
- `storeRepr_phic_mono : StoreClosuresBounded s → PhiExtends φc φc' s.closures.size → StoreRepr m N A φf φc s → StoreRepr m N A φf φc' s`.
- ROUTE TAKEN: `storeRepr_phic_mono` under the honest `StoreClosuresBounded` side-condition (NOT the two-map generalization). General mono is genuinely FALSE (frame-value `.closure ca` with ca≥size). This discharges `hEntryRebase` given `StoreClosuresBounded st.store` + `hpc`.

### Item 1 WIRED into FnResidSupply
- Added `import Vsa.Sim.rows.StoreReprPhicRebase` + `fnResid_of_pipeline_wf` to FnResidSupply.lean.
- `fnResid_of_pipeline_wf` = `fnResid_of_pipeline` with `hEntryRebase` DISCHARGED from `StoreClosuresBounded st.store` (hWF) + hpc via `(fun _ hsr => storeRepr_phic_mono hWF hpc hsr)`.
- GREEN + axiom-clean, 1.6s. Oleans regenerated.
- NET: the ONE genuine new lemma-gap of wave 39 (hEntryRebase) is now a real proven lemma modulo the honest store-WF side-condition StoreClosuresBounded (a spec invariant, not a machine residual).

### Items 2-4 DONE — FnResid top-level supplier + residual analysis

**Item 2/3 assessment (bundle suppliers + 9 dispatch facts):**
- `AllocBuildStagingLink`/`AllocBuildTailFacts`/`AllocBuildReloadPost` (FnArmSeams.lean) are ALREADY landed as named-field bundles with `staging_of_link`/`allocBuildEntry_tail`/`fnArmSeamRun_of_seams` closing FnArmSeamRun modulo them. Their fields are the IRREDUCIBLE off-path machine residuals (arm-front a3:=φf env decode, the AllocBuildEntry ~30-field marshalling, the reload lds head). No combinator removes them; they are the same class as the strdup StrdupMemcpyContent bundle.
- The 9 dispatch facts (hkind/hslot/hcallee/... for fn tag 10 @ armPC 0x800033c4): these are Layout-GROUNDED. `KindSlotPinned 10 armPC m0` needs the concrete .rodata jump-table bytes at slot 10, which are only concrete at M6 Layout. `int_slot_kindPinned` works only because EvalEntry bakes int (tag 0) couplings; tag 10 has no such carried fact. So these stay as premises, exactly as every leaf/arm row threads dispatch facts down to the Layout. NOT derivable here.

**Item 4 — FnResid top-level supplier LANDED:**
- `FnResidBundle` (named-field structure, ∀-closed over the FnResid ghosts): hAlloc + hWF (StoreClosuresBounded) + perGhost (∃ φc' + hpc + hout + 9 dispatch facts + hSeam:FnArmSeamRun + hW:EvalRecWiden).
- `fnResid_from_bundle : FnResidBundle → FnResid` — GREEN + axiom-clean. Intros the FnResid ghosts, unpacks perGhost, applies fnResid_of_pipeline_wf.
- eval_fn_row's oracle `∀ st d env..., FnResid ...` is now premise-free MODULO one `∀ st d env..., FnResidBundle ...`.

## FINAL STATUS

### Rebase route
- `storeRepr_phic_mono` under `StoreClosuresBounded` (NOT two-map generalization). General mono genuinely FALSE (frame-value `.closure ca`, ca≥size, unconstrained by StoreRepr).
- LEMMA: `storeRepr_phic_mono {m N A φf φc φc' s} (hcb : StoreClosuresBounded s) (hpe : PhiExtends φc φc' s.closures.size) (hr : StoreRepr m N A φf φc s) : StoreRepr m N A φf φc' s`.
- discharges `hEntryRebase` in `fnResid_of_pipeline_wf`.

### Supplier status per bundle
- AllocBuildStagingLink: closed by staging_of_link (FnArmSeams.lean, wave39) modulo the named bundle fields = irreducible arm-front decode residuals. NOT further reducible.
- AllocBuildTailFacts/AllocBuildReloadPost: closed by allocBuildEntry_tail (FnArmSeams.lean, wave39) modulo the named bundle = ~28 arm-entry-carried facts transported via CallSpec foot/memOut. NOT further reducible.
- These feed FnArmSeamRun via fnArmSeamRun_of_seams; FnArmSeamRun is the `hSeam` field of FnResidBundle.perGhost.

### 9 dispatch facts (fn tag 10 @ 0x800033c4)
- Layout-grounded (need M6 .rodata jump-table bytes at slot 10); threaded as premises inside FnResidBundle.perGhost, exactly as every leaf/arm row. NOT derivable pre-Layout.

### FnResid / eval_fn_row end-state
- eval_fn_row (CallRows.lean:364) hFn slot: ALREADY green (wave39). Demands `∀ st d env..., FnResid ...`.
- FnResid is now premise-free MODULO ONE named bundle: `fnResid_from_bundle : FnResidBundle → FnResid` (green, axiom-clean).
- FnResidBundle fields = the itemized irreducible residuals: hAlloc (row's own), hWF (StoreClosuresBounded — spec invariant), perGhost (∃ φc' + hpc + hout + 9 dispatch facts + hSeam:FnArmSeamRun + hW:EvalRecWiden).
- So: the whole EX_FN → FnResid → hFn chain is CLOSED down to (a) the FnArmSeams named bundles (arm-front decode + AllocBuildEntry marshalling), (b) the 9 Layout-grounded dispatch facts, (c) EvalRecWiden, (d) StoreClosuresBounded. The wave39 φc-rebase gap is ELIMINATED (now a real lemma).

### Files
- NEW: Vsa/Sim/rows/StoreReprPhicRebase.lean (green, axiom-clean, discipline OK, 0.5s)
- EDIT: Vsa/Sim/rows/FnResidSupply.lean (+import + fnResid_of_pipeline_wf + FnResidBundle + fnResid_from_bundle; green, axiom-clean, discipline OK, 2.1s)
- Oleans regenerated into .lake/build/lib/lean/Vsa/Sim/rows/
- observations.md: rebase observation marked RESOLVED.

### WIRING (report-only, NOT applied)
- Vsa.lean: add `import Vsa.Sim.rows.StoreReprPhicRebase` (before FnResidSupply) — FnResidSupply already imports it, but Vsa.lean needs it for #print axioms of its theorems. Actually FnResidSupply import chain covers it; add `import Vsa.Sim.rows.FnResidSupply` if not already present (wave39 reported it should be added).
- scripts/check_all.sh axiom list: add
  `Vsa.Sim.valueRepr_phic_mono`, `Vsa.Sim.frameRepr_phic_mono`, `Vsa.Sim.storeRepr_phic_mono`,
  `Vsa.Sim.fnResid_of_pipeline_wf`, `Vsa.Sim.fnResid_from_bundle`.

### Signals / blockers
- No falsity found beyond the (expected) general-storeRepr_phic_mono falsity, which is handled by the honest StoreClosuresBounded side-condition.
- The remaining residuals (FnArmSeams bundles + 9 dispatch facts + EvalRecWiden) are the SAME class every arm carries to M6; not new gaps.
- StoreClosuresBounded is a NEW spec-WF obligation the caller must supply for the .fn arm; it is a genuine store invariant (closures are only created by allocClosure, returning in-bounds indices) — a candidate for a global store-WF lemma if a StoreWF invariant is ever threaded through the interpreter's EvalE/ExecStmt.
