# Cure suite — the crux (hCallClosure, hDivCorr)

> **PRE-WAVE SEALED BANNER.** Sealed 2026-09-02, tree @c9e1453 (CEGIS production
> sweep: io/str/singleton/crux). Sealed = production input AND uncontaminated
> prospective validation. Written BEFORE the proving wave; reseal a new dated
> block rather than editing. Nothing here enters a proof (Law 4 / design-time).
> The crux inputs are ALREADY mined + validated (`invariants/crux-relations.md`);
> this suite records the verdict, it does not re-open the mining.

Fields (`Vsa/Sim/TermAssembly.lean`):
- `hCallClosure` (:200) — the closure-call depth **CRUX** (X7). Whole premise:
  `∀ st d a cd vs store' frame st' status v (a_1…a_5), …` with `a_3 : d < maxCallDepth`
  and `a_5 : ExecSeq …` — recursion-composition over the body handoff.
- `hDivCorr` (:297) `Vsa.Sim.DivFamily.DivCorrFamily L` — the divergence oracle
  family (X8), progress-only ("≥1 step, still corresponds") over the recursor.

## 1. Obstruction — SURVIVED (no refutation exists)

- `statement_fuzz` (mining): `hCallClosure` **candidate-mined+SURVIVED**; kind-seam
  aligned. `hDivCorr` has no span (oracle family) — validated via its inputs below.
- `cegis_cure.py --file invariants/hCallClosure.lean --prop mined`:
  **Detected defects: none — Survivors: 0** (defers).
- `crux-relations.md` (mined+validated, `mine_crux_ladder.py`): **no mismatch, no
  pre-proof falsity**. Every mined constant matched `StackNeed`:
  R1 per-call descent 1088 = `evalFrame`; R2 max-level 2352 ≤ `perCallBudget` 6144;
  R4 ladder `1264·d + 1175` (the falsity-#13 form, budget INDEXED BY d — the old
  constant `stackOK` 2176 refuted at depth 1, already amended); R5 `d < maxCallDepth`
  guard holds (max d=4 < 1000); R6 one `allocFrame`/call = `PhiExtends +1`.
- Real-input probes (axiom-clean, `/tmp/crux_{real,budget}_probe.lean`):
  `BodyGhostTie` inhabited by `⟨rfl,rfl,rfl⟩` AND non-vacuous (ghost mutant refuted);
  `StackOK.child` carries per-descent 1088 through the `(maxCallDepth−d)·perCallBudget`
  ladder for all `d < maxCallDepth`, machine-checked.
- `smt_check --joint-inhabit` on the mined budget structs → **UNKNOWN-OPAQUE**
  (Nat-budget arithmetic; opaque, so no countermodel — consistent with SURVIVED;
  the ladder is already validated axiom-clean by the /tmp probes above).

**⇒ PROVE-DIRECTLY-HARD.** The statement is TRUE as stated (inputs mined AND
validated); it is HARD because it needs the *induction*, not because it is false.

## 2. cegis_cure — N/A (no false field to cure)

`Detected defects: none, Survivors: 0`. There is no cure suite for the crux
because there is nothing to cure — falsity #13 (the constant-budget unsoundness)
was ALREADY amended (budget re-indexed by depth `d` in `StackNeed`, B0 landed;
budgeted-entry re-index B1). The current statement carries `d < maxCallDepth` and
the `(maxCallDepth − d)·perCallBudget` ladder, which the mining confirms sound.

## 3. Classification — PROVE-DIRECTLY-HARD (recursion composition)

Both fields are **recursion-composition** obligations, which is exactly why the
CEGIS/SMT tools defer:

- **hCallClosure — WHY THE TOOLS DEFER:** the obligation is a *composition over the
  body handoff* (`a_5 : ExecSeq …` at depth `d+1`), i.e. a self-referential
  strong-induction on fuel/depth. `cegis_cure` operates on a SINGLE statement's
  address-map/quantifier structure; it cannot synthesize an induction hypothesis or
  a fold combinator — so it correctly reports no defect. `smt_check` sees the
  `ExecSeq`/`allocFrame`/`Store` predicates as opaque (uninterpreted) → no
  countermodel. The residual is the depth/budget induction: consume the LANDED
  `StackNeed.StackOK.child` ladder (validated) + `CallClosureGeom`/`BodyHandoff`
  (`BodyGhostTie` identity handoff) + `env_define` env-fold. Sibling-owned
  (`rows/CallClosureRow`, `TermGuards.depthCrux` + `TermCallees.envDefine`).
  **Likely TRUE-just-needs-the-induction.**

- **hDivCorr — WHY THE TOOLS DEFER:** `DivCorrFamily L` is a per-load correspondence
  family with NO machine span — a progress-only oracle threaded through the mutual
  recursor. It has no telescope for the fuzzer to witness and no encodable atom for
  SMT. Divergence endgame is CLOSED per memory (waves 22-33) onto
  hEntry + hIter + ArmStages (29-field fold by strong-induction-on-fuel); hDivCorr
  is the capstone re-home of that. **FINAL-ASSEMBLY item** (assembled once with
  hSBlock/hSForStart loop IHs + `term_sim` residual-unification, NOT per-field).

Neither is a falsity and neither is address-map/String math — they are the
recursor-threaded capstone. Do LAST, after the bounded fields relight.

## Relights

hCallClosure relights off the depth/budget induction + `env_define` composition
(landed). hDivCorr assembles with the final-assembly capstone. NO amendment.
