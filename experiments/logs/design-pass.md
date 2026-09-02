# Global design pass — log (2026-09-02)

SCOPE: wrote ONLY `experiments/design/*` + this file. No `Vsa/` writes. 2 lean
processes used (fuzzer spot-checks, all in /tmp).

## Inputs read (in order)
1. `corpus/INDEX.md` + per-case files (hIAdd, err_80003b54, io_write, io_value_print,
   io_write_r, hStr, hFn, hSCont, hSBrk, hEpilogueSpill, hInitStore, hDivCorr,
   vparm_VP_NULL, hVar, hSVarInit, hSForStart) — machine-code shapes per cluster.
2. `entry-needs-audit.md` — N1-N5 entry-suppliable set (interface LANDED,
   INSERTION missing), X1-X8 Law-4 exclusions.
3. `bridge-algebra-review.md` — EntryBridge/repack; the flat-∧→structure mandate;
   the never-factored entry-transport leg.
4. `invariant-gen-plan.md` (3 rounds) + `invariants/*` — mining pipeline
   validated end-to-end (io_write WInv, falsity-#13 ladder, brk/cont relational).
5. `field-census.tsv` (3 FOUND / 54 NOT_FOUND), `assembly_skeleton.tsv`, the
   fleet obstruction files (B2/B5/B6/McallPop), `observations.md` waves 47a-i.

## Key synthesis
The 55 fields fail via 4 STATEMENT-shape defects (B5 ∀-m0 slot pin, B2 ∀-sp
sp_headroom, X1 mcall totality, B6 code-free SegEntry) — NOT semantic gaps. All
4 fixed by: carry the entry (`ground` projection) as a hypothesis field +
restate residuals as named-field structures. Genuine remaining content = X6
callee seams + X4/X7 recursor oracles. Wave 0 (restate + ground insertion +
IoGround generator) is the gate; it converts 24+ refuted fields to record-fills.

## Fuzz validation (all SURVIVED, hermetic --file/--prop/--struct)
StmtArmResid(conditioned), UnaryArmResid(deadPres), BinIntCellResid(entry-carry
= LeafResidAmended), WriteLoopInv, CallPrintResid, ErrArmResid, VParmArmResid
(conditioned), FnResid. Negative validation = the OLD shapes stay machine-false
in fleet/obstructions. Fuzzer caveat noted in MASTER: --struct checks per-field
inhabitability, not cross-field consistency (structural guard = entry-carry).

## Deliverables
- design/MASTER.md — sequencing (Waves 0-4), generator-vs-hand split, 31 bounded tasks.
- design/loop-arm.md (36), error-jal-seam.md (19), io-loop-fold.md (16),
  env-seam.md (13), singletons.md (13 grouped).

## Handoffs / open items for provers
- Wave 0b (ground INSERTION) is fleet-scale plumbing — audit §D map; do FIRST.
- io reachability-audit (T-IO-reachability-audit) should prune io_vfprintf_r/
  io_svfprintf_r/io_sfvwrite_r if off the 3 native-print arms (%lld LANDED).
- ES-var value-repr mining is the round-3 UNTESTED risk (value ↔ repr conjunct);
  pilot on hVar as the acceptance test before the harder crux relations.
- error-seam: do NOT collapse rows by shared slice — 19 distinct armPCs.
