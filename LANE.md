# Lane E5: `exec_stmt`'s statement arms

Branch `lane-e5` (from `wave4-base`). Design: `VsaIris/INTERP_DESIGN.md` §4, §6,
§8 (row "exec"); statement change in §10 "STATEMENT CHANGES (E5)".
Family: expr, varInit, varNull, block, if (3 outcomes), return (2), break,
continue, and the while/for arms' non-loop parts. Rows go in
`scripts/iris_arms/arms.d/e5-exec.tsv`.

## STATEMENT CHANGE: the exec motive is stated at the dispatch point

gcc compiled `if`'s `return exec_stmt(in, branch, env, ret)` as an in-frame
tail call: `0x8000422c ld s0,16(s0); j 0x80004014` (then) and
`0x800042cc ld s0,24(s0); bnez s0,0x80004014` (else), after reloading `a6`/`a4`.
The branch never runs from `exec_stmt`'s entry, so the entry-shaped
`execSpecT_body` of the branch cannot discharge it. Every exec arm is therefore
proved at the DISPATCH point `0x80004014` (`VsaIris/Interp/SpecExecDisp.lean`):

- `execDispT_body … D` (total, derivation-indexed) — the recursor motive of
  `ExecSCost` for lane A;
- `execDispP_body Core …` (partial) and its Löb hypothesis `execDispsP`;
- `execSpecT_of_disp`, `execSpecP_of_disp`, `execSpecsP_of_disps`
  (`ExecDisp.lean`) recover the entry specs (prologue run `ExecProl_run`,
  `wp_execProl`) for every `jal exec_stmt` caller (block/while/for bodies,
  closure bodies, `interp_run`).

State at the dispatch point: `ms 0x80004014 R (InExt (s-176,176)) Mt` with
`DispRegs` (`sp = s-176`, `s0 = stmt`, `s1 = in`, `s2 = ret`, `s3 = env`,
`a6 = 8`, `a4 = 0x80019fb8`) and `ExecSaved Mt s ret v8 v9 v18 v19` (the
spills); the continuation `execDispK` gets `ExecRet` (sp, s0-s3 restored,
s4-s11 kept, status in `a0`) at the return address.

**For E6 / A:** the while arm enters its loop at `0x8000403c` and the for arm at
`0x8000426c`, both in the frame at the dispatch-point state above; E5 proves
the dispatch → loop-head part and the exits. The loop lemmas' shape is
coordinated below (in flight).

## Done
- `SpecExecDisp.lean` (statement), `ExecDisp.lean` (prologue and the entry
  specs from the dispatch-point ones). Axioms ⊆ {propext, Classical.choice, Quot.sound}.

## In flight
- Arm families (brk/cont first, then ret/expr/var/if/block).

## Holes
None added.
