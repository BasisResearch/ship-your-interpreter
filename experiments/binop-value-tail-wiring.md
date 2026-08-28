# Binary-op eval-case wiring — seam layer landed, concrete bridges remain

Goal: turn `divDispatchRow`/`modDispatchRow`/`eqDispatchRow`/`neDispatchRow` (all
landed, axiom-clean, carrying caller-linkage as a hypothesis) into UNCONDITIONAL
eval cases, mirroring the hand-built `evalGeSim` (`Vsa/Sim/rows/EvalGeRow.lean`,
855 lines: `blockB_binary ≫ blockC_ge ≫ blockD_v_rec`).

## Landed this session (2026-08-28) — the reusable seam layer

- **`Vsa/Sim/BoxSuffixSeams.lean`** — item-3 box suffixes as named `callSeg` bricks:
  - `valueIntCallSeam` (div/mod): `Triple P (int_pre) ≫ value_int_spec ≫ Triple (int_post) Q`.
  - `valueBoolCallSeam` (eq/ne): threads `value_bool_spec_full` over named
    `boxBool_pre`/`boxBool_post` (def-equal to the spec's inline predicates) +
    `value_bool_box` repackaging.
- **`Vsa/Sim/BinOpValueTails.lean`** — the full TWO-call value tail per arm, both
  real callees threaded:
  - `divValueTail` = `divCallSeam` (`divdi3_spec`) ∘ `valueIntCallSeam` (`value_int_spec`).
  - `modValueTail` = `modCallSeam` (`moddi3_spec`) ∘ `valueIntCallSeam`.
  - `eqNeValueTail` = `valueEqualCallSeam` (`value_equal_spec_full`) ∘ `valueBoolCallSeam`
    (`value_bool_spec_full`); shared by eq/ne.

All axiom-clean, pure `callSeg` plumbing (constant elab), wired into `Vsa.lean` +
`check_all.sh`. Build 854 jobs green. Also backfilled the mod/eqne dispatch rows +
`binOpSem_*` bridges into `check_all.sh` (they had landed but weren't listed).

## What each value tail leaves as residual — the 3 concrete machine bridges

Each `*ValueTail` reduces an arm's item-2+item-3 to three named `Triple`
hypotheses. These are the genuine remaining machine work (block-reflection / site
lemmas), each buildable in isolation:

1. **`pre`** — dispatch row + `jal <callee>` link → callee entry predicate.
   - div/mod: `Triple P (divdi3_pre Wl Wr rC mA)` — compose `divDispatchRow`
     (`DivDispatchPost`, PC=0x8000381c, x10=Wl, x11=Wr) with the `jal __divdi3`
     step landing PC=0x800046a4, x1=return, mem=mA. `SegPre divDispatch` itself is
     fed by item 1 (below).
   - eq/ne: `Triple P (ve_pre … ∧ x2=sp)` — `eqDispatchRow`/`neDispatchRow`
     (`EqDispatchPost`, PC=0x8000371c/…376c, x10=bufa, x11=bufb) + `jal value_equal`.
2. **`stage`** — callee exit → box entry, across the `mv` arg shuffles + `jal <box>`.
   - div/mod: `Triple (divdi3_post …) (int_pre g sret pay rB mB out0)`. The
     `mv a1,a0` (pay←quotient) + reload a0←sret + `jal value_int` @0x80003828.
     `pay = Wl.tdiv Wr` (`binOpSem_div_int` gives `wrap64 (a.tdiv b)`).
   - eq/ne: `Triple (ve_str_post …) (boxBool_pre g sret bw rB mB out0)`. For **ne**
     this is where the extra `seqz a1,a1` negates before `jal value_bool`.
3. **`suf`** — box exit → arm post `Q` = `PreEpilogueVD` (fed to `blockD_v_rec`).
   - div/mod: `Triple (int_post …) Q`; eq/ne: `Triple (boxBool_post …) Q`.

## Item 1 — entry linkage (the biggest remaining hole, shared shape)

Bridge `TwoSubReturn` (post-arg-eval arm state, PC=0x8000351c, from
`blockB_binary`) → `SegPre <arm>Dispatch` (dispatch row entry). This is the
kind-check prefix + the `jr` jump-table @0x80003558 dispatch that routes token→arm
PC (div→0x800037dc, mod→0x80003784, eq→0x800036e4, ne→0x80003734). Mirrors the
first ~200 lines of `blockC_ge` (the `evalGeChain_run` prefix + `SegPre` frame
windows). The `#derive_case` seg can only TERMINATE at the `jr` (data-dependent
target), so the prefix 0x8000351c→0x80003558 is a separate seg and the `jr` routing
is a hand step — see `CmpDispatchSeg.lean` header.

Note: **ge migration onto `cmpDispatchRow` stays blocked** on the slt/subw
register-fold timeout (cmpDispatch block K5 has slt/slt/subw; the register-outcome
`rfl` fold times out). div/mod/eq/ne are NOT blocked by this — their dispatch rows
have no slt/subw (div/mod extract x10=Wl/x11=Wr via the `+0` bridge; eq/ne extract
bufa/bufb via the `addi +imm` bridge), which is why they are the tractable frontier.

## Assembly recipe for one unconditional eval case (e.g. `evalDivSim`)

```
blockB_binary  (entry linkage → TwoSubReturn)         -- item 1 (exists, shared)
  ≫ [item-1 bridge: TwoSubReturn → SegPre divDispatch]  -- NEW machine bridge
  ≫ divValueTail pre stage suf                         -- item 2+3 (LANDED as combinator)
  ≫ blockD_v_rec (epilogue → EvalExitD)                -- exists, shared
```
with `pre`/`stage`/`suf` the three concrete bridges above. `binOpSem_div_int`
supplies the spec-side value `.int (wrap64 (a.tdiv b))`.
```
```
