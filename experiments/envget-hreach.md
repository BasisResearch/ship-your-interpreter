# env_get `hreach` / `evalVarSim` — state assessment (2026-08-30)

## TL;DR

The mission's premised residual — "derive the `env_get` prologue segment + prove
the `AtHit → HitTailSt` repack" — is **ALREADY FULLY LANDED**, axiom-clean, in
`EnvGetSpec7/8/9.lean`. `hreach` (the abstract `Steps`-shaped hypothesis of
`env_get_found_spec`, EnvGetSpec6) is no longer the frontier: `env_get_found_uncond''`
(EnvGetSpec9) is the **complete, unconditional, immediate-frame** `env_get` FOUND
case, depending only on two honest caller/geometry facts (`FoundSt` + `FrameStackDisj`).

What actually still blocks `evalVarSim` is a **different and larger** piece than the
mission assumed: the var-arm dispatch → `env_get` call-site bridge, which needs
`ArmEntryK`/`EvalVarEntry` to expose the env-frame representation and the `x13`
env-pointer provenance (a statement change), PLUS — in the general case — the
**parent-chain walk** that `env_get_found_uncond''` does not cover.

## What was verified present + landed (not by me — pre-existing, uncommitted-import)

| Artifact | File | Statement | Axioms |
|----------|------|-----------|--------|
| `env_get_prologue` | EnvGetSpec7 | `PrologueSt @0x80002c10 → 0x80002c60` (17-instr spill prologue, 7 callee-saveds, `sp-=64`, loads `s4/s3/s5/s2/s1/s0`, `j` to do-while body) | clean |
| `env_get_found_uncond'` | EnvGetSpec8 | prologue ≫ from-c60 first body ≫ scan-to-HIT loop ≫ `AtHit→HitTailSt` repack ≫ verified HIT tail; modulo ONE residual `hScanReady` | clean |
| `hitAt_to_hitTail` | EnvGetSpec8 | the `AtHit → HitTailSt` field repack (the mission's item 2) | clean |
| `foundSt_scanReady` | EnvGetSpec9 | discharges `hScanReady` — the `FrameRepr`/`ScanNames`/per-slot geometry transport `m0 → m9` across the 7 spills (heap-vs-stack `AgreeP`) | clean |
| `env_get_found_uncond''` | EnvGetSpec9 | **FULL immediate-frame FOUND case**, no scan/reach hypothesis; needs only `FoundSt` + `FrameStackDisj` | clean |

`env_get_found_uncond''` at a glance (EnvGetSpec9:363): from `FoundSt` (the C-ABI
call-site facts at `0x80002c10`: `a0=env`, `a1=name`, `a2=out`, `ra=r`, `FrameRepr`,
`ScanNames`, a HIT witness `iw`/`nameStr`, and the out/spill/src geometry) plus
`FrameStackDisj` (the honest heap-vs-stack disjointness of the frame footprint),
the machine runs to `PC=r`, `a0=1`, `sp` popped, callee-saveds restored, and
`ValueRepr m' N φc out.toNat (f.vars[iHit].2)`.

`hreach` in `env_get_found_spec` (EnvGetSpec6) is thus **superseded** — that theorem's
abstract `∃ c1, Steps c c1 ∧ HitTailSt …` hypothesis is exactly what EnvGetSpec7/8/9
now build from honest facts. `env_get_found_spec` remains as the earlier scaffold.

## Wired into build + audit (this pass)

* `Vsa.lean`: added `import Vsa.Sim.EnvGetSpec9` (was committed but NOT imported —
  so `env_get_found_uncond''` was a dead artifact, invisible to the whole-project
  build). EnvGetSpec7/8 were already imported.
* `scripts/check_all.sh`: added `env_get_prologue`, `env_get_found_uncond'`,
  `foundSt_scanReady`, `env_get_found_uncond''` to the axiom audit.
* Measured elab: EnvGetSpec9 = 5.0s, EnvGetSpec8 = 22.7s, both axiom-clean
  `{propext, Classical.choice, Quot.sound}`.

## Why `evalVarSim` is STILL conditional (the real gap, precisely)

`evalVarSim` (EvalVarSim.lean:1571) is conditional on the `EvalVarEntry.env_get_found`
field (EvalVarSim.lean:1550): a `Triple` from `ArmEntryK … 0x80003434` (the var arm
dispatch entry) to `VarPostCall … 0x80003444` (the `env_get` link return). To
discharge it with `env_get_found_uncond''` one must bridge THREE things, and each is a
real, non-mechanical obstacle:

1. **Arg-setup segment** `0x80003434 → 0x80003440` (`ld a1,8(a2)`; `mv a0,a3`;
   `addi a2,sp,240`; `jal 0x80002c10`). Sites all exist (`site_80003434_var …
   site_80003440_var`). This part is a mechanical `#derive_case`/chain — TRACTABLE.

2. **Building `FoundSt` at the `env_get` entry from `ArmEntryK`.** BLOCKED by two
   statement-level gaps:
   * `env_get`'s env pointer is `a3` (x13), set by the dispatch prologue as the
     interpreter's current-environment pointer. `ArmEntryK` does NOT track x13, and
     `EvalVarEntry` carries no `FrameRepr` at the env pointer nor the `iw`/`nameStr`
     HIT witness. `FoundSt` needs `FrameRepr m0 N φf φc env.toNat f`, `ScanNames`,
     `iw < f.vars.length`, `f.vars[iw].1 = nameStr`, plus `pvVals` per-slot geometry.
     These come from `StoreRepr` (`.frames fa` gives `FrameRepr … (φf fa)`) ONLY after
     identifying `aEnv/a3 = φf fa` for the resolving frame `fa` and that `x` is an
     *immediate* binding of `s.frames[fa]`. `EvalVarEntry` exposes neither `fa` nor
     `x ∈ frame`. Supplying them requires a statement change to `EvalVarEntry`/`ArmEntryK`
     (add x13 + the env-frame `FrameRepr`/witness) — which the mission forbids.
   * `FrameStackDisj` (heap-vs-stack disjointness of the env-frame footprint) is a
     new honest geometry field EvalVarEntry does not carry.

3. **The parent-chain walk.** `Store.get? s a x = s.lookup s.frames.size a x`
   (Semantics.lean:110/137) walks the parent chain. `env_get_found_uncond''` covers
   ONLY the **immediate-frame** hit (its docstring is explicit). A general `.var`
   lookup that resolves in an ancestor frame needs `env_get`'s OUTER parent-walk loop
   (`env_get+0xc4` region), which is unproven. So even with (1)+(2), the wiring is
   only sound when the binding is in the immediate frame — the general case needs a
   whole additional loop spec.

## Recommendation / correct sequencing

The env_get machine side is DONE for the immediate frame. To close `evalVarSim`:

* **Statement change is unavoidable.** Widen `EvalVarEntry` (and the shared
  `ArmEntryK`) to expose: `x13 = φf fa` (env pointer), `fa`/immediate-frame witness
  from the `EvalE.var` derivation via a `StoreRepr → FrameRepr @ φf fa + x ∈ vars`
  bridge, and `FrameStackDisj`. Then `EvalVarEntry.env_get_found` is dischargeable by
  arg-setup-chain ≫ `env_get_found_uncond''` ≫ `VarPostCall` repack — for the
  immediate-frame case.
* **Parent-chain**: separately, prove `env_get`'s outer parent-walk loop and a
  `Store.lookup`-chain ↔ machine-walk correspondence to cover ancestor hits.

Both are Layer-4 representation-bridge tasks, not Shape-A/segment residuals. This is
why the mission's "prologue + repack" framing under-scoped the actual work: those two
were the LAST *machine* pieces (now landed); what remains is the *representation*
bridge (`StoreRepr`↔env-frame + chain walk) at the caller boundary.

## Mechanical / fan-out observations

* The `env_get` prologue segment (`env_get_prologue`) is the canonical Shape-A spill
  prologue; `env_define`/other arena-callee prologues share its exact recipe (7-spill
  `sd` tower + header loads + do-while `j`, `writeMap8`-disjoint survival). Reusable.
* `foundSt_scanReady`'s `*_outsideSpill`/`*_agreeP` transport family (frameRepr,
  scanNames, strcmpLoaded, cstring) is the generic "representation survives a spill
  window" kit — directly reusable for any callee that spills before using a
  caller-provided heap representation.
