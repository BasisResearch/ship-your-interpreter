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

## Item-1 SegPre composition — EXACT residual characterised (2026-08-28)

`SegFrameFacts.lean` (frame_ld/frame_sd/frame_ea + FrameBundle, all axiom-clean,
committed 2ee463c) is the reusable frame-window tool. Composing it into
`divDispatch_facts` (→ `SegPre divDispatch` → `divDispatchRow` live Triple) — the
residual `chain_facts h with "Vsa.Sim.Code.eval_expr_at_"` leaves on
`ChainFacts σ.mem σ.mem (divDispL v2 sret Wr Wl) lds divDispatch`:

- **10 `MemFacts`** (5 ld + 5 sd), each over a DEEPENING `stepMemM` chain: goal N's
  memory = `stepMemM (… (stepMemM σ.mem instr1) … ) instrN`. Loads are identity in
  stepMemM; stores are `applyW = writeMap8`. So D1's two loads (@v2+0x78,+0x88) are
  over σ.mem; D2's three loads (@+0x90,+0x98,+0xa0) are under D1's 2 stores
  (@+0xf0,+0x100) — DISJOINT (0x90+7 < 0xf0), peel via `writeLog_getElem_disjoint`
  (BlockAdapter.lean:51, widths∈{1,4,8} + per-store `k<a ∨ a+w≤k` by omega) or
  `getElem?_writeMap8_out`. Bounds via `frame_ea`(=v2+off)+omega from FrameBundle.
  eaddrM addresses (v2.toNat+): loads 0x78/0x88/0x90/0x98/0xa0, stores
  0xf0/0x100 (D1) + 0xf0/0xf8/0x100 (D2).
- **3 guards** (`all_goals try decide` does NOT close them — they thread stepGM over
  the symbolic L): 2 kind `bne` (x16=2 vs li x13=2; x10=2 vs x16=2 — concrete once
  stepGM reduced) + 1 divisor `beq` (x17=Wr vs x0 — needs `hWr : Wr ≠ 0`, the genuine
  semantic obligation).

**Recommended form (the exponentiating move): a `seg_frame_facts` TACTIC** that runs
after `chain_facts`, walks each residual `MemFacts`, `simp only [stepMemM]` to
collapse loads/peel stores (with `getElem?_writeMap8_out` + omega side-conditions),
then closes via `memFacts_ld_frame`/`memFacts_sd_frame` (bounds omega, pins from a
`pop`/read hypothesis), and reduces the guards via `simp [stepGM]; decide` (kind) /
the supplied `hWr` (divisor). Write once → discharges every arm's SegPre (shared
1088 frame) and any sp-relative window elsewhere. A hand `divDispatch_facts` (explicit
byte args, per-goal peel) is the fallback prototype to abstract the tactic FROM.

Then: `divDispatch_facts` → `SegPre divDispatch` (choose lds = the read words) →
`divDispatchRow` gives `Triple (frame-bundle entry) DivDispatchPost` = item 1 DONE →
compose `divValueTail` (items 2+3, landed) + `blockB_binary`/`blockD_v_rec` (shared)
= `evalDivSim`. Lift the shared skeleton → `binOpArmSim` combinator → mod/eq/ne as
~10-line instantiations (Level-2 exponentiation).

## Item-1 seam LANDED for `.div` (2026-08-28) — `Vsa/Sim/EvalDivArm.lean`

The whole `.div` item-1 span `0x8000351c → 0x8000381c` is now ONE proved bridge,
axiom-clean, in `check_all` (236/236, build 1080). Two theorems:

- **`divDispatchPost_of_chainEnd`** — reusable chain-end→dispatch glue. From a
  config at the `.div` arm entry `0x800037dc` with the `divDispL` pins
  (`x16=2/x10=2/x2=v2/x9=sret/x17=Wr/x19=Wl`, `mem=m0`) + `FrameBundle m0 v2` +
  `Wr≠0`, it builds `SegFramePre` (GHolds from the raw `regs.get?` pins via the
  anon constructor; `KeysOK` via `show KeysOK [16,10,2,9,17,19]; decide` — plain
  `decide` chokes on the open `keysG (divDispL …)`) and runs
  `divDispatchRow_frame` → `DivDispatchPost` at `0x8000381c`. The `.div` analogue
  of a caller invoking `eqDispatchRow_frame`.
- **`evalDivChain_dispatch`** — full-span bridge. Chains `evalDivChain_run` (entry
  linkage, `mem=σ.mem`) onto `divDispatchPost_of_chainEnd` (rewriting `FrameBundle`/
  `Eval_exprLoaded`/`DivDispatchPost` across `σ'.mem = σ.mem`), `Steps.trans`.
  Divisor `Wr = bytesVal MKind.ld [d0..d7]` (the `x17` pin the chain lands); caller
  supplies `Wr≠0` + `FrameBundle σ.mem v2`.

**Remaining for the live `evalDivSim`** (all Triple-composable on top of
`evalDivChain_dispatch`'s `DivDispatchPost`):
1. `blockB_binary` on the FRONT (`TwoSubReturn` → the `evalDivChain_run` entry
   battery) — shared, exists.
2. `divValueTail pre stage suf` (LANDED combinator) — the 3 concrete machine bridges.
3. `blockD_v_rec` epilogue → `EvalExitD` — shared, exists.

## Value-tail bridges: PRE landed, STAGE blocked on a weak `divdi3_post` (2026-08-28)

**Site battery** `Vsa/Sim/DivTailSites.lean` (generated via `scripts/gen_sites.py`
from `scripts/divtail_sites.tsv`, code-loaded `Eval_exprLoaded`, suffix `_ee`) —
the six `.div` value-tail sites `0x8000381c…0x80003830`: `jal __divdi3` (imm21
`000e88`→0x800046a4), `mv a1,a0`/`mv a0,s1` (0x00050593/0x00048513, decode lemmas
already present), `jal value_int` (imm21 `1fefe4`→0x8000280c), `ld s3,0x418(sp)`
(0x41813983), `j 0x800033ec` (0xbbdff06f). All six words already had decode-table
lemmas. Clean.

**`pre` LANDED** — `Vsa/Sim/EvalDivValueTail.lean` `divPreBridge`, axiom-clean, in
`check_all` (237/237, build 1082). `Triple (DivDispatchPost … ∧ tick<2 ∧ ∃x12 ∧
∃x13) (divdi3_pre Wl Wr 0x80003820 mA)` — the single `jal __divdi3 @0x8000381c`.
Caller obligations surfaced as hyps: the three `divdi3`/`umoddi3`/`udivdi3` loaded
preds on the post-dispatch memory `mA` (= `writeLog m0 (evalBlocks divDispatch …)`),
`Wr.toInt≠0`, `¬(Wl.toInt=-2^63 ∧ Wr.toInt=-1)` (the `__divdi3` overflow exclusion,
NOT just `Wr≠0` — `divdi3_pre` demands both). Pattern mirrors `blockC_mul` feeding
`muldi3_pre`; `obs_jal_pc/rd/other/minstret` off the site `ReadsLikePost`.

**STAGE + SUF BLOCKER — `divdi3_post` is the WEAK post, unusable in `divValueTail`.**
`divValueTail`'s `stage : Triple (divdi3_post Wl Wr rC mA) (int_pre g sret pay …)`
is **not provable** against the current `divdi3_post` (`DivSpec3.lean:934`):

    divdi3_post = GoodState ∧ mem=m0 ∧ PC=r ∧ ∃res, x10=res ∧ res.toInt = n.tdiv d

Compare `muldi3_post` (`Muldi3Spec.lean:921`, the STRONG post that `blockC_mul`
uses), which additionally carries **`sailOutput=o`**, **`x1=r`**, **`tick<2`**, and
the **ABI callee-saved frame** `∀R, NotWrittenM R → regs.get? R = g R`. `int_pre`
needs ALL of these: `x10:=sret` comes from `mv a0,s1` i.e. `x9=sret` must survive
`__divdi3` (callee-saved frame), `sailOutput=out0` (arithmetic emits nothing but the
weak post drops it), and `tick<2`. `divdi3_post` exposes none, so `stage` can't be
built. `res` is also `∃`-bound but that's fine: `res.toInt` pins `res` uniquely
(`BitVec.toInt` injective on 64), so a `pay` bridge hyp `pay.toInt = Wl.toInt.tdiv
Wr.toInt` recovers `res=pay` — the real gap is the missing frame/output/tick.

**NEXT (the true value-tail critical path): strengthen `divdi3_spec` to the
`muldi3_post` shape** — add `(g : Register→Option …)` frame ghost + `(o : Array
String)` output params to `divdi3_pre`/`divdi3_post`, and carry `sailOutput=o` +
`x1=r` + `tick<2` + `NotWrittenM` frame through the proof. This threads through the
udivdi3 core (`core_call_tail`/`udivdi3_spec` in `DivLoops`, whose posts ALSO drop
the frame+output today) → `divdi3_same_tail`/`divdi3_mixed_tail` → the sign-branch
prefix. Invasive (DivSpec3 ~1425 lines + DivLoops) but it is exactly what `__divdi3`
genuinely satisfies (callee-saved + no console I/O). Once `divdi3_post` is strong:
`stage` = 3 sites (`site_80003820/24/28_ee`) + `pay` toInt-injectivity bridge;
`suf` (`int_post`→`PreEpilogueVD`) is unblocked already (int_post is strong) but,
like `blockC_mul`'s tail, needs the arm's StackLayout/StoreRepr/slot bundle as hyps.

## STRONG `divdi3_spec` LANDED (2026-08-28) — the stage blocker is gone

Strengthened in place (via an additive `core_call_tail_f` so the moddi3-shared
`core_call_tail` is untouched). New signatures (`DivSpec3.lean`):
- `divdi3_pre (g) (n d r) (m0) (o)` / `divdi3_post (g) (n d r) (m0) (o)` — now carry
  the ghost `g` + output `o`; post adds `GoodState ∧ mem=m0 ∧ sailOutput=o ∧ PC=r ∧
  tick<2 ∧ (∀R, NotWrittenD R → regs=g R)` keeping `∃res, x10=res ∧ res.toInt=n.tdiv d`.
- `NotWrittenD R := NotWritten R ∧ x1≠R ∧ x5≠R` — the wrapper genuinely clobbers
  `x1`/`ra` (internal `jal`) and `x5`/`t0` (`mv t0,ra`), so they are EXCLUDED from the
  frame set rather than pinned to `r` (deliberate deviation from `muldi3_post`, which
  DOES pin `x1=r` — divdi3's mixed-sign path returns via `jr t0` leaving `x1` = the
  internal jal link). `x1`/`x5` are caller-saved and not consumed downstream.
- SAILOUTPUT threaded through the udivdi3 core: `Ust` gained a `sailOut` field,
  `udivdi3_pre/post` gained `(o)`, all ~28 `utr_*` + both loop bodies + 8 loop-invariant
  defs (`DivLoops.lean`) thread it; consumers `DivSpec2`(umoddi3)/`SnprintfSpec2/3`
  updated (pass `o := <st>.σ.sailOutput`, `sailOut := rfl`). moddi3/snprintf behavior
  unchanged, `moddi3_spec` still axiom-clean.
- Downstream rethreaded: `divCallSeam (g o …)`, `divValueTail (g gd … out0 outD)`,
  `divPreBridge` (concludes `divdi3_pre gd Wl Wr 0x80003820 mA outD`; added precond
  hyps `sailOutput=outD` + `∀R,NotWrittenD R→regs=gd R`, threaded through the entry jal).
Gate: `check_all` 237/237, build 1082, all of divdi3_spec/moddi3_spec/divValueTail/
divPreBridge axiom-clean `[propext, Classical.choice, Quot.sound]`.

### STAGE — the remaining ghost-frame subtlety (measure before building)
`divValueTail`'s `stage : Triple (divdi3_post gd Wl Wr rC mA outD) (int_pre g sret pay
rB mB out0)` fixes ONE ghost `g` shared with `value_int_spec` + `suf`'s `int_post`.
`int_pre`'s frame is `∀R, NotWrittenV R → regs=g R`, and **`NotWrittenV` includes
`x10`, `x1`, `x5`** (it only excludes `x11/x15/PC/nextPC/minstret*/mcycle/mtime/mip`).
The 3 stage steps WRITE `x10:=sret` and `x1:=0x8000382c`, and `x5`(t0) was already
clobbered by `__divdi3` (not in `NotWrittenD`, so `divdi3_post` doesn't expose it).
So a FIXED `g` shared across the whole tail cannot satisfy `int_pre`'s frame unless
`g` = the value_int-ENTRY register snapshot (which makes it `rfl`, exactly what
`blockC_mul` does inline with `g := τ19.regs.get?`). This is why `blockC_mul` uses NO
combinator: with a fixed shared ghost the `int_pre`/`int_post` frames are entry-snapshot
ghosts, not the arm-entry `gpre`. To build `stage`+`suf` through `divValueTail`, either
(a) set the tail's `g` := the value_int-entry snapshot and prove `suf` relates that back
to `gpre`/stack for the epilogue restore, or (b) reconsider whether `divValueTail` should
thread `int_pre`/`int_post` over an entry-snapshot ghost internally.

### VERDICT (2026-08-28, measured): `divValueTail` CANNOT host `stage`/`suf` — assemble inline like `blockC_mul`
The three-Triple split with a single FIXED shared `g` is not instantiable. `int_pre`'s
frame `∀R, NotWrittenV R → regs=g R` is provable only for `g` = the value_int-entry
register SNAPSHOT (makes it `rfl`), because the 3 stage steps write `x10:=sret`, `x1:=rB`
(both in NotWrittenV) and `__divdi3` clobbered `x5`/t0 to an unknown value (x5 ∈ NotWrittenV
but ∉ NotWrittenD, so `divdi3_post` never exposes it — though FYI `x5=r` IS actually true
at exit via `mv t0,ra`+`jr t0`, threaded through the tails, so it could be re-pinned if
wanted). That snapshot is a RUNTIME value of the input config, so it cannot be the
universally-quantified `Triple` parameter `g` that `divValueTail` shares across `stage`,
`value_int_spec`, and `suf`. This is exactly why `blockC_mul` (`rows/EvalMulRow.lean:446+`)
runs `jal __muldi3 ≫ muldi3_spec ≫ mv;mv;jal value_int ≫ value_int_spec ≫ ld;j` INLINE and
builds `int_pre` with `g := τ19.regs.get?` (the concrete entry snapshot), never a combinator.

**NEXT ACTION (revised): build `blockC_div` inline, cloning `blockC_mul`'s tail** —
`Triple (DivDispatchPost-ish) (PreEpilogueVD …)`, using: `divPreBridge` (or the inline jal)
→ the STRONG `divdi3_spec` (now landed, gives x10=quotient + sailOutput=o + NotWrittenD
frame; supply `g := <divdi3-entry snapshot>`, `o := sailOutput`, `Wr≠0`, no-overflow) →
`site_80003820/24/28_ee` (mv a1,a0; mv a0,s1; jal value_int) → `value_int_spec` with
`g := τ_vi.regs.get?` → `site_8000382c/30_ee` (ld s3; j 0x800033ec) → assemble
`PreEpilogueVD` from the StackLayout/StoreRepr bundle exactly as `blockC_mul` (lines
589-800). `binOpSem_div_int` gives `.int (wrap64 (Wl.tdiv Wr))`. `pay=res` pinned by
`res.toInt=Wl.toInt.tdiv Wr.toInt` + toInt-injectivity. ALL PIECES ARE NOW GREEN — this is
the ~350-line inline assembly, no remaining blocker. `divValueTail`/the value-tail
combinators stay as documentation of the two-seam shape, not the live vehicle.
