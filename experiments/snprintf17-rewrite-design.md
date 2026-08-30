# SnprintfSpec17 rewrite design — kill the per-site decision-tactic wall

Target: `Vsa/Sim/SnprintfSpec17.lean` (2239 lines, 3025 `by decide` + ~99 `omega`
occurrences ≈ 3194 decision-tactic calls, the #1 static offender in
`build-speed-exponentiation-plan.md`). Precedent: `rows/EvalGtRow` 226→68s by the
same "omega/decide paid ONCE, applied by name" rewrite (`SpillSafe.lean` /
`OmegaHelpers.lean`).

This doc is the mechanical rewrite spec for a follow-up implementation agent.
Everything below was verified by reading current code, NOT by compiling (a serial
profiler owns the toolchain).

Key structural fact learned by reading: this file is **not** a spill-slot cohort
file. Its decision tax is overwhelmingly a DIFFERENT shape — the **register-frame
disequality ladder** `obs_*_other hobs Register.xN (by decide) ×7-8 …` — which the
`Eval*` cohort helpers (`SpillSafe`/`OmegaHelpers`) do NOT cover. So the new helper
family is a distinct file: `Vsa/Sim/SnprintfSafe.lean`.

---

## 1. Shape census (every recurring tactic-block pattern)

Measured counts (grep over the file). The `by decide` total is 3025; the two
register-frame ladders alone account for ~2436 (80%).

| # | shape | callsite pattern | decides | approx count | file:line examples |
|---|-------|------------------|--------:|-------------:|--------------------|
| **S1** | **ALU reg-frame ladder** | `obs_alu_other hobsN Register.xM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hxM_k` | **8/site** | **175 sites ≈ 1400 decides** | `:220`, `:222`, `:300` |
| **S2** | **store reg-frame ladder** | `obs_store_other_sn4 Register.xM hobsN (by decide) ×7 hxM_k` | 7/site | 60 sites ≈ 420 | `:339`, `:341`, `:357` |
| **S3** | **branch-nottaken reg-frame** | `obs_branch_nottaken_other hobsN Register.xM (by decide) ×7 hxM_k` | 7/site | 55 sites ≈ 385 | (branch blocks, e.g. `:373` region) |
| **S4** | **branch-taken reg-frame** | `obs_branch_taken_other hobsN Register.xM (by decide) ×7 hxM_k` | 7/site | 33 sites ≈ 231 | (taken-branch blocks) |
| **S5** | **jal reg-frame** | `obs_jal_other hobsN Register.xM (by decide) ×7 hxM_k` | 7/site | 13 sites ≈ 91 | (jal block near `0x80008684`) |
| **S6** | **decode-word bit-eq** | `(by apply BitVec.eq_of_toNat_eq; decide)` ×2 per `stepObs_*` | 1/arg | 66 args | `:183`, `:321` |
| **S7** | **GoodState-thru-prelude** | `(by rw [get?_afterPrelude σN _ (by decide)]; exact hGN.misa)` ×3 (misa/cur_privilege/mseccfg) per `stepObs` | 1 inner + rewrite | 90 blocks | `:185-187`, `:323-325` |
| **S8** | **nextPC read-through** | `(by rw [get?_afterNextPC σN pc _ (by decide) (by decide)]; exact hxK)` | 2/site | 6 sites ≈ 12 | `:172`, `:309`, `:378` |
| **S9** | **store/load addr-safety** | `(by rw [hoffK]; omega)` ×4 (or ×3+`Or.inr`) in `exec_sd_val`/`exec_ld` | 4/site | 55 blocks | `:206-207`, `:330`, `:463-464` |
| **S10** | **`…Loaded`/SlotHolds survival** | `svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffK]; omega) hloadN` ; `slotHolds_writeMap8 … (Or.inl (by rw [hoffJ, hoffK]; omega)) hstrN` | 1-2/site | ~28 blocks | `:366`, `:368`, `:372` |
| **S11** | **offset normal-form** | `addoff_toNat_sn5 vsp (0xKKK#12) N (by omega) (by decide) hnw` | 1 omega + 1 decide | 9 sites | `:163-167`, `:773-783` |
| **S12** | **frame-bound scaffolding** | `have hnw : vsp.toNat + 348 < 2^64 := by omega` ; `have hsplo : 0x8000b000 ≤ vsp.toNat := by omega` | 1/have | ~6 | `:160`, `:768-770` |
| **S13** | **local slot-survival lemma** | `slotHolds_insert … (Or.inr (by omega))` ×4 nested (the `slotHolds_writeMap4_i2` helper body) | 4 | 1 (one-time, `:99-102`) | `:99` |

S1-S5 (register-frame ladders) = ~2527 decides ≈ **80% of the file's decision tax**
and are the primary target. S6-S8 are cheap ground `decide`s but numerous. S9-S11
are the omega tax (~99 omega).

---

## 2. Per-shape resolution — existing lemma vs new helper

### Existing coverage (REUSE, do not reinvent)
- **S11 `addoff_toNat_sn5`** is already the "offset paid once" lemma (lives in
  `SnprintfSpec5.lean:61`, `n ≤ 348` frame). Already collapsed; leave as-is. It is
  the Snprintf analogue of `SpillSafe`'s `spill_load_safe*` offset form.
- **S9/S10** are already routed through the reusable `svfprintfSlice_writeMap8_sn5`,
  `flushPins_writeMap8_fl`, `slotHolds_writeMap8` survival lemmas — but each still
  pays a fresh `(by rw [hoffK]; omega)` for the disjointness side-condition. See NEW
  `snoff_disjoint` below.
- **`SpillSafe` / `OmegaHelpers` / `GeomFacts` / `FrameCalc` / `SegFrameFacts` do
  NOT apply here** — those cover the `Eval*` spill-slot shapes (`sp.toNat - K`,
  code/value-region disjointness against `SL.lo`). SnprintfSpec17 uses
  `vsp.toNat + N` positive offsets with a fixed `[0x8000b000, +348)` frame window
  and htif at `0x8001ad00`. Different arithmetic ⇒ a distinct helper file.

### NEW helpers — all in `Vsa/Sim/SnprintfSafe.lean` (import `Vsa.Sim.SnprintfSpec4`
for the `obs_*_other` bases + `Muldi3Spec` for `obs_alu_other`; verify the minimal
import that brings `ReadsLikePost`, `sigmaPost_*`, `svfprintfSlice_writeMap8_sn5`,
`addoff_toNat_sn5` into scope).

#### H1 — S1: batched ALU reg-frame (`obs_alu_other` ×8 decide → 0 decide)
The 8 `(by decide)` args each prove one ground register disequality that depends
ONLY on the two concrete register literals `rd` (from `hobs`'s `sigmaPost_alu σ pc vm
rd v`) and `R`. Fold the whole conjunction into ONE `decide` inside a wrapper. Both
registers are concrete at every callsite, so the internal `decide` is ground.

```lean
/-- ALU reg-frame preservation with the 8-way register-disequality bundle proved by
ONE `decide` (both `rd` and `R` are concrete literals at every callsite). Conclusion
matches `obs_alu_other`'s verbatim; callsite drops all 8 `(by decide)` args. -/
theorem obs_alu_other' {σ' σ : MState} {pc vm : BitVec 64} {rd : Register}
    {v : RegisterType rd} (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (rd == R) = false ∧
            (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_alu_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2.1 hdis.2.2.2.2.2.2.2 hσ
```
Callsite becomes `obs_alu_other' hobs1 Register.x2 (by decide) hx2` — **8 decides → 1
per site** (175 sites: 1400 → 175 decides). The single `decide` on the ∧-chain is one
kernel `Bool`-and reduction over `Register.decEq`, strictly cheaper than 8 separate
`decide` elaborations (8× the `whnf`/instance setup).

> NOTE: prefer the ∧-bundle form over a `(by decide)`-per-conjunct so there is exactly
> ONE tactic block per site. If the implementer would rather not touch the wrapped
> lemma, an equivalent zero-new-lemma option is to replace the eight
> `(by decide) (by decide) …` with one `(by decide) (by decide) …` collapsed via
> `⟨by decide, …⟩`-free `And.intro` — but the wrapper is cleaner and the recommended
> path.

#### H2 — S2: batched store reg-frame (7 decide → 1)
```lean
theorem obs_store_other_sn4' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_store_other_sn4 R hobs hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ
```
Callsite: `obs_store_other_sn4' Register.x2 hobs3 (by decide) hx2_2`. 60 sites: 420 →
60. (Note the arg order matches the base: `R` before `hobs`.)

#### H3/H4/H5 — S3/S4/S5: identical ∧-bundle wrappers for
`obs_branch_nottaken_other'`, `obs_branch_taken_other'`, `obs_jal_other'` (all take
the SAME 7-way disequality bundle as store; only the `hobs` sigmaPost type differs).
Copy H2's body, swap the base lemma name and the `sigmaPost_*` in `hobs`'s type. 101
sites total: ~707 → 101.

**S1-S5 net: ~2527 decides → ~336 (one per site).** This is the whole win.

#### H6 — S9/S10: `snoff_disjoint` (the `(by rw [hoffK]; omega)` store-safety fold)
Every S9/S10 side-condition, after `rw [hoffK]`, is a ground linear fact about
`vsp.toNat + N` within the frame `[0x8000b000, +348)` vs htif `0x8001ad00`. Currently
each of the 4 `exec_sd_val` args (`hlo`/`hhi`/`hhtif`/`halign`) is a separate
`(by rw [hoff16]; omega)`. Provide ONE lemma stating the 4-way conjunction over a
concrete offset `N` (`N % 8 = 0`), analogous to `SpillSafe.spill_load_safe8` but for
the `vsp + N` frame:

```lean
/-- The four store/load preconditions at frame offset `vsp.toNat + N`, derived once
from the fixed [0x8000b000, +348) window + htif@0x8001ad00. `hoff : addr = vsp+N`. -/
theorem sn_store_safe (vsp addr : BitVec 64) (N : Nat)
    (hoff : addr.toNat = vsp.toNat + N)
    (hsplo : tohostAddr + 16 + 64 ≤ vsp.toNat) (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspalign : vsp.toNat % 8 = 0)
    (hN : N + 8 ≤ 348) (hN8 : N % 8 = 0) :
    0x80000000 ≤ addr.toNat ∧ addr.toNat + 8 ≤ 0x100000000 ∧
    (addr.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr.toNat) ∧
    addr.toNat % 8 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  rw [hoff]; refine ⟨by omega, by omega, Or.inl (by omega), by omega⟩
```
Plus a `sn_disjoint_slot` sibling for the `slotHolds_writeMap8 … (Or.inl/Or.inr …)`
disjointness (S10): conclusion `vsp.toNat + J + 8 ≤ vsp.toNat + K ∨ …` proved once
from `J + 8 ≤ K` (`by decide` on the two ground offsets). Callsites: the 4 omega args
→ `(sn_store_safe vsp _ N hoffK hsplo hsphi hspalign (by decide) (by decide)).1`
etc., pushing the omega into the lemma olean. ~55 store blocks × 4 omega ≈ 220 omega →
~55 lemma applications (the ground `(by decide)` args are ms-cheap kernel `Nat.ble`).

> If threading the 4-way conjunction is awkward at the varied callsites (some take
> `Or.inl`, some `Or.inr` for htif), split into `sn_addr_lo`/`sn_addr_hi`/
> `sn_addr_htif_below`/`sn_addr_htif_above`/`sn_addr_align` single-conclusion lemmas
> matching each arg slot verbatim — same "omega once" effect, more surgical sed.

#### S6/S7/S8 — leave, or lightly batch (LOW priority)
- **S6** `(by apply BitVec.eq_of_toNat_eq; decide)`: ground 32-bit word equality, ~ms
  each; 66 of them. Optional: precompute each decode word as a `def … := rfl` bit-eq
  lemma and `exact` it, but the marginal win is small. **Defer** unless the profiler
  flags decode as hot.
- **S7** `(by rw [get?_afterPrelude σN _ (by decide)]; exact hGN.misa)`: the inner
  `(by decide)` is a single ground `Register` disequality. Batchable into a
  `goodState_thru_prelude` helper that returns the misa/cur_privilege/mseccfg triple
  in one shot (`⟨…, …, …⟩`), cutting 90 blocks × (1 decide + 1 rw) to 30 calls.
  MEDIUM priority — do after S1-S5 if profiler still shows headroom.
- **S8** `get?_afterNextPC` (2 decide/site, 6 sites): trivial, leave.

---

## 3. Memoised normal-form opportunities

1. **`writeMap8` towers (S10, 32 occurrences).** The same
   `writeMap8 c.σ.mem (vsp + sign_extend (0x010#12)).toNat (sdData_val (...))` term is
   re-spelled at the `stepObs_store` call, the `hmem'` `have`, the `hloadN`/`hfpN`/
   `hstrN` survivals, AND the postcondition. Define ONE
   `def sn17_mem_total (vsp : BitVec 64) (vsel vtot : BitVec 64) (m : …) : …` (the
   canonical post-memory after the `sd a5,16(sp)`) marked reducible, so the survival
   lemmas and postcondition consume it by `rfl`/`exact` instead of re-`whnf`'ing the
   `sdData_val (sign_extend (extractLsb + extractLsb))` tower. This mirrors B's
   `eqDispatch_mem_tower` one-line-`rfl` win (`fast-reflection-rules` rule 5:
   canonical write-log NF so seams compose by `rfl`). Apply to each of the ~4 distinct
   store windows in the file (offset 16, offset 240/0xf0, iov base, iov+8).
2. **Offset equalities (S11) are already memoised** via `addoff_toNat_sn5` producing
   `hoff16`/`hoff8`/`hoff224`/`hoff240`/`hoffiov0` — good. Ensure downstream `rw
   [hoffK]` sites (S9/S10) reference these `have`s rather than re-deriving; they
   already do. No change.
3. **`sdData_val (...)` payload term.** The nested `extractLsb'`/`append` 8-byte
   little-endian tower (`:177-181`) recurs identically in the `exec_ld`/`stepObs_alu`
   witness. Hoist to a `let`/`def sdBytesLE (v : BitVec 64)` consumed by `rfl` so the
   elaborator does not re-normalize the 8-append tower per occurrence.

---

## 4. Mechanical rewrite recipe (ordered)

Do S1-S5 first (80% of the win, purely mechanical, near-leaf file — nothing imports
SnprintfSpec17, so iterate freely).

**Step 0.** Create `Vsa/Sim/SnprintfSafe.lean` with H1-H6 (statements above). Add
`import Vsa.Sim.SnprintfSafe` to SnprintfSpec17 (and later 49/5). Build it ALONE
first, confirm axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only), no
`decide` >2s (fast-reflection rule 7).

**Step 1 (S1, sed-able).** Regex replace, per line:
```
obs_alu_other (\w+) (Register\.\w+) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) (\w+)
→  obs_alu_other' \1 \2 (by decide) \3
```
(175 lines, each a single self-contained line — safe for `sed`/`perl -pi`.)

**Step 2 (S2).** 
```
obs_store_other_sn4 (Register\.\w+) (\w+) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) \(by decide\) (\w+)
→  obs_store_other_sn4' \1 \2 (by decide) \3
```
**Steps 3-5 (S3/S4/S5).** Same regex with `obs_branch_nottaken_other` /
`obs_branch_taken_other` / `obs_jal_other` → the primed name, 7 `(by decide)` → 1.
(Confirm arg order per base: alu is `hobs R …`; store is `R hobs …`; branches are
`hobs R …`; jal — check `DivSites2.lean:100` before writing the regex.)

**Step 6 (S9/S10, HAND).** These have varied `Or.inl`/`Or.inr` shapes and per-site
offsets; NOT a blind sed. Replace the 4 `(by rw [hoffK]; omega)` in each `exec_sd_val`
with the `sn_store_safe` projections (or the split single-conclusion siblings). ~55
blocks, ~1-2 min each by hand or a careful script keyed on the `hoffK` name.

**Step 7 (memoisation).** Introduce `sn17_mem_total` / `sdBytesLE` defs (Section 3),
replace the inline towers. HAND, ~4 store windows.

**Step 8 (optional S7).** `goodState_thru_prelude` batching if profiler shows headroom.

After each step: re-grep the decide/omega count as a cheap regression witness; the
implementer cannot compile (profiler owns toolchain) so rely on axiom-clean + count
drop + a single deferred build by the profiler owner.

---

## 5. Estimated decision-call reduction

| shape | before | after | mechanism |
|-------|-------:|------:|-----------|
| S1 ALU ladder | 1400 | 175 | H1 ∧-bundle (1 decide/site) |
| S2 store ladder | 420 | 60 | H2 |
| S3/S4/S5 branch/jal | 707 | 101 | H3/H4/H5 |
| S9 store-safety omega | ~220 | ~55 | H6 `sn_store_safe` |
| S10 survival omega | ~40 | ~28 | H6 sibling (partial) |
| S6/S7/S8 (deferred) | ~228 | ~228 | unchanged (cheap ground) |
| **decision total** | **~3194** | **~750** | **~76% cut** |

Aggressive S7 batching would drop another ~120. On the measured 226→68s (~3×) ratio
for a comparable decide/omega cut, expect SnprintfSpec17 to fall roughly
**proportional to the 76% decision cut** — a several-fold single-file wall drop. The
same helpers (H1/H2, and the `obs_alu_other'`/`obs_store_other_sn4'` pair especially)
transfer directly to Spec49 and Spec5 (Section 6), so the file cost is amortised.

---

## 6. Cohort commonality (Spec49, Spec5) — maximise shared helpers

Skim of the two sibling files (grep counts):

| shape | Spec17 | Spec49 | Spec5 | shared helper |
|-------|-------:|-------:|------:|---------------|
| S1 `obs_alu_other` (×8) | 175 | 170 | 100 | **H1 covers all three** |
| S2 `obs_store_other` (×7) | 60 | 52 | 57 | **H2 covers all three** |
| S3/4 branch | 88 | 0 | 0 | H3/H4 Spec17-only |
| S9/10 `rw[hoff];omega` | 55 | 50 | 70 | H6 covers all three |
| S11 `addoff_toNat_sn5` | 9 | 7 | 61 | already shared (defined in Spec5) |
| `by decide` total | 3025 | 2526 | 1615 | — |

**Commonality ≈ 85-90%** on the load-bearing shapes: `obs_alu_other'` (H1) +
`obs_store_other_sn4'` (H2) + `sn_store_safe` (H6) alone cover the dominant tax in all
three files. Spec49 has NO branch shapes (pure alu/store straight-line); Spec5 leans
even harder on `addoff_toNat_sn5` (61×, already collapsed). ⇒ `SnprintfSafe.lean`
should be authored as the shared cohort helper file from the start, and the same
Step-1/Step-2/Step-6 sed passes rerun on Spec49 and Spec5. Fan out the three files as
disjoint near-leaves (Wave-D protocol) once H1/H2/H6 are green.

---

## 7. Risks (fast-reflection-rules compliance)

- **∧-bundle `decide` must stay ground and small.** H1's single `decide` reduces a
  7-8-way `Bool`-and of `Register.decEq` on two concrete literals — a bounded kernel
  reduction, NO `whnf` on `writeLog`/`ExtHashMap` (rule 1), NO WF recursion (rule 2).
  Cheaper than the 8 it replaces. **Low risk** — but VERIFY the wrapped lemma's
  `decide` timing on one retrofit site before fanning out (rule 7: >2s leaf decide =
  revert). If `Register.decEq` is unexpectedly slow, fall back to keeping the 7-8
  conjuncts but as ONE `by decide` proving the ∧ (still 1 elaboration vs 8).
- **Do NOT restate the disequality bundle as a searchy typeclass / instance.** Keep it
  a plain `∧` argument closed by one `decide` (rule 6: no instance backtracking).
- **`sn17_mem_total`/`sdBytesLE` defs must be `rfl`-reducible, not `whnf`-triggering.**
  If marking them reducible forces the elaborator to unfold the `writeMap8`/`ExtHashMap`
  tower at every seam, that regresses (rule 5 warns exactly this — the ExtHashMap is
  non-reducible). SAFE pattern: define the def, prove ONE `sn17_mem_total_eq : … = …`
  lemma, and `rw`/`exact` THAT lemma downstream — never let a raw `rfl` drive
  reduction through the hashmap. If a memoisation attempt raises per-file elab >10%,
  revert that def and keep the inline term (the S1-S5 win stands independently).
- **H6 `sn_store_safe` htif disjunct.** Confirm every S9 callsite takes the SAME
  disjunct side after `rw`; the file mixes `Or.inl` (`:372`, below-htif) and `Or.inr`
  (`:206`, above-htif) at DIFFERENT offsets. The 4-way-conjunction form bakes in one
  side — if offsets straddle htif, use the split single-conclusion siblings so each
  arg slot matches verbatim. **Medium risk**: get the disjunct direction right per
  offset or the `exact` fails to typecheck.
- **Import weight.** `SnprintfSafe.lean` imports must be MINIMAL (just what brings
  `obs_*_other` bases + `ReadsLikePost`/`sigmaPost_*` + `addoff_toNat_sn5` into scope).
  It sits below Spec17/49/5 (3 importers) — keep it light so it is not itself a hot
  base per Axis-2. Do NOT pull `SnprintfSpec4`'s heavy body if only the `obs_*` sigs
  are needed; relocate the `obs_*_other` bases into `SnprintfSafe` if that is cleaner
  than importing Spec4/Muldi3.
