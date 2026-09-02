# Cure suite — singletons (hFn, hEpilogueSpill, hInitStore, hVar, hAssign)

> **PRE-WAVE SEALED BANNER.** Sealed 2026-09-02, tree @c9e1453 (CEGIS production
> sweep: io/str/singleton/crux). Sealed = production input AND uncontaminated
> prospective validation. Written BEFORE the proving wave; reseal a new dated
> block rather than editing. Nothing here enters a proof (Law 4 / design-time).

Fields (`Vsa/Sim/TermAssembly.lean`):
- `hFn` (:193) `∀ …, FnResid …` — closure-alloc arm + native-store repr (entry `0x800033c4`)
- `hEpilogueSpill` (:290) `∀ g N A SL …, EpilogueSpill …` — interp_run exit-0 restore (entry `0x80004514`)
- `hInitStore` (:286) `∀ p, InterpInitStoreRepr L p` — interp_init decode (entry `0x80004308`)
- `hVar` (:103) `∀ st x v, VarLeafResid st x v` — env_get caller-linkage (entry `0x80003434`)
- `hAssign` (:108) `∀ …, AssignResid …` — assign arm oracle (entry `0x8000347c`)

## 1. Obstruction — SURVIVED (no refutation exists)

- `statement_fuzz` (mining, `BATCH-REPORT.md`): all 5 **candidate-mined+SURVIVED**;
  relational kind-seam aligned (hFn/hVar/hInitStore/hEpilogueSpill on the stmt/expr
  seam, all agreeing kinds; hAssign 8-kind full agreement).
- `cegis_cure.py --file invariants/<field>.lean --prop mined`:
  **Detected defects: none — Survivors: 0** for every one of the five.
- No obstruction file exists for any singleton in `fleet/obstructions/`.

**⇒ PROVE-DIRECTLY** (SURVIVED). Each is TRUE as stated; residual is bounded
span/bridge content, no amendment.

## 2. cegis_cure — N/A (no false field to cure)

Every field returned `Detected defects: none, Survivors: 0`. No ranked suite: the
address-map / entry / quantifier cure vocabulary has no defect to repair. The gaps
are missing *bounded suppliers*, not wrong statements.

## 3. Classification — all SINGLE-CURE / PROVE-DIRECTLY (bounded segs)

| field | class | missing supplier (bounded) | landed assets |
|---|---|---|---|
| hVar | **SINGLE-CURE** | `EvalVarCallBridge` (env_get caller-linkage) | `env_get_found_uncond''` LANDED (`EnvGetSpec6`) — the whole HIT tail is proved; residual = the ONE call-linkage bridge |
| hAssign | **SINGLE-CURE** | `AssignArmSpec` arm oracle (row now / seg later) | assign arm decode + block-reflection precedent |
| hFn | **SINGLE-CURE** | `NativeStoreRepr` readback | malloc / fwrite / exit callees LANDED; content = closure-alloc arm + `callSeg` on malloc |
| hInitStore | **SINGLE-CURE** | `InterpInitStoreRepr` decode (X8) | interp_init PC span decoded in its doc; bounded `block_facts` |
| hEpilogueSpill | **SINGLE-CURE** | `EpilogueSpill` restore ChainFacts (`s5=0` latch) | epilogue restore block; bounded `block_facts` per `design/singletons.md §S-entry` |

None of these is HARD: no recursion, no math gap, no ∀-ghost. Each is a single
bounded machine span or one call-splice bridge over an already-landed callee. They
were SURVIVED and defect-free under `cegis_cure` because the statement shape is
correct (named-field `*Resid`, `EvalEntry.ground` carry now present, 47i). This is
the "bounded seg / single bridge" pit-of-success class — the writer transcribes a
`#derive_case` seg or one `callSeg`, not a cure.

**Ordering (unlock leverage):** hVar (bridge only, HIT tail landed) → hAssign
(arm oracle) → hFn (native-store repr) → hEpilogueSpill / hInitStore (X8 entry
segs, bounded but decode-heavy). See `design/singletons.md` and `design/env-seam.md`.

## Relights

hVar relights off `env_get_found_uncond''` the moment the call-linkage bridge
lands. hFn off malloc/fwrite/exit. All statement-stable — NO amendment.
