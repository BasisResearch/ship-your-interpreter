# Cure suite — str-cell + div-overflow fields (hStrAddL/R, hStrLt/Le/Gt/Ge, hDivOv)

> **PRE-WAVE SEALED BANNER.** Sealed 2026-09-02, tree @c9e1453 (CEGIS production
> sweep: io/str/singleton/crux). Sealed = production input AND uncontaminated
> prospective validation. Written BEFORE the proving wave; reseal a new dated
> block rather than editing. Nothing here enters a proof (Law 4 / design-time).

Fields (`Vsa/Sim/TermAssembly.lean:151-179`), all `∀ …, EvalIH … (.binary …) …`:
- `hStrAddL` `.str (lv.catDisplay ++ rv.catDisplay)` (left-str concat)
- `hStrAddR` right-str concat
- `hStrLt` `.bool (sl < sr)`, `hStrLe` `.bool (sl<sr || sl==sr)`,
  `hStrGt` `.bool (sr < sl)`, `hStrGe` `.bool (sr<sl || sl==sr)`
- `hDivOv` `.int (wrap64 ((-2^63).tdiv (-1)))` — the INT64_MIN/-1 overflow-wrap arm

Cluster: loop-arm entry `0x800034e8`. Suppliers: `StrConcatCellResid`
(`hStrAdd*`), `StrCmpOrderBridge`/`StrArmPrologue` (`hStr{Lt,Le,Gt,Ge}`),
`TermGuards.divOvfArm` (`hDivOv`).

## 1. Obstruction — SURVIVED (no refutation exists)

- `statement_fuzz` (mining, `BATCH-REPORT.md`): all 7 **candidate-mined+SURVIVED**;
  full relational kind-seam alignment (8 kinds, machine==spec every kind).
- `cegis_cure.py --file invariants/hStr*.lean / hDivOv.lean --prop mined`:
  **Detected defects: none — Survivors: 0** for every field.
- No obstruction file exists for any str/divov field.
- Empirical (t5 harness, `TOOLING.md §5`): the div-overflow WRAP direction and the
  String-order DIRECTION were both **confirmed** against the exact model — the
  statements match the machine, no falsity.

**⇒ PROVE-DIRECTLY.** `hDivOv` and the two `hStrAdd*` concat cells and the four
order cells are all TRUE as stated.

## 2. cegis_cure — N/A (no false field to cure)

Every field: `Detected defects: none, Survivors: 0`. No ranked suite (no defect).
The cure vocabulary cannot bite; the remaining gap is *callee-seam content*
(strcmp / stringify / divdi3), which is outside the address-map cure fragment.

## 3. Classification

| field | class | why |
|---|---|---|
| hDivOv | **PROVE-DIRECTLY** (SINGLE-SEAM) | div-overflow arm via `divdi3_spec` (LANDED seam, `DivDispatchSeg`); wrap semantics confirmed empirically. Bounded arm, no math gap. |
| hStrAddL / hStrAddR | **PROVE-DIRECTLY-HARD** (String bridge) | `StrConcatCellResid` blocked on the **stringify spec** (`rows/StringifySpec.lean`, `TermGuards.strConcat`): `catDisplay` byte-materialization needs a byte-induction over the concat heap (`StrConcatHeap`), not an address-map fact. |
| hStrLt / hStrLe / hStrGt / hStrGe | **HARD-MATH** (String.lt lexicographic) | `StrCmpOrderBridge`: the spec layer LACKS a `String.lt` ⇔ `strcmpSpecSign` agreement — only *equality* is landed (`string_eq_iff_strcmpSpecSign_zero`). Closing it needs a lexicographic byte-induction lemma (`sl < sr ↔ first-differing-byte`), OUTSIDE the address-map fragment. |

### WHY THE TOOLS DEFER (HARD items)

- **StrCmpOrderBridge (hStrLt/Le/Gt/Ge) = String.lt lexicographic math.** This is
  NOT an address-map defect and NOT an entry/quantifier repair — `cegis_cure` finds
  no defect precisely because the statement is TRUE; the missing artifact is a
  *math lemma* (`String.lt` ↔ per-byte compare), which the CEGIS cure vocabulary
  (address-map fragment) cannot express. `smt_check` treats `String.lt`/`CString`
  as opaque → REFUTED-MODULO-OPAQUE, never a countermodel. **Flag: HARD-MATH.**
  Needs a byte-induction lemma landed in the spec layer, then `strCmpCellResid_of`
  (`rows/StrCmpBlockC.lean`) consumes it per operator (Le/Gt/Ge fold off Lt+eq).
- **StrConcatCellResid (hStrAddL/R) = stringify byte-materialization.** Same
  fragment-boundary reason: `catDisplay` is opaque to SMT; the residual is a
  byte-induction over the concat-heap write chain (`StrConcatHeap.lean`), not a
  falsity. Deferred to the writer as a proof, HARD but not HARD-MATH (it is a heap
  byte-fold, precedent = memcpy `iterW`).

hDivOv is the only genuinely bounded one here — SINGLE-SEAM via the landed
`divdi3_spec`; land it independent of the two String campaigns.

## Relights

Value/compare block-reflection paths (Lt/Le/Gt/Ge machine arms landed,
`StrCmpSignTail`) relight verbatim once the String.lt lemma lands. `hDivOv`
relights off `DivDispatchSeg` immediately. NO statement amendment for any field.
