# Cure suite — io native-print fields (hCallPrint / hCallPrintln / hCallAssertOk)

> **PRE-WAVE SEALED BANNER.** Sealed 2026-09-02, tree @c9e1453 (CEGIS production
> sweep: io/str/singleton/crux). Sealed = production input AND uncontaminated
> prospective validation. This suite is written BEFORE the proving wave opens; do
> not edit the verdicts after a writer session touches these fields — reseal a new
> dated block instead. Nothing here enters a proof (Law 4 / design-time only).

Fields: `TermResidualsCore.hCallPrint`, `.hCallPrintln`, `.hCallAssertOk`
(`Vsa/Sim/TermAssembly.lean:184-188`). Each is `∀ st d vs, CallPrint*Resid …`.
Cluster: env-seam entry `0x800031b0` (native call arm) → the io print DAG.

## 1. Obstruction — SURVIVED (no refutation exists)

- `statement_fuzz` (mining pass, `BATCH-REPORT.md`): all three
  **candidate-mined+SURVIVED**; relational kind-seam aligned (machine 13 = spec 13
  `.expr`). No lethal outer/descend witness.
- `cegis_cure.py --file invariants/hCallPrint{,ln}.lean --prop mined`:
  **Detected defects: none — Survivors: 0** (tool defers; no address-map/entry
  cure defect present). Same verdict for `hCallAssertOk`.
- No obstruction file exists in `experiments/fleet/obstructions/` for any of the
  three (that dir carries only X2 int-cell + unary/logic + MemExt/Mcall shapes).

**⇒ PROVE-DIRECTLY** (SURVIVED). The statements are TRUE as stated; the residual
is *content*, not a falsity — assemble the print DAG, do not amend.

## 2. cegis_cure — N/A (no false field to cure)

Ran per field; every run returned `Detected defects: none, Survivors: 0`. There is
no ranked cure suite because there is no defect: the cure vocabulary (entry-
conditioning / quantifier-repair / guard-repair / conjunct-deletion / oracle-
rehome) has nothing to bite on. `--joint` interlock not run (no candidate).

## 3. Classification — PROVE-DIRECTLY (io = degenerate-flush + contract splice)

The three fields are served by the io print DAG (`design/io-loop-fold.md §c`), not
by a single span. Sub-shape per field is identical; the WORK is the compose:

| field | route | supplier state | why not HARD |
|---|---|---|---|
| hCallPrint | value_print → fputs/fwrite/fprintf → _write_r → _write → tohost | `ValuePrintContract` LANDED; io_write fold LANDED | %lld path LANDED (M3); flush loops **degenerate on the live path** |
| hCallPrintln | as hCallPrint + trailing `\n` | same | same |
| hCallAssertOk | assert-ok arm (no value render on the ok branch) | same | shortest route |

**io degeneracy finding (from `BATCH-REPORT.md` §io + `SEEDS-io.md`):** stdout is
UNBUFFERED (`main.c setvbuf _IONBF`). The flush/drain loops (`_fflush_r`,
`__sflush_r`, `__swbuf_r`) therefore execute a **degenerate-drain instance on the
live path** — `written = 0`, `out` unchanged, `_flags = 0x10009` pinned — a real
SURVIVED T5-slot fact, NOT a loop stride. So the print fields do NOT need the
loop-fold in anger: the drain is a constant-window splice. The heavy printf
machinery (`io_vfprintf_r`/`io_svfprintf_r`) is off the live print path for these
fields (int rendering already covered by `snprintf_lld_spec`, M3).

So the io class is **degenerate-flush + contract splice**, not a mining problem:
1. relight `CallPrint*Resid` as named-field structures over the io-fold posts
   (`design/io-loop-fold.md §a`, `CallPrintResid { dispatch, emit, frame }`);
2. splice the LANDED `ValuePrintContract` (Fputs/Fwrite/Fprintf) + io_write fold;
3. discharge the degenerate flush as a constant-window `bridgeOfSeg` (no loop).

**Prereq (bounded, not a cure):** `io_value_print` 3-block dispatch (jump table
`0x80019f10`) + the 6 `vparm_VP_*` arms — these ground `dispatch`. See the
singletons suite (`experiments/cures/singletons.md`) for the vparm arms and
`design/io-loop-fold.md §d` for T-IO-valueprint / T-IO-compose.

## Relights

Value paths + `ValuePrintContract` + io_write fold relight verbatim. New content
= io_value_print dispatch (bounded) + the 3-way compose. NO statement amendment.
