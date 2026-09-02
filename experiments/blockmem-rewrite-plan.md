# BlockMem load-layer rewrite: presence → total-read (foundational)

The int/unary interlock stalled five waves (48e→48j) on `frame_pop`, and 48j
machine-checked the root: it is not a missing supplier, it is a foundational
mis-statement in the load-abstraction layer. Fix the layer, delete the
`frame_pop` class, relight the 17 fields. This is a foundational change with a
large blast radius; scope it as its own wave, not a tired late one.

## The root cause (machine-checked, `FramePopRamTotalityVerdict48j.lean`)

The Sail model reads memory TOTALLY: `readByte a = (m.get? a).getD 0` — an
unmapped/unwritten address reads as `0`, it does not fault. But the Lean
load-abstraction layer (`Vsa/Sim/BlockMem.lean` and the `vmem_read_data_*` /
`exec_l*` characterizations it wraps) demands HASHMAP PRESENCE as a hypothesis:
`h0 : m[a]? = some b`. Those are different facts. For the callee's own unwritten
entry frame the map genuinely has `m[a]? = none`, yet the read still succeeds
(returns `0` via `.getD`). So every downstream presence obligation over
unwritten stack bytes — `frame_pop`'s `[sp-1120,sp)` presence, and its whole
class — is asking for something the model never guarantees and no entry-supplier
can honestly provide (`∀a,∃b, m[a]? = some b` is outright FALSE; `GoodState`
carries no memory invariant at all).

The presence hypothesis is an OVER-STRENGTHENING introduced by the load layer,
not a semantic requirement. The model only ever needed the value the total read
returns.

## The fix

Reformulate the load characterizations to consume the TOTAL READ and drop the
presence hypothesis:

- A width-1 load's result becomes `(m[a]?).getD 0` (matching `readByte`), not
  `b` under `h0 : m[a]? = some b`. Wider loads compose the byte totals.
- The `h0`/`LPins`/byte-present hypotheses disappear from `exec_lbu_bm`,
  `exec_lw`/`exec_ld`/`exec_lh*`, `vmem_read_data_{one,two,four,eight}`, and the
  `MemFacts` load rows in `BlockMem.lean`.
- Consequently the seg/write-log layer stops EMITTING presence obligations for
  reads (`ProgFactsM`/`LPins*`), and `frame_pop` and its sibling presence
  conjuncts are DELETED from `BinArmExtras` / the unary residuals / any
  `*Geom` that carried them — deleted, not supplied.

This is semantics-preserving: the total read is what the model always did; the
proofs that currently thread `h0` were proving a stronger thing than needed.
Where a load's VALUE matters (a readback of a specific written byte), the caller
still supplies the write fact that pins that byte — that path is unchanged; only
the blanket presence-of-unwritten-bytes demand goes.

## Blast radius and order

`BlockMem.lean` is foundational — every seg/`#derive_case`/block proof depends
on it. Work outward, dependency-ordered, `lake env lean -o` per file (never
`lake build`; watchdog-killed):

1. **Diagnose**: enumerate every load lemma with a presence/`LPins`/`h0`
   hypothesis, and every downstream consumer of that hypothesis (grep
   `LPins`, `m[.*]? = some`, `frame_pop`, the `MemFacts` `.lw/.ld/.lbu` rows).
   Produce the change-list BEFORE editing.
2. **Reformulate the leaf load lemmas** (total-read result, drop presence).
   Keep the write-STORE side unchanged (stores still produce `writeMap`).
3. **Propagate** through `ProgFactsM`/`stepGM`/`wlogM`'s fact generation, the
   seg layer (`segEval_sound`/`bblocks_sound_bt`), and the frame/widen layer —
   deleting the now-unemitted presence obligations.
4. **Delete `frame_pop`** and its class from the residuals; regen the skeleton.
5. **Relight** the 17 int/eq + unary/logical fields (their `frame_pop` conjunct
   is gone; the remaining conjuncts were already dischargeable — x13_pres landed
   in 48i, entry-carry is the design B2 cure).

## Verification and success

- Incremental `lake env lean` per touched module; the FULL `check_all.sh`
  (via `rbuild.sh` on the remote box) at the end — this touches the widest
  cone in the tree, so the battery is the contract.
- Inversion: the harvested refutation battery must still behave (the amended
  statements are TRUE now, so `field_census.py` FOUND count must rise).
- SUCCESS = `frame_pop` class gone, 17 fields relit, `field_census.py` reports
  the actual jump (target 6→23, VERIFY — no census figure in a commit title
  beyond the census output), axioms ⊆ {propext, Classical.choice, Quot.sound},
  discipline OK.
- STOP-LOUD rule: if dropping presence breaks a proof that genuinely needed a
  written-byte VALUE (not mere presence), that is a real consumer — fix it by
  threading the specific write fact, NOT by re-adding blanket presence. If the
  total-read reformulation itself hits a semantic obstruction (the model does
  NOT in fact read total somewhere), machine-check it and STOP — that would mean
  the diagnosis is wrong.

## Sound-not-a-barrier note

`FramePopRamTotalityVerdict48j.lean` already proves the presence supplier false
and the total read total. This rewrite makes the abstraction layer match the
model it abstracts. It is the root fix the five-wave ladder was working around;
expect it to also simplify unrelated presence-threading elsewhere.

## Aside — the recursive-Repr residual (for the autoprove/Houdini track, not this rewrite)

StoreRepr/CString survival closes fully at design level via base/step
decomposition; it does NOT need Lean induction to be *discovered*, only
*applied*:
1. Houdini/LLM finds the (possibly strengthened) survival IH — the one hard
   bit — proposing until Z3-UNSAT, fuzz-validated to hold at runtime.
2. Decompose structural induction into base (`P(nil)`) + step
   (`(∀children c, P c) → P node`, IH as hypothesis). Mechanical, follows the
   datatype constructors.
3. Z3 discharges base and step SEPARATELY — each is non-recursive/QF once the
   IH is a hypothesis.
4. Lean `induction x with | nil => <cert> | cons h ih => <cert using ih>` chains
   them — a one-liner; the kernel applies the schema and checks.
The residual creative core is only step 1 (finding the strengthening); 2-4 are
mechanical. Fold into scripts/autoprove.py's recursive branch.

---

## VERDICT (wave 48k, 2026-09-02)

**Steps 1-4 LANDED; step 5 is machine-refuted and returned as an obstruction.**

Landed:
* the `Load Data` chain in `MemLoad.lean` FACTORED over the value the layer below
  returns, so one proof serves presence and total;
* `read_ram_*_total` at widths 1/2/4/8 and the whole total chain up to
  `vmem_read_data_*_total` (`MemLoadTotal.lean`);
* `SiteGood` + `exec_{ld,lw,lwu,lh,lhu,lbu}_tot`/`_totv` (`ExecLoadTotal.lean`, NEW);
* `LPins4`/`LPins8` and the width-1/2 pins are TOTAL-READ EQUALITIES.  `lds` is
  KEPT as the value name — dropping it would disconnect `runGM`/`wlogM` from
  memory; the equations are what keeps reflected execution tied to the machine;
* `gen_sites.py` grew `ld_tot`/`lw_tot`/`lbu_tot` and `ld_totb`/`lw_totb`;
  `LoadSitesTot.lean` (17) + `LoadSitesTotB.lean` (68) generated;
* `valueRepr_copy_total{,_of_writeWindow}` — the STOP-LOUD case: a machine copy
  moves `getD 0`, so byte-for-byte agreement is false at unwritten source bytes,
  but `ValueRepr` already witnesses presence for every byte it READS.  Value
  facts come from the source `ValueRepr`, not a blanket presence premise;
* `frame_pop` DELETED — with the 6 unary/logic `∀mcall` closures, the `hpop`
  mid-arm premise, and the `hMentPop` conjunct in 14 rows;
* full tree green: `rbuild.sh check` → 1378 jobs, `check_all: OK` (grep gate,
  the whole `#print axioms` battery ⊆ {propext, Classical.choice, Quot.sound},
  discipline OK).

**Step 5 (relight the 17 fields) is FALSE as premised.**  `field_census.py` on
the rebuilt tree: **6 FOUND / 52 NOT_FOUND — unchanged**.
`experiments/fleet/obstructions/X2_Field_hIAdd.lean` still proves
`field_hIAdd_refuted`, axiom-clean: `BinIntCellResid` ∀-closes over `m0`/`g` with
no entry hypothesis, and its ∃-body still demands `BinArmExtras.slot6`
(a static jump-table pin) and `gx19_pres`.  At `m0 := ∅` the cell is false
regardless of `frame_pop`; deleting a field only weakens the ∃-body.

CORRECTION (checked, same session): the 17 are NOT one class.

* The **11 int/eq** fields are genuinely refuted, and want the **B2-carry
  amendment**: add `entry : EvalEntry …` as a hypothesis field to
  `BinIntCellResid` so `slot6`/`sproom`/`gx19_pres` become preconditions the
  entry supplies.  A statement change to `rows/BinDispatchRow.lean`, a different
  wave, and a coordinator decision.
* The **6 unary/logic** fields already HAVE that carry: `NegResid` and its five
  siblings in `rows/TermRouting.lean` take `EvalEntry g N A SL … → …` as a
  leading hypothesis.  They are NOT refuted; NOT_FOUND means only that `exact?`
  finds no one-term discharge.  `B2_Field_hNeg.lean` claims otherwise but no
  longer elaborates (it calls `SkelHNeg` in the pre-entry-carry shape and Lean
  fills the gap with `sorryAx`); it is marked stale in-file.
