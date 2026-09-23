---
name: autoprove
description: Discharge a proof record field end-to-end with the design-time validation stack — encode the field VC via the write-log machine effect, ask Z3 for validity, synthesize an inductive hypothesis with Houdini, escalate a vocabulary gap to an LLM via a request/response protocol, then transcribe and lean-check a proof skeleton. Use when asked to autoprove/auto-discharge a record field, triage whether a supplier field is Z3-provable, run the IH-selector, or close the LLM vocabulary-gap loop. NEVER enters a Lean proof (validation stack only).
---

# autoprove

`scripts/autoprove.py` is the INTEGRATED loop that discharges one record field
end-to-end by composing the LANDED validation stack (TOOLING.md §3 — NOTHING
here enters a proof). It does not rebuild the stack; it wires the write-log
emitter, the bounded ValueRepr/read encoder, Z3, Houdini, an LLM protocol, and a
Lean transcribe step.

## Run it

```
scripts/autoprove.py --field hNull            # PROVED-DIRECT   (leaf, no IH)
scripts/autoprove.py --field hStr             # PROVED-WITH-IH  (Houdini)
scripts/autoprove.py --field hVarShort        # NEEDS-LLM       (vocabulary gap)
scripts/autoprove.py --batch hNull,hStr,hVarShort
scripts/autoprove.py --field hVar             # ENCODE-GAP      (machine-step Prop)
```

Flags: `--no-lean` (emit the Lean file, don't run it), `--no-transcribe` (skip
it), `--no-block` (don't block polling for an LLM response — single check).

## The pipeline (five steps)

1. **ENCODE** the field VC. The machine effect is the arm's computed write-log
   (`BlockMem.wlogM`/`writeLog`, a `(addr,width,value)` store list) emitted as an
   SMT `store` chain so `mp = writeLog m log` — the destination memory is
   DERIVED from the effect, not assumed by a hand copy-hypothesis. Repr
   predicates via the bounded encoder (`experiments/smt/bounded/gen_probe.py`:
   `Value` case-split + `readLE` unfold). The store chain alone leaves the 8-byte
   `.int` payload UNKNOWN (nonlinear); we also emit its select-store readback
   facts (`wlog_readback_facts`), Z3-trivial consequences of the effect.
2. **Z3 VALIDITY**. Negation UNSAT ⇒ **PROVED-DIRECT** (cert + landed Lean lemma,
   per BOUNDED-PROBE.md null/bool/int → `read32_copy`/`readLE_copy`). Non-vacuity
   and false-twin (drop-byte) checks run automatically.
3. **IH-SYNTH**. On SAT/UNKNOWN, Houdini (`scripts/houdini_ih.py`) over mined
   candidates → Z3-confirmed maximal-consistent minimal-sufficient subset ⇒
   **PROVED-WITH-IH** (named survivors; for `.str` this is `cstring_agreeP`'s
   content).
4. **LLM PROTOCOL**. Houdini converges WITHOUT closing = vocabulary gap ⇒ write
   `experiments/autoprove/requests/<field>.json` and BLOCK on the response.
5. **TRANSCRIBE**. On PROVED, emit `experiments/autoprove/out/Field_<field>.lean`
   and `lake env lean` it read-only against the tree; report green + axioms
   (⊆ {propext, Classical.choice, Quot.sound}).

## The LLM request/response protocol

When a field is NEEDS-LLM, the driver has written a request describing the gap.
**As the coordinator/LLM, answer it by proposing a candidate template**, then
serve it:

- **Request** `requests/<field>.json`: `{ field, statement, encoder_target,
  z3_CTI_model, candidates_tried, residual_gap, shapes_exhausted,
  vocabulary_hint }`. The CTI model shows exactly what is free to disagree (e.g.
  payload bytes at pointer `p`); the hint names the SMT vocabulary you may use.
- **Response** `responses/<field>.json`: `{ field, candidates: [{name, smt}...],
  manual: false }`. Each `smt` is an SMT-LIB Bool term over the bounded encoder
  vocabulary (`m_def`/`m_val`/`mp_def`/`mp_val` Arrays, `m_p`/`mp_p` Int
  pointers, `cstr_tail_m`/`mp` opaque tails). Set `manual: true` when there is no
  automatable candidate (verdict stays NEEDS-LLM — hand to a human).

Serve it with the helper (parse/type-checks each candidate before writing):

```
scripts/autoprove.py --serve-request <field> --response @resp.json
scripts/autoprove.py --field <field>          # resume → PROVED-VIA-LLM
```

Example response (the payload-window agreement the `.str-short` gap needs):

```json
{ "field": "hVarShort", "manual": false, "candidates": [
  {"name": "llm:cstr_payload_agree[0]",
   "smt": "(and (= (select mp_def (+ mp_p 0)) (select m_def (+ m_p 0))) (= (select mp_val (+ mp_p 0)) (select m_val (+ m_p 0))))"} ] }
```

## OUT-OF-FRAGMENT honesty (do not overclaim)

autoprove is the opportunistic prover for the **leaf, memory-arithmetic
ValueRepr copy-readback stratum** and the IH-triage/escalation loop on top of it.
It is NOT a route to the machine-step bulk. Any field whose statement is
∀-closed machine-step content (`Triple`/`SegEntry`/`ExecEntry`/`*Geom`/
`NativeSpec`/`Steps` — the 24 NO-CURE-SEMANTIC-GAP supplier fields) reports
honest **ENCODE-GAP** (defers to `houdini_ih.py`'s FIELD_REGISTRY, citing the
dominating predicate). The recursive `CString` cut means the `.str` fact must be
a SUPPLIED hypothesis, which Houdini selects or the LLM proposes — never a
Z3-closed recursion. Those fields remain the Lean abstraction stack's job
(TOOLING.md §1). Every limit is surfaced, none silent.

## Verify

The transcribe step already runs `lake env lean` (never `lake build`, never LSP;
≤2 lean processes). See `experiments/autoprove/DEMO.md` for the three worked
outcomes (PROVED-DIRECT / PROVED-WITH-IH / PROVED-VIA-LLM), all lean-green and
axiom-clean.
