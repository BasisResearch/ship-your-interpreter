# autoprove — end-to-end demo (three outcomes)

Date: 2026-09-02. Tool: `scripts/autoprove.py` (Z3 4.15.4 oracle; `lake env lean`
for transcribe). Whole demo < 30s of Z3 + three ~5s Lean checks. NOTHING here
enters a proof (TOOLING.md §3: validation stack is design-time only).

`autoprove.py` composes the LANDED stack: the WRITE-LOG emitter
(`experiments/smt/bounded/gen_probe.py`, extended — the arm's computed
`(addr,width,value)` store list `BlockMem.wlogM`/`writeLog` as SMT Array stores,
so the destination memory is DERIVED from the machine effect, not a hand
copy-hypothesis), the bounded `ValueRepr`/`read*` encoder + DumpSmtLib OPAQUE
policy, Z3 for validity + Houdini (`houdini_ih.py`), the LLM request/response
protocol, and a Lean transcribe/verify step.

## Pipeline

1. ENCODE the field VC: `mp = writeLog m [(dstAddr+j,1,m[srcAddr+j]) | j<24]`
   (the 24-byte struct copy the ValueRepr arm performs) emitted as an SMT
   `store` chain + its select-store readback facts. Repr preds via the bounded
   encoder (case-split on `Value` + `readLE` unfold). Honest ENCODE-GAP where
   the arm reads genuinely-unbounded input structure (the machine-step
   supplier class — see `houdini_ih.py` FIELD_REGISTRY / DISPATCH.md).
2. Z3 VALIDITY: negation UNSAT ⇒ PROVED-DIRECT (+ SMT cert + landed Lean lemma).
3. IH-SYNTH: on SAT/UNKNOWN, Houdini over mined candidates ⇒ Z3-confirmed
   maximal inductive subset ⇒ PROVED-WITH-IH (named survivors).
4. LLM PROTOCOL: Houdini converges WITHOUT closing (vocabulary gap) ⇒ write
   `requests/<field>.json`, BLOCK on `responses/<field>.json`; an LLM/agent fills
   it via `--serve-request`; resume ⇒ PROVED-VIA-LLM.
5. TRANSCRIBE: emit `out/Field_<field>.lean`, `lake env lean` it read-only.

## The three demonstrated fields

### 1. hNull — PROVED-DIRECT  (ValueRepr leaf, non-recursive)

    $ scripts/autoprove.py --field hNull
    hNull   PROVED-DIRECT   GREEN   neg UNSAT (0.006s), no IH; twin(drop-byte)=sat; leaf lemma Vsa/Sim/ReprCopy.lean::read32_copy | lean: green

The `.null` case is `read32 · = some 0`: one read, no recursion. The write-log
store chain makes `mp = writeLog m log`; Z3 proves the negation UNSAT with no IH.
Non-vacuity checked (positive model SAT); the false-twin (drop copied byte 0) is
SAT, so the encoder can still refute. Cert maps to the landed lemma
`Vsa.Sim.read32_copy` (`ReprCopy.lean:87`) — the SMT proof and the Lean proof are
the same byte-agreement object. `out/Field_hNull.lean` is GREEN; axioms
⊆ {propext, Classical.choice, Quot.sound}.

### 2. hStr — PROVED-WITH-IH  (recursive CString; Houdini)

    $ scripts/autoprove.py --field hStr
    hStr    PROVED-WITH-IH  GREEN   neg SAT; Houdini survivors: read64_copy@ptr(mp_p=m_p), cstr_agreeP@tail, cstr_agreeP@payload[0..2]; leaf Vsa/Sim/ReprSurvival.lean::cstring_agreeP | lean: green

The `.str` case pulls in the recursive `CString`; the bounded encoder cuts the
recursion, so the un-strengthened negation is SAT (IH genuinely missing). Houdini
over the mined 8-candidate pool selects the maximal-consistent minimal-sufficient
subset — pointer transfer + tail equality + the 3 payload-window byte agreements
— and Z3 confirms it closes the goal (UNSAT). That set is exactly
`cstring_agreeP`'s content (`ReprSurvival.lean:150`) in the bounded vocabulary.
`out/Field_hStr.lean` GREEN, axiom-clean.

### 3. hVarShort — PROVED-VIA-LLM  (vocabulary gap → LLM loop closes)

`hVarShort` is a SHORT-VOCABULARY variant of the `.str` field: the candidate
pool is deliberately missing the payload-agreement shape (only ptr-eq / tail-eq /
tag / ptr≥0 / addr-disjoint). Houdini converges WITHOUT closing the goal → the
LLM protocol fires:

    $ scripts/autoprove.py --field hVarShort --no-block
    hVarShort  NEEDS-LLM   vocabulary gap; request at experiments/autoprove/requests/hVarShort.json

The request records the field, statement, `z3_CTI_model` (the counterexample-to-
induction: the payload bytes at pointer `p` are free to disagree),
`candidates_tried`, `residual_gap`, `shapes_exhausted`, and a `vocabulary_hint`.
An LLM/agent then answers by proposing the missing shape (payload-window byte
agreement) via `--serve-request` (which parse/type-checks each candidate's SMT):

    $ scripts/autoprove.py --serve-request hVarShort --response @resp.json
    WROTE response .../responses/hVarShort.json (3 candidate(s), manual=False)
    $ scripts/autoprove.py --field hVarShort
    hVarShort  PROVED-VIA-LLM  GREEN  LLM candidate(s) ['llm:cstr_payload_agree[0..2]'] closed the goal; leaf cstring_agreeP | lean: green

The LLM-supplied `cstr_payload_agree[0..2]` candidates enter the pool, Houdini
re-runs, Z3 confirms UNSAT, and the loop closes. `out/Field_hVarShort.lean` GREEN,
axiom-clean. (The response schema also supports `manual: true` = "no automatable
candidate; hand to a human" → verdict stays NEEDS-LLM.)

## OUT-OF-FRAGMENT honesty (the rest)

The write-log store-chain encoder reaches exactly the **leaf, memory-arithmetic
ValueRepr copy-readback stratum** (`.null/.bool/.int` PROVED-DIRECT; `.str`
PROVED-WITH-IH once the payload IH is selected/supplied). Two honest sub-strata
limits, both surfaced by the tool rather than hidden:

* **Value reconstruction is nonlinear.** The raw store chain alone leaves the
  8-byte `.int` payload readI64 as UNKNOWN (Z3 will not reconstruct the value
  through the symbolic store chain). autoprove emits the store chain AND its
  select-store readback facts (`wlog_readback_facts`) — Z3-trivial consequences
  of the effect, NOT extra hypotheses — which restores UNSAT for `.int`.
* **The recursive cut.** Beyond the `CString` tail the bounded encoding cannot
  close the recursion; the `.str` fact must be a SUPPLIED hypothesis
  (`cstring_agreeP`), which is what Houdini selects and the LLM proposes. This is
  the inductive wall of BOUNDED-PROBE.md / HOUDINI-IH.md, inherited exactly.

Everything ELSE — the 24 NO-CURE-SEMANTIC-GAP supplier fields (`hSExpr`, `hVar`,
`hCall`, `hSBlock`, the seq/args/if/while/for geoms, the native-print specs, …)
— is honest **ENCODE-GAP**: their statement is ∀-closed machine-step content
(`Triple`/`SegEntry`/`ExecEntry`/`*Geom`/`NativeSpec`/`Steps`) the bounded QF-ABV
encoder cannot express. `autoprove.py --field hVar` (or any of them) defers to
`houdini_ih.py`'s FIELD_REGISTRY and reports `ENCODE-GAP` with the dominating
predicate cited. Those remain the Lean abstraction stack's job (TOOLING.md §1),
never a bounded-SMT one. autoprove is the opportunistic prover for the leaf
pocket + the IH-triage + the vocabulary-gap escalation loop, not a route to the
machine-step bulk.
