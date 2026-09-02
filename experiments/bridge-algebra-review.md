# Bridge algebra review — the machine↔spec bridge idiom, its convergent algebra, and higher-order compression

Design-research deliverable.  READ-ONLY audit of `Vsa/`; prototype in a COW
clone (`/tmp/vsa-bridge-proto/Vsa/Sim/EntryBridge.lean`, green + axiom-clean).
The categorical lens (Triples as morphisms, conseq as profunctor dimap, Widen as
lax morphism) is used to DIAGNOSE only; every proposal is a self-contained
named-field Lean object in repo idiom, no Mathlib, obeying the fast-reflection
laws.

## 1. Trajectory (what each generation factored; what residue remained)

| Gen | Layer | Factored | Residue |
|-----|-------|----------|---------|
| G0 | per-site `StepObs` batteries (`Str{cmp,cpy}Sites`, `MemcpySites`) | one lemma per instruction; ~30 lines each | EVERYTHING — every run hand-threaded |
| G1 | `block_facts` / `bblock_sound_bt` (`ChainFactsTac`) | straight-line + terminator run in ONE call (180→39 lines) | end-PC/frame/mem still per-block ghosts |
| G2 | `#derive_case` + `segToTriple`/`segToTripleFramed` (`DeriveCaseRow`, `SegToTripleFramed`) | seg run + marshalled regs + ABI/mem frame FREE off ONE kernel `decide` | seam predicates hand-stated per row |
| G3 | `callSeg`/`callSegConseq` + `bridgeOfSeg`/`jalStep_of_obs` (`DeriveCallSeg`, `BridgeSeg`) | `prefix ≫ callee ≫ suffix` splice + jal seam + frame, ONE combinator per call | the per-callee jal word + the `*_closed` marshaller |
| G4 | `Widen`/`FnSummary.{seq,callSplice,tailJump}`/`TripleCat`/`repack` (`WidenMeta`, `FnSummary`, `TripleCat`, `RepackTac`) | the 5-widener zoo → ONE `Widen`; conseq → `dimap`; bundle→bundle → `repack` | leaf/exec-arm entry-rebuild rows STILL hand-write 40-field records + positional `.2.2` residual towers |

The layers strictly climb: raw `Step` → `Steps` chain (`block_facts`) → `Triple`
(`segToTriple`) → composed `Triple` (`callSeg`) → whole-function `Triple`
(`FnSummary`) → widened motive-exit (`Widen`).  Each generation converted a
per-instance hand-cost into a `decide` + a named datum.

## 2. The NEVER-factored invariant

Across every generation, ONE thing was re-threaded by hand at every site and
NEVER abstracted: **the entry→post transport of a named-field bundle** — the
`∀ params, EntryP c → PostBundle(c)` map where `EntryP` is `EvalEntry`/
`ExecEntry`/`SegPre` and `PostBundle` is `*LeafResid`/`*Geom`/`Eval*Entry`.
It shows up three ways, all uncombinatored:

- **Leaf field discharge** (`field_h{Int,Null,Bool,Str}_of_geom`): destructure a
  k-conjunct geometry ONLY to re-pair it with the widener, `exact ⟨h1,…,hk,
  leafWidenP_of_entry hc⟩`.  The entry `hc` is consumed TWICE (geom + widener),
  identically at every leaf.
- **Entry record rebuild** (`eval_null_row`'s `EvalNullEntry := {good := hc.good,
  … 40 fields …}`): a positional field-by-field copy of `EvalEntry` into the
  callee entry, with a handful substituted from the geometry residuals.  This is
  R6/R7's *exact* enemy (reorder `EvalEntry` and all 40 lines shift), landed
  10+ lines per row, ~14 rows.
- **B5 exec twin**: the identical shape on the statement side (`Exec*Geom →
  *Resid`), currently blocked (§ below) but structurally the same transport.

`Widen` factored the *exit* transport (`*Exit → *ExitD`); `TripleCat` factored
the *Triple*-level pre/post transport (`dimap`).  The **entry** transport — the
contravariant leg from `EvalEntry` into the residual bundle — was never given a
combinator.  That is the gap.

## 3. Remaining bridge classes (cost split: glue vs semantic content)

From `entry-needs-audit.md`, `B5ExecArmObstructions.lean`, the census:

| Class | Glue (mechanical transport) | Per-instance SEMANTIC content |
|-------|------------------------------|-------------------------------|
| Leaf fields (int/null/bool/str) | the `_of_geom` + entry-rebuild transport (§2) | the geometry conjunction itself — closed TODAY by `nbs_pins`/`omega` off the amended entry. LANDED for int/null/bool; str needs N3 AST-region |
| Exec arms B5 (11 dispatch fields) | same transport, statement side | **BLOCKED, provably false as stated** (`StmtSlotPinned` under ∀-`m0`, `m0=∅` refutes): needs the `ground` entry amendment (N2), a STATEMENT change, not a bridge |
| Exec arms B5 (3 loop fields) | — | self-referential loop IH oracle (X4) — capstone-supplied, not a bridge |
| Call/native seams (X6) | `callSeg`/`bridgeOfSeg` ALREADY factor this | per-callee jal word + callee contract (genuine) |
| Entry `ground` bundle (N1-N5) | `EvalGround.survive_stack` transport (47f `NBSPins` shape) | the M6 rodata/arena/AST-region literals (genuine, top-level) |

Verdict: the remaining cost is ~70% **mechanical entry-transport glue** (§2's
never-factored invariant, replicated leaf×exec×entry-rebuild) and ~30% genuine
semantic content that no combinator can supply (rodata pins, AST region, loop
IH, jal words).  The glue is the compressible part.

## 4. Per-lens verdict (with line-count evidence)

**Landed bridges measured** (`Vsa/Sim/rows/`): `field_hNull_of_geom` body = 4
lines (obtain-5 + re-pair-6-tuple); `field_hStr_of_geom` = 6; `eval_null_row`
`EvalNullEntry` rebuild = 10+ lines of positional `{field := hc.field}` over 40
fields; `bridgeOfSeg` already collapses a ~175-line `*Prefix_run` to ~20.

### Lens A — single `Bridge P Q` transport (contravariant pre / covariant post): subsumes weaken/conseq/widen/repack?

**PARTIAL YES, and it is already HALF-LANDED.**  `TripleCat.Triple.dimap` IS the
profunctor transport at the `Triple` level (`conseq` = `dimap`; `lmap`/`rmap` =
the one-sided legs; `PredIso` collapses adapter pairs).  What it does NOT cover
is the ENTRY transport (`EvalEntry → bundle`), because that leg is not a
`Triple` — it is a plain `Ent EntryP Post` at the predicate level.  A single
`EntryBridge EntryP Post := Ent EntryP Post` with `pull` (contravariant
re-seat) + `andWiden` (append the fixed widener structure-map) closes the leaf
class.  It does NOT subsume `Widen`: `Widen` carries genuine ∃-φ DATA in `surv`
(a lax-morphism structure map), not a mere entailment — so `Widen` stays its own
object, consumed BY the bridge (`andWiden`'s second argument is
`leafWidenP_of_entry`, a `Widen`-producer).  **So: one `Bridge` subsumes
weaken/conseq/repack-of-entailments, but Widen remains an orthogonal
structure-map the bridge threads, not one it absorbs.**

### Lens B — bifunctor machine×spec pairing to restructure `Approx`?

**NO — no compression, real risk.**  `Approx`/the sim relations are already
stated as `Config → Prop` predicates with the spec state `st : While.St` as an
ordinary parameter, so a machine×spec *product* category buys nothing the
current parameterisation lacks, and a paired `structure` would force whnf of
Sail state on the machine leg (fast-reflection law 1 forbids: reflect on the
first-order write-log, never Sail state).  The spec side is already a cheap
`While.St` value; pairing it into a bifunctor object would make the seams
NON-`rfl`.  Leave `Approx` as-is.

### Lens C — Kleisli composition over `Steps`?

**NO — already subsumed, redundant.**  `Steps.trans` + `Triple.seq` IS the
Kleisli composition of the `Steps` relation (monadic bind of the reachability
relation), and `TripleCat.seq_assoc` already proves it associative *by proof
irrelevance* (`Subsingleton.elim` — free at `Prop`).  A Kleisli-category
reification would add a typeclass/newtype layer (instance search =
elaboration-hostile, gate-banned in spirit) for laws that are already `Eq.refl`.
The categorical structure is the SPEC and is already machine-checked in
`TripleCat`; reifying it as data is negative value.

## 5. Prototype result

`EntryBridge` (`/tmp/vsa-bridge-proto/Vsa/Sim/EntryBridge.lean`, green,
axioms ⊆ {propext, Classical.choice, Quot.sound}):

```
def EntryBridge (EntryP Post : Config → Prop) : Prop := ∀ c, EntryP c → Post c
theorem EntryBridge.pull    (hpre : Ent EntryP' EntryP) (B : EntryBridge EntryP Post) : EntryBridge EntryP' Post
theorem EntryBridge.push    (B : EntryBridge EntryP Post) (hpost : Ent Post Post') : EntryBridge EntryP Post'
theorem EntryBridge.andWiden (geom : EntryBridge EntryP Geom) (wid : ∀ c, EntryP c → W c)
      : EntryBridge EntryP (fun c => Geom c ∧ W c)
```

Applied to the REAL pending `field_hNull_of_geom` (`field_hNull_of_geom_viaBridge`,
verified green): `andWiden` absorbs the ∀-intro, the double use of `hc`, and the
widener append — the caller passes ONLY the geom supplier and
`leafWidenP_of_entry`.  **Measured finding at the seam:** `andWiden` delivers
`(Geom) ∧ W` but the residual `NullLeafResid` is a FLAT right-nested
`Geom₁ ∧ … ∧ Geomₖ ∧ W` — the one remaining line is an ∧-reassociation.  That is
the crux: **the residuals are raw ∧-towers, so the transport's last seam is
positional `.2.2` (R6/R7 violation) NO MATTER the combinator.**  The combinator
is correct; the *statement layer* (residuals as `∧`-towers, not named-field
structures) is what forces the residue.

Corollary discovered during prototyping: `repack` (landed, `RepackTac.lean`) is
NOT used in `eval_null_row`'s 40-field `EvalNullEntry` rebuild, even though
`EvalNullEntry` IS a flat named-field structure and `repack hc <geomResids>`
would close it field-by-field with zero positional copying.  **The single
highest-value UNTAPPED win is applying the already-landed `repack` to the ~14
entry-rebuild rows** — no new combinator needed.

## 6. Build/no-build recommendation

**Do NOT build a new grand `Bridge`/bifunctor/Kleisli layer** — Lens B and C are
net-negative, and Lens A's `Triple`-level half already exists (`TripleCat`).

**Two bounded, high-value actions, in priority order:**

1. **Apply `repack` to the entry-rebuild rows** (`eval_null_row` and its ~13
   siblings in `TermRouting`/`ExecRouting`). Zero new abstraction — the tool is
   landed. Kills the 40-field positional `{field := hc.field}` records (the
   worst R6/R7 residue). Highest ROI.

2. **Land `EntryBridge`** (the prototype, ~40 lines) as the named home for the
   leaf/exec-twin entry transport, with `pull` for the 47-style re-seats. BUT
   its full payoff REQUIRES the residuals (`*LeafResid`, `Exec*Resid`) to be
   re-stated as **named-field `structure … : Prop`** (per the R6/R7 mandate)
   instead of raw ∧-towers — then `andWiden` delivers straight into the carrier
   and `repack` closes the seam, eliminating the last positional line. That
   residual-restatement is a statement-layer wave, not a combinator; sequence it
   with the B5 `ground` amendment (which touches the same rows).

**Combinator signature to land (action 2):**

```
def EntryBridge (EntryP Post : Config → Prop) : Prop := ∀ c, EntryP c → Post c
theorem EntryBridge.pull     : Ent EntryP' EntryP → EntryBridge EntryP Post → EntryBridge EntryP' Post
theorem EntryBridge.andWiden : EntryBridge EntryP Geom → (∀ c, EntryP c → W c)
                             → EntryBridge EntryP (fun c => Geom c ∧ W c)   -- deliver into the RESID STRUCTURE, not a raw ∧
```

Net: the machine↔spec bridge algebra converged to a **profunctor over `Config →
Prop`** (contravariant pre / covariant post), already realised at the `Triple`
level (`TripleCat`) and the exit level (`Widen`). The one un-realised leg is the
ENTRY transport; it needs a thin `EntryBridge` PLUS the statement-layer
discipline (residuals as structures) to pay off — the combinator alone cannot,
because the residue lives in the `∧`-tower shape, not the proof.
