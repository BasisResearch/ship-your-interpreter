# Cluster design — error-jal-seam (19 fields)

> **RECONCILED @ea30e22.** All 19 errSite Triples LANDED (`ErrSitesBatch{0..3}`,
> confirmed in tree). These 19 feed `ErrWork`/`hErrFam` (split out of
> `TermResidualsCore`), so they are NOT among the 52 open `TermResidualsCore`
> census fields — they are the error-family residual. Cluster status unchanged:
> the hard part is done, residual = per-arm `Reaches` (T-ERR-reach) + kindname
> readback + the `ErrWork` restate. See `experiments/REMAINING.md` (ErrWork reach
> is a flagged hard item — no combinator supplies caller-linkage).

**Fields (cases).** err_80003b54, err_80003b9c, err_80003bc8, err_80003c10,
err_80003c7c, err_80003cc4, err_80003ce8, err_80003d14, err_80003d5c,
err_80003da0, err_80003950, err_800034e4, err_80003de8, err_80003e98,
err_80003f58, err_80003fac, err_80003fdc, err_80002e90, err_80002ebc.

Each case is a `jal runtime_error` site inside `eval_expr`/`exec_stmt`. The
`ErrWork`/`hErrFam` premises they feed (hVarUndef, hExpr, hAssignE, …) are the
error family, split OUT of `TermResidualsCore` into `TermResiduals.hErrFam`
(`TermAssembly.lean:73`) so `EndToEnd.lean` swaps them for `ErrWork`.

## Status: the hard part is ALREADY LANDED

Per the M4/M5 memory + INDEX: all 19 distinct `errSite_<pc>` Triples are
**LANDED** (`rows/ErrSitesBatch{0..3}.lean`, `#derive_error_site` +
`jalStep_of_obs`; the ~200-line jal→RuntimeErrorAt marshalling every row
assumed is proved). The remaining residual per row is uniformly the **`hsite`
caller-linkage** — that the arm PC is reachable from the eval/exec caller with
the runtime-error precondition — NOT a new machine span.

## (a) Amended / new statement shapes

The error family currently threads `hsite`/`hVarUndef`/… as bare premises. The
bridge-review flat-∧ finding applies: restate `ErrWork` as a named-field
structure keyed by arm PC, each field carrying (i) the LANDED `errSite` Triple
and (ii) the caller-linkage as an explicit reachability field — no ∀-ghost.

```lean
/-- One row per error arm PC. `errSite` is the LANDED Triple; `reach` is the
    caller-linkage (hsite) — the ONLY residual. `pre` names the runtime-error
    precondition the caller establishes (type mismatch / undefined var / …). -/
structure ErrArmResid (armPC : BitVec 64) (msg : ErrKind) : Prop where
  pre    : ErrPre armPC msg            -- caller-side error condition (spec)
  reach  : Reaches callerPC armPC pre  -- hsite: the arm is jumped-to (computed j / branch)
  site   : ErrSiteTriple armPC          -- LANDED (rows/ErrSitesBatch*)  ← consumed, not proved
```

`ErrWork` becomes `structure ErrWork (L) where hVarUndef : ErrArmResid 0x…b54 …`
etc. (19 named fields), and `hErrFam := ErrWork` as today — the SPLIT already
supports this (`TermResiduals extends TermResidualsCore`).

**No falsity class here.** These are not the ∀-ghost residuals; they are
reachability facts. The fuzz-relevant check is only that `reach`/`pre` are
inhabitable (they are — a jump target with a satisfied precondition).

Note the corpus shows several arms share a slice (err_80003b54's slice spans
b54→c10→c34): the `Reaches` field must key on the SPECIFIC computed-jump edge,
so the 19 rows are 19 distinct `armPC`s even where slices overlap. This is a
design correctness point — do NOT collapse rows by slice.

## (b) Invariants / bridges to mine

Low mining yield (these are reachability, not loop invariants). The useful mine:
- **Relational** at the eval/exec dispatch: which spec error transition
  (`EvalErr`/`ExecErr` constructor) reaches which arm PC. Probe the dispatch +
  the computed-jump target register; align by the spec error kind. One seam,
  tag-discriminated — same shape as the round-3 brk/cont pilot. This grounds
  the `Reaches callerPC armPC` edge per arm.
- No T1-T5 numeric mining (no loop; stores are spills, already in errSite).

## (c) Supplier DAG

```
errSite_<pc> Triples (19)           ── LANDED (rows/ErrSitesBatch0..3)
runtime_error_spec                  ── LANDED
value_kind_name                     ── NONE (needed by ~14 arms for the msg string)
    │  (the msg-building block calls value_kind_name; its contract is the one seam)
ErrPre / EvalErr-ExecErr transitions ── spec layer, LANDED
Reaches (hsite caller-linkage)       ── per-arm, MISSING (the residual)
```

The `value_kind_name` callee (NONE) is the one genuine content gap: ~14 arms
build the error message via `value_kind_name` before the final
`jal runtime_error`. But the errSite Triple starts AT the `jal runtime_error`,
so the message-build prefix is part of the `reach`/`pre` establishment, not the
site. Design decision: fold `value_kind_name`'s post into `ErrPre` as a named
premise (`ErrPre.kindName : ValueKindName v = s`) — it is a pure-function
readback, cheaply mined/landed as a small callee contract.

## (d) Proving-task decomposition (bounded, ≤1 session each)

1. **T-ERR-restate** (statement): restate `ErrWork` as the 19-field
   `ErrArmResid` structure; wire `hErrFam := ErrWork` (split already exists).
   Template: `rows/ErrFamilyAssembly.lean` + bridge-review named-field mandate.
2. **T-ERR-reach** (×2-3 sessions, batched by shared dispatch): discharge the
   `Reaches` field per arm from the eval/exec computed-jump decode. The jump
   decode lemmas exist (INDEX: "all decode lemmas present"). Template: the
   `hsite` derivation shape + `M4` caller-linkage note. Batch the 19 by their 3
   dispatch origins (eval type-error family, eval arity/depth family, exec).
3. **T-ERR-kindname** (×1): a small `value_kind_name` readback contract feeding
   `ErrPre.kindName`. Template: pure-function callee contract (like `value_null`).

Bounded tasks: **≈5** (1 restate + 3 reach-batches + 1 kindname). The 19
errSite Triples are DONE, so this cluster is the closest to closed.
