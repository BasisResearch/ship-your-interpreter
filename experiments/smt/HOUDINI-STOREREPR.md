# Houdini on the recursive `StoreRepr` survival IH (Z3 as pure oracle)

Date: 2026-09-02. Tools: Z3 4.15.4 (`z3 -in`, binary; z3py NOT installed).
Harness: `scripts/houdini_ih.py --storerepr` → `experiments/smt/bounded/gen_storerepr.py`
(the recursive-Repr-cone twin of the `.str` pilot in `gen_probe.py`). Whole run <1s.

## Question

`HOUDINI-IH.md` showed a blind Houdini loop rediscovers `cstring_agreeP` for the
`.str` ValueRepr-copy readback. `WLOG-EXTRACT.md` then Z3-closed the FRAME conjunct
of 14/24 supplier fields (incl. the brk/cont exec-leaf `hSBrk`) and deferred one
residual to Houdini: **"recursive `StoreRepr` survival"**. This applies the
validated Houdini IH-loop to that residual.

## Target (shallowest StoreRepr-survival obligation with a landed lemma)

The **brk/cont exec-leaf `StoreRepr` survival** (`hSBrk`, `WLOG-EXTRACT.md`): an
`exec_stmt` arm that KEEPS the frame (no `Store.define`). Its write-log is confined
to the stack window `[SL.lo, sp)`; the arena (`frames_arena`/`closures_arena`) and
the AST/string regions are DISJOINT from that window, so the survival fact is
`AgreeP` over the window's complement. GROUND TRUTH in tree:
`Vsa/Sim/ReprSurvival.lean` **`storeRepr_agreeP`** (line 342), factored as

    storeRepr_agreeP  =  frames-field ∘ frameRepr_agreeP (288)
                             ∘ { valueRepr_agreeP (202), cstring_agreeP (150) }
                         with φf_inj/φc_inj/arena transferred VERBATIM (mem-indep).

`StoreRepr` (`RuntimeRepr.lean:128`) is a named-field structure over the frame and
closure **vectors**; each `FrameRepr` (103) recurses into `ValueRepr`/`CString`
(payload) AND `φf pa` (the **parent frame** — StoreRepr-internal recursion) AND
`ClosureRepr → ExprRepr` (AST, carried as a caller side-condition). Structurally
the same class as `CString` PLUS one extra recursion axis (nested frames).

## Encoding (mirrors `gen_probe.py`, definition-encoded, bounded)

Depth axis over the StoreRepr cone, one frame, one binding:

* **L0/L1** — env header `[e,e+32)` + a `.int` value slot (finite, NON-recursive;
  the null/int analogue).
* **L2** — adds the name `char*` + value inner `char*` as bounded `CString`
  prefixes (W=3) with an OPAQUE tail Bool (the `cstr_*_tail` cut) — the SAME
  CString wall as the `.str` pilot.
* **L3** — adds the **parent-frame link** `read64(e+24)=φf pa ≠ 0` + the parent
  `FrameRepr` as an opaque `frame_par_*` cut — the nested-frame recursion UNIQUE
  to StoreRepr, absent in the flat ValueRepr-copy pilot.

The un-strengthened hypothesis `C` supplies byte-agreement ONLY on the 32-byte env
header (the flat frame-vector survival the write-log frame slice gives); the deeper
per-object windows are the IH.

**Linearity fix (answers the "why did z3 hang / can't you bound it" question).**
`gen_probe.py` reconstructs `read32/read64` as `Σ byte·256^j` (Int) — fine for the
flat copy pilot, but chaining ~7 pointer reads through the StoreRepr cone made Z3
diverge in NONLINEAR arithmetic (measured: single queries pinned a core at 40–55s+
and never returned). Fix: model each read as an UNINTERPRETED function `rd4/rd8`
(linear + UF) and add, per concrete read site, the `readLE_agreeP` congruence
`(∀j<w, m_val[a+j]=mp_val[a+j]) → rd_w m a = rd_w mp a` as a background fact — the
SMT image of `ReprSurvival.readLE_agreeP`. This keeps everything in QF+UF; every
query answers in ≤0.01s. (Bitvector value reconstruction would also bound it, but
survival never needs the numeric value — only read-equality-under-agreement — so
uninterpreted reads are the cheaper faithful model.)

## Results (per depth, all Z3-confirmed, <1s total)

| depth | un-strengthened | positive-model | Houdini survivors | goal-closes |
|-------|-----------------|----------------|-------------------|-------------|
| L0 (hdr+int)   | **SAT** | sat | `valueRepr_agreeP@valhdr[pv,pv+24)` | UNSAT |
| L1 (=L0)       | **SAT** | sat | `valueRepr_agreeP@valhdr` | UNSAT |
| L2 (+CString)  | **SAT** | sat | `valhdr` + `nameptr[pn,pn+8)` + `cstring_agreeP@{name,valstr}[0..2]` + both tails | UNSAT |
| L3 (+parent)   | **SAT** | sat | L2 survivors **+ `storeRepr_agreeP@parent-frame(IH)`** | UNSAT |

* Un-strengthened SAT at every depth = the survival IH is genuinely missing (as the
  `.str` VC was); `positive-model=sat` confirms NON-VACUITY (H∧C∧Cncl consistent).
* All 3–4 noise candidates DROPPED at every depth: `noise@φf_inj(memory-indep)`,
  `noise@arena-bound` (the VERBATIM-transferred fields — correctly seen as
  irrelevant to the survival goal), `noise@force-dst-name-true`,
  `noise@force-dst-parent-true` (the direct-assumption forms).
* The parent-link BYTE window `[e+24,e+32)` was dropped as **subsumed** by the env
  header agreement `[e,e+32)` (it is `⊂` it) — an honest redundancy elimination,
  leaving the genuinely-needed parent-frame IH cut.

### Nested-frame WALL probe (the StoreRepr-specific result)

At L3, supplying EVERY byte-agreement window + both string tails but WITHHOLDING
the parent-frame IH cut:

    all byte-windows, NO parent-frame IH : SAT     (wall: the recursion is open)
    + parent-frame IH cut (survival)     : UNSAT   (the IH closes it)

## Verdict

**Did Houdini rediscover the StoreRepr survival IH? YES**, blind, from the generic
`*_agreeP` window shape + a CTI, without being handed `storeRepr_agreeP`.

**Matched the landed lemma? YES.** The surviving set is exactly the hypothesis list
of `storeRepr_agreeP`/`frameRepr_agreeP` in this bounded vocabulary:
`valhdr` = `valueRepr_agreeP`'s value-slot window; `nameptr` = `frameRepr_agreeP`'s
name-pointer slot; `cstring_agreeP@{name,valstr}` + tails = the two `cstring_agreeP`
calls `frameRepr_agreeP` makes; `parent-frame(IH)` = the recursive `frames`-field
call `storeRepr_agreeP` makes on the parent. The dropped noise candidates map 1:1
to the fields `storeRepr_agreeP` transfers VERBATIM (`φf_inj`/`φc_inj`/`arena`).

**Depth reached: L2 fully (flat frame + CString payload), and L3 modulo one cut.**
The flat frame-vector survival + the CString payload recursion are BOTH rediscovered
and Z3-closed. At L3 the nested-frame recursion is closed only with the
`parent-frame(IH)` cut supplied as an equality hypothesis.

**Vocabulary sufficient? YES for selection — no LLM-proposed shape needed.** Every
surviving predicate is the generic `region_agree`/window shape instantiated at a
CTI-mined address; Houdini SELECTS the right subset. As in the pilot, it does not
INVENT the window shape (standard Houdini contract), and the recursion cuts
(`cstr_*_tail`, `frame_par`) are opaque — Houdini distinguishes the honest EQUALITY
cut from the `force-*-true` direct-assumption via the same drop-priority rule.

## Honest wall location — deeper than CString, and exactly where

StoreRepr is a HARDER wall than CString, by ONE recursion axis:

1. **CString axis (L2):** identical to the pilot. The bounded prefix closes; the
   tail is an opaque cut requiring the `cstring_agreeP` hypothesis past the cut. Not
   new.
2. **Nested-frame axis (L3):** NEW to StoreRepr and the true additional wall. The
   `φf`-parent link makes `FrameRepr` recurse into ANOTHER `FrameRepr`; the
   WALL-probe shows that **no amount of byte-window agreement closes it** — it stays
   SAT until the parent-frame survival is supplied as its own IH cut. This is the
   self-referential `frames`-field recursion of `storeRepr_agreeP`. Bounded Houdini
   REACHES it (rediscovers that the cut is needed and that the equality form is the
   honest one) but, exactly as with CString, cannot CLOSE the recursion — that
   remains the Lean structure's job (`storeRepr_agreeP`'s `frames fa hfa := …`
   recursion, terminating on the finite `s.frames.size`).
3. **ExprRepr/closure axis (not exercised):** `ClosureRepr → ExprRepr` over the AST
   subtree is, in the LANDED lemma, ALREADY a caller side-condition (`hcloexpr`/
   `hexpr'`), not a closed recursion — so it is a HYPOTHESIS by design, and bounded
   Houdini would (correctly) surface it as another opaque equality cut, not a
   provable obligation. Left out of the probe because the landed lemma does not
   close it either.

**Precise statement:** Houdini reaches the flat frame-vector survival AND the
CString-payload survival, and Z3-confirms both close; it reaches — but does not
close — the nested-frame (`φf`-parent) recursion, which is the exact point where
StoreRepr goes one level deeper than the flat ValueRepr-copy pilot. That is the
honest wall.

## On the user's "quickly validate IHs with bounded runs to build confidence"

This IS that: a candidate IH (e.g. a proposed `frameRepr_agreeP` variant) is
validated in ≤0.01s by a bounded run — the un-strengthened SAT proves the IH is
load-bearing, the WALL probe proves WHICH conjunct is load-bearing, and the
`goal-closes UNSAT` proves sufficiency at bounded depth. It is a confidence oracle,
NOT a proof: bounded UNSAT (fixed depth k, W=3) does not discharge the Lean
obligation — it flags a sufficient-at-depth IH and pinpoints the recursion cut to
hand to the Lean stack. Keep runs finite via uninterpreted linear reads (here) or
bounded bitvectors; never let the nonlinear Int reconstruction chain (that was the
hang).

## Files

* `experiments/smt/bounded/gen_storerepr.py` — the StoreRepr-cone bounded encoder +
  Houdini loop + nested-frame WALL probe.
* `scripts/houdini_ih.py --storerepr` — wired driver (pilot + supplier batch intact).
* Ground truth: `Vsa/Sim/ReprSurvival.lean` `storeRepr_agreeP`/`frameRepr_agreeP`/
  `valueRepr_agreeP`/`cstring_agreeP`; `Vsa/RuntimeRepr.lean` `StoreRepr`/`FrameRepr`.
