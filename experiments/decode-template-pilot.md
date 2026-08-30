# Decode-table per-lemma template speedup (pilot)

Goal: cut the per-lemma cost of the 530 `Vsa/Sim/DecodeTable/Batch*.lean`
files (the single biggest build cost, 31,627 s CPU = 80% of the tree). Each
lemma proves, under 3 register pins, `(ext_decode W).run σ = .ok <instr> σ`
for one ground 32-bit word W.

## Result

**7.2x on the pilot file** (`Batch16Part13.lean`, 16 lemmas):
`time lake env lean` user time **35.88 s → 4.96 s**; wall **6.7 s → 1.48 s**.
Per-lemma ~2.5 s → ~0.25 s. All statements byte-identical to HEAD; all lemmas
axiom-clean (`{propext, Classical.choice, Quot.sound}`); no
sorry/native_decide/bv_decide.

## Root-cause diagnosis (profiler)

Baseline single lemma (`decode_fead8fa3`, `set_option profiler true`):
- old template `simp_all [...]` = 1.55 s, second `simp +decide [...]` = 0.165 s.

New minimal proof = one grounding `simp only [ext_decode, encdec_backwards,
EStateM.run, bind/pure/…, PreSail.readReg, get/getThe/…, currentlyEnabled,
hartSupports, get_xLPE, Vsa.Sim.initMisa, <3 pins>]` then `rfl`. This grounds
every register read to its pinned constant (misa=initMisa, priv=Machine,
mseccfg=0), collapsing the whole monadic decode tower to a ground term threaded
on σ; `rfl` (kernel) then evaluates the ground `if`/`match` tower on the
literal word. `simp only + rfl` on its own: **2.47 s** isolated.

Fine profiler (`trace.profiler`) on that 2.47 s: the dominant cost is a *single*
`Meta.realizeConst` of **`currentlyEnabled.match_1.splitter` = 1.16 s** (plus
`hartSupports.match_1.splitter` 0.10 s) — the auto-generated match-splitter for
`currentlyEnabled`'s giant `match` on the `extension` enum. This is realized on
first use **per module**. Confirmed by amortization: within one file,
1 lemma = 2.47 s, 4 lemmas = 3.64 s ⇒ first lemma pays ~1.6 s for the splitter,
each later lemma only **~0.39 s**.

## Fix: pay the splitter once, in `DecodeCommon.lean`

`Vsa/Sim/DecodeTable/DecodeCommon.lean` contains one seed lemma proved by the
exact per-word template. Elaborating it realizes both splitters into
`DecodeCommon.olean`. Every per-word file now does `import
Vsa.Sim.DecodeTable.DecodeCommon`; importers reuse the persisted splitters and
pay **0 s** for realization.

Effect (1 lemma, isolated): **2.45 s → 0.52 s** (incl. import). Full pilot file
(16 lemmas): **4.96 s** user.

## Measurements per variant tried

| variant | user time | note |
|---|---|---|
| baseline (`simp_all`+`simp +decide`+And.intro/omega), 16 lemmas | 35.88 s | HEAD |
| grounding `simp only` + `rfl`, 1 lemma isolated | 2.47 s | 1.6 s of it = splitter |
| same, config `{ground:=true}` | 3.59 s | worse |
| same, config `{ground:=true,decide:=true}` | 3.17 s | worse |
| same, config `{singlePass}` / `{index:=false}` | rfl fails | not fully reduced |
| `unfold` then `simp only` (encdec_backwards out of set) | 1.44 s tac | splitter still paid |
| dropping `currentlyEnabled`/`hartSupports` from set | rfl fails | reads not grounded |
| **grounding `simp only`+`rfl`, importing DecodeCommon, 1 lemma** | **0.52 s** | splitter reused |
| **full pilot file, importing DecodeCommon, 16 lemmas** | **4.96 s** | **7.2x** |

## Final per-lemma profiler breakdown (importing DecodeCommon)

`simp only` (rewrite engine) ~90 ms + `rfl`/type-check ~25 ms; no `realizeConst`
(reused from the import). Amortized ~0.25 s/lemma across the file (import
overhead ~1 s shared).

## Robustness

The `simp only + rfl` finisher was verified against one representative word of
**every reachable instruction class**: JAL, ITYPE, UTYPE, JALR, LOAD, STORE,
BTYPE, ADDIW, SHIFTIOP, SHIFTIWOP, RTYPE, RTYPEW — all close (see
`/tmp/decode_pilot/allclasses.lean` recipe). No word reaches an `mstatus` read
under the pins (grep of the symbolic-`w` grounded term: 0 residual reads), so
the read set really is just misa/cur_privilege/mseccfg, all pinned.

## Approaches that did NOT pan out

- **Read-independence generic lemma** `(ext_decode w).run σ = .ok (pureDecode w)
  σ`, `pureDecode w := extract ((encdec_backwards w).run pinnedσ)`: proving it is
  fine, but reducing `pureDecode <word>` per-word requires evaluating
  `pinnedσ.regs.get?` on an `Std.ExtDHashMap`, which does **not** reduce by
  `rfl`/`simp` (no cheap `get?_insert` reduction for `Register`). Dead end.
- Copying the 417-line grounded tower into a hand-written pure `def`: the
  profiler-elided (`⋯`) term can't be pasted, and the win was already captured
  more cheaply by the splitter-caching insight.
- Simp `Config` tweaks (ground/decide/singlePass/memoize/index): none beat the
  default; several break the finisher.

## Generator

`experiments/gen_decode_table.py`:
- default now emits the fast template (`TEMPLATE_FAST`) and adds
  `import Vsa.Sim.DecodeTable.DecodeCommon` to each part's header.
- `--legacy` re-emits the original template (`TEMPLATE_LEGACY`) with no
  DecodeCommon import — verified byte-identical to HEAD `Batch16Part13.lean`.
- Fidelity: regenerating `Batch16Part13.lean` (default) is **byte-identical** to
  the hand-written validated pilot.

## Deliverables

- `Vsa/Sim/DecodeTable/DecodeCommon.lean` (new; must be built/imported first).
- `Vsa/Sim/DecodeTable/Batch16Part13.lean` (rewritten pilot).
- `experiments/gen_decode_table.py` (fast default + `--legacy`).

The other 529 batch files are left unchanged for the coordinator to fan out
(regenerate with `python3 experiments/gen_decode_table.py`; ensure
`DecodeCommon` is built before the batches). Expected fan-out saving: from
~31,627 s CPU toward ~1/7 of that, i.e. roughly a 25,000+ s CPU reduction.
