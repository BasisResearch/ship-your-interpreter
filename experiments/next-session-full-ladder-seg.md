# Next session — full binary-op dispatch ladder as a `#derive_case` seg

## Goal
Scale the demonstrated exponentiation from a *fragment* to a *full row*. Rebuild the
binary-op comparison arm's **entire** dispatch ladder (`0x8000351c → 0x800036c8`, ending
just before `jal value_bool`) as ONE `#derive_case` seg + `chain_facts` + `segToTriple`,
proving it reproduces the hand row's outcome. Then use the validated pattern to build
**div** (the first genuinely NEW leaf assembled on the combinator, not hand-cloned).

Success = a comparison row (pick `ge` or `lt`) rebuilt on the combinator, green +
axiom-clean, measured against its ~1724-line hand version; then `div` landed the same way.

## Why this is the right next step (read `experiments/exponentiation-endgame-design.md`)
The v2 "auto-threader" already exists: `#derive_case` emits the whole threaded seg
(computed regs / end PC / write-log / fuel / frame from a `(pc,word)` block table, closed
by ONE `ChainOK` decide), and `segToTriple` marshals it into the row `Triple`. The done
eval rows (gt/le/lt/ge/add/sub/mul) predate its adoption and hand-thread `bblock_sound_bt`
(~1724 lines each). Clone-by-reuse does NOT shrink them (measured: ge = 1724 ≈ lt's 1846).
Applying `#derive_case`+`segToTriple` DOES: measured 3.6× on a fragment, ~13× extrapolated.

## The worked template — STUDY THIS FIRST: `Vsa/Sim/CmpArmSeg.lean` (commit 0de8550)
It rebuilds the ge operator-fixup *tail* (`0x800036a4 → 0x800036c8`) this way and is
green + axiom-clean + gated. It shows the exact three-part pattern you will scale up:
1. `#derive_case cmpFixupTail chain [(pc,word)] terminator ⟨…⟩ ;; [ … ] …` — the block
   table with branch/jump terminators (copy terminator tuples verbatim from the existing
   block defs to avoid imm-encoding errors).
2. `cmpFixupTail_facts` — `chain_facts h with "Vsa.Sim.Code.eval_expr_at_"` discharges the
   whole `ChainFacts` bundle; the only leftovers are the branch guards, closed by
   `all_goals rfl` once the op token `x12` is pinned concretely in `L`.
3. `cmpFixupTailRow` — `segToTriple cmpFixupTail L lds pc0 m0 Q hwf hpost`; `hwf` is the one
   `ChainOK` decide, `hpost` projects the outcome (end PC / regs / mem) into the post.

## Gotchas already paid for (do not rediscover)
- **A `/-- doc comment -/` cannot precede a `#derive_case` (or any `#`-command)** — it's a
  parse error ("unexpected token"). Use a plain `/- … -/` block comment before it.
- **`decide` on `ChainOK`/guards fails with "Expected type must not contain free variables"**
  when `L` carries variable register *values* (e.g. `cmpV`, `sret`). Two fixes, both used
  in CmpArmSeg: for guards, pin the token (`x12 = 23#64`) in `L` and close with `rfl`
  (the lookup reduces without forcing the free values); for `ChainOK`, `show ChainOK pc0
  [<explicit key list>] name; decide` (reduce `keysG L` to the literal `[11,12,9]` first).
- **Branch guard polarity is per-operator.** For a resolved path, each `beq`'s taken/not is
  fixed (ge: all three operator beqs fall through; lt: the third is taken). `#derive_case`
  encodes this in the terminator's `.br bop.BEQ <true|false>`.
- **Step counts are auto-computed** by `#derive_case`/`segToTriple` — the hand `u29`/fuel
  bookkeeping (which had an off-by-5 bug in the ge row) disappears. Do not hand-thread it.

## The full ladder structure (from the hand `Vsa/Sim/EvalGeChain.lean` + `EvalLtChain.lean`)
Path `0x8000351c → 0x800036c8`, currently split across these hand theorems (harvest every
`(pc,word)` and terminator from their `def *Lad*`/`mkLine` bodies and `evalXChain_run`):
- `evalGeChain_run` 0x8000351c → 0x80003628 — 16-instr prefix. **Contains the kind-dispatch
  `jr` jump-table (jr@~0x80003558).** `#derive_case` reaches `jr` terminators (design doc
  line 26); confirm the jr target computes from the chain (it's a `CSWTCH`-table load + jr).
- `evalGeLadderAB` 0x80003628 → 0x8000367c region — kind ladder.
- `evalGeLadderC/D` 0x8000367c → 0x80003698 — **operand loads + stack STORES** (`sd …(sp)`).
  `#derive_case` handles stores via the canonical write-log (`out.log`); the row's `hpost`
  reads `writeLog m0 out.log` (non-empty here, unlike the fixup tail). This is the main new
  wrinkle vs the fixup-tail demo — verify the store windows discharge in `chain_facts`
  (they become `MemFacts` leftovers needing the sp-window bounds, like the hand `a_lo/a_hi/
  a_ht/a_al` args to `evalLtLadderD`).
- `evalGeLadderEF` 0x80003698 → 0x800036c0 — the operator beqs + `not` (already in the
  fixup-tail demo).
- `ltLadG` 0x800036c0 → 0x800036c8 — `srli`/`mv` (already in the demo).

Then `jal value_bool @0x800036c8` is the Shape-D seam — NOT part of the `#derive_case` seg;
compose it with `callSeg` (see `Vsa/Sim/DeriveCallSeg.lean`) using `value_bool_spec_full`,
exactly as the hand `blockC_ge` does. The row = `SegPre`-seg (dispatch ladder via
`segToTriple`) ≫ `callSeg` (value_bool) ≫ tiny tail → `PreEpilogueVD`.

## Suggested order
1. **Validate the full ladder on ge/lt** (no new semantics): emit `cmpDispatch` seg for
   `0x8000351c→0x800036c8`, prove `cmpDispatch_facts` via `chain_facts` (the store-window
   MemFacts + branch guards are the leftovers — pin token, supply sp-window bounds), and a
   `cmpDispatchRow` via `segToTriple`. Confirm the computed `out.regs`/`out.log`/end PC match
   the hand `blockC_ge` outcome. **Measure line count** vs `EvalGeChain.lean` (870) +
   the ladder part of `EvalGeRow.lean`.
2. **(optional) Migrate ge** onto it per the migration invariant (keep hand proof until the
   new row is green, delete in the same commit) — only if the shrink is clean.
3. **Build div** (`EvalE.binary .div`, token 14): the arm shares the operand-load+dispatch
   prefix but the tail is the **arithmetic-with-libgcc** shape (`jal __divdi3`, callee spec
   in `Vsa/Sim/DivSpec*` / see `muldi3_spec` pattern in `Muldi3Spec.lean` used by the landed
   `blockC_mul` in `rows/EvalMulRow.lean`, commit 7a96b72). Emit the div dispatch+arith seg
   via `#derive_case`, splice `__divdi3` via `callSeg`, marshal via `segToTriple`,
   concluding `.int (wrap64 (a.tdiv b))` (see `binOpSem` in `Vsa/While/Semantics.lean:266`).
   div then templates mod (`__moddi3`, `a.tmod b`, `:267`); eq/ne swap the seam to
   `value_equal_spec_full` (ValueEqualSpec4, already complete).

## Tooling / references
- `#derive_case` command + `SegEvalState` normal form: `Vsa/Sim/DeriveCase.lean`,
  `Vsa/Sim/SegEval.lean`.
- `segToTriple` (seg→Triple marshalling) + `SegPre`: `Vsa/Sim/DeriveCaseRow.lean`.
- `chain_facts` tactic: `Vsa/Sim/ChainFactsTac.lean` (demo `chainFactsDemo`).
- `callSeg`/`callSegConseq` (Shape-D jal splice): `Vsa/Sim/DeriveCallSeg.lean`.
- Disassembly: `experiments/disasm.txt`. Decode lemmas: `Vsa/Sim/DecodeTable/Batch*` —
  grep `decode_<word>` to confirm each block word has one (all comparison-arm words do).
- `binOpTok` (op→token): `Vsa/MemRepr.lean:62` (add 11 sub 12 mul 13 div 14 mod 15 ne 17
  eq 19 lt 20 le 21 gt 22 ge 23).

## Verification protocol (per repo gates)
- Build incrementally: `lake build Vsa.Sim.<Module>` (warm .lake, no lock contention).
  Do NOT run `lake build` on the whole tree while iterating.
- Axiom check: `lake env lean` on a tiny scratch importing the module with
  `#print axioms <thm>` — must be ⊆ `{propext, Classical.choice, Quot.sound}`.
- Full gate before commit: `scripts/check_all.sh` (build + sorry/native_decide/axiom grep +
  per-theorem axiom audit). Add new capstones to the `THEOREMS` list in `check_all.sh`.
- New file per deliverable; wire `import` into `Vsa.lean`; specific `git add` (never `-A`).
- NO `sorry`/`axiom`/`native_decide`/`bv_decide`.

## State at handoff (commits this session)
`7a96b72` mul · `526f575` ge · `0de8550` CmpArmSeg proof-of-method · docs `4caa98e`/`4b3785e`
/`a8bca35`. Gate: `lake build Vsa` = 1071 jobs green, `check_all` **198/198** axiom-clean.
Binary-op frontier: **div, mod, eq, ne** remain.
