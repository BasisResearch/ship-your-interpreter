# Implementing the block abstractions (A/B/C/D) and refactoring the proofs

A staged, green-throughout plan to build the four abstractions from
[block-reflection-plan.md](block-reflection-plan.md) and migrate the existing
proofs onto them. Each sub-stage is independently committable and gated.

## Key finding that reshapes Stage A

The program logic already exists. `Vsa/Triple.lean` defines
`Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'` over `Config = ⟨σ, tick,
steps⟩`, with `of_imp`, `of_step`, `conseq`, `seq`, `cases`, `exists_pre`,
`loop` (this is Layer 1 of `PLAN-InterpSim.md`). `value_int_spec` and
`blockC_neg` are *already* stated as `Triple`s.

So Stage A is not "invent a block Hoare logic". It is: restate each block lemma
as a `Triple`, compose with the existing `seq`/`conseq`, and add the one missing
rule (`frame`). The call seam composes via `seq` because `value_int_spec` is
already a `Triple`.

## Constraints (all stages)

- Green frontier throughout. Build each helper, prove it green and axiom-clean,
  then refactor its consumers. Keep the old proof until the new one is green —
  the pattern used across this whole migration.
- Elaboration stays flat. Composition is lemma application (`seq`/`conseq`/
  `frame`); the `decide` VC stays at block leaves. Record the elab-time delta per
  stage; a >~10% rise means a stray `simp`/search crept in.
- Gates on every commit: `lake build`; `scripts/check_all.sh` (no `sorry`/
  `native_decide`/`axiom`; `#print axioms` ⊆ {`propext`, `Classical.choice`,
  `Quot.sound`} on `blockC_neg` and every new block triple).

## Stage C — discharge helpers (do first; smallest; no new theory)

Extend `Vsa/Sim/BlockTactics.lean` (or a sibling `BlockTactics2.lean`).

- **C1 frame discharge.** Lemma `abiNoise_noiseRegs : AbiPreservedNoise R →
  ∀ rr ∈ noiseRegs, (rr == R) = false` (rcases the seven). Tactic `block_frame_wr`
  closing `∀ n ∈ wrRegsM b.body, (gprReg n == R) = false` by
  `intro n hn; simp only [<wrRegs reduction>, List.mem_cons, …] at hn;
  rcases … <;> first | exact abi_ne' (by decide) | assumption` (the `assumption`
  arm picks up the callee-saved exceptions like `he8`). An `hframeG` entry then
  reads `have f_X : σ'.R = σ.R := hframeBlk R (abiNoise_noiseRegs hR)
  (by block_frame_wr)` — ~10 lines to ~1.
- **C2 register projection.** `block_reg hGH n` = `gholds_lookup (runGM …) hGH rfl`,
  where `rfl` computes `lookupG n (runGM …)`. Replaces positional
  `hGH.2.2.2.1` and its fragility.
- **C3 bundle discharge.** `ld_ok`/`st_ok` elaborators that assemble an `LdOK`/
  `StOK` from an address-normaliser lemma + pin proofs. Call site becomes
  `ld_ok haddr152 [hpb0..hpb7]`.

Refactor targets in `EvalNegSim2.lean`: the three `hframeG` collapses (C1), every
block-output projection (C2), the load/store bundles at the three call sites (C3).
Commit each helper, then the refactor. Payoff: per-migration glue roughly halved,
no structural change.

## Stage B — reflected disassembly (parallel to C; independent)

New `Vsa/Sim/BlockDecode.lean`.

- **B1** `bsplit : BitVec 32 → BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8` and
  `decodeM : BitVec 32 → Option MInstr` for the nine `MKind`s (opcode/funct3/
  funct7 slice). ~50 lines.
- **B2** soundness: `decodeM w = some a` implies `a.word = w` and `astOfM a`
  matches `DecodeTable.decode_w`. A general theorem, or a per-word `by decide`
  corollary. `block_facts` still runs the decode check, so `decodeM` only has to
  be *right* — wrong fields make the block lemma unprovable.
- **B3** `mkLine pc w : MInstr := { pc, word := w, bsplit w, decodeM w … }`, or a
  `blockLine%` elaborator. A `BBlock` becomes a list of `mkLine pc w`.

Refactor: rewrite `negLoadStoreBlk`/`negPrologueBlk`/`negTailBlk*` as `mkLine`
lists (drop the hand-written kind/rd/rs1/rs2/imm). Retire the two prototype
lemmas (`neg_loadstore_block`/`_tac`) once transcription is free. Payoff: removes
`BBlock` transcription and the field/decode-mismatch class.

## Stage A — restate blocks as triples and compose (the multiplier)

New `Vsa/Sim/BlockLogic.lean` (thin; reuses `Vsa/Triple.lean`).

- **A0 wrap.** Each block lemma already yields `∃ σ' i' u', Steps ⟨σ,i,u⟩
  ⟨σ',i',u'⟩ ∧ …`. Restate as `Triple blkPre blkPost` with `blkPre`/`blkPost :
  Config → Prop` over `⟨σ, tick, steps⟩` (tick`< 2` lives in the assertions).
  Thin adapters `<lemma>_triple`.
- **A1 compose (uses existing `seq`/`conseq`).** Rewrite `blockC_neg`'s spine as
  `prologueT.seq (loadstoreT.seq (tailT.seq (callT.seq epilogueT)))`, with
  `Triple.conseq` at each seam absorbing the marshalling (`bytesVal`↔`payV`, the
  `m1/m2/m3` tower bridge, `v + sext 0 = v`). The `Steps` tower, the output-to-
  input rebridging, and the minstret/`GoodState`/`sailOutput` threading all
  vanish into `seq`. `callT` is `value_int_spec` — already a `Triple`.
- **A2 `Triple.frame` (the one new rule).** `Triple P Q → Stable F (footprint) →
  Triple (P ∧ F) (Q ∧ F)`, folding the register frame (`hframeBlk`) and the
  memory survival (`writeLog_agreeP_disjoint`) into one separation rule. Prove
  once in the `Triple` namespace. Refactor `hframeG` and the survival section
  onto it — two ad-hoc mechanisms become one.

Refactor: the `blockC_neg` spine (A1) then its frame/survival (A2). Large rewrite;
keep the old proof until the new one is green. Payoff: an N-block domain proof is
N block-triples + O(1) `seq`/`conseq`/`frame` glue; the call seam and both frame
mechanisms are rules, not inline work.

## Stage D — meta-generation (last; needs A/B/C stable)

New `Vsa/Sim/BlockGen.lean` (elaborator).

- **D1** `#gen_block name (pc,word)-list entryPre exitPost` emits
  `theorem name : Triple entryPre exitPost := by obtain … := bblock(s)_sound_bt …;
  block_facts …; <block_reg / block_frame>`. Uses B's `decodeM` for the block, C's
  tactics for the leaves, A's `Triple` shape.
- **D2** regenerate the block triples from `(pc,word)` + spec; diff the proofs.

Payoff: authoring a block = write the `(pc,word)` list and the pre/post; the rest
is generated.

## Refactor sequencing and risk

- Order: **C ∥ B** (both independent, quick), then **A** (uses C's tactics,
  benefits from B), then **D** (needs all three).
- Never half-migrate `blockC_neg`. Each refactor: helper green + axiom-clean →
  migrate one consumer → green → commit. `git` keeps it revertible.
- Elaboration budget: record `EvalNegSim2` + block-file elab time at each stage.
  `seq`/`conseq`/`frame` are lemma applications; the leaf `decide` is unchanged.

## Keep the master PLAN updated as abstractions land

`PLAN-InterpSim.md` is the entry point M5/M6 read first. Its Layer 1 is the
`Triple` program logic; its Appendix (2026-08-25) holds the per-segment pipeline
and the Tooling list. These must track the abstractions, not lag them.

After each stage lands (green + committed), in the *same or immediately following
commit*:

- **Layer 1** — record any new `Triple` rule. Stage A2 adds `frame`; the program
  logic grew, so the layer that documents it grows.
- **Appendix pipeline / Tooling** — replace the current per-segment recipe with
  the new one, keeping the "use in this order" list current: Stage C adds
  `block_frame`/`block_reg`/`ld_ok`; Stage B adds `mkLine`; Stage A makes the
  segment a `Triple` composed by `seq`/`conseq`/`frame`; Stage D makes it
  `#gen_block`. An M5/M6 agent reading the pipeline should always see the latest.
- **Milestones** — tick the abstraction done and name its consumers.
- Mirror the one-line durable record into `memory/block-reflection-tooling.md`,
  and update the stage status at the top of this doc.

Rule: never let `PLAN-InterpSim.md` describe superseded tooling. A landed
abstraction that the PLAN still ignores is a half-landed abstraction — downstream
agents will re-derive the old, longer path.

## Payoff projection

- After C: per-migration glue roughly halved.
- After B: `BBlock` transcription gone.
- After A: the spine is `seq`/`conseq`/`frame`; the call seam and both frame
  mechanisms are rules; `blockC_neg`'s spine is on the order of a dozen lines.
- After D: a block is a `(pc,word)` list plus its pre/post.

## Stage status

- [ ] C1 frame discharge · [ ] C2 block_reg · [ ] C3 ld_ok/st_ok · [ ] C refactor
- [x] B1 decodeM · [x] B2 soundness (light: per-word `rfl` defeq examples) · [x] B3 mkLine · [x] B refactor (neg blocks on `mkLine`; prototype lemmas `neg_loadstore_block`/`_tac` retired)
- [x] A0 wrap (`negPrologue_triple`/`negLoadStore_triple`/`negTail_triple` in `Vsa/Sim/BlockLogic.lean`) · [x] A1 compose (`neg_blocks_triple` = full σ0→σ15 3-block spine as ONE `Triple.seq`/`conseq` chain; two seams — prologue→loadstore + the new loadstore→tail, absorbing the kind-int/payload bridges and `Eval_exprLoaded`/`LdOK4` survival across the three error stores via `writeLog_getElem_disjoint`) · [x] A2 block-triple Posts carry **real entry-frames** (assertion-carried framing: each block Post/Pre takes an `entryRegs` ghost and the frame conjunct is `c.σ.regs.get? R = entryRegs R` under the block's noise/wrRegs guards, not the tautology `= c.σ.regs.get? R`; `neg_prologue_loadstore_triple`/`neg_blocks_triple` `.trans`-compose the σ15↔σ10↔σ4↔σ0 frames at each seam under the union of the blocks' guards — no unsound generic `Triple.frame`) · [x] A refactor (`blockC_neg` consumes `neg_blocks_triple`: the three per-block `obtain`s + inter-block seams — kind-dword/payload bridges, `Eval_exprLoaded`/`LdOK4` survival across the error stores, the `m3` tower defeq `writeLog`↦`writeMap8` — collapse into ONE spine application; `hframeG`'s f_pro/f5/f_tail collapse to one `f_spine := hframeSpine …` discharging all three wrRegs guards via `block_frame_wr`; the block Posts also gained a threaded `out0`/sailOutput survival so the composed spine still exposes `σ15.sailOutput = c.σ.sailOutput`; EvalNegSim2 −20 lines; `blockC_neg` axiom-clean)
- [x] D1a #gen_block (`Vsa/Sim/BlockGen.lean`: `#gen_block <name> [(pc,word),…] (terminator <TInstr>)?` emits `def <name> : BBlock := {body := [mkLine pc w,…], term := …}` via command quotation + `elabCommand`; body reuses Stage B `mkLine`, so kind/rd/rs1/rs2/imm are derived, not transcribed; terminator keeps a hand `TInstr` literal, as in Stage B) · [x] D2 regenerate (`negLoadStoreBlkGen = negLoadStoreBlk` and `negPrologueBodyGen = negPrologueBlk`, both `by rfl` — generated blocks are *definitionally equal* to the audited hand blocks) · [~] D1b `#gen_block_sound` (STRETCH, partial): emits `def <name>` + `theorem <name>_sound` for a load-free fall-through block (`genDemoBlk`/`genDemoBlk_sound`, three `addi`s), `obtain … := bblock_sound_bt <name> …` exposing the `Steps` chain / computed end PC / `GHolds`/frame; axiom-clean {propext,Classical.choice,Quot.sound}. Blocker: the data-dependent leaves (`BBlockFacts` memory/guard facts, the per-register projections) cannot be synthesised from `(pc,word)` alone — they stay as the emitted theorem's HYPOTHESES (`hfacts`) and residual `GHolds`, exactly as the plan acknowledges. Full parameterised soundness (loads/stores/branch terminators) is future work.
