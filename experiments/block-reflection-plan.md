# Block-reflection migration — abstractions and roadmap

How to collapse a hand-threaded `StepObs` battery onto block reflection with the
least redundant work, and where the next abstractions should go.

Written after migrating all of `blockC_neg`'s σ0→σ15 machine path (three block
applications; `EvalNegSim2.lean` 873→605). The proof that motivates every claim
here is that file.

## 1. The abstraction stack (reuse these)

The reflection layer already computes the hard part. A block application runs
`runGM`/`writeLog`/`endPCB` in the kernel and returns the whole step chain,
every register, the memory, and the frame in one `decide`-backed term. Nothing
below searches; elaboration stays at 1–3s per block.

- **Straight-line + terminator run.** `block_mem_sound` (`BlockMem.lean`),
  `bblock_sound_bt` (`BlockTerm.lean:782`). One block: body `List MInstr` +
  optional branch/jump terminator.
- **Contiguous chain.** `bblocks_sound_bt` (`BlockTerm.lean:1012`). A
  `List BBlock` whose terminators line up (`ChainOK` = `TermChainO`: each
  terminator target equals the next block's start PC). Handles taken/not-taken
  branches mid-chain.
- **Mechanical VC discharge.** `block_facts` tactic (`BlockTactics.lean`) —
  every code-byte pin + decode, from the instruction literal. Leaves exactly the
  data-dependent leaves: load `MemFacts` and branch guards, one bullet each.
- **Bundled side-conditions.** `LdOK8` / `LdOK4` / `StOK8` (`NegBlockProto.lean:207`).
  One hypothesis per load/store instead of five (RAM lo/hi + HTIF-disjoint window
  + alignment + pins). Defeq to the `MemFacts` leaf, so the `block_facts` bullet
  is `exact h`.
- **Memory survival.** `writeLog_agreeP_disjoint` (`BlockAdapter.lean:72`) — a
  `writeLog` fold agrees with the entry memory on any region disjoint from the
  store windows. Feeds `read64_agreeP` / `StoreRepr` survival.
- **Register projection.** `gholds_lookup` (`BlockPilot.lean:448`) — `(n,v) ∈ L`
  gives `σ.regs.get? (gprReg n) = some v`. The block hands back
  `GHolds σ' (runGM …)`, a concrete conjunction you project positionally.
- **Adding an ALU kind.** Mirror `.add` in ~6 sites: `MKind`, `astOfM`, `wvalM`,
  `MemFacts`, `KindOK` (+ `Decidable`), the `block_mem_sound` induction case, and
  three `cases akind` in `BlockTerm`. The compiler's "Alternative X not provided"
  pinpoints each. The `execute_rtype_*_char` lemma usually already exists
  (`ExecuteAlu.lean`). Non-store kinds fall through `stepGM`/`wrRegsM`/`stepLdsM`'s
  `_` arm — no edits there. Worked example: `.sub` (commit `15f82ad`).

## 2. Migration cookbook

For a straight-line-plus-terminator segment σ_a → σ_b:

1. Write the `BBlock`(s): body `MInstr` literals `⟨pc, word, b0..b3, kind, rd,
   rs1, rs2, imm⟩` + terminator. Read the words off the `stepObs_*` site calls or
   the disassembly.
2. State a block lemma: entry register pins, one `LdOK`/`StOK` per memory op,
   outputs projected from `runGM` order (most-recently-written first; regs already
   in the pin list `L` are carried, so project them too — no frame needed).
3. Prove it: `obtain … := bblock(s)_sound_bt …`; `block_facts h with "<prefix>"`;
   the remaining bullets are `exact hLd`/`exact hSt` and any branch guard
   (`show guardB … = <bool>; …; decide`). Expose the block frame in the conclusion
   for the caller's frame collapse.
4. Splice at the call site: discharge each bundle (`⟨⟨by rw [haddr]; omega, …⟩,
   pins⟩`), bridge outputs (defeq for `bytesVal`↔payload; normalise computed regs
   like `v + sext 0`), bridge memory (`writeLog` ≡ the domain tower by `rfl`, or
   the `AgreeP` adapter), collapse the frame (one `hframeBlk` application), splice
   the `Steps` tower.

Recurring manual cost, ranked (this is what the roadmap attacks):

1. **Boundary marshalling** — bridging a block's outputs to the next block's
   inputs and to the domain facts: `bytesVal`↔`payV`, the `m1/m2/m3` tower, the
   `Eval_exprLoaded`/`Value_intLoaded` survival, computed-reg normalisation.
2. **The call seam** — a `jal` to a function with its own spec (`value_int`).
   Not a block terminator; composed by hand.
3. **Frame collapse** — the `noiseRegs`/`wrRegs`-from-`AbiPreservedNoise`
   discharge, ~10 lines per collapsed segment.
4. **Output projection** — positional `hGH.2.2.2.1` counting; fragile.
5. **`BBlock` transcription** — hand-copying kind/rd/rs1/rs2/imm from the word.
6. **`Steps` tower splice** — re-bracketing the `.trans` chain.

Reflection already removed the big cost (per-step `obs_*_other` carries). What
remains is glue. The reflection layer is sound and complete for what it covers;
the glue is where a human still reads and writes.

## 3. Further abstractions (roadmap)

Ordered by leverage. Each keeps elaboration flat by construction: the
`decide`-heavy VC stays at the block leaves, and composition is proof-term
(lemma application), never re-run search.

### A. A block Hoare logic — the compositionality multiplier

The block lemmas are already triples in disguise: `pre-registers → Steps → post
facts`. What is missing is the *composition rules* that thread the plumbing. Lift
to an explicit judgement and prove the rules once:

```
-- abstract state: the ghost register map + memory the domain reasons about
def BState := GRegs × Mem
def BTriple (P : BState → Prop) (blk : Segment) (Q : BState → Prop) : Prop := …
--   ∀ σ realising P, running blk reaches σ' realising Q, with the machine
--   Steps/minstret/GoodState/output bookkeeping inside the definition.

theorem btriple_seq   : BTriple P a Q → BTriple Q b R → BTriple P (a ++ b) R
theorem btriple_frame : BTriple P blk Q → Disjoint (footprint blk) F →
                        BTriple (P ∗ F) blk (Q ∗ F)
theorem btriple_conseq: (P' ⊢ P) → BTriple P blk Q → (Q ⊢ Q') → BTriple P' blk Q'
theorem btriple_call  : CalleeSpec f Pre Post → BTriple (pre-of Pre) [jal f] (post-of Post)
```

What each rule removes:

- **`seq`** folds the `Steps`-tower splice, the minstret/`GoodState`/`sailOutput`
  threading, and the output-to-input rebridging into one lemma. `blockC_neg`'s
  three applications + hand glue become `t_pro.seq t_ls |>.seq t_tail`. This is
  the general composition `bblocks_sound_bt` does *not* give: it composes across a
  far taken branch (post ⟹ pre, PC-agnostic) and does not require contiguity.
- **`frame`** subsumes *both* the register frame (`hframeBlk`) and the memory
  survival (`writeLog_agreeP_disjoint`) as one separation-logic rule. Two ad-hoc
  frame mechanisms become one. Attack the class, not the instance.
- **`conseq`** absorbs the marshalling — `bytesVal`↔`payV`, `v + sext 0 = v`, the
  tower bridge — at the pre/post boundary, where it is a one-off entailment rather
  than repeated inline.
- **`call`** abstracts the `value_int` seam: given the callee's spec, the `jal`
  is just another triple. The last hand-threaded thing in `blockC_neg` becomes a
  rule application.

Elaboration: `BTriple` is a `Prop`; the rules are lemma applications. The
`decide` VC lives in the leaf triples (proved once via `bblock_sound_bt`). No
tactic search in composition → flat. Upfront cost is O(1) — define `BTriple`,
prove four rules — and it pays back across every future migration (M5/M6, the
other leaf/epilogue proofs). This is the highest-leverage item.

### B. Reflected disassembly — `decodeM : BitVec 32 → MInstr`

Compute the `MInstr` fields from the 32-bit word by a verified `decodeM`, proven
consistent with `astOfM`/the machine decoder. A block becomes a list of
`(pc, word)` and the kind/rd/rs1/rs2/imm come out by `rfl`. Removes cost #5 (hand
transcription) and the class of field/decode-mismatch bugs. Elaboration:
kernel computation of a bit-slice per word — cheap; verify `decodeM`↔decode once,
not per block.

### C. Discharge tactics/lemmas for the mechanical leaves

Quick wins that cut the per-migration cost without any new theory:

- `block_frame` lemma: `AbiPreservedNoise R → (wrRegs blk ⊆ caller-saved) →` the
  `noiseRegs`/`wrRegs` conditions, closing the `hframeBlk` arguments in one
  application. Kills cost #3 (the 10-line `intro/rcases`).
- `block_reg hGH n`: project register `n` by computing `lookupG n (runGM …)`
  (`decide` the membership) instead of counting `hGH.2.2.2.1`. Kills cost #4 and
  its fragility.
- `ld_ok haddr pins` / `st_ok haddr` tactic: discharge an `LdOK`/`StOK` bundle
  from the address-normaliser + pin hypotheses. Shrinks the call site.

All are `rw`/`decide`/`omega` — cheap, no search.

### D. Meta-generation (last)

Once the block-lemma shape is stable, a `#gen_block` elaborator emits the lemma
statement + proof skeleton from the `(pc, word)` list and an entry/exit spec.
Removes the boilerplate. Compile-time generation; the emitted proof is what a
human would have written.

## 4. Elaboration guards (do not regress)

- Keep `decide`/`rfl`/kernel reduction on hot paths. No `simp`/`omega` *search*
  where a computation suffices.
- No typeclass-driven reflection — instance search does not stay flat.
- `native_decide` is forbidden by `check_all` (stage b).
- The `decide` VC (`BBlockOK`/`ChainOK`) belongs at block leaves only.
  Composition rules must be proof-term, never a re-run `decide`.

## 5. Priority

1. **B/C tactics and lemmas** (`block_frame`, `block_reg`, `ld_ok`, `decodeM`).
   Days of work, immediate per-migration savings, no new theory.
2. **A, the block Hoare logic.** The structural win. Turns N-block domain proofs
   from O(N) manual threading into O(N) triple applications with O(1) glue, and
   folds the call seam and the two frame mechanisms into rules. Do this before
   M5/M6 scale the number of blocks.
3. **D meta-generation** once A/B/C have fixed the shape.

The through-line: reflection already made each block cheap; the next gains come
from making the *composition* cheap. A program logic is how you buy that without
paying elaboration time — the plumbing moves from per-proof tactic work into
once-proved rules.
