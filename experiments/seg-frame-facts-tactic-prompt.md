# Prompt: build the `seg_frame_facts` tactic

Hand this to a fresh coding session (ideally via `/prover-workflows`) working in
`/Users/kirancodes/Documents/code/verified-semantic-abstraction`. Read the memory
`fast-reflection-rules` and `full-ladder-seg-and-div` first; they are binding.

## Objective

Write a Lean 4 tactic **`seg_frame_facts`** that discharges the frame-window
residual `chain_facts` leaves when proving a `#derive_case` segment's `ChainFacts`
bundle, using ONE `FrameBundle`. It is the companion to `chain_facts`
(`Vsa/Sim/ChainFactsTac.lean`, `elab "chain_facts " h:term " with " pfx:str`):
`chain_facts` strips every decode/byte-pin leaf and leaves the pure frame-geometry
`MemFacts` (one per ld/sd) plus the seg's data-dependent branch guards.
`seg_frame_facts` closes all the frame windows. Together they reduce a real arm's
`SegPre` construction to one `FrameBundle` + the seg's genuine semantic guard (e.g.
`Wr ≠ 0` for div), replacing the ~200-line `spill_addr`/`read64_bytes`/
`writeMap8`-disjoint ritual every `blockC_*` row hand-writes.

This is the top of the exponentiation ladder: write once, discharge every binary-op
arm's `SegPre` (div/mod/eq/ne share the same 1088-byte frame) and any sp-relative
window elsewhere (recursive M4 arms, M5 error-site reads).

## Building blocks (ALL LANDED, axiom-clean — reuse, do not reinvent)

`Vsa/Sim/SegFrameFacts.lean` (already committed):
- `structure FrameBundle (m) (base : BitVec 64)` with fields `pop : ∀ k, ∃ w, m[k]? = some w`,
  `lo : 0x80000000 ≤ base.toNat`, `hi : base.toNat + 0x108 ≤ 0x100000000`,
  `htif : tohostAddr + 16 ≤ base.toNat`, `al : base.toNat % 8 = 0`.
- `frame_ea (a L base off) (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend a.imm).toNat = off) (hoff : off ≤ 0x108) (fb) : (eaddrM a L).toNat = base.toNat + off`
- `memFacts_ld_frame (m L a b0..b7) (hk : a.kind = .ld) (hlo hhi hht hal) (p0..p7 : m[(eaddrM a L).toNat + i]? = some bi) : MemFacts m L [b0..b7] a`
- `memFacts_sd_frame (m L a bs) (hk : a.kind = .sd) (hlo hhi hht hal) : MemFacts m L bs a`
- `frame_ld (m L a base off fb) (hk hsrc himm hoff hoff8) : ∃ bs, MemFacts m L bs a` (reads bytes from `fb.pop`, returns them for the seg's `lds`)
- `frame_sd (m L a base off bs fb) (hk hsrc himm hoff hoff8) : MemFacts m L bs a`

Definitions to unfold: `MemFacts` (`Vsa/Sim/BlockMem.lean:590` — ld = `(bounds) ∧
LPins8`, sd = `bounds`, ALU = `True`), `eaddrM = srcVal a.rs1 L + sign_extend a.imm`
(`BlockMem.lean:462`), `srcVal` (`BlockPilot.lean:270`), `stepMemM`
(`BlockMem.lean` — store = `applyW`/`writeMap8`, load/ALU = `m` identity),
`ChainFacts` (`BlockMem.lean`, recursion `BBlockFacts ∧ ChainFacts (writeLog …) …`).

Threading lemmas: `writeLog_getElem_disjoint (k) (log m) (hw : widths∈{1,4,8}) (hdisj : ∀e∈log, k<e.1 ∨ e.1+e.2.1≤k) : (writeLog m log)[k]? = m[k]?` (`Vsa/Sim/BlockAdapter.lean:51`), `getElem?_writeMap8_out (mem k d a) (a<k ∨ k+8≤a) : (writeMap8 mem k d)[a]? = mem[a]?`.

## The residual (measured — build your tactic to close exactly these)

After `chain_facts h with "Vsa.Sim.Code.eval_expr_at_"` the open goals are, in order,
one `MemFacts _ L _ (mkLine addr word)` per memory instruction plus one `guardB _`
per branch terminator. Two representative segs:

**`eqDispatch`** (`Vsa/Sim/EqNeDispatchSeg.lean`, EASIEST — do this first): a single
terminator-less block, six `ld` (`+0x78,+0x80,+0x88,+0x90,+0x98,+0xa0`) then two
`addi` then six `sd` (`+0x40,+0x48,+0x50,+0x20,+0x28,+0x30`). Base reg `x2 = sp`
(`eqDispL sp = [(2, sp)]`). Residual = 6 load `MemFacts` + 6 store `MemFacts`, NO
guards, NO threading (all loads precede all stores; loads are `stepMemM`-identity so
every load window is over `σ.mem`; stores are bounds-only so their threaded memory is
irrelevant). Target: `∃ lds, ChainFacts σ.mem σ.mem (eqDispL sp) lds eqDispatch` from
`FrameBundle σ.mem sp`.

**`divDispatch`** (`Vsa/Sim/DivDispatchSeg.lean`, harder — threading + guards): four
blocks. D1 `ld +0x78, ld +0x88, li, sd +0xf0, sd +0x100, bne`; D2 `ld +0x90, ld +0x98,
ld +0xa0, sd +0xf0, sd +0xf8, sd +0x100, bne`; D3 empty + `beqz`; D4 two `mv`. Base
`x2 = v2` (`divDispL v2 sret Wr Wl = [(16,2),(10,2),(2,v2),(9,sret),(17,Wr),(19,Wl)]`).
Residual = 10 `MemFacts` + 3 guards. The two kind `bne`s (x16=2 vs li x13=2; x10=2 vs
x16=2) close after reducing `stepGM` (they are concrete). The divisor `beqz` (x17=Wr
vs x0) needs `hWr : Wr ≠ 0#64` — the GENUINE semantic obligation, passed as a tactic
arg or left as a goal. D2's three loads (`+0x90..+0xa0`) sit under D1's two stores
(`+0xf0,+0x100`), DISJOINT — peel with `writeLog_getElem_disjoint` (offsets differ,
`k+8 ≤ a` by omega). D2's own loads precede its own stores, so no intra-block threading.

## Discharge algorithm (per residual goal)

1. **`MemFacts … (ld)`**: reduce the goal memory to `σ.mem` peeling any preceding
   stores via `stepMemM`/`writeLog_getElem_disjoint` (loads are identity; stores are
   disjoint from load windows by omega on the offsets). Then `apply memFacts_ld_frame`
   with `hk` by `decide` (`(mkLine _ _).kind = .ld`), the four bounds by `frame_ea` +
   `omega` from `FrameBundle`, the eight pins from `fb.pop` (or supplied load-byte
   hyps). The `lds` entry is the eight read bytes.
2. **`MemFacts … (sd)`**: `apply memFacts_sd_frame`; four bounds only (memory-independent).
3. **kind `guardB` (bne, concrete)**: `simp only [stepGM, …]` to concretise the compared
   registers, then `decide`.
4. **divisor `guardB` (beq over a symbolic pin)**: close from the supplied semantic
   hypothesis (e.g. `hWr`), or leave as the tactic's single residual goal.

The `lds` is chosen by the tactic (the concatenated load-byte lists), so the top-level
theorem is `∃ lds, ChainFacts …` — the caller instantiates the seg's `lds` with it.

## Interface

`seg_frame_facts fb` (or `seg_frame_facts fb with hWr`), run after `chain_facts`, on a
`ChainFacts σ.mem σ.mem L lds bs` goal where `lds` is a metavariable/existential the
tactic fills. Base register value and the per-instruction offsets are read off `L`/`bs`.
Prove a `seg_frame_facts_of` term-level lemma first if a tactic is awkward; a robust
lemma the caller applies per-arm is acceptable and often cleaner than macro-heavy
tactics (see `fast-reflection-rules`: emit plain terms, one small `decide` per leaf).

## Constraints

- NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib. `#print axioms` must show
  only `[propext, Classical.choice, Quot.sound]`.
- Respect the per-file elab budget (`fast-reflection-rules`): bounds by `omega`, one
  small `decide` per kind/guard leaf, no whole-Sail-state reflection.

## Acceptance

1. `eqDispatch_facts : FrameBundle σ.mem sp → Eval_exprLoaded σ.mem → ∃ lds, ChainFacts σ.mem σ.mem (eqDispL sp) lds eqDispatch` — GREEN, axiom-clean.
2. `divDispatch_facts` (same, `divDispL`, with `hWr : Wr ≠ 0#64`) — GREEN, axiom-clean.
3. Compose one into `SegPre <arm>Dispatch` and apply `<arm>DispatchRow` to yield a live
   `Triple (frame-bundle entry) <arm>DispatchPost` — the item-1 SegPre composition, done.
4. Wire the new file into `Vsa.lean` + `scripts/check_all.sh`; full `lake build` green.

Then the payoff: fold the shared eval-case skeleton (`blockB_binary ≫ [item1] ≫
DispatchRow ≫ ValueTail ≫ blockD_v_rec`) into a `binOpArmSim` combinator taking a small
per-arm descriptor, so mod/eq/ne become ~10-line instantiations.
