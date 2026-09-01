import Vsa.Sim.BlockMem

/-!
# `BlockTerm` — basic blocks: the reflection block lemma + BRANCH TERMINATORS

Completes the reflection layer over `BlockMem`: a **basic block** is a
straight-line `List MInstr` body (consumed by `block_mem_run`) plus an optional
*terminator* — a conditional branch (`beq`/`bne`/`blt`/`bge`/`bltu`/`bgeu`,
either polarity), an unconditional `j` (`jal x0`), or a `jr`/`ret`
(`jalr x0`) — consumed by one `stepObs_branch_taken`/`stepObs_branch_nottaken`/
`stepObs_j`/`stepObs_jr` step at the end.  On top of the single-block lemma
(`bblock_sound_bt`) sits a **chain** lemma (`bblocks_sound_bt`): a list of
basic blocks whose branch/jump targets are contiguity-checked by one decidable
VC (`ChainOK`, closed by a single `by decide`), giving a whole multi-block
branch-crossing path — `Steps`, computed registers, computed memory, final PC —
in ONE application.  This is the shape the M4 dispatch-arm-epilogue segments
consume (arm = dispatch block + arm body + epilogue = 3 blocks).

## Measured verdict (acceptance test: the real `memmove` dispatch+setup
segment `0x800069c4 (bgeu TAKEN) → 0x800069f0 … → 0x80006a0c` — 8 steps,
4 basic blocks (empty body + taken bgeu; li + not-taken bltu; mv,addi +
not-taken beqz; addi,add + fall-through), real byte pins (`Code/Memmove.lean`)
and DecodeTable lemmas, ONE `bblocks_sound_bt` application (`BlockTermDemo`) vs
the same 8 steps via the `SnprintfSpec18` per-site ceremony — `tr_dispatch_mv`
arm 1 + `tr_setup_mv`, re-derived at identical hypotheses/conclusions in
`/tmp/bt_ceremony.lean`)

* `lean --profile` proof work (elaboration + tactic + kernel): reflection
  **≈ 384 ms** (68 + 244 + 72) vs ceremony **≈ 1069 ms** (95 + 895 + 79) —
  **≈ 2.8× less** at 8 steps / 5 tracked registers, consistent with
  `BlockMem`'s 4× at 7 instructions; the branch ceremony's per-site cost
  (guard massage + `obs_*` transports per register per site) is what the
  terminator case absorbs into the computed `runGM`/`tgtPCT` outcome.
* wall-clock `lean` on the use site (3 runs): reflection **3.0–3.1 s** vs
  ceremony **3.6–3.7 s** — both dominated by the `SnprintfSpec18` olean import
  (≈ 2.5 s), which the ceremony *needs* for its site lemmas and the demo only
  imports for the shared guard-massage lemmas + `Code.Memmove` pins.
* line count (identical theorem statement, ≈ 40 shared hypothesis/conclusion
  lines): reflection proof body **43** lines + **21** block-data lines
  (`mvB1..mvB4`) vs ceremony proof body **151** lines.  Marginal cost per
  extra block in a chain: ≈ 5 data lines + 2 `ChainFacts` entries + 1 guard
  fact; the ceremony pays ≈ 15–20 lines per site *and* one transport line per
  (site × tracked register).
* one-time cost: this file (≈ 700 lines) compiles in ≈ 30 s wall (import-
  dominated; ≈ 1.6 s of it is proof work).

**Verdict: WIN, same shape as `BlockMem` and compounding with it** — the chain
lemma turns "N sites + N×R transports + per-branch PC-target massage" into
"1 application + 1 `decide` + per-branch guard facts", and branch targets are
checked (not asserted) by the `ChainOK` `decide`.

## Design

* `TInstr` — the terminator description (fully concrete structure: pc, word,
  4 LE bytes, kind, source indices, the 13/21/12-bit immediates).  `TKind` =
  `br op taken? | j | jr`.  `jal rd` (a call) is deliberately OUT of scope:
  a call ends the chain at the callee anyway, so a `jal` terminator buys
  nothing until callee specs compose — see "loop/call" below.
* The branch **guard is a caller hypothesis** (`TermFactsT`), phrased over the
  *computed* end-of-body register values: `guardB op (srcVal rs1 L') (srcVal
  rs2 L') = taken` with `L' = runGM body L lds` — exactly like `BlockMem`'s
  store-window facts, it whnf-reduces at the use site to a guard over the
  computed symbolic values.  `jr`'s target-alignment fact is the same kind of
  symbolic-value hypothesis; `j`/branch target alignment is concrete and lives
  in the decidable VC.
* `tgtPCT` computes the post-terminator PC (branch target when taken,
  fall-through when not, jump target, cleared `rs1 + imm` for `jr`);
  `endPCB`/`chainEndPC` lift it to blocks/chains.  For `br`/`j` the target is
  concrete (`tgtPC0`), so chain contiguity is decided (`ChainOK` recurses from
  `tgtPC0`, and each successor block's own `BlockOKM` pins its entry pc to
  it); a `jr` may only terminate the *last* block of a chain (`TermChainO`).
* No new 33-branch batteries: the terminator classes write **no GPR**, so one
  `rfl` battery (`gprGet_eq_bt`) + one bounded-∀ `decide` lemma
  (`gprReg_noise_bt`) + the per-class `sigmaPost` frame lemmas transport the
  whole pin list (`gholds_regs_eq_bt`) — confirming the `BlockMem` header's
  prediction ("no new batteries, only a last non-inductive step case").

## What a loop (back-edge) needs: NOTHING NEW

A back-edge is just a basic block whose terminator target is *its own head* —
`bblock_sound_bt` with `tgtPCT = head` IS the loop-body lemma: it takes the
loop invariant's register pins `L` to `runGM body L lds` and lands PC back at
the head.  The existing loop combinators (`Triple.loop` / the `iterW`-style
induction used by `MemcpySpec2`/`SnprintfSpec18.loop_body_mv`) consume exactly
this shape: package `bblock_sound_bt`'s conclusion as the `St i → St (i+1)`
step of the measure induction (the guard hypothesis at iteration `i` comes
from the invariant, `taken = true` on the back-edge, `taken = false` on exit —
two `bblock_sound_bt` instances of the SAME block datum).  The only per-loop
work that remains is what was always semantic: the invariant itself and the
guard's arithmetic at `i` vs `i+1`.

## Obstructions hit

(8) `chainEndPC` mentions the symbolic pin list (for a final `jr`), so the
use site cannot `decide` it away; solved by `chainEndPCc` (the concrete-only
end PC) + `chainEndPC_eq_bt` under a decidable `NoJr` side condition — one
`rw [chainEndPC_eq_bt …]; decide` pair at the use site.  (9) a `jr` followed
by more blocks would make the chain lemma unsound (the successor VC could be
vacuously satisfiable by a constraint-free empty block), hence the explicit
`TermChainO` conjunct in `ChainOK` — it is *not* redundant with contiguity.
(10) the guard hypothesis must be phrased over computed values (`0#64 +
sign_extend 0x01f`, not the pretty `0x1f#64`) — same phrasing rule as
`BlockMem`'s obstruction (6); one `show`+`rw` per guard at the use site.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The branch guard, generic over the six BTYPE ops -/

/-- The BTYPE guard of `op` at source values `v1`/`v2` (the model's
`execute_BTYPE` comparison, op by op). -/
def guardB (op : bop) (v1 v2 : BitVec 64) : Bool :=
  match op with
  | bop.BEQ  => v1 == v2
  | bop.BNE  => v1 != v2
  | bop.BLT  => zopz0zI_s v1 v2
  | bop.BGE  => zopz0zKzJ_s v1 v2
  | bop.BLTU => zopz0zI_u v1 v2
  | bop.BGEU => zopz0zKzJ_u v1 v2

/-- Generic **taken**-branch execute characterization: any BTYPE op with
`guardB op v1 v2 = true` runs to `sigma3_branch_taken` (folds the six
per-op `execute_btype_*_taken` lemmas into one op-dispatch). -/
theorem exec_btype_taken_bt (σ : MState) (pc : BitVec 64) (imm : BitVec 13)
    (rs1 rs2 : regidx) (op : bop) (v1 v2 : BitVec 64)
    (hG : GoodState σ)
    (hpcσ : σ.regs.get? Register.PC = some pc)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : guardB op v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have hpc' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpcσ
  have hmisa' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa
      = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  cases op with
  | BEQ => exact execute_btype_beq_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv
  | BNE => exact execute_btype_bne_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv
  | BLT => exact execute_btype_blt_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv
  | BGE => exact execute_btype_bge_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv
  | BLTU => exact execute_btype_bltu_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv
  | BGEU => exact execute_btype_bgeu_taken imm rs1 rs2 v1 v2 pc initMisa _ hrs1 hrs2 hpc' hmisa' htgt hv

/-- Generic **not-taken**-branch execute characterization
(`guardB op v1 v2 = false` ⇒ execute leaves the state at
`sigma3_branch_nottaken`). -/
theorem exec_btype_nottaken_bt (σ : MState) (pc : BitVec 64) (imm : BitVec 13)
    (rs1 rs2 : regidx) (op : bop) (v1 v2 : BitVec 64)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok v2 (afterNextPC (afterPrelude σ) pc))
    (hv : guardB op v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  cases op with
  | BEQ => exact execute_btype_beq_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv
  | BNE => exact execute_btype_bne_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv
  | BLT => exact execute_btype_blt_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv
  | BGE => exact execute_btype_bge_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv
  | BLTU => exact execute_btype_bltu_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv
  | BGEU => exact execute_btype_bgeu_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-! ## Post-terminator read-backs (PC / minstret / frame), per class -/

theorem pc_btaken_bt {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_branch_taken_pc σ pc vm imm)

theorem pc_bnottaken_bt {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_branch_nottaken_pc σ pc vm)

theorem pc_jx0_bt {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_jump_x0_pc σ pc vm tgt)

theorem mi_btaken_bt {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC
    (pc + sign_extend (m := 64) imm)).insert Register.minstret
    (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem mi_bnottaken_bt {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC
    (BitVec.addInt pc 4)).insert Register.minstret
    (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem mi_jx0_bt {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert Register.minstret
    (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Frame through a taken-branch step (noise registers only are written). -/
theorem frame_term_btaken_bt {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_branch_taken σ pc vm imm R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

/-- Frame through a not-taken-branch step. -/
theorem frame_term_bnottaken_bt {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_branch_nottaken σ pc vm R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

/-- Frame through a `j`/`jr` (x0-jump) step. -/
theorem frame_term_jx0_bt {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_jump_x0 σ pc vm tgt R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

/-! ## Pin-list transport through a GPR-preserving step (no per-class batteries)

Terminators write no GPR, so the whole pin list survives whenever every
non-noise register read is preserved.  ONE 33-branch dispatch
(`obs_gpr_frame_bt`, the `obs_gpr_store` shape abstracted over the step class)
serves all three terminator post-shapes through their `frame_term_*_bt`. -/

/-- Any `gprGet` pin survives a step whose register frame preserves every
non-noise register (the terminator classes). -/
theorem obs_gpr_frame_bt {σ' σ : MState}
    (h : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    ∀ (w : BitVec 64), gprGet σ n = some w → gprGet σ' n = some w
  | 0, h1, _, _, _ => absurd h1 (by omega)
  | 1, _, _, w, hw => (h Register.x1 (by decide)).trans hw
  | 2, _, _, w, hw => (h Register.x2 (by decide)).trans hw
  | 3, _, _, w, hw => (h Register.x3 (by decide)).trans hw
  | 4, _, _, w, hw => (h Register.x4 (by decide)).trans hw
  | 5, _, _, w, hw => (h Register.x5 (by decide)).trans hw
  | 6, _, _, w, hw => (h Register.x6 (by decide)).trans hw
  | 7, _, _, w, hw => (h Register.x7 (by decide)).trans hw
  | 8, _, _, w, hw => (h Register.x8 (by decide)).trans hw
  | 9, _, _, w, hw => (h Register.x9 (by decide)).trans hw
  | 10, _, _, w, hw => (h Register.x10 (by decide)).trans hw
  | 11, _, _, w, hw => (h Register.x11 (by decide)).trans hw
  | 12, _, _, w, hw => (h Register.x12 (by decide)).trans hw
  | 13, _, _, w, hw => (h Register.x13 (by decide)).trans hw
  | 14, _, _, w, hw => (h Register.x14 (by decide)).trans hw
  | 15, _, _, w, hw => (h Register.x15 (by decide)).trans hw
  | 16, _, _, w, hw => (h Register.x16 (by decide)).trans hw
  | 17, _, _, w, hw => (h Register.x17 (by decide)).trans hw
  | 18, _, _, w, hw => (h Register.x18 (by decide)).trans hw
  | 19, _, _, w, hw => (h Register.x19 (by decide)).trans hw
  | 20, _, _, w, hw => (h Register.x20 (by decide)).trans hw
  | 21, _, _, w, hw => (h Register.x21 (by decide)).trans hw
  | 22, _, _, w, hw => (h Register.x22 (by decide)).trans hw
  | 23, _, _, w, hw => (h Register.x23 (by decide)).trans hw
  | 24, _, _, w, hw => (h Register.x24 (by decide)).trans hw
  | 25, _, _, w, hw => (h Register.x25 (by decide)).trans hw
  | 26, _, _, w, hw => (h Register.x26 (by decide)).trans hw
  | 27, _, _, w, hw => (h Register.x27 (by decide)).trans hw
  | 28, _, _, w, hw => (h Register.x28 (by decide)).trans hw
  | 29, _, _, w, hw => (h Register.x29 (by decide)).trans hw
  | 30, _, _, w, hw => (h Register.x30 (by decide)).trans hw
  | 31, _, _, w, hw => (h Register.x31 (by decide)).trans hw
  | _+32, _, h31, _, _ => absurd h31 (by omega)

/-- The whole pin list survives any step that preserves every non-noise
register read (list form of `obs_gpr_frame_bt`). -/
theorem gholds_frame_bt {σ' σ : MState}
    (h : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ (L : GRegs), KeysOK (keysG L) → GHolds σ L → GHolds σ' L := by
  intro L
  induction L with
  | nil => intro _ _; exact trivial
  | cons p L ih =>
    obtain ⟨n, w⟩ := p
    intro hK hL
    have hn := hK n (List.mem_cons_self ..)
    exact ⟨obs_gpr_frame_bt h n hn.1 hn.2 w hL.1,
      ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2⟩

/-! ## The terminator description -/

/-- Terminator kind: conditional branch (`op` and *which polarity fired*),
unconditional `j` (`jal x0`), or `jr`/`ret` (`jalr x0`).  `jal rd` (calls) is
out of scope — a call hands control to a callee spec anyway. -/
inductive TKind where
  | br (op : bop) (taken : Bool) : TKind
  | j : TKind
  | jr : TKind

/-- One terminator, fully concrete structure (symbolic values never enter).
`rs1`/`rs2` are the branch sources (`rs1` also the `jr` base); the three
immediates serve `br` (13-bit), `j` (21-bit), `jr` (12-bit) — unused ones 0. -/
structure TInstr where
  pc    : BitVec 64
  word  : BitVec 32
  b0    : BitVec 8
  b1    : BitVec 8
  b2    : BitVec 8
  b3    : BitVec 8
  kind  : TKind
  rs1   : Nat
  rs2   : Nat
  imm13 : BitVec 13
  imm21 : BitVec 21
  imm12 : BitVec 12

/-- The decoded AST the DecodeTable lemma for `t.word` must produce.
(BTYPE tuple order is `(imm, rs2, rs1, op)`.) -/
def astOfT (t : TInstr) : instruction :=
  match t.kind with
  | .br op _ => instruction.BTYPE (t.imm13, gprIdx t.rs2, gprIdx t.rs1, op)
  | .j => instruction.JAL (t.imm21, regidx.Regidx 0x00#5)
  | .jr => instruction.JALR (t.imm12, gprIdx t.rs1, regidx.Regidx 0x00#5)

/-- The concrete part of the post-terminator PC (`0` junk for `jr`, whose
target is symbolic; a `jr` never chains, so the junk is never consulted). -/
def tgtPC0 (t : TInstr) : BitVec 64 :=
  match t.kind with
  | .br _ true => t.pc + sign_extend (m := 64) t.imm13
  | .br _ false => BitVec.addInt t.pc 4
  | .j => t.pc + sign_extend (m := 64) t.imm21
  | .jr => 0#64

/-- The post-terminator PC over the end-of-body pin list `L`. -/
def tgtPCT (t : TInstr) (L : GRegs) : BitVec 64 :=
  match t.kind with
  | .jr => BitVec.update (srcVal t.rs1 L + sign_extend (m := 64) t.imm12) 0 0#1
  | _ => tgtPC0 t

/-- `t` is not a `jr` (whose target is symbolic ⇒ cannot chain). -/
def TermNotJr : TKind → Prop
  | .jr => False
  | _ => True

instance instDecTermNotJr : (k : TKind) → Decidable (TermNotJr k)
  | .br _ _ => isTrue trivial
  | .j => isTrue trivial
  | .jr => isFalse (fun h => h)

theorem tgtPCT_eq_bt (t : TInstr) (L : GRegs) (h : TermNotJr t.kind) :
    tgtPCT t L = tgtPC0 t := by
  obtain ⟨pc, word, b0, b1, b2, b3, kind, rs1, rs2, i13, i21, i12⟩ := t
  cases kind with
  | br op taken => rfl
  | j => rfl
  | jr => exact (h : False).elim

/-! ## Per-terminator facts (caller hypotheses) and the decidable VC -/

/-- The four little-endian code-byte pins for the terminator, on the code
memory `mc` (entry memory — code survives the block's stores internally). -/
def BytePinsT (m : Std.ExtHashMap Nat (BitVec 8)) (t : TInstr) : Prop :=
  m[t.pc.toNat]? = some t.b0 ∧ m[t.pc.toNat + 1]? = some t.b1 ∧
  m[t.pc.toNat + 2]? = some t.b2 ∧ m[t.pc.toNat + 3]? = some t.b3

/-- σ-generic decode fact — the DecodeTable lemma shape, inhabited directly. -/
def DecodeFactT (t : TInstr) : Prop :=
  ∀ s : SequentialState RegisterType trivialChoiceSource,
    s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
    s.regs.get? Register.cur_privilege =
      some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
    s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode t.word).run s = .ok (astOfT t) s

/-- The data-dependent terminator fact, phrased over the **computed**
end-of-body pin list `L`: the branch guard fired with the stated polarity
(`br`), nothing (`j`), or the symbolic return-target alignment (`jr`). -/
def TermFactsT (L : GRegs) (t : TInstr) : Prop :=
  match t.kind with
  | .br op taken => guardB op (srcVal t.rs1 L) (srcVal t.rs2 L) = taken
  | .j => True
  | .jr => (BitVec.update (srcVal t.rs1 L + sign_extend (m := 64) t.imm12) 0 0#1).toNat % 4 = 0

/-- Kind-dependent decidable structure VC: source availability and (for
concrete-target kinds) target alignment. -/
def TermKindOK (dom : List Nat) (pc : BitVec 64) (rs1 rs2 : Nat)
    (i13 : BitVec 13) (i21 : BitVec 21) : TKind → Prop
  | .br _ _ => SrcOK rs1 dom ∧ SrcOK rs2 dom ∧
      (pc + sign_extend (m := 64) i13).toNat % 4 = 0
  | .j => (pc + sign_extend (m := 64) i21).toNat % 4 = 0
  | .jr => SrcOK rs1 dom

instance instDecTermKindOK (dom : List Nat) (pc : BitVec 64) (rs1 rs2 : Nat)
    (i13 : BitVec 13) (i21 : BitVec 21) :
    (k : TKind) → Decidable (TermKindOK dom pc rs1 rs2 i13 i21 k)
  | .br _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .j => inferInstanceAs (Decidable (_ = _))
  | .jr => inferInstanceAs (Decidable (_ ∧ _))

/-- The decidable terminator VC at its own pc (word/byte coherence, non-RVC,
code range/alignment, kind obligations).  The pc-contiguity link to the block
body lives in `TermOKo`. -/
abbrev TermWF (dom : List Nat) (t : TInstr) : Prop :=
  (((t.b3.append t.b2).append t.b1).append t.b0).toNat = t.word.toNat ∧
  (Sail.BitVec.extractLsb (((t.b3.append t.b2).append t.b1).append t.b0) 1 0).toNat
    = (0b11#2 : BitVec 2).toNat ∧
  0x80000000 ≤ t.pc.toNat ∧
  t.pc.toNat + 4 ≤ tohostAddr ∧
  t.pc.toNat % 4 = 0 ∧
  TermKindOK dom t.pc t.rs1 t.rs2 t.imm13 t.imm21 t.kind

/-! ## The one-terminator step lemma -/

/-- **One terminator step** from a state pinned at `t.pc`: a `Step` to the
computed target `tgtPCT t L`, with `GoodState`, memory and HTIF output
unchanged, the whole pin list `L` intact, and the noise-only register frame. -/
theorem term_step_bt (t : TInstr) (σ : MState) (i u : Nat) (vm : BitVec 64)
    (L : GRegs) (dom : List Nat)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some t.pc)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
    (hdom : ∀ n ∈ dom, n ∈ keysG L)
    (hb0 : σ.mem[t.pc.toNat]? = some t.b0) (hb1 : σ.mem[t.pc.toNat + 1]? = some t.b1)
    (hb2 : σ.mem[t.pc.toNat + 2]? = some t.b2) (hb3 : σ.mem[t.pc.toNat + 3]? = some t.b3)
    (hdec : DecodeFactT t)
    (hwf : TermWF dom t)
    (htf : TermFactsT L t)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (tgtPCT t L) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' L ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨tpc, tword, tb0, tb1, tb2, tb3, tkind, trs1, trs2, ti13, ti21, ti12⟩ := t
  obtain ⟨hwn, hrvcn, hlo, hhi, halign, hkok⟩ := hwf
  have hword : (((tb3.append tb2).append tb1).append tb0) = tword :=
    BitVec.eq_of_toNat_eq hwn
  have hnotrvc : Sail.BitVec.extractLsb (((tb3.append tb2).append tb1).append tb0) 1 0
      = (0b11#2 : BitVec 2) := BitVec.eq_of_toNat_eq hrvcn
  have hdec' := hdec (afterPrelude σ)
    (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
    (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
    (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
  cases tkind with
  | br op taken =>
    obtain ⟨hs1ok, hs2ok, htgt⟩ :=
      (hkok : SrcOK trs1 dom ∧ SrcOK trs2 dom ∧
        (tpc + sign_extend (m := 64) ti13).toNat % 4 = 0)
    have hsp1 : srcPin σ trs1 (srcVal trs1 L) :=
      srcPin_srcVal σ L trs1 (hs1ok.2.imp (fun h => h) (hdom trs1)) hL
    have hrx1 := rX_src σ tpc trs1 hs1ok.1 (srcVal trs1 L) hsp1
    have hsp2 : srcPin σ trs2 (srcVal trs2 L) :=
      srcPin_srcVal σ L trs2 (hs2ok.2.imp (fun h => h) (hdom trs2)) hL
    have hrx2 := rX_src σ tpc trs2 hs2ok.1 (srcVal trs2 L) hsp2
    cases taken with
    | true =>
      have hexec := exec_btype_taken_bt σ tpc ti13 (gprIdx trs1) (gprIdx trs2) op
        (srcVal trs1 L) (srcVal trs2 L) hG hpc hrx1 hrx2 htgt htf
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_branch_taken σ i u tpc vm ti13 (gprIdx trs1) (gprIdx trs2) op tword
          tb0 tb1 tb2 tb3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      exact ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1.2, pc_btaken_bt hobs1, mi_btaken_bt hobs1,
        gholds_frame_bt (fun R hn => frame_term_btaken_bt hobs1 R hn) L hkeys hL,
        fun R hn => frame_term_btaken_bt hobs1 R hn⟩
    | false =>
      have hexec := exec_btype_nottaken_bt σ tpc ti13 (gprIdx trs1) (gprIdx trs2) op
        (srcVal trs1 L) (srcVal trs2 L) hrx1 hrx2 htf
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_branch_nottaken σ i u tpc vm ti13 (gprIdx trs1) (gprIdx trs2) op tword
          tb0 tb1 tb2 tb3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      exact ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1.2, pc_bnottaken_bt hobs1,
        mi_bnottaken_bt hobs1,
        gholds_frame_bt (fun R hn => frame_term_bnottaken_bt hobs1 R hn) L hkeys hL,
        fun R hn => frame_term_bnottaken_bt hobs1 R hn⟩
  | j =>
    have htgt : (tpc + sign_extend (m := 64) ti21).toNat % 4 = 0 := hkok
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      stepObs_j σ i u tpc vm tword ti21 tb0 tb1 tb2 tb3
        hG hpc hmi hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec' htgt hi
    exact ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1.2, pc_jx0_bt hobs1, mi_jx0_bt hobs1,
      gholds_frame_bt (fun R hn => frame_term_jx0_bt hobs1 R hn) L hkeys hL,
      fun R hn => frame_term_jx0_bt hobs1 R hn⟩
  | jr =>
    have hs1ok : SrcOK trs1 dom := hkok
    have hsp1 : srcPin σ trs1 (srcVal trs1 L) :=
      srcPin_srcVal σ L trs1 (hs1ok.2.imp (fun h => h) (hdom trs1)) hL
    have hrx1 := rX_src σ tpc trs1 hs1ok.1 (srcVal trs1 L) hsp1
    have htgt : (BitVec.update (srcVal trs1 L + sign_extend (m := 64) ti12) 0 0#1).toNat % 4
        = 0 := htf
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      stepObs_jr σ i u tpc vm (srcVal trs1 L) tword ti12 (gprIdx trs1) tb0 tb1 tb2 tb3
        hG hpc hmi hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec' hrx1 htgt hi
    exact ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1.2, pc_jx0_bt hobs1, mi_jx0_bt hobs1,
      gholds_frame_bt (fun R hn => frame_term_jx0_bt hobs1 R hn) L hkeys hL,
      fun R hn => frame_term_jx0_bt hobs1 R hn⟩

/-! ## Threading lemmas for the body run -/

/-- Domain threading over a whole body (matches `BlockOKM`'s `domStepM`). -/
def domRunM : List MInstr → List Nat → List Nat
  | [], dom => dom
  | a :: r, dom => domRunM r (domStepM a dom)

/-- Load-data threading over a whole body. -/
def ldsRunM : List MInstr → List (List (BitVec 8)) → List (List (BitVec 8))
  | [], lds => lds
  | a :: r, lds => ldsRunM r (stepLdsM a.kind lds)

/-- The threaded domain stays inside the computed pin keys. -/
theorem domRun_keys_bt : ∀ (is : List MInstr) (L : GRegs)
    (lds : List (List (BitVec 8))) (dom : List Nat),
    (∀ n ∈ dom, n ∈ keysG L) →
    ∀ n ∈ domRunM is dom, n ∈ keysG (runGM is L lds) := by
  intro is
  induction is with
  | nil => intro L lds dom h n hn; exact h n hn
  | cons a r ih =>
    intro L lds dom h
    show ∀ n ∈ domRunM r (domStepM a dom),
      n ∈ keysG (runGM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds))
    apply ih
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    cases akind with
    | addi => exact dom_cons_erase h
    | add => exact dom_cons_erase h
    | sub => exact dom_cons_erase h
    | lw => exact dom_cons_erase h
    | lwu => exact dom_cons_erase h
    | ld => exact dom_cons_erase h
    | lbu => exact dom_cons_erase h
    | addiw => exact dom_cons_erase h
    | slli => exact dom_cons_erase h
    | srli => exact dom_cons_erase h
    | slti => exact dom_cons_erase h
    | slt => exact dom_cons_erase h
    | subw => exact dom_cons_erase h
    | auipc => exact dom_cons_erase h
    | xori => exact dom_cons_erase h
    | slliw => exact dom_cons_erase h
    | sw => exact h
    | sd => exact h
    | sb => exact h

/-- The computed pin keys stay GPR indices (`1..31`), given the body VC. -/
theorem keysOK_runGM_bt : ∀ (is : List MInstr) (pc0 : BitVec 64) (dom : List Nat)
    (L : GRegs) (lds : List (List (BitVec 8))),
    BlockOKM pc0 dom is → KeysOK (keysG L) → KeysOK (keysG (runGM is L lds)) := by
  intro is
  induction is with
  | nil => intro _ _ L lds _ h; exact h
  | cons a r ih =>
    intro pc0 dom L lds hwf hkeys
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    have hwf' : InstrOKM pc0 dom ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        BlockOKM (BitVec.addInt apc 4)
          (domStepM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ dom) r := hwf
    obtain ⟨⟨_, _, _, _, _, _, hkok⟩, hwfr⟩ := hwf'
    cases akind with
    | addi =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .addi ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | add =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .add ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | sub =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .sub ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | lw =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .lw ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | lwu =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .lwu ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | ld =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .ld ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | lbu =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .lbu ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | addiw =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .addiw ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | slli =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .slli ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | srli =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .srli ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | slti =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .slti ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | slt =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .slt ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | subw =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .subw ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | auipc =>
      obtain ⟨hrd1, hrd31⟩ := (hkok : KindOK dom .auipc ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | xori =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .xori ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | slliw =>
      obtain ⟨⟨hrd1, hrd31⟩, _⟩ := (hkok : KindOK dom .slliw ard ars1 ars2)
      exact ih _ _ _ _ hwfr (keysOK_cons_erase hrd1 hrd31 L hkeys)
    | sw => exact ih _ _ _ _ hwfr hkeys
    | sd => exact ih _ _ _ _ hwfr hkeys
    | sb => exact ih _ _ _ _ hwfr hkeys

/-- The computed write-log image agrees with the input memory below the HTIF
window: every logged store lands above `tohostAddr + 16` (its `MemFacts`
window fact), so the fold misses all low addresses.  This re-exports the
block-internal code-pin-survival invariant to the *conclusion* side, where the
terminator fetch (and the next chained block) needs it. -/
theorem writeLog_wlog_low_bt (mc : Std.ExtHashMap Nat (BitVec 8)) :
    ∀ (is : List MInstr) (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs)
      (lds : List (List (BitVec 8))),
    ProgFactsM mc m L lds is →
    ∀ j, j < tohostAddr → (writeLog m (wlogM is L lds))[j]? = m[j]? := by
  intro is
  induction is with
  | nil => intro m L lds _ j _; rfl
  | cons a r ih =>
    intro m L lds hf j hj
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    have hf' : BytePinsM mc ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        DecodeFactM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        MemFacts m L (lds.headD []) ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        ProgFactsM mc
          (stepMemM m ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L)
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM akind lds) r := hf
    obtain ⟨_, _, hmf, hfr⟩ := hf'
    cases akind with
    | addi => exact ih m _ _ hfr j hj
    | add => exact ih m _ _ hfr j hj
    | sub => exact ih m _ _ hfr j hj
    | lw => exact ih m _ _ hfr j hj
    | lwu => exact ih m _ _ hfr j hj
    | ld => exact ih m _ _ hfr j hj
    | lbu => exact ih m _ _ hfr j hj
    | addiw => exact ih m _ _ hfr j hj
    | slli => exact ih m _ _ hfr j hj
    | srli => exact ih m _ _ hfr j hj
    | slti => exact ih m _ _ hfr j hj
    | slt => exact ih m _ _ hfr j hj
    | subw => exact ih m _ _ hfr j hj
    | auipc => exact ih m _ _ hfr j hj
    | xori => exact ih m _ _ hfr j hj
    | slliw => exact ih m _ _ hfr j hj
    | sw =>
      have hwin : tohostAddr + 16 ≤
          (eaddrM ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L).toNat :=
        hmf.2.2.1
      exact (ih _ _ _ hfr j hj).trans (writeMap4_low_miss m _ _ j (by omega))
    | sd =>
      have hwin : tohostAddr + 16 ≤
          (eaddrM ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L).toNat :=
        hmf.2.2.1
      exact (ih _ _ _ hfr j hj).trans (writeMap8_low_miss m _ _ j (by omega))
    | sb =>
      have hwin : tohostAddr + 16 ≤
          (eaddrM ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L).toNat :=
        hmf.2.2
      exact (ih _ _ _ hfr j hj).trans (insert_low_miss m _ _ j (by omega))

/-! ## The basic block -/

/-- A basic block: straight-line body + optional terminator (`none` =
fall-through into the next block). -/
structure BBlock where
  body : List MInstr
  term : Option TInstr

/-- Machine steps a block takes. -/
def blenB (b : BBlock) : Nat :=
  match b.term with
  | none => b.body.length
  | some _ => b.body.length + 1

/-- Post-block PC: fall-through end of the body, or the terminator target. -/
def endPCB (pc0 : BitVec 64) (b : BBlock) (L : GRegs) (lds : List (List (BitVec 8))) :
    BitVec 64 :=
  match b.term with
  | none => endPCM pc0 b.body
  | some t => tgtPCT t (runGM b.body L lds)

/-- Terminator byte-pin + decode obligations (nothing for fall-through). -/
def TermPins (mc : Std.ExtHashMap Nat (BitVec 8)) : Option TInstr → Prop
  | none => True
  | some t => BytePinsT mc t ∧ DecodeFactT t

/-- Terminator data-dependent facts, over the end-of-body pin list. -/
def TermFactsO (L : GRegs) : Option TInstr → Prop
  | none => True
  | some t => TermFactsT L t

/-- Terminator structural VC: pinned to the body's fall-through pc + `TermWF`. -/
def TermOKo (pc0 : BitVec 64) (dom : List Nat) : Option TInstr → Prop
  | none => True
  | some t => t.pc.toNat = pc0.toNat ∧ TermWF dom t

instance instDecTermOKo (pc0 : BitVec 64) (dom : List Nat) :
    (o : Option TInstr) → Decidable (TermOKo pc0 dom o)
  | none => isTrue trivial
  | some _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The per-block non-computable obligations. -/
def BBlockFacts (mc m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs)
    (lds : List (List (BitVec 8))) (b : BBlock) : Prop :=
  ProgFactsM mc m L lds b.body ∧ TermPins mc b.term ∧
  TermFactsO (runGM b.body L lds) b.term

/-- The per-block decidable VC. -/
abbrev BBlockOK (pc0 : BitVec 64) (dom : List Nat) (b : BBlock) : Prop :=
  BlockOKM pc0 dom b.body ∧ TermOKo (endPCM pc0 b.body) (domRunM b.body dom) b.term

/-! ## The single basic-block lemma -/

/-- Generalized form (`mc` code memory, `m` current memory with low-address
agreement, `dom` under-approximating the pinned keys) — the chain lemma
threads through this. -/
theorem bblock_run_bt (b : BBlock) (σ : MState) (i u : Nat) (pc0 vm : BitVec 64)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (mc m : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m)
    (hlow : ∀ j, j < tohostAddr → m[j]? = mc[j]?)
    (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
    (hdom : ∀ n ∈ dom, n ∈ keysG L)
    (hfacts : BBlockFacts mc m L lds b)
    (hwf : BBlockOK pc0 dom b)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + blenB b⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog m (wlogM b.body L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCB pc0 b L lds) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM b.body L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM b.body, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨body, term⟩ := b
  obtain ⟨hbf, htp, htfo⟩ := hfacts
  obtain ⟨hbo, hto⟩ := hwf
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    block_mem_run body σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hbf hbo hi
  cases term with
  | none =>
    exact ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩
  | some t =>
    obtain ⟨hpceq, hwft⟩ :=
      (hto : t.pc.toNat = (endPCM pc0 body).toNat ∧ TermWF (domRunM body dom) t)
    have hpct : t.pc = endPCM pc0 body := BitVec.eq_of_toNat_eq hpceq
    obtain ⟨htb, htd⟩ := (htp : BytePinsT mc t ∧ DecodeFactT t)
    obtain ⟨vm1, hmi1'⟩ := hmi1
    have hlow1 : ∀ j, j < tohostAddr → σ1.mem[j]? = mc[j]? := by
      intro j hj
      rw [hmem1]
      exact (writeLog_wlog_low_bt mc body m L lds hbf j hj).trans (hlow j hj)
    have hhit : t.pc.toNat + 4 ≤ tohostAddr := hwft.2.2.2.1
    have hb0 : σ1.mem[t.pc.toNat]? = some t.b0 := (hlow1 _ (by omega)).trans htb.1
    have hb1 : σ1.mem[t.pc.toNat + 1]? = some t.b1 := (hlow1 _ (by omega)).trans htb.2.1
    have hb2 : σ1.mem[t.pc.toNat + 2]? = some t.b2 := (hlow1 _ (by omega)).trans htb.2.2.1
    have hb3 : σ1.mem[t.pc.toNat + 3]? = some t.b3 := (hlow1 _ (by omega)).trans htb.2.2.2
    have hkeys1 : KeysOK (keysG (runGM body L lds)) :=
      keysOK_runGM_bt body pc0 dom L lds hbo hkeys
    have hdom1 : ∀ n ∈ domRunM body dom, n ∈ keysG (runGM body L lds) :=
      domRun_keys_bt body L lds dom hdom
    have hpc1' : σ1.regs.get? Register.PC = some t.pc := by rw [hpct]; exact hpc1
    obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
      term_step_bt t σ1 i1 (u + body.length) vm1 (runGM body L lds) (domRunM body dom)
        hG1 hpc1' hmi1' hGH1 hkeys1 hdom1 hb0 hb1 hb2 hb3 htd hwft htfo hi1
    refine ⟨σ2, i2, ?_, hi2, hG2, hmem2.trans hmem1, hout2.trans hout1, hpc2, hmi2, hGH2, ?_⟩
    · have h := hsteps1.trans (Steps.single hstep2)
      have e : u + body.length + 1 = u + (body.length + 1) := by omega
      rw [e] at h
      exact h
    · intro R hn hw
      exact (hframe2 R hn).trans (hframe1 R hn hw)

/-- **The basic-block lemma.**  A straight-line body + optional branch/jump
terminator, from an entry state with pinned PC / minstret / source registers:
the full `Steps` chain to the *computed* target PC (`endPCB` — branch target
when taken, fall-through when not, jump target), with the computed register
outcome (`runGM`), computed memory outcome (`writeLog`), tick invariant,
`GoodState`, HTIF output unchanged, and the register frame outside
`noiseRegs ∪ wrRegsM`.  The branch guard is the caller hypothesis inside
`BBlockFacts` (`TermFactsO`, phrased over the computed end-of-body values);
the structural VC `BBlockOK` closes by one `decide`. -/
theorem bblock_sound_bt (b : BBlock) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : BBlockFacts σ.mem σ.mem L lds b)
    (hwf : BBlockOK pc0 (keysG L) b)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + blenB b⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem (wlogM b.body L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCB pc0 b L lds) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM b.body L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM b.body, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) :=
  bblock_run_bt b σ i u pc0 vm L lds σ.mem σ.mem (keysG L)
    hG hpc hmi rfl (fun _ _ => rfl) hL hkeys (fun _ h => h) hfacts hwf hi

/-! ## Chains of basic blocks -/

/-- `jr` may only terminate the last block (its target is symbolic). -/
def TermNotJrO : Option TInstr → Prop
  | none => True
  | some t => TermNotJr t.kind

instance instDecTermNotJrO : (o : Option TInstr) → Decidable (TermNotJrO o)
  | none => isTrue trivial
  | some t => instDecTermNotJr t.kind

/-- Chainability of a block's terminator given its successors. -/
def TermChainO : Option TInstr → List BBlock → Prop
  | _, [] => True
  | o, _ :: _ => TermNotJrO o

instance instDecTermChainO :
    (o : Option TInstr) → (bs : List BBlock) → Decidable (TermChainO o bs)
  | _, [] => isTrue trivial
  | o, _ :: _ => instDecTermNotJrO o

/-- The concrete continuation PC of a block (target of `br`/`j`, fall-through
end otherwise).  The successor block's own `BlockOKM` pins its entry pc to
this, so chain contiguity is *checked* by the `ChainOK` `decide`. -/
def nextPC0 (pc0 : BitVec 64) (b : BBlock) : BitVec 64 :=
  match b.term with
  | none => endPCM pc0 b.body
  | some t => tgtPC0 t

/-- Total machine steps of a chain. -/
def chainLen : List BBlock → Nat
  | [] => 0
  | b :: bs => blenB b + chainLen bs

/-- Computed register outcome of a chain. -/
def runChain : List BBlock → GRegs → List (List (BitVec 8)) → GRegs
  | [], L, _ => L
  | b :: bs, L, lds => runChain bs (runGM b.body L lds) (ldsRunM b.body lds)

/-- Computed memory outcome of a chain. -/
def memChain : List BBlock → Std.ExtHashMap Nat (BitVec 8) → GRegs →
    List (List (BitVec 8)) → Std.ExtHashMap Nat (BitVec 8)
  | [], m, _, _ => m
  | b :: bs, m, L, lds =>
    memChain bs (writeLog m (wlogM b.body L lds)) (runGM b.body L lds) (ldsRunM b.body lds)

/-- Registers written by a chain. -/
def wrChain : List BBlock → List Nat
  | [] => []
  | b :: bs => wrRegsM b.body ++ wrChain bs

/-- Final PC of a chain (the last block's `endPCB`; symbolic only for a final
`jr`). -/
def chainEndPC (pc0 : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8))) :
    List BBlock → BitVec 64
  | [] => pc0
  | b :: bs =>
    match bs with
    | [] => endPCB pc0 b L lds
    | _ :: _ => chainEndPC (nextPC0 pc0 b) (runGM b.body L lds) (ldsRunM b.body lds) bs

/-- The chained non-computable obligations, memory/pins/load-data threaded. -/
def ChainFacts (mc : Std.ExtHashMap Nat (BitVec 8)) :
    Std.ExtHashMap Nat (BitVec 8) → GRegs → List (List (BitVec 8)) → List BBlock → Prop
  | _, _, _, [] => True
  | m, L, lds, b :: bs =>
    BBlockFacts mc m L lds b ∧
    ChainFacts mc (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
      (ldsRunM b.body lds) bs

/-- The chained decidable VC: per-block VCs + chainability, recursing from the
concrete continuation PC (contiguity enforced by the successor's `BlockOKM`/
`TermOKo` at that pc). -/
def ChainOK (pc0 : BitVec 64) (dom : List Nat) : List BBlock → Prop
  | [] => True
  | b :: bs => BBlockOK pc0 dom b ∧ TermChainO b.term bs ∧
      ChainOK (nextPC0 pc0 b) (domRunM b.body dom) bs

instance instDecChainOK (pc0 : BitVec 64) (dom : List Nat) :
    (bs : List BBlock) → Decidable (ChainOK pc0 dom bs)
  | [] => isTrue trivial
  | b :: bs =>
    have : Decidable (ChainOK (nextPC0 pc0 b) (domRunM b.body dom) bs) :=
      instDecChainOK _ _ bs
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A non-final block's realized target equals its concrete continuation. -/
theorem endPCB_eq_nextPC0_bt (b : BBlock) (pc0 : BitVec 64) (L : GRegs)
    (lds : List (List (BitVec 8))) (h : TermNotJrO b.term) :
    endPCB pc0 b L lds = nextPC0 pc0 b := by
  obtain ⟨body, term⟩ := b
  cases term with
  | none => rfl
  | some t => exact tgtPCT_eq_bt t _ h

/-- No block of the chain ends in `jr` (⇒ the whole end PC is concrete). -/
def NoJr : List BBlock → Prop
  | [] => True
  | b :: bs => TermNotJrO b.term ∧ NoJr bs

instance instDecNoJr : (bs : List BBlock) → Decidable (NoJr bs)
  | [] => isTrue trivial
  | _ :: bs =>
    have : Decidable (NoJr bs) := instDecNoJr bs
    inferInstanceAs (Decidable (_ ∧ _))

/-- Concrete-only chain end PC (well-defined under `NoJr`). -/
def chainEndPCc (pc0 : BitVec 64) : List BBlock → BitVec 64
  | [] => pc0
  | b :: bs => chainEndPCc (nextPC0 pc0 b) bs

/-- Under `NoJr`, `chainEndPC` ignores the pin list — the use site rewrites to
the concrete `chainEndPCc` and closes it by `decide` (obstruction (8)). -/
theorem chainEndPC_eq_bt : ∀ (bs : List BBlock) (pc0 : BitVec 64) (L : GRegs)
    (lds : List (List (BitVec 8))), NoJr bs →
    chainEndPC pc0 L lds bs = chainEndPCc pc0 bs := by
  intro bs
  induction bs with
  | nil => intro pc0 L lds _; rfl
  | cons b bs ih =>
    intro pc0 L lds h
    obtain ⟨hb, hbs⟩ := (h : TermNotJrO b.term ∧ NoJr bs)
    cases bs with
    | nil =>
      show endPCB pc0 b L lds = nextPC0 pc0 b
      exact endPCB_eq_nextPC0_bt b pc0 L lds hb
    | cons b2 rest =>
      show chainEndPC (nextPC0 pc0 b) (runGM b.body L lds) (ldsRunM b.body lds) (b2 :: rest)
        = chainEndPCc (nextPC0 pc0 b) (b2 :: rest)
      exact ih _ _ _ hbs

/-! ## The chain lemma -/

/-- Generalized chain run (the induction). -/
theorem bblocks_run_bt (bs : List BBlock) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (lds : List (List (BitVec 8))) (mc m : Std.ExtHashMap Nat (BitVec 8))
      (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m →
    (∀ j, j < tohostAddr → m[j]? = mc[j]?) →
    GHolds σ L → KeysOK (keysG L) → (∀ n ∈ dom, n ∈ keysG L) →
    ChainFacts mc m L lds bs → ChainOK pc0 dom bs → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + chainLen bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = memChain bs m L lds ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (chainEndPC pc0 L lds bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runChain bs L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction bs with
  | nil =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem _ hL _ _ _ _ hi
    exact ⟨σ, i, Steps.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons b bs ih =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hfacts hwf hi
    have hfacts' : BBlockFacts mc m L lds b ∧
        ChainFacts mc (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
          (ldsRunM b.body lds) bs := hfacts
    obtain ⟨hbf, hcf⟩ := hfacts'
    have hwf' : BBlockOK pc0 dom b ∧ TermChainO b.term bs ∧
        ChainOK (nextPC0 pc0 b) (domRunM b.body dom) bs := hwf
    obtain ⟨hbo, htc, hco⟩ := hwf'
    obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
      bblock_run_bt b σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hbf hbo hi
    cases bs with
    | nil =>
      exact ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1,
        fun R hn hw =>
          hframe1 R hn (fun n h => hw n (List.mem_append_left [] h))⟩
    | cons b2 rest =>
      obtain ⟨vm1, hmi1'⟩ := hmi1
      have hpc1' : σ1.regs.get? Register.PC = some (nextPC0 pc0 b) := by
        rw [endPCB_eq_nextPC0_bt b pc0 L lds (htc : TermNotJrO b.term)] at hpc1
        exact hpc1
      have hlow1 : ∀ j, j < tohostAddr → (writeLog m (wlogM b.body L lds))[j]? = mc[j]? :=
        fun j hj => (writeLog_wlog_low_bt mc b.body m L lds hbf.1 j hj).trans (hlow j hj)
      have hkeys1 : KeysOK (keysG (runGM b.body L lds)) :=
        keysOK_runGM_bt b.body pc0 dom L lds hbo.1 hkeys
      have hdom1 : ∀ n ∈ domRunM b.body dom, n ∈ keysG (runGM b.body L lds) :=
        domRun_keys_bt b.body L lds dom hdom
      obtain ⟨σf, i', hstepsf, hif, hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + blenB b) (nextPC0 pc0 b) vm1 (runGM b.body L lds)
          (ldsRunM b.body lds) mc (writeLog m (wlogM b.body L lds)) (domRunM b.body dom)
          hG1 hpc1' hmi1' hmem1 hlow1 hGH1 hkeys1 hdom1 hcf hco hi1
      refine ⟨σf, i', ?_, hif, hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have h := hsteps1.trans hstepsf
        have e : u + blenB b + chainLen (b2 :: rest)
            = u + (blenB b + chainLen (b2 :: rest)) := by omega
        rw [e] at h
        exact h
      · intro R hn hw
        exact (hframef R hn (fun n h => hw n (List.mem_append_right _ h))).trans
          (hframe1 R hn (fun n h => hw n (List.mem_append_left _ h)))

/-- **The chain lemma.**  A list of basic blocks whose branch/jump targets
chain (checked by the ONE `decide` on `ChainOK` — each successor's entry pc is
pinned to the predecessor's concrete target), from an entry state with pinned
PC / minstret / source registers: the whole multi-block `Steps` path with the
computed final PC (`chainEndPC`; rewrite to the concrete `chainEndPCc` via
`chainEndPC_eq_bt` + `decide` when no `jr` is involved), computed registers
(`runChain`), computed memory (`memChain`), and the frame outside
`noiseRegs ∪ wrChain`.  This is the M4 dispatch-arm-epilogue shape: one
application per arm. -/
theorem bblocks_sound_bt (bs : List BBlock) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + chainLen bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = memChain bs σ.mem L lds ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (chainEndPC pc0 L lds bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runChain bs L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) :=
  bblocks_run_bt bs σ i u pc0 vm L lds σ.mem σ.mem (keysG L)
    hG hpc hmi rfl (fun _ _ => rfl) hL hkeys (fun _ h => h) hfacts hwf hi

end Vsa.Sim
