import Vsa.Sim.SegEvalSound
import Vsa.Sim.BlockAdapter

/-!
# `LoopStep` — the machine-side loop-iteration core + call seam (L4)

The per-iteration step contracts (`ExecWhileStep`'s loop-back branch,
`EvalArgsStep`, `ExecForStep`, `ExecSeqStep`'s continue case) all share ONE
machine-side core: from an entry state pinned at the loop head, the body
segment runs and lands BACK at the head with (a) the computed register outcome,
(b) the canonical write-log memory, (c) memory agreement outside the stack
window and the arena, and (d) the register frame outside the written set. The
φ-extension ghosts and the spec-side `SegEntry`/`ExecEntry` re-entry predicate
stay per-row (they mention the spec store); this file supplies everything
under them:

* `WinsInSA` — a write log's store windows all lie in the stack window
  `[SL.lo, sp)` or the arena `[A.lo, A.hi)`: the GEOMETRY half of every
  loop-back memory-agreement clause (discharged per row from `GeomFacts` /
  `FrameCalc` windows), with append-closure so segment logs compose across
  call seams.
* `wlogM_width` / `evalBlocks_log_width` — reflected logs only ever contain
  1/4/8-byte stores (the `BlockAdapter` disjointness side condition).
* `mem_agree_of_winsInSA` — the loop-back memory agreement, off-the-shelf from
  `BlockAdapter.writeLog_getElem_disjoint` (ONE fold induction, never
  `ExtHashMap` reduction).
* `loopStep` — the packaged loop-back run: `segEval_sound` (L1) + the
  back-edge PC (`chainEndPCc pc0 bs = pc0` via `chainEndPC_eq_bt` under
  `NoJr`) + the memory agreement. A loop row is then: `#derive_case` chain(s)
  + callee Triples via `callStep` + ONE `loopStep` + the per-row φ-glue.
* `callStep` — the call seam: pre-call segment ≫ callee Triple (spec or IH)
  ≫ post-call segment (`Triple.seq` composition; the ghost bridge from the
  callee's post to the post-segment's pins is the per-row glue).

A back-edge is a chain whose last terminator targets its own head —
`BlockTerm`'s "a loop needs NOTHING new" note — so the whole reflection
stack applies unchanged; `loopStep` only adds the loop-specific projections.

Demo: a fabricated one-instruction self-loop (`j .` at `0x80000000`, word
`0x0000006f`) — empty body, `j`-to-self terminator, ONE `decide` for the
structural VC, abstract byte-pins/decode hypotheses (real rows take those
from the `Code.*` pins and the DecodeTable battery).

Timing witness (2026-08-26): see this file's commit gate; the combinator adds
no reflection of its own beyond L1's.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr (Arena)
open Vsa.Alloc (StackLayout)

namespace Vsa.Sim

/-! ## Write-window containment (`WinsInSA`) and its closure -/

/-- Every store window `[e.1, e.1 + e.2.1)` of the log lies in the stack
window `[SL.lo, sp)` or the arena `[A.lo, A.hi)` — where a loop iteration is
allowed to scribble. The loop-back memory-agreement clauses of
`ExecWhileStep`/`EvalArgsStep`/`ExecForStep` are exactly this, stated over
the computed log. -/
def WinsInSA (SL : StackLayout) (sp : Nat) (A : Arena) (log : List WEntry) : Prop :=
  ∀ e ∈ log, (SL.lo ≤ e.1 ∧ e.1 + e.2.1 ≤ sp) ∨ (A.lo ≤ e.1 ∧ e.1 + e.2.1 ≤ A.hi)

/-- Window containment is closed under log append — segment logs compose
across call seams and multi-segment loop bodies. -/
theorem winsInSA_append {SL : StackLayout} {sp : Nat} {A : Arena}
    {l1 l2 : List WEntry} (h1 : WinsInSA SL sp A l1) (h2 : WinsInSA SL sp A l2) :
    WinsInSA SL sp A (l1 ++ l2) := fun e he =>
  (List.mem_append.mp he).elim (h1 e) (h2 e)

/-! ## Reflected logs only contain 1/4/8-byte stores -/

/-- Every entry of a reflected body log has width 1, 2, 4, or 8 (the store kinds
`sb`/`sh`/`sw`/`sd` are the only log producers). -/
theorem wlogM_width : ∀ (is : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (e : WEntry), e ∈ wlogM is L lds → e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
  intro is
  induction is with
  | nil => intro L lds e he; exact by simp [wlogM] at he
  | cons a r ih =>
    intro L lds e he
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    rw [wlogM] at he
    cases akind with
    | sw =>
        rcases List.mem_cons.mp he with heq | hetail
        · subst heq; exact Or.inr (Or.inr (Or.inl rfl))
        · exact ih _ _ _ hetail
    | sd =>
        rcases List.mem_cons.mp he with heq | hetail
        · subst heq; exact Or.inr (Or.inr (Or.inr rfl))
        · exact ih _ _ _ hetail
    | sb =>
        rcases List.mem_cons.mp he with heq | hetail
        · subst heq; exact Or.inl rfl
        · exact ih _ _ _ hetail
    | sh =>
        rcases List.mem_cons.mp he with heq | hetail
        · subst heq; exact Or.inr (Or.inl rfl)
        · exact ih _ _ _ hetail
    | addi => exact ih _ _ _ he
    | add => exact ih _ _ _ he
    | sub => exact ih _ _ _ he
    | or => exact ih _ _ _ he
    | and => exact ih _ _ _ he
    | srl => exact ih _ _ _ he
    | lw => exact ih _ _ _ he
    | lwu => exact ih _ _ _ he
    | ld => exact ih _ _ _ he
    | lbu => exact ih _ _ _ he
    | lh => exact ih _ _ _ he
    | lhu => exact ih _ _ _ he
    | addiw => exact ih _ _ _ he
    | slli => exact ih _ _ _ he
    | srli => exact ih _ _ _ he
    | srai => exact ih _ _ _ he
    | slti => exact ih _ _ _ he
    | slt => exact ih _ _ _ he
    | subw => exact ih _ _ _ he
    | addw => exact ih _ _ _ he
    | auipc => exact ih _ _ _ he
    | lui => exact ih _ _ _ he
    | xori => exact ih _ _ _ he
    | andi => exact ih _ _ _ he
    | ori => exact ih _ _ _ he
    | slliw => exact ih _ _ _ he
    | srliw => exact ih _ _ _ he
    | sraiw => exact ih _ _ _ he

/-- The computed log of a whole chain only contains 1/4/8-byte stores (the
entry state's log must already satisfy it; `init` has `log := []`). -/
theorem evalBlocks_log_width : ∀ (bs : List BBlock) (s : SegEvalState),
    (∀ e ∈ s.log, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8) →
    ∀ e ∈ (evalBlocks bs s).log, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
  intro bs
  induction bs with
  | nil => intro s hlog e he; exact hlog e he
  | cons b bs ih =>
    intro s hlog e he
    refine ih (evalBlock s b) ?_ e he
    intro e' he'
    rcases List.mem_append.mp he' with he' | he'
    · exact hlog e' he'
    · exact wlogM_width b.body s.regs s.loads e' he'

theorem evalBlocks_init_log_width (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (e : WEntry)
    (he : e ∈ (evalBlocks bs (SegEvalState.init L lds)).log) :
    e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 :=
  evalBlocks_log_width bs (SegEvalState.init L lds)
    (fun _ he' => by simp [SegEvalState.init] at he') e he

/-! ## The loop-back memory agreement -/

/-- Outside the stack window and the arena, the computed memory equals the
entry memory — the memory-agreement clause of every loop-back step contract,
derived from `BlockAdapter.writeLog_getElem_disjoint` (one use, no
`ExtHashMap` reduction). -/
theorem mem_agree_of_winsInSA {SL : StackLayout} {sp : Nat} {A : Arena}
    {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry}
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hwin : WinsInSA SL sp A log) :
    ∀ a, ¬ (SL.lo ≤ a ∧ a < sp) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (writeLog m log)[a]? = m[a]? := by
  intro a hstk hare
  have hstk' : a < SL.lo ∨ sp ≤ a := by
    by_cases hc : SL.lo ≤ a
    · exact Or.inr (Nat.not_lt.mp fun hlt => hstk ⟨hc, hlt⟩)
    · exact Or.inl (Nat.not_le.mp hc)
  have hare' : a < A.lo ∨ A.hi ≤ a := by
    by_cases hc : A.lo ≤ a
    · exact Or.inr (Nat.not_lt.mp fun hlt => hare ⟨hc, hlt⟩)
    · exact Or.inl (Nat.not_le.mp hc)
  refine writeLog_getElem_disjoint a log m hw (fun e he => ?_)
  rcases hwin e he with h | h
  · rcases hstk' with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hare' with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-! ## `loopStep` — the packaged loop-back run -/

/-- **The machine-side loop-iteration core.** From an entry state pinned at
the loop head `pc0` (PC / minstret / pin list `L`), a chain `bs` whose
realized end PC is the head again (`hback`, checked through the structural VC
`ChainOK`), and window containment for the computed log (`hwin`, from
`GeomFacts`/`FrameCalc`): the machine runs `evalBlocksFuel bs` steps BACK to
`pc0` with the computed registers (`out.regs`), the canonical write-log
memory, unchanged HTIF output, the register frame outside `noiseRegs ∪
wrChain`, and memory agreement outside the stack window ∪ arena.

The loop rows (`ExecWhileStep` loop-back branch, `EvalArgsStep`, …) compose
this with their φ-extension ghosts and re-entry predicate — the per-row glue
is purely spec-side. -/
theorem loopStep (bs : List BBlock) (σ : MState) (i u : Nat) (pc0 vm : BitVec 64)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (SL : StackLayout) (A : Arena) (sp : Nat)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hi : i < 2)
    (hnjr : NoJr bs)
    (hback : chainEndPCc pc0 bs = pc0)
    (hwin : WinsInSA SL sp A (evalBlocks bs (SegEvalState.init L lds)).log) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + evalBlocksFuel bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem (evalBlocks bs (SegEvalState.init L lds)).log ∧
      σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some pc0 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) ∧
      (∀ a, ¬ (SL.lo ≤ a ∧ a < sp) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        σ'.mem[a]? = σ.mem[a]?) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem, hout, hpc', hmi', hGH, hframe⟩ :=
    segEval_sound bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  refine ⟨σ', i', hsteps, hi', hG', hmem, hout, ?_, hmi', hGH, hframe, ?_⟩
  · have hcc : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pc0 := by
      show chainEndPC pc0 L lds bs = pc0
      rw [chainEndPC_eq_bt bs pc0 L lds hnjr, hback]
    rw [hcc] at hpc'
    exact hpc'
  · intro a hstk hare
    rw [hmem]
    exact mem_agree_of_winsInSA
      (evalBlocks_init_log_width bs L lds) hwin a hstk hare

/-! ## `callStep` — the call seam -/

/-- Compose a pre-call segment, the callee (a spec `Triple` or an IH), and a
post-call segment. `Triple.seq` composition; the ghost bridge from the
callee's postcondition (e.g. `SubEvalReturn`) to the post-call segment's
concrete pins is the per-row glue this leaves to the caller. -/
theorem callStep {P Q R S : Config → Prop}
    (hpre : Triple P Q) (hcall : Triple Q R) (hpost : Triple R S) :
    Triple P S :=
  Triple.seq (Triple.seq hpre hcall) hpost

/-! ## Demo — the fabricated self-loop `j .` -/

/-- A one-instruction self-loop: empty body, `j .` at `0x80000000` (the
J-type encoding of `jal x0, 0`, word `0x0000006f`, LE bytes `6f 00 00 00`). -/
def loopDemoBlk : BBlock :=
  { body := [],
    term := some ⟨0x80000000#64, 0x0000006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x00#8,
      .j, 0, 0, 0#13, 0#21, 0#12⟩ }

/-- **One loop iteration of the self-loop**: from a state pinned at the head,
ONE machine step (the `j`) lands back at the head with memory, output, pins,
and the register frame unchanged, and the memory-agreement clause holding
trivially (the empty log writes nothing). The structural VC closes by ONE
kernel `decide`; the byte pins and the decode fact are hypotheses (real rows
take them from `Code.*` pins and the DecodeTable battery). -/
theorem loopDemo (σ : MState) (i u : Nat) (vm : BitVec 64)
    (SL : StackLayout) (A : Arena) (sp : Nat)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80000000#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hb0 : σ.mem[0x80000000]? = some (0x6f#8))
    (hb1 : σ.mem[0x80000001]? = some (0x00#8))
    (hb2 : σ.mem[0x80000002]? = some (0x00#8))
    (hb3 : σ.mem[0x80000003]? = some (0x00#8))
    (hdec : DecodeFactT ⟨0x80000000#64, 0x0000006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x00#8,
      .j, 0, 0, 0#13, 0#21, 0#12⟩)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x80000000#64) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' [] ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) ∧
      (∀ a, ¬ (SL.lo ≤ a ∧ a < sp) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        σ'.mem[a]? = σ.mem[a]?) := by
  have hfacts : ChainFacts σ.mem σ.mem [] [] [loopDemoBlk] :=
    ⟨⟨trivial, ⟨⟨hb0, hb1, hb2, hb3⟩, hdec⟩, trivial⟩, trivial⟩
  have hlognil : (evalBlocks [loopDemoBlk] (SegEvalState.init [] [])).log = [] := rfl
  have hwrnil : wrChain [loopDemoBlk] = [] := rfl
  have hwf : ChainOK (0x80000000#64) (keysG []) [loopDemoBlk] := by decide
  have hnjr : NoJr [loopDemoBlk] := by decide
  have hback : chainEndPCc (0x80000000#64) [loopDemoBlk] = 0x80000000#64 := by decide
  obtain ⟨σ', i', hsteps, hi', hG', hmem, hout, hpc', hmi', hGH, hframe, hagree⟩ :=
    loopStep [loopDemoBlk] σ i u (0x80000000#64) vm [] [] SL A sp
      hG hpc hmi trivial (by decide) hfacts hwf hi hnjr hback
      (fun _ he => by rw [hlognil] at he; simp at he)
  refine ⟨σ', i', hsteps, hi', hG', ?_, hout, hpc', hmi', hGH, ?_, hagree⟩
  · rw [hmem]; rfl
  · intro R hn
    exact hframe R hn (fun _ hn' => by rw [hwrnil] at hn'; simp at hn')

#print axioms loopStep
#print axioms callStep
#print axioms loopDemo

end Vsa.Sim
