import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockTactics
import Vsa.Sim.NegTailSites

/-!
# `NegBlockProto` — prototype: the neg-tail load/store run via ONE block lemma

Proof-of-concept for migrating the hand-threaded `blockC_neg` (EvalNegSim2) to
the basic-block reflection lemma. The segment `0x800039ac – 0x800039c0`
(σ5–σ10 in the hand proof, **180 lines**): three loads that extract the
sub-value's payload / dead / kind words, then three error-arg staging stores.

Here it is ONE `bblock_sound_bt` application (fall-through terminator). The
loads' values (`bytesVal`), the three stores (`writeLog`), the PC, the `Steps`
chain, the minstret/tick/output invariants, and the callee-saved frame all come
out computed. Compare the line counts at the bottom of the file.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (Eval_exprLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The load/store run as a basic block: `ld a1,152(sp); ld a4,160(sp);
lw a0,144(sp); sd a3,240(sp); sd a1,248(sp); sd a4,256(sp)`, fall-through. -/
def negLoadStoreBlk : BBlock :=
  { body :=
      [mkLine 0x800039ac#64 0x09813583#32,   -- ld a1,152(sp)
       mkLine 0x800039b0#64 0x0a013703#32,   -- ld a4,160(sp)
       mkLine 0x800039b4#64 0x09012503#32,   -- lw a0,144(sp)
       mkLine 0x800039b8#64 0x0ed13823#32,   -- sd a3,240(sp)
       mkLine 0x800039bc#64 0x0eb13c23#32,   -- sd a1,248(sp)
       mkLine 0x800039c0#64 0x10e13023#32],  -- sd a4,256(sp)
    term := none }

/-- Bundled load side-conditions (8-byte): RAM bounds + HTIF-disjoint window +
alignment + the byte pins. Defeq to the `MemFacts` load leaf `⟨⟨lo,hi,win,al⟩,
pins⟩` that `bblock_sound_bt` consumes, so a block proof discharges it with
`exact`. Collapses each load's 5-hypothesis battery to one. -/
def LdOK8 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  (0x80000000 ≤ ea.toNat ∧ ea.toNat + 8 ≤ 0x100000000 ∧
    (ea.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea.toNat) ∧ ea.toNat % 8 = 0) ∧
  LPins8 m ea.toNat bs

/-- Bundled load side-conditions (4-byte), cf. `LdOK8`. -/
def LdOK4 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  (0x80000000 ≤ ea.toNat ∧ ea.toNat + 4 ≤ 0x100000000 ∧
    (ea.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea.toNat) ∧ ea.toNat % 4 = 0) ∧
  LPins4 m ea.toNat bs

/-- Bundled store side-conditions (8-byte): RAM bounds + above-HTIF window +
alignment. Defeq to the `MemFacts` store leaf `⟨lo,hi,win,al⟩`. -/
def StOK8 (ea : BitVec 64) : Prop :=
  0x80000000 ≤ ea.toNat ∧ ea.toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ ea.toNat ∧ ea.toNat % 8 = 0

/-- Full-output collapse of the neg load/store run (σ4→σ10 of `blockC_neg`, the
6 steps `0x800039ac → 0x800039c4`): one `bblock_sound_bt`, with **every**
downstream fact the domain tail consumes projected out — the three load results
(`x11`/`x14`/`x10`), the carried callee-saved (`x8` via the block frame,
`x9`/`x13`/`x2` via the pin list), and the memory in `writeLog` form (ready for
`writeLog_agreeP_disjoint`). This is the primitive the `blockC_neg` migration
consumes in place of the ~200-line per-step `obs_*_other` carry battery. -/
theorem neg_loadstore_full (σ : MState) (i u : Nat)
    (vm v2 v13 v9 v8 : BitVec 64)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800039ac#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Eval_exprLoaded σ.mem)
    (hLdP : LdOK8 σ.mem (v2 + sign_extend (m := 64) (0x098#12)) [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7])
    (hLdD : LdOK8 σ.mem (v2 + sign_extend (m := 64) (0x0a0#12)) [q0,q1,q2,q3,q4,q5,q6,q7])
    (hLdK : LdOK4 σ.mem (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3])
    (hSt1 : StOK8 (v2 + sign_extend (m := 64) (0x0f0#12)))
    (hSt2 : StOK8 (v2 + sign_extend (m := 64) (0x0f8#12)))
    (hSt3 : StOK8 (v2 + sign_extend (m := 64) (0x100#12)))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 6⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x800039c4#64) ∧
      σ'.regs.get? Register.x11 = some (bytesVal .ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7]) ∧
      σ'.regs.get? Register.x14 = some (bytesVal .ld [q0,q1,q2,q3,q4,q5,q6,q7]) ∧
      σ'.regs.get? Register.x10 = some (bytesVal .lw [kb0,kb1,kb2,kb3]) ∧
      σ'.regs.get? Register.x13 = some v13 ∧
      σ'.regs.get? Register.x9 = some v9 ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x8 = some v8 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      σ'.mem = writeLog σ.mem (wlogM negLoadStoreBlk.body [(2, v2), (13, v13), (9, v9)]
        [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM negLoadStoreBlk.body, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    bblock_sound_bt negLoadStoreBlk σ i u (0x800039ac#64) vm
      [(2, v2), (13, v13), (9, v9)]
      [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]
      hG hpc hmi ⟨hx2, hx13, hx9, trivial⟩ (show KeysOK [2, 13, 9] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact hLdP
        · exact hLdD
        · exact hLdK
        · exact hSt1
        · exact hSt2
        · exact hSt3)
      (show BBlockOK (0x800039ac#64) [2, 13, 9] negLoadStoreBlk by decide)
      hi
  rw [show endPCB (0x800039ac#64) negLoadStoreBlk [(2, v2), (13, v13), (9, v9)]
        [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]]
      = (0x800039c4#64 : BitVec 64) from by
        show endPCM (0x800039ac#64) negLoadStoreBlk.body = (0x800039c4#64 : BitVec 64)
        decide] at hpc'
  refine ⟨σ', i', hsteps, hi', hG', hout', hpc',
    hGH.2.2.1, hGH.2.1, hGH.1, hGH.2.2.2.2.1, hGH.2.2.2.2.2.1, hGH.2.2.2.1, ?_, hmi', hmem', hframe⟩
  -- x8 survives via the block frame (x8 ∉ noiseRegs, x8 ∉ gprReg '' wrRegsM)
  rw [hframe Register.x8 (by decide) (by decide)]; exact hx8

def negPrologueBlk : BBlock :=
  { body :=
      [mkLine 0x800035ec#64 0x00842703#32,   -- lw a4,8(s0)
       mkLine 0x800035f0#64 0x00c00793#32,   -- li a5,12
       mkLine 0x800035f4#64 0x09013683#32],  -- ld a3,144(sp)
    term := some ⟨0x800035f8#64, 0x3af70a63#32, 0x63#8, 0x0a#8, 0xf7#8, 0x3a#8,
      .br bop.BEQ true, 14, 15, 0x03b4#13, 0#21, 0#12⟩ }

/-- Full-output collapse of the neg PROLOGUE (σ0→σ4 of `blockC_neg`, the 4 steps
`0x800035ec → 0x800039ac`: op-token load, `li a5,12`, kind-dword load, and the
taken `beq a4,a5`). One `bblock_sound_bt`. -/
theorem neg_prologue_block (σ : MState) (i u : Nat)
    (vm v8 v2 v9 v1 : BitVec 64)
    (ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800035ec#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Eval_exprLoaded σ.mem)
    (hob12 : bytesVal .lw [ob0,ob1,ob2,ob3] = (12#64 : BitVec 64))
    (hLdO : LdOK4 σ.mem (v8 + sign_extend (m := 64) (0x008#12)) [ob0,ob1,ob2,ob3])
    (hLdK : LdOK8 σ.mem (v2 + sign_extend (m := 64) (0x090#12)) [kb0,kb1,kb2,kb3,d4,d5,d6,d7])
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 4⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x800039ac#64) ∧
      σ'.regs.get? Register.x14 = some (bytesVal .lw [ob0,ob1,ob2,ob3]) ∧
      σ'.regs.get? Register.x15 = some (12#64) ∧
      σ'.regs.get? Register.x13 = some (bytesVal .ld [kb0,kb1,kb2,kb3,d4,d5,d6,d7]) ∧
      σ'.regs.get? Register.x9 = some v9 ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      σ'.regs.get? Register.x8 = some v8 ∧
      σ'.regs.get? Register.x1 = some v1 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM negPrologueBlk.body, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    bblock_sound_bt negPrologueBlk σ i u (0x800035ec#64) vm
      [(8, v8), (2, v2), (9, v9), (1, v1)]
      [[ob0,ob1,ob2,ob3], [kb0,kb1,kb2,kb3,d4,d5,d6,d7]]
      hG hpc hmi ⟨hx8, hx2, hx9, hx1, trivial⟩ (show KeysOK [8, 2, 9, 1] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact hLdO
        · exact hLdK
        · show guardB bop.BEQ (bytesVal MKind.lw [ob0,ob1,ob2,ob3])
              ((0#64:BitVec 64) + sign_extend (m := 64) (0x00c#12)) = true
          rw [hob12]; decide)
      (show BBlockOK (0x800035ec#64) [8, 2, 9, 1] negPrologueBlk by decide)
      hi
  exact ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc',
    hGH.2.2.1, hGH.2.1, hGH.1, hGH.2.2.2.2.2.1, hGH.2.2.2.2.1, hGH.2.2.2.1, hGH.2.2.2.2.2.2.1,
    hmi', hframe⟩

def negTailBlkA : BBlock :=
  { body :=
      [mkLine 0x800039c4#64 0x00200613#32,   -- li a2,2
       mkLine 0x800039c8#64 0x00442403#32],  -- lw s0,4(s0)
    term := some ⟨0x800039cc#64, 0x18c51663#32, 0x63#8, 0x16#8, 0xc5#8, 0x18#8,
      .br bop.BNE false, 10, 12, 0x018c#13, 0#21, 0#12⟩ }

def negTailBlkB : BBlock :=
  { body :=
      [mkLine 0x800039d0#64 0x40b005b3#32,   -- neg a1,a1 (sub x11,x0,x11)
       mkLine 0x800039d4#64 0x00048513#32],  -- mv a0,s1
    term := none }

def negTailChain : List BBlock := [negTailBlkA, negTailBlkB]

/-- Full-output collapse of the neg TAIL (σ10→σ15, 5 steps `0x800039c4 →
0x800039d8`: li a2,2; lw s0,4(s0); bne a0,a2 not-taken; neg a1,a1; mv a0,s1)
via ONE `bblocks_sound_bt`. The `bne` splits it into two blocks; the `neg`
needs the `.sub` block-model kind. `jal value_int`@σ16 stays the call seam. -/
theorem neg_tail_block (σ : MState) (i u : Nat)
    (vm v8 v9 v2 p11 : BitVec 64) (lb0 lb1 lb2 lb3 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800039c4#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx10 : σ.regs.get? Register.x10 = some (2#64))
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hx11 : σ.regs.get? Register.x11 = some p11)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Eval_exprLoaded σ.mem)
    (hLdL : LdOK4 σ.mem (v8 + sign_extend (m := 64) (0x004#12)) [lb0,lb1,lb2,lb3])
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 5⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (0x800039d8#64) ∧
      σ'.regs.get? Register.x10 = some v9 ∧
      σ'.regs.get? Register.x11 = some ((0#64) - p11) ∧
      σ'.regs.get? Register.x9 = some v9 ∧
      σ'.regs.get? Register.x2 = some v2 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain negTailChain, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    bblocks_sound_bt negTailChain σ i u (0x800039c4#64) vm
      [(8, v8), (10, 2#64), (9, v9), (11, p11), (2, v2)] [[lb0,lb1,lb2,lb3]]
      hG hpc hmi ⟨hx8, hx10, hx9, hx11, hx2, trivial⟩ (show KeysOK [8, 10, 9, 11, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact hLdL
        · show guardB bop.BNE (2#64) ((0#64) + sign_extend (m := 64) (0x002#12)) = false
          decide)
      (show ChainOK (0x800039c4#64) [8, 10, 9, 11, 2] negTailChain by decide)
      hi
  rw [show memChain negTailChain σ.mem [(8, v8), (10, 2#64), (9, v9), (11, p11), (2, v2)]
        [[lb0,lb1,lb2,lb3]] = σ.mem from by rfl] at hmem'
  refine ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', ?_, hGH.2.1, hGH.2.2.2.2.1,
    hGH.2.2.2.2.2.1, hmi', hframe⟩
  have h := hGH.1
  change σ'.regs.get? Register.x10 = some (v9 + sign_extend (m := 64) (0x000#12)) at h
  rwa [show (v9 + sign_extend (m := 64) (0x000#12)) = v9 from by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero]] at h

end Vsa.Sim
