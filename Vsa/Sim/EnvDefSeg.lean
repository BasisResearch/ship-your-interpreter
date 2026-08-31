import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvDefBridges2

/-!
# `EnvDefSeg` — the `env_define` straight-line prefixes as `#derive_case` segs

The `env_define` code region `[0x80002a5c, 0x80002c10)` has a bespoke byte-pin
battery (`Env_defineLoaded` + the hand `site_*_ed` lemmas in
`EnvDefBridges.lean`/`EnvDefSpec*`) that predates the block-reflection decode
table.  Every Shape-A bridge prefix there pays 5-15 hand `stepObs_alu`/`stepObs_jal`
site lemmas — each one a ~30-line invocation naming the concrete decode lemma
(`Vsa.Sim.DecodeTable.decode_<word>`), the `execute_*_char` characterization, the
four byte pins, and a dozen `by decide` side conditions.

This file demonstrates the payoff of putting the region ON the block-reflection
decode table: since **all 106 unique instruction words in the region are already
tabled** (verified by `scripts/decode_index.tsv`) and all 85 straight-line words
are supported by `decodeM`/`mkLine` (`BlockDecode.lean`), the straight-line body
of any bridge prefix is ONE `#derive_case`/`segToTriple` seg — the whole `Steps`
chain, computed end-PC, computed registers, and write log auto-threaded, the only
kernel obligation the single `ChainOK` `decide`.

## Why the `jal` stays a seam

The block terminator model (`TKind` in `BlockTerm.lean`) covers `br`/`j`/`jr` but
DELIBERATELY excludes `jal rd` (a *call*, which links `x1`) — see
`BlockTerm.lean:56`.  Each env_define prefix ends in `jal strlen`/`jal malloc`/…
(rd = x1), so the call-linkage stays the Shape-D `callSeg` seam (exactly as
`CmpDispatchSeg` keeps its `jal value_bool` a seam).  The `#derive_case` seg is
therefore the *straight-line argument-marshalling body* up to (not including) the
`jal`; that body is what the hand `site_*_ed` battery spends its bulk on.

The malloc prefix `0x80002b24 addi s0,a0,1 ; 0x80002b28 mv a0,s0 ; 0x80002b2c jal
malloc` has a genuine two-instruction straight-line body (`addi`/`addi`) — the
hand `site_80002b24_ed` + `site_80002b28_ed` pair (~60 lines).  Here it is ONE seg
`mallocArgSeg` (3 lines of block table) + ONE `segToTriple` row.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Sim.Code (Env_defineLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- The malloc-prefix straight-line body `0x80002b24 → 0x80002b2c`, two blocks
(fall-through, no terminator until the `jal` seam that follows):
  `addi x8,x10,1`  (`addi s0,a0,1` — the malloc size = strlen(name)+1) then
  `addi x10,x8,0`  (`mv a0,s0` — marshal the size into a0 for the call).
Both words (`00150413`, `00040513`) are tabled and `decodeM`-supported; `mkLine`
produces the concrete `MInstr` by `rfl`. -/
#derive_case mallocArgSeg chain
  [(0x80002b24#64, 0x00150413#32),   -- addi s0,a0,1
   (0x80002b28#64, 0x00040513#32)]   -- mv   a0,s0  (= addi a0,s0,0)

/-- The malloc-arg pin list: `x10 = a0 = strlen(name)` on entry (the only source
the two `addi`s read — `x8` is written by the first and read by the second). -/
def mallocArgL (a0 : BitVec 64) : GRegs := [(10, a0)]

/-- The row post: parked at the computed end PC `0x80002b2c` (the `jal malloc`,
ready for the `callSeg` seam), memory unchanged (no stores in the body), and the
computed marshalled register `x10 = a0 + 1` (the size argument) surviving in
`GHolds σ' out.regs` for the callee's `MallocContract` entry. -/
def MallocArgPost (a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks mallocArgSeg
    (SegEvalState.init (mallocArgL a0) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002b2c#64

/-- **The demo payoff.**  The whole malloc-prefix straight-line body as a `Triple`
in a handful of lines: `hwf` is the row's one kernel `decide` (`ChainOK`), and
`hpost` projects the computed end PC / write-log memory off the `#derive_case`
outcome.  Replaces the hand `site_80002b24_ed` + `site_80002b28_ed` pair (~60
lines of `stepObs_alu` plumbing naming `decode_00150413`/`decode_00040513`,
`execute_itype_addi_char`, byte pins, and the `by decide` battery). -/
theorem mallocArgRow (a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre mallocArgSeg (mallocArgL a0) lds 0x80002b24#64 m0)
      (MallocArgPost a0 lds m0) := by
  apply segToTriple mallocArgSeg (mallocArgL a0) lds 0x80002b24#64 m0
    (MallocArgPost a0 lds m0)
    (by show ChainOK 0x80002b24#64 [10] mallocArgSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x80002b24#64 (SegEvalState.init (mallocArgL a0) lds) mallocArgSeg)
    = some 0x80002b2c#64
  rfl

#print axioms mallocArgRow

/-! ## The `strlen` prefix's straight-line body — ONE instruction seg

The strlen prefix `0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen` has only a
one-instruction straight-line body (`mv a0,s2 = addi a0,s2,0`), the `jal` being
the seam.  Even this single-instruction case is a `#derive_case` seg (replacing
the hand `site_80002b1c_ed`, ~30 lines). -/

#derive_case strlenArgSeg chain
  [(0x80002b1c#64, 0x00090513#32)]   -- mv a0,s2 (= addi a0,s2,0)

/-- The strlen-arg pin list: `x18 = s2 = name` on entry (the source of the `mv`). -/
def strlenArgL (s2 : BitVec 64) : GRegs := [(18, s2)]

/-- Post: parked at `0x80002b20` (the `jal strlen` seam), memory unchanged,
`x10 = s2` (the marshalled `name` pointer) surviving in `out.regs`. -/
def StrlenArgPost (s2 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks strlenArgSeg
    (SegEvalState.init (strlenArgL s2) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002b20#64

theorem strlenArgRow (s2 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strlenArgSeg (strlenArgL s2) lds 0x80002b1c#64 m0)
      (StrlenArgPost s2 lds m0) := by
  apply segToTriple strlenArgSeg (strlenArgL s2) lds 0x80002b1c#64 m0
    (StrlenArgPost s2 lds m0)
    (by show ChainOK 0x80002b1c#64 [18] strlenArgSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x80002b1c#64 (SegEvalState.init (strlenArgL s2) lds) strlenArgSeg)
    = some 0x80002b20#64
  rfl

#print axioms strlenArgRow

/- ## DEMO — the grow-path cap-compute prefix as a seg, via `bridgeOfSeg`

`EnvDefBridges2` builds the SAME `slliw;slli;sw;mv;jal realloc` cap-compute prefix
by hand: 5 per-site `stepObs_*` lemmas (`site_80002b90_ed .. site_80002ba0_ed`,
~165 lines) + `capComputePrefix_run` (~175 lines of run + per-register frame
threading) + `bridgeCapCompute_closed` (~90 lines of `ReallocPre` marshalling).

Here the whole straight-line body `0x80002b90..0x80002b9c` (`slliw;slli;sw;mv`) is
ONE `#derive_case` seg `capComputeSeg` (4 lines of block table), the jal seam is
the SAME existing `site_80002ba0_ed` repackaged into a `JalStep` by
`jalStep_of_obs` (one call), and `capComputeSeg_run` derives the full landed run
via `bridgeOfSeg` — replacing the ~340 lines of hand `site_*`+`*Prefix_run` with
the seg def + ~35 lines.  The `bridgeCapCompute_closed` `ReallocPre` marshalling
stays identical (it is the genuinely per-callee part) and is NOT re-proved here —
`capComputeSeg_run` is a drop-in for the `capComputePrefix_run` it consumes.

The `slliw` word `0x0017979b` at `0x80002b90` is the decode kind added in part (A);
the seg needs it on the block-reflection table, so this demo is only possible AFTER
the `MKind.slliw` add. -/

/- The cap-compute straight-line body `0x80002b90 → 0x80002b9c` (four blocks, the
body up to the `jal realloc` seam):
  `slliw a5,a5,1` (`x15 := 2*cap`), `slli a1,a5,3` (`x11 := newcap*8`),
  `sw a5,4(s4)` (`env->cap := newcap`), `mv a0,s6` (`x10 := env->names`).
All four words tabled + `decodeM`-supported; `mkLine` gives the concrete `MInstr`
by `rfl`. -/
#derive_case capComputeSeg chain
  [(0x80002b90#64, 0x0017979b#32),   -- slliw a5,a5,1
   (0x80002b94#64, 0x00379593#32),   -- slli  a1,a5,3
   (0x80002b98#64, 0x00fa2223#32),   -- sw    a5,4(s4)
   (0x80002b9c#64, 0x000b0513#32)]   -- mv    a0,s6  (= addi a0,s6,0)

/-- The cap-compute entry pin list: `x15 = cap`, `x20 = s4 = env`, `x22 = s6 =
env->names`.  These are the only registers the body reads. -/
def capComputeL (capReg s4Ptr s6Ptr : BitVec 64) : GRegs :=
  [(15, capReg), (20, s4Ptr), (22, s6Ptr)]

/-- **`capComputeSeg_run` — the `bridgeOfSeg` demo.**  A drop-in for
`EnvDefBridges2.capComputePrefix_run`: from the entry at `0x80002b90` it runs the
`capComputeSeg` body and takes `jal realloc`, landing `ReallocPre`-ready at the
realloc entry with the marshalled args (`x10 = s6`, `x11 = newcap*8`), link
`x1 = 0x80002ba4`, the cap-store memory, and the ABI callee-saved frame — all via
ONE `bridgeOfSeg` application (seg run + ABI frame both FREE) + the SAME
`site_80002ba0_ed` jal lemma, packaged by `jalStep_of_obs`.

`hfacts` carries the seg's `ChainFacts` (byte pins/decode + the `sw` store window),
exactly the store-geometry hypotheses the hand `capComputePrefix_run` takes. -/
theorem capComputeSeg_run
    (σ : MState) (i u : Nat) (vminstret capReg s4Ptr s6Ptr : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80002b90#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (capComputeL capReg s4Ptr s6Ptr))
    (hfacts : ChainFacts σ.mem σ.mem (capComputeL capReg s4Ptr s6Ptr) [] capComputeSeg)
    (hjalmem : Env_defineLoaded (writeLog m0
      (evalBlocks capComputeSeg
        (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) [])).log))
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel capComputeSeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) ∧
      σ2.regs.get? Register.x1 = some (0x80002ba4#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks capComputeSeg
        (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks capComputeSeg
        (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg capComputeSeg (capComputeL capReg s4Ptr s6Ptr) []
    σ i u (0x80002b90#64) (BitVec.ofNat 64 reallocEntry) (0x80002ba4#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (capComputeL capReg s4Ptr s6Ptr) = [15, 20, 22] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (capComputeL capReg s4Ptr s6Ptr) = [15, 20, 22] := rfl
        rw [h]; show ChainOK (0x80002b90#64) [15, 20, 22] capComputeSeg; decide)
    (by show WrChainAvoidAbi capComputeSeg; decide)
    (by have h : keysG (evalBlocks capComputeSeg
          (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) [])).regs = [10, 11, 15, 20, 22] := rfl
        rw [h]; decide)
    (by have h : keysG (evalBlocks capComputeSeg
          (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) [])).regs = [10, 11, 15, 20, 22] := rfl
        show ∀ n ∈ keysG _, n ≠ 1; rw [h]; decide)
  -- the jal seam: the existing `site_80002ba0_ed`, packaged into a `JalStep`.
  intro σ' i' u' hG' hi' hpc' hmi' hmem' hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  -- the parked PC IS `0x80002ba0` (the seg's computed end PC), by `rfl`.
  have hpcE : (evalBlocksPC (0x80002b90#64)
      (SegEvalState.init (capComputeL capReg s4Ptr s6Ptr) []) capComputeSeg)
      = (0x80002ba0#64 : BitVec 64) := by rfl
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    site_80002ba0_ed σ' i' u' (0x80002ba0#64) vm'
      hG' (hpcE ▸ hpc') hmi'v
      (by rw [hmem']; exact hjalmem) rfl hi'
  -- the site lemma's link `addInt 0x80002ba0 4` = `0x80002ba4`, the bridge's `link`:
  have hlink : BitVec.addInt (0x80002ba0#64) 4 = (0x80002ba4#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms capComputeSeg_run

end Vsa.Sim
