import Vsa.Sim.rows.EnvDefineAppendExact
import Vsa.Sim.BridgeSeg
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.EnvDefBridges
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch08Part31

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.RuntimeRepr
open Vsa.MemRepr

namespace Vsa.Sim

/- The successful malloc-return staging, excluding the `jal memcpy` at b40. -/
#derive_case envDefineMemcpyArgSeg chain
  [(0x80002b30#64, 0x00050493#32)]
    terminator ⟨0x80002b34#64, 0x08050e63#32, 0x63#8, 0x0e#8, 0x05#8, 0x08#8,
      .br bop.BEQ false, 10, 0, 0x009c#13, 0#21, 0#12⟩ ;;
  [(0x80002b38#64, 0x00040613#32),
   (0x80002b3c#64, 0x00090593#32)]

def envDefineMemcpyArgL (copy size name : BitVec 64) : GRegs :=
  [(10, copy), (8, size), (18, name)]

def EnvDefineMemcpyArgPost (copy size name : BitVec 64)
    (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80002b40#64 ∧
  GHolds c.σ (evalBlocks envDefineMemcpyArgSeg
    (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs ∧
  c.tick < 2

theorem envDefineMemcpyArgRow (copy size name : BitVec 64) (m0 : Mem) :
    Triple
      (SegPre envDefineMemcpyArgSeg (envDefineMemcpyArgL copy size name) []
        0x80002b30#64 m0)
      (EnvDefineMemcpyArgPost copy size name m0) := by
  apply segToTriple envDefineMemcpyArgSeg (envDefineMemcpyArgL copy size name) []
    0x80002b30#64 m0 (EnvDefineMemcpyArgPost copy size name m0)
    (by show ChainOK 0x80002b30#64 [10, 8, 18] envDefineMemcpyArgSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa +ground [envDefineMemcpyArgSeg, evalBlocks, evalBlock, SegEvalState.init,
      writeLog, wlogM] using hmem'
  · rw [hpc']
    rfl

def AbiExceptS1 (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x9)

/-- Exact successful malloc-return staging followed by the `jal memcpy`. -/
theorem envDefineMemcpyCallRun
    (σ : MState) (i u : Nat) (vminstret copy size name : BitVec 64)
    (m0 : Mem)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80002b30#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (envDefineMemcpyArgL copy size name))
    (hfacts : ChainFacts σ.mem σ.mem
      (envDefineMemcpyArgL copy size name) [] envDefineMemcpyArgSeg)
    (hjalmem : Vsa.Sim.Code.Env_defineLoaded m0)
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩
        ⟨σ2, i2, u + evalBlocksFuel envDefineMemcpyArgSeg + 1⟩ ∧
      i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some 0x80006bc8#64 ∧
      σ2.regs.get? Register.x1 = some 0x80002b44#64 ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks envDefineMemcpyArgSeg
        (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs ∧
      σ2.mem = m0 ∧
      (∀ R, AbiExceptS1 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSegFramed AbiExceptS1 envDefineMemcpyArgSeg
    (envDefineMemcpyArgL copy size name) [] σ i u 0x80002b30#64
    0x80006bc8#64 0x80002b44#64 vminstret m0 hG hpc hminstret hmem hL
    (by have hk : keysG (envDefineMemcpyArgL copy size name) = [10, 8, 18] := rfl
        rw [hk]; decide) hfacts hi
    (by show ChainOK 0x80002b30#64 [10, 8, 18] envDefineMemcpyArgSeg; decide)
    (by show ∀ rr ∈ noiseRegs, AbiExceptS1 rr = false; decide)
    (by show WrChainAvoids AbiExceptS1 envDefineMemcpyArgSeg; decide)
    (by
      have hk : keysG (evalBlocks envDefineMemcpyArgSeg
          (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs =
          [11, 12, 9, 10, 8, 18] := rfl
      rw [hk]
      decide)
    (by
      have hk : keysG (evalBlocks envDefineMemcpyArgSeg
          (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs =
          [11, 12, 9, 10, 8, 18] := rfl
      unfold KeysAvoidRa
      rw [hk]
      decide)
    (by intro R hR
        exact (Bool.and_eq_true _ _).mp hR |>.1)
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  have hpc'' : σ'.regs.get? Register.PC = some 0x80002b40#64 := by
    rw [hpc', evalBlocksPC, chainEndPC_eq_bt envDefineMemcpyArgSeg _ _ _ (by decide)]
    try rfl
  have hlog : writeLog m0 (evalBlocks envDefineMemcpyArgSeg
      (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).log = m0 := by rfl
  have hloaded' : Vsa.Sim.Code.Env_defineLoaded σ'.mem := by
    rw [hmem', hlog]
    exact hjalmem
  obtain ⟨hb0, hb1, hb2, hb3⟩ :=
    Vsa.Sim.Code.env_define_at_80002b40 hloaded'
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal σ' i' u' 0x80002b40#64 vm' 0x088040ef#32 0x004088#21
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt 0x80002b40#64 4)
      0xef#8 0x40#8 0x80#8 0x08#8 hG' hpc'' hmi'v hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (Vsa.Sim.DecodeTable.decode_088040ef (afterPrelude σ')
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.misa)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.cur_privilege)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt 0x80002b40#64 4)) hi'
  have hlink : BitVec.addInt 0x80002b40#64 4 = (0x80002b44#64 : BitVec 64) := by
    decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs (by decide)

#print axioms envDefineMemcpyArgRow
#print axioms envDefineMemcpyCallRun

end Vsa.Sim
