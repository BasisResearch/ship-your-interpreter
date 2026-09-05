import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.Code.Env_set

/-! The successful `env_set` epilogue, including the concrete `ret`. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

#derive_case envSetReturnSeg chain
  [(0x80002d68#64, 0x00100513#32),   -- li   a0,1
   (0x80002d6c#64, 0x03813083#32),   -- ld   ra,56(sp)
   (0x80002d70#64, 0x03013403#32),   -- ld   s0,48(sp)
   (0x80002d74#64, 0x02813483#32),   -- ld   s1,40(sp)
   (0x80002d78#64, 0x02013903#32),   -- ld   s2,32(sp)
   (0x80002d7c#64, 0x01813983#32),   -- ld   s3,24(sp)
   (0x80002d80#64, 0x01013a03#32),   -- ld   s4,16(sp)
   (0x80002d84#64, 0x00813a83#32),   -- ld   s5,8(sp)
   (0x80002d88#64, 0x04010113#32)]   -- addi sp,sp,64
    terminator ⟨0x80002d8c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def envSetReturnL (sp : BitVec 64) : GRegs := [(2, sp)]

def envSetWordBytes (v : BitVec 64) : List (BitVec 8) :=
  [(sdData_val v).extractLsb' 0 8, (sdData_val v).extractLsb' 8 8,
   (sdData_val v).extractLsb' 16 8, (sdData_val v).extractLsb' 24 8,
   (sdData_val v).extractLsb' 32 8, (sdData_val v).extractLsb' 40 8,
   (sdData_val v).extractLsb' 48 8, (sdData_val v).extractLsb' 56 8]

theorem envSetWordBytes_val (v : BitVec 64) :
    bytesVal MKind.ld (envSetWordBytes v) = v :=
  sext_reassemble v
    ((sdData_val v).extractLsb' 0 8) ((sdData_val v).extractLsb' 8 8)
    ((sdData_val v).extractLsb' 16 8) ((sdData_val v).extractLsb' 24 8)
    ((sdData_val v).extractLsb' 32 8) ((sdData_val v).extractLsb' 40 8)
    ((sdData_val v).extractLsb' 48 8) ((sdData_val v).extractLsb' 56 8)
    rfl rfl rfl rfl rfl rfl rfl rfl

def envSetReturnLds (ret r8 r9 r18 r19 r20 r21 : BitVec 64) :
    List (List (BitVec 8)) :=
  [envSetWordBytes ret, envSetWordBytes r8, envSetWordBytes r9,
   envSetWordBytes r18, envSetWordBytes r19, envSetWordBytes r20,
   envSetWordBytes r21]

def EnvSetReturnPost (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.mem = m0 ∧ c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some
    (evalBlocksPC 0x80002d68#64
      (SegEvalState.init (envSetReturnL sp) lds) envSetReturnSeg) ∧
  c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  GHolds c.σ (evalBlocks envSetReturnSeg
    (SegEvalState.init (envSetReturnL sp) lds)).regs

theorem env_set_return_row (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (out0 : Array String) :
    Triple
      (SegPreO envSetReturnSeg (envSetReturnL sp) lds 0x80002d68#64 m0 out0)
      (EnvSetReturnPost sp lds m0 out0) := by
  apply segToTripleOut envSetReturnSeg (envSetReturnL sp) lds 0x80002d68#64
    m0 out0 (EnvSetReturnPost sp lds m0 out0)
    (by show ChainOK 0x80002d68#64 [2] envSetReturnSeg; decide)
  intro σ' i' u' hG' hi' hmem' hout' hpc' hmi' hregs
  refine ⟨hG', hi', ?_, hout', hpc', ?_, hmi', hregs⟩
  · simpa using hmem'
  · have hone : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12)) = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [← hone]
    exact gholds_lookup (n := 10)
      (v := (0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12)) _ hregs (by rfl)

structure EnvSetReturnExactPost
    (sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (m0 : Mem) (out0 : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m0
  output : c.σ.sailOutput = out0
  pc : c.σ.regs.get? Register.PC = some ret
  found : c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  ra : c.σ.regs.get? Register.x1 = some ret
  sp : c.σ.regs.get? Register.x2 = some (sp + 64#64)
  s0 : c.σ.regs.get? Register.x8 = some r8
  s1 : c.σ.regs.get? Register.x9 = some r9
  s2 : c.σ.regs.get? Register.x18 = some r18
  s3 : c.σ.regs.get? Register.x19 = some r19
  s4 : c.σ.regs.get? Register.x20 = some r20
  s5 : c.σ.regs.get? Register.x21 = some r21

theorem env_set_return_exact
    (sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (m0 : Mem) (out0 : Array String)
    (hret : BitVec.update (ret + sign_extend (m := 64) (0x000#12)) 0 0#1 = ret) :
    Triple
      (SegPreO envSetReturnSeg (envSetReturnL sp)
        (envSetReturnLds ret r8 r9 r18 r19 r20 r21) 0x80002d68#64 m0 out0)
      (EnvSetReturnExactPost sp ret r8 r9 r18 r19 r20 r21 m0 out0) := by
  apply Triple.rmap ?_
    (env_set_return_row sp (envSetReturnLds ret r8 r9 r18 r19 r20 r21) m0 out0)
  intro c h
  obtain ⟨hG, htick, hmem, hout, hpc, hfound, hmi, hregs⟩ := h
  have hpc' := hpc
  change c.σ.regs.get? Register.PC = some
    (BitVec.update
      (bytesVal MKind.ld (envSetWordBytes ret) + sign_extend (m := 64) (0x000#12))
      0 0#1) at hpc'
  rw [envSetWordBytes_val, hret] at hpc'
  have hra := gholds_lookup (n := 1)
    (v := bytesVal MKind.ld (envSetWordBytes ret)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hra
  have hs0 := gholds_lookup (n := 8)
    (v := bytesVal MKind.ld (envSetWordBytes r8)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs0
  have hs1 := gholds_lookup (n := 9)
    (v := bytesVal MKind.ld (envSetWordBytes r9)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs1
  have hs2 := gholds_lookup (n := 18)
    (v := bytesVal MKind.ld (envSetWordBytes r18)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs2
  have hs3 := gholds_lookup (n := 19)
    (v := bytesVal MKind.ld (envSetWordBytes r19)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs3
  have hs4 := gholds_lookup (n := 20)
    (v := bytesVal MKind.ld (envSetWordBytes r20)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs4
  have hs5 := gholds_lookup (n := 21)
    (v := bytesVal MKind.ld (envSetWordBytes r21)) _ hregs (by rfl)
  rw [envSetWordBytes_val] at hs5
  have hsp := gholds_lookup (n := 2)
    (v := sp + sign_extend (m := 64) (0x040#12)) _ hregs (by rfl)
  have hspEq : sp + sign_extend (m := 64) (0x040#12) = sp + 64#64 := by
    congr 1
  rw [hspEq] at hsp
  exact
    { good := hG, tick := htick, mem := hmem, output := hout, pc := hpc',
      found := hfound, minstret := hmi, ra := hra, sp := hsp, s0 := hs0, s1 := hs1,
      s2 := hs2, s3 := hs3, s4 := hs4, s5 := hs5 }

#print axioms env_set_return_row
#print axioms env_set_return_exact

end Vsa.Sim
