import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.EnvSetSites
import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.EnvSetReturn

/-!
# `env_set` successful update block

The first matching frame reaches `0x80002d3c`.  This reflected segment loads
the frame value-array pointer and the three words of the caller's value, then
writes exactly one 24-byte value slot.  Its post exposes the computed write log.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

#derive_case envSetHitSeg chain
  [(0x80002d3c#64, 0x010a3783#32),   -- ld   a5,16(s4)
   (0x80002d40#64, 0x00141713#32),   -- slli a4,s0,1
   (0x80002d44#64, 0x000ab583#32),   -- ld   a1,0(s5)
   (0x80002d48#64, 0x008ab603#32),   -- ld   a2,8(s5)
   (0x80002d4c#64, 0x010ab683#32),   -- ld   a3,16(s5)
   (0x80002d50#64, 0x00870733#32),   -- add  a4,a4,s0
   (0x80002d54#64, 0x00371713#32),   -- slli a4,a4,3
   (0x80002d58#64, 0x00e787b3#32),   -- add  a5,a5,a4
   (0x80002d5c#64, 0x00b7b023#32),   -- sd   a1,0(a5)
   (0x80002d60#64, 0x00c7b423#32),   -- sd   a2,8(a5)
   (0x80002d64#64, 0x00d7b823#32)]   -- sd   a3,16(a5)

def envSetHitL (env valuePtr idx : BitVec 64) : GRegs :=
  [(20, env), (21, valuePtr), (8, idx)]

def envSetHitLds (pv w0 w1 w2 : BitVec 64) : List (List (BitVec 8)) :=
  [envSetWordBytes pv, envSetWordBytes w0, envSetWordBytes w1, envSetWordBytes w2]

def EnvSetHitPost (env valuePtr idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.mem = writeLog m0 (evalBlocks envSetHitSeg
    (SegEvalState.init (envSetHitL env valuePtr idx) lds)).log ∧
  c.σ.regs.get? Register.PC = some (0x80002d68#64 : BitVec 64)

/-- Verified machine execution of the one-slot update block. -/
theorem env_set_hit_block (env valuePtr idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre envSetHitSeg (envSetHitL env valuePtr idx) lds 0x80002d3c#64 m0)
      (EnvSetHitPost env valuePtr idx lds m0) := by
  apply segToTriple envSetHitSeg (envSetHitL env valuePtr idx) lds 0x80002d3c#64 m0
    (EnvSetHitPost env valuePtr idx lds m0)
    (by
      have h : keysG (envSetHitL env valuePtr idx) = [20, 21, 8] := rfl
      rw [h]
      show ChainOK 0x80002d3c#64 [20, 21, 8] envSetHitSeg
      decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hi', hmem', ?_⟩
  rw [hpc']
  rfl

/-- Output-preserving form used by the assignment bridge. -/
def EnvSetHitPostO (env valuePtr idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) (c : Config) : Prop :=
  EnvSetHitPost env valuePtr idx lds m0 c ∧ c.σ.sailOutput = out0

/-- The successful one-slot update block preserves the output stream. -/
theorem env_set_hit_block_out (env valuePtr idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) :
    Triple
      (SegPreO envSetHitSeg (envSetHitL env valuePtr idx) lds 0x80002d3c#64 m0 out0)
      (EnvSetHitPostO env valuePtr idx lds m0 out0) := by
  apply segToTripleOut envSetHitSeg (envSetHitL env valuePtr idx) lds
    0x80002d3c#64 m0 out0 (EnvSetHitPostO env valuePtr idx lds m0 out0)
    (by
      have h : keysG (envSetHitL env valuePtr idx) = [20, 21, 8] := rfl
      rw [h]
      show ChainOK 0x80002d3c#64 [20, 21, 8] envSetHitSeg
      decide)
  intro σ' i' u' hG' hi' hmem' hout' hpc' _hmi' _hregs
  refine ⟨⟨hG', hi', hmem', ?_⟩, hout'⟩
  rw [hpc']
  rfl

#print axioms env_set_hit_block
#print axioms env_set_hit_block_out

end Vsa.Sim
