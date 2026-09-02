import Vsa.Sim.AddTailSites
import Vsa.Sim.BlockMem
import Vsa.Sim.BlockTactics
import Vsa.Sim.BlockDecode

/-!
# `EvalGtBlk1Pilot` — P1 reflection pilot: EvalGtRow's opening block via ONE `block_mem_sound`

Measurement vehicle. EvalGtRow (226s) hand-threads its opening straight-line run
`0x8000351c … 0x80003530` (lw/li/lw/addiw/lw/ld) as 6 `site_*_ee` obtains + ~40
`obs_alu_*` register carries. Here the SAME run is one `block_mem_sound` application:
one kernel computation over the 6-instruction write-log model, all code-byte pins +
decodes auto-discharged by `block_facts`, only the four load MemFacts supplied. If this
elaborates in a few seconds, the reflection rewrite (P1) is the transformative lever for
the whole cohort. Follows `BlockMemDemo.ssputs_prologue_block` verbatim in shape.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

-- No heartbeat/recDepth overrides: block_mem_sound reflection elaborates within ALL defaults.

namespace Vsa.Sim

/-- The opening block of `blockC_gt`, fully concrete via `mkLine` (auto-decode). -/
def evalGtBlk1 : List MInstr :=
  [mkLine 0x8000351c#64 0x00842603#32,   -- lw  x12, 8(x8)
   mkLine 0x80003520#64 0x00c00713#32,   -- li  x14, 12
   mkLine 0x80003524#64 0x00442403#32,   -- lw  x8,  4(x8)
   mkLine 0x80003528#64 0xff56079b#32,   -- addiw x15, x12, -11
   mkLine 0x8000352c#64 0x09012503#32,   -- lw  x10, 144(x2)
   mkLine 0x80003530#64 0x09813883#32]   -- ld  x17, 152(x2)

/-- The opening run of `blockC_gt` via ONE `block_mem_sound`. Four loads (no stores), so
every byte pin is on entry memory `σ.mem`. -/
theorem evalGtBlk1_run (σ : MState) (i u : Nat) (vm v2 v8 : BitVec 64)
    -- load1 @ v8+8 (lw x12), load2 @ v8+4 (lw x8), load3 @ v2+0x90 (lw x10), load4 @ v2+0x98 (ld x17)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 8)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x8000351c#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    -- load1 @ v8 + 0x008 (4-byte)
    (a_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_hi : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ 0x100000000)
    (a_ht : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (a_al : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 4 = 0)
    (a_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some a0)
    (a_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some a1)
    (a_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some a2)
    (a_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some a3)
    -- load2 @ v8 + 0x004 (4-byte)
    (b_lo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_hi : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ 0x100000000)
    (b_ht : (v8 + sign_extend (m := 64) (0x004#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x004#12)).toNat)
    (b_al : (v8 + sign_extend (m := 64) (0x004#12)).toNat % 4 = 0)
    (b_p0 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat]? = some b0)
    (b_p1 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 1]? = some b1)
    (b_p2 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 2]? = some b2)
    (b_p3 : σ.mem[(v8 + sign_extend (m := 64) (0x004#12)).toNat + 3]? = some b3)
    -- load3 @ v2 + 0x090 (4-byte)
    (c_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_hi : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ 0x100000000)
    (c_ht : (v2 + sign_extend (m := 64) (0x090#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x090#12)).toNat)
    (c_al : (v2 + sign_extend (m := 64) (0x090#12)).toNat % 4 = 0)
    (c_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat]? = some c0)
    (c_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 1]? = some c1)
    (c_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 2]? = some c2)
    (c_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x090#12)).toNat + 3]? = some c3)
    -- load4 @ v2 + 0x098 (8-byte)
    (d_lo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_hi : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ 0x100000000)
    (d_ht : (v2 + sign_extend (m := 64) (0x098#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x098#12)).toNat)
    (d_al : (v2 + sign_extend (m := 64) (0x098#12)).toNat % 8 = 0)
    (d_p0 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat]? = some d0)
    (d_p1 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 1]? = some d1)
    (d_p2 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 2]? = some d2)
    (d_p3 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 3]? = some d3)
    (d_p4 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 4]? = some d4)
    (d_p5 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 5]? = some d5)
    (d_p6 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 6]? = some d6)
    (d_p7 : σ.mem[(v2 + sign_extend (m := 64) (0x098#12)).toNat + 7]? = some d7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 6⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some (0x80003534#64) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, hframe⟩ :=
    block_mem_sound evalGtBlk1 σ i u (0x8000351c#64) vm
      [(8, v8), (2, v2)]
      [[a0, a1, a2, a3], [b0, b1, b2, b3], [c0, c1, c2, c3], [d0, d1, d2, d3, d4, d5, d6, d7]]
      hG hpc hmi ⟨hx8, hx2, trivial⟩
      (show KeysOK [8, 2] by decide)
      (by
        block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"
        · exact ⟨⟨a_lo, a_hi, a_ht, a_al⟩, lpin_of_present a_p0, lpin_of_present a_p1, lpin_of_present a_p2, lpin_of_present a_p3⟩
        · exact ⟨⟨b_lo, b_hi, b_ht, b_al⟩, lpin_of_present b_p0, lpin_of_present b_p1, lpin_of_present b_p2, lpin_of_present b_p3⟩
        · exact ⟨⟨c_lo, c_hi, c_ht, c_al⟩, lpin_of_present c_p0, lpin_of_present c_p1, lpin_of_present c_p2, lpin_of_present c_p3⟩
        · exact ⟨⟨d_lo, d_hi, d_ht, d_al⟩, lpin_of_present d_p0, lpin_of_present d_p1, lpin_of_present d_p2, lpin_of_present d_p3, lpin_of_present d_p4, lpin_of_present d_p5, lpin_of_present d_p6, lpin_of_present d_p7⟩)
      (show BlockOKM (0x8000351c#64) [8, 2] evalGtBlk1 by decide) hi
  rw [show endPCM (0x8000351c#64) evalGtBlk1 = (0x80003534#64 : BitVec 64) from by decide] at hpc'
  exact ⟨σ', i', hsteps, hi', hG', hpc'⟩

end Vsa.Sim
