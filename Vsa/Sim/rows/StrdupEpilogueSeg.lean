import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# `StrdupEpilogueSeg` — the shared `strdup`/`stringify` tail epilogue as a `jr`-seg

Task #71 Part 1 (the epilogue).  The shared `stringify` strdup tail
(`0x80003044 → 0x80003084`, `Vsa/Sim/rows/StringifyStrdupTail.lean`) returns the
fresh copy through the standard function epilogue:

```
80003070  ld   ra,104(sp)   -- x1  := saved return address
80003074  mv   a0,s0        -- x10 := s0 = new (the fresh block, saved by the memcpy prefix)
80003078  ld   s0,96(sp)    -- x8  := restored caller s0
8000307c  ld   s1,88(sp)    -- x9  := restored caller s1
80003080  addi sp,sp,112    -- x2  := sp + 112 (frame teardown)
80003084  ret               -- jr ra  → returns to the caller's link
```

This is a self-contained straight-line span terminated by `ret` (= `jr ra`), the
mandated `#derive_case`/`bblocks_sound_bt` shape — NO external `jal` (unlike the
three arg-staging prefixes, whose trailing `jal strlen`/`malloc`/`memcpy` seams
need the stringify code-byte pins that do not yet exist; see
`experiments/observations.md#stringify-code-pins-missing`).  The whole `Steps`
chain / write-log / `jr`-target end-PC is auto-threaded by `#derive_case`; the
row's only kernel obligation is the single `ChainOK` `decide`.

The `jr ra` target is the caller-supplied saved return address, read back from the
`ld ra,104(sp)` load — i.e. the pinned `ra` byte-list slot, exactly the
`interpContChain` (`Vsa/Sim/ExitPathSpans.lean`) jr-epilogue idiom.  `x10` lands
`s0` (the fresh block pointer the memcpy prefix saved), which the `StrdupTailExit`
consumer reads as `res`.  The `CString mem res str` fact `StrdupTailExit` also
demands is NOT a machine fact of this span — it is the bytes→`CString` readback of
the memcpy byte-post, supplied by the `bridgeEpilogue` frame layer above the seg
(named as a residual, `StringifyStrdupTail.lean`'s `bridgeEpilogue` premise).

GENERATED shape (hand, one-off — jr terminator not covered by `genseg.py`).
NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- The `strdup`/`stringify`-tail epilogue span `0x80003070 → 0x80003084`, a single
straight-line block terminated by `ret` (`jr ra`, word `00008067`, bytes
`67 80 00 00`).  Body: `ld ra,104(sp) ; mv a0,s0 ; ld s0,96(sp) ; ld s1,88(sp) ;
addi sp,sp,112`. -/
#derive_case strdupEpilogueSeg chain
  [(0x80003070#64, 0x06813083#32),   -- ld   ra,104(sp)   rd=1  rs1=2 off=0x068
   (0x80003074#64, 0x00040513#32),   -- mv   a0,s0        addi a0,s0,0
   (0x80003078#64, 0x06013403#32),   -- ld   s0,96(sp)    rd=8  rs1=2 off=0x060
   (0x8000307c#64, 0x05813483#32),   -- ld   s1,88(sp)    rd=9  rs1=2 off=0x058
   (0x80003080#64, 0x07010113#32)]   -- addi sp,sp,112    rd=2  rs1=2 off=0x070
    terminator ⟨0x80003084#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

/-- The epilogue entry pins: `x2 = sp` (the spill base), `x8 = s0 = new` (the fresh
block pointer the memcpy prefix saved; moved to `a0` by `mv a0,s0`).  The `ld`s that
restore `s0`/`s1` and reload `ra` read from `lds` (the spilled images), NOT from
these register pins. -/
def strdupEpilogueL (sp s0 : BitVec 64) : GRegs := [(2, sp), (8, s0)]

/-- The epilogue row post: parked at the computed `jr` end PC (the reloaded `ra`,
= `evalBlocksPC`), `x10 = s0` (the fresh block, moved from `s0` by `mv a0,s0`),
memory = the entry memory with the (empty — the span has no stores) write-log
applied, i.e. unchanged.  The reloaded `ra`/restored `s0`/`s1`/torn-down `sp` are
all in the computed `out.regs`; `StrdupTailExit`'s `res` is the `x10 = s0` here. -/
def StrdupEpiloguePost (sp s0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks strdupEpilogueSeg
    (SegEvalState.init (strdupEpilogueL sp s0) lds)).log ∧
  c.σ.regs.get? Register.PC
    = some (evalBlocksPC 0x80003070#64 (SegEvalState.init (strdupEpilogueL sp s0) lds)
        strdupEpilogueSeg) ∧
  c.σ.regs.get? Register.x10 = some s0

/-- **`strdupEpilogueRow`** — the epilogue span as a `Triple`, via `segToTriple`
over the `jr`-terminated `strdupEpilogueSeg`.  `hwf` is the row's one kernel
`decide` (`ChainOK`); `hpost` reads the computed end PC (the `jr ra` target) off
`evalBlocksPC`, `x10 = s0` off `GHolds out.regs` (`mv a0,s0` writes `x10` from the
`s0` pin), and the write-log memory (empty log ⇒ unchanged).  Replaces the hand
`site_*` `stepObs` battery + jr-target thread for this span. -/
theorem strdupEpilogueRow (sp s0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strdupEpilogueSeg (strdupEpilogueL sp s0) lds 0x80003070#64 m0)
      (StrdupEpiloguePost sp s0 lds m0) := by
  apply segToTriple strdupEpilogueSeg (strdupEpilogueL sp s0) lds 0x80003070#64 m0
    (StrdupEpiloguePost sp s0 lds m0)
    (by have h : keysG (strdupEpilogueL sp s0) = [2, 8] := rfl
        rw [h]; show ChainOK 0x80003070#64 [2, 8] strdupEpilogueSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', hpc', ?_⟩
  -- `x10 = s0`: read off `GHolds σ' out.regs` — `mv a0,s0` (= `addi a0,s0,0`) wrote
  -- key 10 from the `s0` pin (key 8) as `s0 + sext 0`; the subsequent `ld s0,96(sp)`
  -- rewrites key 8 but leaves key 10, so key 10 ↦ `s0 + sext 0 = s0`.
  have e : (s0 + sign_extend (m := 64) (0#12) : BitVec 64) = s0 := by
    rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
  rw [← e]
  exact gholds_lookup (n := 10) (v := s0 + sign_extend (m := 64) (0#12)) _ hregs (by rfl)

#print axioms strdupEpilogueRow

end Vsa.Sim
