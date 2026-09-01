import Vsa.Sim.ExitPath
import Vsa.Sim.DeriveCase
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics

/-!
# Wave 44 — `Crt0ExitSeg` discharged (the crt0 `j exit` → `_exit` entry span)

`Vsa/Sim/ExitPath.lean` reduced the opaque `ErrorTailChain` residual to four
straight-line segment `Triple`s.  `Vsa/Sim/ExitPathSpans.lean`/`ExitPathSeg.lean`
discharged `InterpContSeg` + `ExitPrologSeg`.  This file discharges the **third**,
`Crt0ExitSeg` (`0x80000038 → 0x80000180`).

## The decoded span (`experiments/disasm.txt`)

```
── crt0 → exit ────────────────────────────────────────────────────────────────
80000038:  j    80004764 <exit>          -- a0 = 70; `j` = jal x0 (block terminator)
── exit() body ─────────────────────────────────────────────────────────────────
80004764:  addi sp,sp,-16
80004768:  li   a1,0
8000476c:  sd   s0,0(sp)
80004770:  sd   ra,8(sp)
80004774:  mv   s0,a0                    -- s0 := a0 = 70   (the exit status is stashed)
80004778:  jal  __call_exitprocs         -- 0x800070a8  ── EXTERNAL CALL #1
8000477c:  ld   a5,__stdio_exit_handler
80004780:  beqz a5,80004788
80004784:  jalr a5                        -- stdio flush ── EXTERNAL CALL #2 (conditional)
80004788:  mv   a0,s0                     -- a0 := s0 = 70   (restore exit status)
8000478c:  jal  80000180 <_exit>          -- ── CALL #3 → _exit entry 0x80000180
```

## Structure — one decoded `j` seam + one NAMED interior contract

The crt0 `j exit` @0x80000038 is a plain **unconditional `j`** (`jal x0`), which IS a
block terminator (`br`/`j`/`jr` are in-model; `jal rd` calls are not).  We decode it
with `#derive_case`/`segToTriple` as a one-block chain landing at the `exit` entry
`0x80004764` with `a0 = 70` and `output` unchanged (empty body ⇒ no register touched,
no `tohost` store), i.e. `AtExitEntry out`.  The crt0 code bytes at 0x80000038 are NOT
in the `Code` module (there is no crt0/`_start` `Code` module in the tree), so the
`j`-block's byte pins / `ChainFacts` are supplied as the minimal named residual
`Crt0JFrame` — the exit-70 analogue of `InterpContFrame`/`ExitPrologGeom`.

The `exit()` **interior** (`0x80004764 → 0x80000180`) contains three external calls:
`__call_exitprocs` (0x800070a8 — a locked loop over the `__atexit` handler chain;
whether that chain is empty at boot is a whole-program data/bss + registration
invariant, NOT decidable from this span), the optional stdio-exit-handler indirect
`jalr a5` (a data-dependent indirect call), and the `jal _exit`.  None of these
callees' bytes are pinned in `Code`, and none is forward-simulable in a decode wave.
Per CLAUDE.md Law 2 the exit-interior's output-neutrality + status-preservation is a
NAMED typed premise, `ExitInteriorNeutral out` — the exit-70 analogue of
`FprintfStderrNeutral`/`SnprintfContract`.  `Crt0ExitSeg` is then
`crt0 j-seam ≫ ExitInteriorNeutral` via `Triple.seq`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps output)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-! ## The `j exit` seam block (decoded via `#derive_case`) -/

-- The crt0 `j exit` @0x80000038: empty body, terminator `j 0x80004764` (`jal x0`).
-- Word `0x72c0406f`; `#derive_case` decodes the word and computes the `j` target
-- `0x80004764` (= `0x80000038 + 0x0472c`).
#derive_case crt0JSeg chain
  [] terminator ⟨0x80000038#64, 0x72c0406f#32, 0x6f#8, 0x40#8, 0xc0#8, 0x72#8,
      .j, 0, 0, 0#13, 0x0472c#21, 0#12⟩

/-! ## Boundary predicate at the `exit` entry -/

/-- Parked at the `exit` entry (`0x80004764`) with the exit status `a0 = 70`,
`GoodState`, tick-bounded, and the console output still `out`. -/
def AtExitEntry (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004764#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some (70#64 : BitVec 64) ∧
  output c.σ = out

/-! ## The crt0-`j` frame residual (the byte pins the `AtCrt0Exit` pre lacks)

`AtCrt0Exit`'s precondition names only `{GoodState, tick<2, PC = 0x80000038,
a0 = 70, output = out}`.  Decoding the `j exit` additionally needs the crt0 code
bytes at 0x80000038 (`ChainFacts` for the one-block `crt0JSeg`), which are not in
any `Code` module.  We package exactly that `ChainFacts` obligation as the named
residual `Crt0JFrame`.  This is the exit-70 analogue of `ExitPrologGeom`
(the `_exit`-code residual). -/
def Crt0JFrame (out : String) : Prop :=
  ∀ c : Config, AtCrt0Exit out c →
    ChainFacts c.σ.mem c.σ.mem [(10, (70#64 : BitVec 64))] [] crt0JSeg

/-! ## The crt0 `j exit` seam discharged (conditional on `Crt0JFrame`) -/

/-- **The crt0 `j exit` seam.**  From `AtCrt0Exit out` (`PC = 0x80000038`,
`a0 = 70`), the single `j exit` lands at the `exit` entry `0x80004764` with `a0`
unchanged (empty body) and `output` unchanged (no `tohost` store — `bblocks_sound_bt`
gives `σ'.sailOutput = σ.sailOutput`), i.e. `AtExitEntry out`.  ONE
`bblocks_sound_bt` over the decoded one-block `crt0JSeg`, conditional only on the
`Crt0JFrame` byte pins. -/
theorem crt0ExitPre_of (out : String) (hframe : Crt0JFrame out) :
    Triple (AtCrt0Exit out) (AtExitEntry out) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hx10, hout⟩ := hpre
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hcf : ChainFacts c.σ.mem c.σ.mem [(10, (70#64 : BitVec 64))] [] crt0JSeg :=
    hframe c ⟨hG, htick, hpc, hx10, hout⟩
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, _hframe⟩ :=
    bblocks_sound_bt crt0JSeg c.σ c.tick c.steps (0x80000038#64) vm
      [(10, (70#64 : BitVec 64))] []
      hG hpc hmi ⟨hx10, trivial⟩
      (show KeysOK [10] by decide)
      hcf
      (show ChainOK (0x80000038#64) [10] crt0JSeg by decide)
      htick
  refine ⟨⟨σ', i', c.steps + chainLen crt0JSeg⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · exact hG'
  · exact hi'
  · -- PC = chainEndPC … = 0x80004764 (the `j` target; NoJr ⇒ concrete).
    have hce : chainEndPC (0x80000038#64) [(10, (70#64 : BitVec 64))] [] crt0JSeg
        = (0x80004764#64 : BitVec 64) := by
      rw [chainEndPC_eq_bt crt0JSeg (0x80000038#64) _ _ (by decide)]
      apply BitVec.eq_of_toNat_eq; decide
    rw [hce] at hpc'; exact hpc'
  · -- a0 = 70: empty body ⇒ runChain preserves the pin (key 10).
    have hlk : lookupG 10 (runChain crt0JSeg [(10, (70#64 : BitVec 64))] [])
        = some (70#64 : BitVec 64) := by rfl
    exact gholds_lookup (runChain crt0JSeg [(10, (70#64 : BitVec 64))] []) hGH hlk
  · -- output unchanged.
    unfold output; rw [hout']; unfold output at hout; exact hout

/-! ## The NAMED exit-interior contract

`ExitInteriorNeutral out` is the one semantic gap this span leaves: the `exit()`
body (`0x80004764 → 0x80000180`) reaches the `_exit` entry with the exit status
`a0 = 70` preserved (stashed in `s0` across `__call_exitprocs`/stdio-handler,
restored by `mv a0,s0` @0x80004788) and the console `output` unchanged.  This
bundles the output-neutrality of the two atexit-path external calls
(`__call_exitprocs` + optional stdio flush), neither of which writes the `tohost`
console mailbox on the error-exit path.  Named because their callee bytes are not
pinned in `Code` and the `__atexit`-empty / stdio-handler-null facts are
whole-program runtime invariants, not decode facts.  The exit-70 analogue of
`FprintfStderrNeutral`. -/
def ExitInteriorNeutral (out : String) : Prop :=
  Triple (AtExitEntry out) (AtExitProlog out)

/-! ## `Crt0ExitSeg` discharged (conditional on `Crt0JFrame` + `ExitInteriorNeutral`) -/

/-- **`Crt0ExitSeg` discharged.**  The decoded crt0 `j exit` seam (`crt0ExitPre_of`,
conditional on the `Crt0JFrame` byte pins) composed with the NAMED exit-interior
contract (`ExitInteriorNeutral out`) gives the whole `AtCrt0Exit → AtExitProlog`
segment `Triple`, i.e. `Crt0ExitSeg out`. -/
theorem crt0ExitSeg_of (out : String)
    (hframe : Crt0JFrame out) (hint : ExitInteriorNeutral out) :
    Crt0ExitSeg out :=
  Triple.seq (crt0ExitPre_of out hframe) hint

#print axioms crt0ExitSeg_of

end Vsa.Sim
