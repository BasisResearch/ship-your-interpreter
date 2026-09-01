import Vsa.Sim.ExitPath
import Vsa.Sim.DeriveCase
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics
import Vsa.Sim.DeriveCallSeg

/-!
# Wave 44 — `MainErrorSeg` discharged (main's error return → crt0 exit call)

`Vsa/Sim/ExitPath.lean` reduced the opaque `ErrorTailChain` residual to four
straight-line segment `Triple`s.  This file discharges the **second**,
`MainErrorSeg` (`0x800045ec → 0x80000038`), including the `fprintf(stderr,…)` call.

## The decoded span (`experiments/disasm.txt`)

```
── main error path ────────────────────────────────────────────────────────────
800045ec:  bnez a0,80004600              -- a0 = 1 ⇒ TAKEN → 0x80004600   (B0 terminator)
── B1 @0x80004600 (fprintf-arg marshalling, fall-through into the jal) ──────────
80004600:  ld   a5,0(s0)                 -- s0 = &_impure_ptr
80004604:  addi a2,sp,496                -- a2 = &buf (the ap area — unused by us)
80004608:  auipc a1,0x15
8000460c:  addi a1,a1,-40                -- a1 = &"…" format string
80004610:  ld   a0,24(a5)                -- a0 = stderr FILE*
80004614:  jal  fprintf                  -- ── EXTERNAL CALL (output-neutral: stderr ≠ tohost)
── B2 @0x80004618 ──────────────────────────────────────────────────────────────
80004618:  li   a0,70                     -- exit status 70                 (B2 body)
8000461c:  j    800045f0                  -- (B2 terminator) → main epilogue
── B3 @0x800045f0 (main epilogue) ──────────────────────────────────────────────
800045f0:  ld   ra,760(sp)               -- ra ← crt0's `jal main` link 0x80000038
800045f4:  ld   s0,752(sp)
800045f8:  addi sp,sp,768
800045fc:  ret                            -- (B3 terminator, jr ra) → 0x80000038
```

## Structure — `prefix ≫ fprintf ≫ suffix` (`callSeg`)

`MainErrorSeg` is a textbook `jal rd` call splice (`Vsa/Sim/DeriveCallSeg.lean`):

* **prefix** (`0x800045ec → 0x80004614`): the taken `bnez` + the 5-instr fprintf-arg
  marshalling body, fall-through to the `jal fprintf` site.  Decoded via
  `#derive_case`/`bblocks_sound_bt` as the two-block chain `mainErrPreSeg`,
  landing at `0x80004614` with `output` unchanged (no `tohost` store — the loads set
  up `a0/a1/a2`), i.e. `AtFprintfCall out`.
* **fprintf** (`0x80004614 → 0x80004618`): the `jal fprintf` + the whole `fprintf`
  body.  Writes through the **stderr** `FILE*` (`a0 = 24(_impure_ptr)`), NOT the
  `tohost` console mailbox, so `output`/`sailOutput` are UNCHANGED.  We do NOT
  forward-simulate `fprintf`; its output-neutrality + return-linkage is the NAMED
  typed premise `FprintfStderrNeutral out : Triple (AtFprintfCall out) (AtMainErrRet out)`
  (`AtMainErrRet` = parked at the return site `0x80004618`).  This is the fact
  `ExitPath.lean`'s comment already flags as `FprintfStderrNeutral`.
* **suffix** (`0x80004618 → 0x80000038`): `li a0,70` (exit status), `j 0x800045f0`,
  and the main epilogue `ld ra/s0; addi sp; ret` → crt0's `jal main` link
  `0x80000038`.  Decoded via `#derive_case`/`bblocks_sound_bt` as the two-block chain
  `mainErrSufSeg`, landing at `0x80000038` with `a0 = 70` and `output` unchanged, i.e.
  `AtCrt0Exit out`.

The prefix/suffix code bytes are in the `Code` module (`MainLoaded`,
`Vsa/Sim/Code/Main.lean` covers 0x800045ec..0x8000461c); the two blocks' byte-pin
`ChainFacts` are bundled as the named residual `MainErrFrame` (supplied by
`MainLoaded`) — the exit-70 analogue of `InterpContFrame`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## The prefix chain (`#derive_case`): bnez-taken ≫ fprintf-arg marshalling -/

-- B0 @0x800045ec: empty body, `bnez a0,0x80004600` (BNE a0,x0) — TAKEN (a0 = 1).
--   word 0x00051a63, bytes 63 1a 05 00, imm13 0x014 (= 0x80004600 - 0x800045ec).
-- B1 @0x80004600: the fprintf-arg body (5 instrs), NO terminator (fall-through into
--   the `jal fprintf` @0x80004614).
#derive_case mainErrPreSeg chain
  [] terminator ⟨0x800045ec#64, 0x00051a63#32, 0x63#8, 0x1a#8, 0x05#8, 0x00#8,
      .br bop.BNE true, 10, 0, 0x0014#13, 0#21, 0#12⟩
  ;;
  [(0x80004600#64, 0x00043783#32),   -- ld   a5,0(s0)
   (0x80004604#64, 0x1f010613#32),   -- addi a2,sp,496
   (0x80004608#64, 0x00015597#32),   -- auipc a1,0x15
   (0x8000460c#64, 0xfd858593#32),   -- addi a1,a1,-40
   (0x80004610#64, 0x0187b503#32)]   -- ld   a0,24(a5)   (falls through to 0x80004614)

/-! ## The suffix chain (hand-built BBlock records): li a0,70 ≫ j ≫ epilogue ≫ ret

The suffix is hand-built as concrete `TInstr`/`MInstr` records (rather than
`#derive_case`, which threads its bodies through `mkLine`) so the `jr ra` end-PC
readback (`srcVal 1 (runChain …)`) and the `a0 = 70` register readback reduce by
`simp only [seB2, seB3, …]` on the concrete records — the exact `icB0`/`icB1`
discipline of `ExitPathSpans.interpContSeg_of`. -/

-- B2 @0x80004618: `li a0,70` (addi a0,x0,70), terminator `j 0x800045f0`
--   (j word 0xfd5ff06f, imm21 = 0x1fffd4 = -0x2c, target 0x800045f0).
def seB2 : BBlock :=
  { body :=
      [ -- li a0,70   word 04600513  addi a0,x0,70
        ⟨0x80004618#64, 0x04600513#32, 0x13#8, 0x05#8, 0x60#8, 0x04#8, .addi, 10, 0, 0, 0x046#12⟩ ],
    term := some ⟨0x8000461c#64, 0xfd5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xfd#8,
      .j, 0, 0, 0#13, 0x1fffd4#21, 0#12⟩ }

-- B3 @0x800045f0: main epilogue, terminator `ret` (jr ra) → the restored ra = 0x80000038.
def seB3 : BBlock :=
  { body :=
      [ -- ld ra,760(sp)   word 2f813083  rd=1 rs1=2 off=0x2f8
        ⟨0x800045f0#64, 0x2f813083#32, 0x83#8, 0x30#8, 0x81#8, 0x2f#8, .ld, 1, 2, 0, 0x2f8#12⟩,
        -- ld s0,752(sp)   word 2f013403  rd=8 rs1=2 off=0x2f0
        ⟨0x800045f4#64, 0x2f013403#32, 0x03#8, 0x34#8, 0x01#8, 0x2f#8, .ld, 8, 2, 0, 0x2f0#12⟩,
        -- addi sp,sp,768  word 30010113  rd=2 rs1=2 off=0x300
        ⟨0x800045f8#64, 0x30010113#32, 0x13#8, 0x01#8, 0x01#8, 0x30#8, .addi, 2, 2, 0, 0x300#12⟩ ],
    term := some ⟨0x800045fc#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩ }

def mainErrSufSeg : List BBlock := [seB2, seB3]

/-! ## Boundary predicates -/

/-- Parked at the `jal fprintf` call site (`0x80004614`), `GoodState`, tick-bounded,
console output `= out` (the fprintf-arg marshalling touched no `tohost` store). -/
def AtFprintfCall (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004614#64 : BitVec 64) ∧
  output c.σ = out

/-- Parked at the `fprintf` return site (`0x80004618`), `GoodState`, tick-bounded,
console output STILL `= out` (`fprintf(stderr,…)` did not touch `tohost`). -/
def AtMainErrRet (out : String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004618#64 : BitVec 64) ∧
  output c.σ = out

/-! ## The frame residual (the prefix/suffix byte pins the `AtMainRet` pre lacks)

`AtMainRet`/`AtMainErrRet`'s preconditions name only their PC / `a0` / `output`.
Decoding the prefix + suffix additionally needs the `main` code bytes at the
relevant PCs (`ChainFacts` for the two `#derive_case` chains) and, for the suffix,
that the spilled `ra` reads back as `0x80000038` (crt0's `jal main` link).  We
package exactly those two `ChainFacts` obligations plus the `ra` load-byte pin as
`MainErrFrame` — supplied by `MainLoaded` + the interp_run/main spill frame; the
exit-70 analogue of `InterpContFrame`.

`sufLds` pins the suffix `ld ra,760(sp)` slot to `0x80000038` (crt0's `jal main`
link); the `ld s0` slot is arbitrary (`s0b`, not observed downstream).

The prefix reads `s0` (`ld a5,0(s0)`) and `sp` (`addi a2,sp,…`); the suffix reads
`sp` (`ld ra/s0,…(sp)`).  Those base registers are pinned with existentially-bound
ghost values (`s0v`/`spv`/`spv2`), exactly as `InterpContFrame`'s spill images. -/
def preL (s0v spv : BitVec 64) : GRegs :=
  [(10, (1#64 : BitVec 64)), (8, s0v), (2, spv)]

def sufL (spv2 : BitVec 64) : GRegs :=
  [(2, spv2)]

def sufLds (s0b : List (BitVec 8)) : List (List (BitVec 8)) :=
  [ [0x38#8, 0x00#8, 0x00#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8],  -- ra = 0x80000038
    s0b ]

/-- The prefix/suffix byte-pin + base-register + `ra`-slot residual for
`MainErrorSeg`.  Existentially binds the ghost `s0`/`sp` bases and the two prefix
load images / suffix `s0` image; the suffix `ra` load image is pinned to
`0x80000038`. -/
def MainErrFrame (out : String) : Prop :=
  (∀ c : Config, AtMainRet out c →
    ∃ (s0v spv : BitVec 64) (a5b a0b : List (BitVec 8)),
      c.σ.regs.get? Register.x8 = some s0v ∧
      c.σ.regs.get? Register.x2 = some spv ∧
      ChainFacts c.σ.mem c.σ.mem (preL s0v spv) [a5b, a0b] mainErrPreSeg) ∧
  (∀ c : Config, AtMainErrRet out c →
    ∃ (spv2 : BitVec 64) (s0b : List (BitVec 8)),
      c.σ.regs.get? Register.x2 = some spv2 ∧
      ChainFacts c.σ.mem c.σ.mem (sufL spv2) (sufLds s0b) mainErrSufSeg)

/-! ## The prefix discharged (conditional on `MainErrFrame`) -/

/-- **The prefix** `0x800045ec → 0x80004614`.  From `AtMainRet out` (`a0 = 1`), the
taken `bnez` + the 5-instr fprintf-arg body fall through to the `jal fprintf` site
`0x80004614`, with `output` unchanged (no `tohost` store).  ONE `bblocks_sound_bt`
over `mainErrPreSeg`, conditional only on the `MainErrFrame` byte pins. -/
theorem mainErrPre_of (out : String) (hframe : MainErrFrame out) :
    Triple (AtMainRet out) (AtFprintfCall out) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hx10, hout⟩ := hpre
  obtain ⟨vm, hmi⟩ := hG.minstret
  obtain ⟨s0v, spv, a5b, a0b, hx8, hx2, hcf⟩ := hframe.1 c ⟨hG, htick, hpc, hx10, hout⟩
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, _hf⟩ :=
    bblocks_sound_bt mainErrPreSeg c.σ c.tick c.steps (0x800045ec#64) vm
      (preL s0v spv) [a5b, a0b]
      hG hpc hmi ⟨hx10, hx8, hx2, trivial⟩
      (by have h : keysG (preL s0v spv) = [10, 8, 2] := rfl
          rw [h]; decide)
      hcf
      (by have h : keysG (preL s0v spv) = [10, 8, 2] := rfl
          rw [h]; show ChainOK (0x800045ec#64) [10, 8, 2] mainErrPreSeg; decide)
      htick
  refine ⟨⟨σ', i', c.steps + chainLen mainErrPreSeg⟩, ?_, ?_, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · exact hG'
  · exact hi'
  · -- end PC = 0x80004614 (fall-through past the B1 body; NoJr ⇒ concrete).
    have hce : chainEndPC (0x800045ec#64) (preL s0v spv) [a5b, a0b] mainErrPreSeg
        = (0x80004614#64 : BitVec 64) := by
      rw [chainEndPC_eq_bt mainErrPreSeg (0x800045ec#64) _ _ (by decide)]
      apply BitVec.eq_of_toNat_eq; decide
    rw [hce] at hpc'; exact hpc'
  · unfold output; rw [hout']; unfold output at hout; exact hout

/-! ## The NAMED fprintf(stderr,…) contract -/

/-- `FprintfStderrNeutral out` — the `jal fprintf` @0x80004614 and the whole
`fprintf` body reach the return site `0x80004618` with the console `output`
UNCHANGED.  `fprintf(stderr,…)` writes through the stderr `FILE*` (`a0 =
24(_impure_ptr)`), a memory sink whose backing device is NOT the `tohost` console
mailbox, so `sailOutput` — and hence `output` — is untouched.  Named (not
forward-simulated) because the `fprintf` body's bytes are not pinned in `Code` and
the stderr-≠-tohost fact is a whole-image device-map invariant.  This is exactly the
`FprintfStderrNeutral` fact `ExitPath.lean`'s `MainErrorSeg` comment carries. -/
def FprintfStderrNeutral (out : String) : Prop :=
  Triple (AtFprintfCall out) (AtMainErrRet out)

/-! ## The suffix discharged (conditional on `MainErrFrame`) -/

/-- **The suffix** `0x80004618 → 0x80000038`.  From `AtMainErrRet out`, `li a0,70`
sets the exit status, `j 0x800045f0` reaches the main epilogue, the `ld ra` restores
crt0's `jal main` link `0x80000038` and `ret` returns there, with `a0 = 70` and
`output` unchanged.  ONE `bblocks_sound_bt` over `mainErrSufSeg`, conditional only on
the `MainErrFrame` byte pins (incl. the `ra`-slot pin `= 0x80000038`). -/
theorem mainErrSuf_of (out : String) (hframe : MainErrFrame out) :
    Triple (AtMainErrRet out) (AtCrt0Exit out) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hout⟩ := hpre
  obtain ⟨vm, hmi⟩ := hG.minstret
  obtain ⟨spv2, s0b, hx2, hcf⟩ := hframe.2 c ⟨hG, htick, hpc, hout⟩
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH, _hf⟩ :=
    bblocks_sound_bt mainErrSufSeg c.σ c.tick c.steps (0x80004618#64) vm
      (sufL spv2) (sufLds s0b)
      hG hpc hmi ⟨hx2, trivial⟩
      (by have h : keysG (sufL spv2) = [2] := rfl
          rw [h]; decide)
      hcf
      (by have h : keysG (sufL spv2) = [2] := rfl
          rw [h]; show ChainOK (0x80004618#64) [2] mainErrSufSeg; decide)
      htick
  refine ⟨⟨σ', i', c.steps + chainLen mainErrSufSeg⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · exact hG'
  · exact hi'
  · -- end PC = the restored ra = 0x80000038 (the `jr ra`; ra pinned by `sufLds`).
    have hra : srcVal 1 (runChain mainErrSufSeg (sufL spv2) (sufLds s0b))
        = (0x80000038#64 : BitVec 64) := by
      simp only [mainErrSufSeg, seB2, seB3, sufL, sufLds, runChain, runGM, stepGM, stepLdsM, wvalM,
        eraseG, srcVal, lookupG, List.headD, List.tail, ldsRunM]
      rfl
    have hce : chainEndPC (0x80004618#64) (sufL spv2) (sufLds s0b) mainErrSufSeg
        = (0x80000038#64 : BitVec 64) := by
      show BitVec.update (srcVal 1 (runChain mainErrSufSeg (sufL spv2) (sufLds s0b))
        + sign_extend (m := 64) (0#12)) 0 0#1 = _
      rw [hra]
      apply BitVec.eq_of_toNat_eq; rfl
    rw [hce] at hpc'; exact hpc'
  · -- a0 = 70: `li a0,70` is the only write to key 10 in the suffix.
    have hlk : lookupG 10 (runChain mainErrSufSeg (sufL spv2) (sufLds s0b))
        = some (70#64 : BitVec 64) := by
      simp only [mainErrSufSeg, seB2, seB3, sufL, sufLds, runChain, runGM, stepGM, stepLdsM, wvalM,
        eraseG, srcVal, lookupG, List.headD, List.tail, ldsRunM]
      rfl
    exact gholds_lookup (runChain mainErrSufSeg (sufL spv2) (sufLds s0b)) hGH hlk
  · unfold output; rw [hout']; unfold output at hout; exact hout

/-! ## `MainErrorSeg` discharged (conditional on `MainErrFrame` + `FprintfStderrNeutral`) -/

/-- **`MainErrorSeg` discharged.**  `prefix ≫ fprintf ≫ suffix` via `callSeg`:
the decoded prefix (`mainErrPre_of`), the NAMED output-neutral fprintf contract
(`FprintfStderrNeutral out`), and the decoded suffix (`mainErrSuf_of`) compose to the
whole `AtMainRet → AtCrt0Exit` segment `Triple`, i.e. `MainErrorSeg out`. -/
theorem mainErrorSeg_of (out : String)
    (hframe : MainErrFrame out) (hfp : FprintfStderrNeutral out) :
    MainErrorSeg out :=
  callSeg (mainErrPre_of out hframe) hfp (mainErrSuf_of out hframe)

#print axioms mainErrorSeg_of

end Vsa.Sim
