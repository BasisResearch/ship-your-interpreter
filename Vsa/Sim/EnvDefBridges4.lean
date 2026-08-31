import Vsa.Sim.EnvDefSeg
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.EnvDefBridges3

/-!
# `EnvDefBridges4` — the remaining `env_define` machine bridges THROUGH the seg layer

`Vsa/Sim/EnvDefCompose.lean` leaves three straight-line machine bridges named:
`bridgeAppendHead` (grow path), `bridgeStore` (append path), and `hUpdate`'s
straight-line prefix.  Each was destined to grow a bespoke `site_*` battery in the
legacy `EnvDefBridges*` idiom (`namesToValsPrefix_run` is the last one hand-built —
~250 lines of per-site `stepObs_*` + a 33-branch register frame).

This file discharges the STRAIGHT-LINE MACHINE RUN of each through the block-reflection
seg layer (`#derive_case` + `segToTriple`, the `EnvDefSeg` model), landing the computed
machine post in a handful of lines.  Every word in these spans is tabled + `decodeM`-
supported (verified against `scripts/decode_index.tsv`), and — unlike the `env_define`
*call* prefixes (`capComputeSeg`/`mallocArgSeg`), which end in a `jal` seam and need
`bridgeOfSeg` — the append-head and store spans END IN A BRANCH/JUMP terminator
(`beqz`/`bnez`/`j`), which `BlockTerm`'s `TKind` (`br`/`j`) carries NATIVELY.  So NO
`bridgeOfSeg` and NO new `bridgeOfSegBr` variant is needed: `segToTriple` (built on
`segEval_sound`, whose end PC is `evalBlocksPC` = the terminator target) marshals the
whole branch-terminated seg directly.  (Recorded in `experiments/observations.md`.)

## What lands here vs. what stays a named spec residual

LANDS (the machine run, replacing the would-be `site_*` battery):
* `appendHeadSeg` / `appendHeadRow` — the grow-path append-head span
  `0x80002bc0..0x80002bcc` (`ld;sd` ▷ `beqz` ▷ `bnez`), landing the computed
  post (env->vals stored, parked at the append head `0x80002b1c`).
* `appendStoreSeg` / `appendStoreRow` — the append-path store block
  `0x80002b44..0x80002b8c` (loads + shifts/adds + `sd`/`sd`/`sd`/`sd`/`sw` ▷ `j`),
  landing the computed write-log post (the three value words, the name word, the
  incremented count) parked at the shared tail `0x80002aec`.

STAYS a named typed premise (the SPEC-side marshalling, NOT machine reasoning):
* the `FrameRepr` reconstruction turning the computed store-block `writeLog` into
  `env_define_update_post`'s `Store.define` result — its content is the LANDED
  `frameRepr_append` (`EnvDefBridges3`); the residual is only the tie of the computed
  `writeLog` byte-images to `frameRepr_append`'s readback hypotheses.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

/-! ## Item 1 — the grow-path append-head span `0x80002bc0..0x80002bcc`

Per the `EnvDefBridges3` ledger the span is 1 load + 1 store + 2 branch sites:
```
80002bc0  ld   a5,8(s4)     -- x15 := env->names   (reload after the two reallocs)
80002bc4  sd   a0,16(s4)    -- env->vals := a0      (the realloc(vals) result)
80002bc8  beqz a5,80002bd0  -- br BEQ; NOT taken on the success path (names ≠ 0)
80002bcc  bnez a0,80002b1c  -- br BNE; taken on the success path (vals ≠ 0) → append head
```
Two blocks (one terminator each): `[ld;sd] ▷ beqz(false)` then `[] ▷ bnez(true)`.
Both branches WRITE NO GPR (BlockTerm's `br` class), so the whole thing is ONE
`#derive_case` seg — no `bridgeOfSeg`, the branch terminators are in-model. -/
#derive_case appendHeadSeg chain
  [(0x80002bc0#64, 0x008a3783#32),   -- ld a5,8(s4)   (x15 := env->names)
   (0x80002bc4#64, 0x00aa3823#32)]   -- sd a0,16(s4)  (env->vals := a0)
    terminator ⟨0x80002bc8#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8,
      .br bop.BEQ false, 15, 0, 0x0008#13, 0#21, 0#12⟩ ;;
  []
    terminator ⟨0x80002bcc#64, 0xf40518e3#32, 0xe3#8, 0x18#8, 0x05#8, 0xf4#8,
      .br bop.BNE true, 10, 0, 0x1f50#13, 0#21, 0#12⟩

/-- The append-head entry pins: `x20 = s4 = env` (base for both accesses),
`x10 = a0 = realloc(vals) result` (stored, and the `bnez` guard). -/
def appendHeadL (s4Ptr a0 : BitVec 64) : GRegs := [(20, s4Ptr), (10, a0)]

/-- Post: parked at the append head `0x80002b1c` (the `bnez` success target), memory
= the entry memory with `env->vals` (word at `s4+16`) overwritten by `a0`, computed
off the seg's write-log. -/
def AppendHeadPost (s4Ptr a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks appendHeadSeg
    (SegEvalState.init (appendHeadL s4Ptr a0) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002b1c#64

/-- **`appendHeadRow`** — the grow-path append-head span as a `Triple`, via
`segToTriple` over the branch-terminated `appendHeadSeg`.  `hwf` is the row's one
kernel `decide` (`ChainOK`); `hpost` projects the computed end PC (the `bnez` target
`0x80002b1c`) and the write-log memory off the `#derive_case` outcome.  Replaces the
hand `site_80002bc0_ed .. site_80002bcc_ed` battery (~4×30-line `stepObs_*` + a run). -/
theorem appendHeadRow (s4Ptr a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre appendHeadSeg (appendHeadL s4Ptr a0) lds 0x80002bc0#64 m0)
      (AppendHeadPost s4Ptr a0 lds m0) := by
  apply segToTriple appendHeadSeg (appendHeadL s4Ptr a0) lds 0x80002bc0#64 m0
    (AppendHeadPost s4Ptr a0 lds m0)
    (by have h : keysG (appendHeadL s4Ptr a0) = [20, 10] := rfl
        rw [h]; show ChainOK 0x80002bc0#64 [20, 10] appendHeadSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x80002bc0#64 (SegEvalState.init (appendHeadL s4Ptr a0) lds)
    appendHeadSeg) = some 0x80002b1c#64
  rfl

#print axioms appendHeadRow

/-! ## Item 2 — the append-path store block `0x80002b44..0x80002b8c`

The store block (name absent, `count < cap`) writes the copied name pointer into
`names[count]`, the value's three words into `vals[count]`, and `count+1` into
`env->count`, then `j`s to the shared finalize tail `0x80002aec`:
```
80002b44  lw   a5,0(s4)     -- x15 := env->count           (= n)
80002b48  ld   a2,8(s4)     -- x12 := env->names
80002b4c  ld   a4,16(s4)    -- x14 := env->vals
80002b50  slli a3,a5,0x1    -- x13 := n*2
80002b54  slli a7,a5,0x3    -- x17 := n*8
80002b58  add  a3,a3,a5     -- x13 := n*3
80002b5c  ld   a6,0(s5)     -- x16 := v.word0   (v = the value struct at s5)
80002b60  ld   a0,8(s5)     -- x10 := v.word1
80002b64  ld   a1,16(s5)    -- x11 := v.word2
80002b68  add  a2,a2,a7     -- x12 := &names[n]  (names + n*8)
80002b6c  slli a3,a3,0x3    -- x13 := n*24
80002b70  sd   s1,0(a2)     -- names[n] := s1    (the copied name ptr)
80002b74  add  a4,a4,a3     -- x14 := &vals[n]   (vals + n*24)
80002b78  addiw a5,a5,1     -- x15 := n+1
80002b7c  sd   a6,0(a4)     -- vals[n].word0 := v.word0
80002b80  sd   a0,8(a4)     -- vals[n].word1 := v.word1
80002b84  sd   a1,16(a4)    -- vals[n].word2 := v.word2
80002b88  sw   a5,0(s4)     -- env->count := n+1
80002b8c  j    80002aec     -- → shared finalize tail
```
One straight-line block, `j` terminator — again NO `jal`, so the whole thing is ONE
`#derive_case` seg carried in-model (the `j` is a `TKind.j`).  The five stores land in
the seg's canonical `writeLog` (`out.log`); the FrameRepr reconstruction that turns that
write-log into `env_define_update_post`'s `Store.define` result is the LANDED
`frameRepr_append` (`EnvDefBridges3`) — NOT re-proved here (it is the genuinely spec-side
part, and its content is already discharged). -/
#derive_case appendStoreSeg chain
  [(0x80002b44#64, 0x000a2783#32),   -- lw   a5,0(s4)
   (0x80002b48#64, 0x008a3603#32),   -- ld   a2,8(s4)
   (0x80002b4c#64, 0x010a3703#32),   -- ld   a4,16(s4)
   (0x80002b50#64, 0x00179693#32),   -- slli a3,a5,0x1
   (0x80002b54#64, 0x00379893#32),   -- slli a7,a5,0x3
   (0x80002b58#64, 0x00f686b3#32),   -- add  a3,a3,a5
   (0x80002b5c#64, 0x000ab803#32),   -- ld   a6,0(s5)
   (0x80002b60#64, 0x008ab503#32),   -- ld   a0,8(s5)
   (0x80002b64#64, 0x010ab583#32),   -- ld   a1,16(s5)
   (0x80002b68#64, 0x01160633#32),   -- add  a2,a2,a7
   (0x80002b6c#64, 0x00369693#32),   -- slli a3,a3,0x3
   (0x80002b70#64, 0x00963023#32),   -- sd   s1,0(a2)
   (0x80002b74#64, 0x00d70733#32),   -- add  a4,a4,a3
   (0x80002b78#64, 0x0017879b#32),   -- addiw a5,a5,1
   (0x80002b7c#64, 0x01073023#32),   -- sd   a6,0(a4)
   (0x80002b80#64, 0x00a73423#32),   -- sd   a0,8(a4)
   (0x80002b84#64, 0x00b73823#32),   -- sd   a1,16(a4)
   (0x80002b88#64, 0x00fa2023#32)]   -- sw   a5,0(s4)
    terminator ⟨0x80002b8c#64, 0xf61ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xf6#8,
      .j, 0, 0, 0#13, 0x1fff60#21, 0#12⟩

/-- The store-block entry pins: `x20 = s4 = env`, `x21 = s5 = &v` (value struct),
`x9 = s1 = the copied name pointer` (result of the memcpy into the fresh block). -/
def appendStoreL (s4Ptr s5Ptr s1Ptr : BitVec 64) : GRegs :=
  [(20, s4Ptr), (21, s5Ptr), (9, s1Ptr)]

/-- Post: parked at the shared finalize tail `0x80002aec`, memory = the entry memory
with the seg's five stores applied (computed off the write-log). -/
def AppendStorePost (s4Ptr s5Ptr s1Ptr : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks appendStoreSeg
    (SegEvalState.init (appendStoreL s4Ptr s5Ptr s1Ptr) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002aec#64

/-- **`appendStoreRow`** — the append-path store block as a `Triple`, via `segToTriple`
over the `j`-terminated `appendStoreSeg`.  `hwf` is the row's one kernel `decide`;
`hpost` projects the computed end PC (the `j` target `0x80002aec`) and the write-log
memory off the outcome.  Replaces the ~18-site hand `stepObs_alu`/`stepObs_store`
battery (loads, shifts, adds, five stores) + its run + 33-branch frame that the legacy
idiom would build. -/
theorem appendStoreRow (s4Ptr s5Ptr s1Ptr : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre appendStoreSeg (appendStoreL s4Ptr s5Ptr s1Ptr) lds 0x80002b44#64 m0)
      (AppendStorePost s4Ptr s5Ptr s1Ptr lds m0) := by
  apply segToTriple appendStoreSeg (appendStoreL s4Ptr s5Ptr s1Ptr) lds 0x80002b44#64 m0
    (AppendStorePost s4Ptr s5Ptr s1Ptr lds m0)
    (by have h : keysG (appendStoreL s4Ptr s5Ptr s1Ptr) = [20, 21, 9] := rfl
        rw [h]; show ChainOK 0x80002b44#64 [20, 21, 9] appendStoreSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x80002b44#64 (SegEvalState.init (appendStoreL s4Ptr s5Ptr s1Ptr) lds)
    appendStoreSeg) = some 0x80002aec#64
  rfl

#print axioms appendStoreRow

/-! ## Item 3 — the update-path HIT store block `0x80002ac0..0x80002ae8` (the `hUpdate` prefix)

The update path (name FOUND in the scan) is `prologue ≫ scan-loop ≫ HIT-store-block`.
Per the task the scan LOOP stays a `loopFromBody` seam (its shape is the env_get scan,
`env_get_scan_spec'` in `EnvGetSpec4`); this row lands the STRAIGHT-LINE HIT tail — the
`hUpdate` prefix's genuinely straight-line part — that overwrites `vals[i]` with the new
value `v` and falls through to the shared finalize tail `0x80002aec`:
```
80002ac0  ld   a5,16(s4)    -- x15 := env->vals
80002ac4  slli a4,s0,0x1    -- x14 := i*2         (s0 = the found index i)
80002ac8  ld   a1,0(s5)     -- x11 := v.word0
80002acc  ld   a2,8(s5)     -- x12 := v.word1
80002ad0  ld   a3,16(s5)    -- x13 := v.word2
80002ad4  add  a4,a4,s0     -- x14 := i*3
80002ad8  slli a4,a4,0x3    -- x14 := i*24
80002adc  add  a5,a5,a4     -- x15 := &vals[i]
80002ae0  sd   a1,0(a5)     -- vals[i].word0 := v.word0
80002ae4  sd   a2,8(a5)     -- vals[i].word1 := v.word1
80002ae8  sd   a3,16(a5)    -- vals[i].word2 := v.word2   (falls through to 0x80002aec)
```
Straight-line, NO terminator (fall-through into the shared epilogue) — exactly the
`mallocArgSeg` shape.  Its three stores land in the seg's canonical `writeLog`; the
`FrameRepr` overwrite (`Store.define` UPDATE case — same var list, `vals[i]` value
replaced) is the spec residual, served by the same readback discipline as
`frameRepr_append`.  No `jal`, no `bridgeOfSeg`; the scan loop above is the only genuine
seam left, and it is a `loopFromBody`/`env_get_scan_spec'` residual (named, not built
here). -/
#derive_case updateStoreSeg chain
  [(0x80002ac0#64, 0x010a3783#32),   -- ld   a5,16(s4)
   (0x80002ac4#64, 0x00141713#32),   -- slli a4,s0,0x1
   (0x80002ac8#64, 0x000ab583#32),   -- ld   a1,0(s5)
   (0x80002acc#64, 0x008ab603#32),   -- ld   a2,8(s5)
   (0x80002ad0#64, 0x010ab683#32),   -- ld   a3,16(s5)
   (0x80002ad4#64, 0x00870733#32),   -- add  a4,a4,s0
   (0x80002ad8#64, 0x00371713#32),   -- slli a4,a4,0x3
   (0x80002adc#64, 0x00e787b3#32),   -- add  a5,a5,a4
   (0x80002ae0#64, 0x00b7b023#32),   -- sd   a1,0(a5)
   (0x80002ae4#64, 0x00c7b423#32),   -- sd   a2,8(a5)
   (0x80002ae8#64, 0x00d7b823#32)]   -- sd   a3,16(a5)

/-- The update-store entry pins: `x20 = s4 = env`, `x21 = s5 = &v`, `x8 = s0 = the
found index i` (from the scan loop). -/
def updateStoreL (s4Ptr s5Ptr idx : BitVec 64) : GRegs :=
  [(20, s4Ptr), (21, s5Ptr), (8, idx)]

/-- Post: parked at the shared finalize tail `0x80002aec`, memory = entry memory with
the three `vals[i]` stores applied (computed off the write-log). -/
def UpdateStorePost (s4Ptr s5Ptr idx : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks updateStoreSeg
    (SegEvalState.init (updateStoreL s4Ptr s5Ptr idx) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002aec#64

/-- **`updateStoreRow`** — the update-path HIT store block as a `Triple`, via
`segToTriple`.  Lands the computed write-log post parked at the shared tail
`0x80002aec`.  This is the straight-line part of the `hUpdate` prefix; the scan LOOP
preceding it stays a `loopFromBody`/`env_get_scan_spec'` seam (named residual). -/
theorem updateStoreRow (s4Ptr s5Ptr idx : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre updateStoreSeg (updateStoreL s4Ptr s5Ptr idx) lds 0x80002ac0#64 m0)
      (UpdateStorePost s4Ptr s5Ptr idx lds m0) := by
  apply segToTriple updateStoreSeg (updateStoreL s4Ptr s5Ptr idx) lds 0x80002ac0#64 m0
    (UpdateStorePost s4Ptr s5Ptr idx lds m0)
    (by have h : keysG (updateStoreL s4Ptr s5Ptr idx) = [20, 21, 8] := rfl
        rw [h]; show ChainOK 0x80002ac0#64 [20, 21, 8] updateStoreSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x80002ac0#64 (SegEvalState.init (updateStoreL s4Ptr s5Ptr idx) lds)
    updateStoreSeg) = some 0x80002aec#64
  rfl

#print axioms updateStoreRow

end Vsa.Sim
