import Vsa.Sim.RamReadPins
import Vsa.Sim.EvalStrSim
import Vsa.Sim.EnvGetSpec4
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.var` simulation Triple (`evalVarSim`)

The `EvalE.var` leaf case (`ExprKind` tag `k = 4`, arm PC `0x80003434`). This is the
first non-leaf-shaped case: the arm calls `env_get` and copies the found `Value`
into the sret buffer. It does NOT use the shared `blockD_v` epilogue — the var arm
carries its OWN inlined epilogue (interleaved with the value copy), so `blockC_var`
reaches `EvalExit` directly.

## The full var arm disassembly (all 18 words decoded/verified against the ELF)

    0x80003434: 00863583  ld   a1, 8(a2)       -- a1 := *(a2+8) = var-name CString ptr
    0x80003438: 00068513  addi a0, a3, 0        -- a0 := a3   (the interp/env arg → env_get arg0)
    0x8000343c: 0f010613  addi a2, sp, 240      -- a2 := sp+0xf0  (24-byte result buffer)
    0x80003440: fd0ff0ef  jal  ra, 0x80002c10   -- call env_get   (link 0x80003444)
    0x80003444: 32050ee3  beq  a0, x0, 0x80003f80 -- NOT taken (found ⇒ a0≠0)
    0x80003448: 0f013683  ld   a3, 0xf0(sp)     -- a3 := *(sp+0xf0)   Value bytes 0..7
    0x8000344c: 0f813703  ld   a4, 0xf8(sp)     -- a4 :=                    bytes 8..15
    0x80003450: 10013783  ld   a5, 0x100(sp)    -- a5 :=                    bytes 16..23
    0x80003454: 43813083  ld   ra, 1080(sp)     -- inlined epilogue: restore ra   (= r)
    0x80003458: 43013403  ld   s0, 1072(sp)     --   restore s0
    0x8000345c: 00d4b023  sd   a3, 0(s1)        -- copy Value into sret (s1): bytes 0..7
    0x80003460: 00e4b423  sd   a4, 8(s1)        --   bytes 8..15
    0x80003464: 00f4b823  sd   a5, 16(s1)       --   bytes 16..23
    0x80003468: 42013903  ld   s2, 1056(sp)     --   restore s2
    0x8000346c: 00048513  addi a0, s1, 0        --   a0 := s1 = sret (return value)
    0x80003470: 42813483  ld   s1, 1064(sp)     --   restore s1
    0x80003474: 44010113  addi sp, sp, 1088     --   restore sp
    0x80003478: 00008067  ret                   --   PC := r

## Structure (mirrors `EvalStrSim.lean`)

* `blockA_k` (k=4, armPC 0x80003434, `Env_getLoaded`, `.var x`) delivers `ArmEntryK`.
* **`blockC_var`** — the whole arm `ArmEntryK … 0x80003434 Env_getLoaded (.var x) →
  EvalExit … v`, taking `env_get`'s FOUND-case contract as an explicit hypothesis
  (`henv_get`, see below) and proving the remainder (beq-not-taken, 3-word result
  load, 3-word store into sret, and the inlined-epilogue restores) concretely,
  establishing `EvalExit` directly.
* **`VarSlotPinned` / `var_slot_kindPinned`** — the jump-table slot pin for tag 4.
* **`EvalVarEntry` / `evalVarSim`** — the `EvalE.var` Triple.

## HONEST DEPENDENCY: `env_get`'s FOUND-case contract (`henv_get`)

The `env_get` Layer-3 spec suite (`EnvGetSpec*.lean`) is, per its own docstring, a
"WORK IN PROGRESS FOUNDATION": every one of the 51 instructions has a `stepObs`
lemma, and the SCAN LOOP is verified up to `ScanExit` (hit @0x80002c70 / miss
@0x80002cc4). But the full end-to-end contract — prologue (0x80002c10 → scan entry),
the FOUND-value copy tail (0x80002c70–0x80002cc0: `a0 := 1`; copy the 24-byte
`values[i]` into `*out`; restore; `addi sp,64`; `ret`), the parent chain-walk loop,
and the `Store.lookup ↔ ValueRepr` bridge — is DESIGNED but NOT PROVEN. Composing
the existing lemmas the way `blockC_str` composes `value_str_spec_full` is therefore
not possible today.

So `blockC_var` threads `env_get`'s found-case as a single, clearly-scoped
`Triple`-shaped hypothesis on `EvalVarEntry` (`env_get_found`): from the machine
config at the call site (PC 0x80002c10, args set) it reaches the link return
(PC 0x80003444) with `a0 = 1`, the 24-byte result buffer at `sp+0xf0` holding
`ValueRepr … v` (the found value from the `EvalE.var` derivation), and all the
frame/store/geometry invariants preserved. Everything ELSE in the var arm — the
argument setup, the not-taken branch, the value copy into sret (preserving
`ValueRepr` via `valueRepr_agreeP`), and the inlined epilogue restores → `EvalExit`
— is proven here for real. When `env_get`'s full contract lands, this one hypothesis
is discharged by it and `blockC_var` closes unconditionally.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `EX_VAR` arm sites (@0x80003434 … @0x80003478) -/

/-! ### The three result-buffer loads (`ld a3/a4/a5, 0xf0/0xf8/0x100(sp)`) and the
four epilogue restores (`ld ra/s0/s2/s1, off(sp)`).  Each is an `ld rd,off(sp)`;
they differ only in PC, offset, destination register/index, word, and code bytes. -/

/-! ## `VarSlotPinned` — the `EX_VAR` (tag 4) jump-table slot pin

Slot at `jumpTableBase + 16` holds `dc 94 fe ff` (LE) = offset `0xfffe94dc`, and
`0x80019f58 + (Int32)0xfffe94dc = 0x80003434` (the var arm). Mirrors `StrSlotPinned`;
discharges `KindSlotPinned 4 0x80003434`. -/

/-! ## `VarPostCall` — the machine state at the `env_get` link return `0x80003444`

The FOUND-case post of the `env_get` call (`henv_get`, threaded from `EvalVarEntry`;
see the header for why this is an honest, clearly-scoped hypothesis rather than a
composition of existing lemmas). At `0x80003444`, `env_get` has returned with `a0 = 1`
(found ⇒ nonzero, so the `beq` is not taken), and the 24-byte result buffer at
`sp+0xf0` holds `ValueRepr … v` (the value the `EvalE.var` derivation supplies via
`store.get?`). The callee-saved spill slots, `s1 = sret`, the lowered `sp`, the store
representation, the eval_expr code image, the g-frame, the output, and all geometry
survive (no register/heap mutation on the lookup path — `env_get` only wrote the
result buffer). This is exactly what the inlined var-arm epilogue consumes. -/

/-! ## `blockC_var` — the var-arm epilogue (`VarPostCall … v → EvalExit … v`)

The twelve instructions from the `env_get` link return `0x80003444` to the `ret`
`0x80003478`: the not-taken `beq`, the three result-buffer loads, the two initial
epilogue restores (`ld ra`, `ld s0`), the three-word copy of the `Value` into `sret`
(`sd a3/a4/a5, {0,8,16}(s1)`), the remaining restores (`ld s2`, `mv a0,s1`, `ld s1`,
`addi sp,1088`) and `ret`.  Because the epilogue is inlined and interleaved with the
copy, this reaches `EvalExit` directly (it does NOT go through the shared `blockD_v`).

The store frame `σ9.mem` = three `writeMap8`s into `[sret, sret+24)` over `mpc`.  The
`ValueRepr … sret v` conjunct of `EvalExit.result` comes from `VarPostCall`'s copy
obligation applied to `σ9.mem` (which reads back the three copied words at `sret` and
agrees with `mpc` outside `[sret, sret+24)`). `StoreRepr`/`Eval_exprLoaded`/`memFrame`
transfer along the same agreement (the sret buffer is disjoint from the store's arena
window and the code, threaded from `VarPostCall`). -/

/-! ## `EvalVarEntry` — the machine precondition for the `EvalE.var` case

Mirrors `EvalStrEntry`'s shared geometry, but carries `VarSlotPinned` + `Env_getLoaded`
(the arm's callee) in place of the str-specific slot/callee, `ExprRepr … (.var x)`, and
— the field unique to `.var` — the **`env_get` FOUND-case contract** `env_get_found`
as an honest, clearly-scoped `Triple` (see the header): from the var arm's entry it
reaches the link return `0x80003444` with `a0 = 1`, the 24-byte result buffer at
`sp+0xf0` copying to `sret` as `ValueRepr … v`, and all invariants preserved.  The
found value `v = st.store.get? env x` is supplied by the `EvalE.var` derivation. -/

end Vsa.Sim
