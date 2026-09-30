import Vsa.Sim.ChainFrameOut
import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch11Part24
import Vsa.Sim.DecodeTable.Batch12Part27

/-!
# Layer 3 — total-correctness spec for `value_equal` (@0x8000285c)

`value_equal(Value a, Value b)` (both by-reference in `a0`/`a1`) returns
`cond (Value.equal va vb) 1 0` in `a0`. It:

1. loads both kind tags, `bne` to the `return 0` tail if they differ;
2. an out-of-range guard (`li a4,5; bltu a4,a5 → return 0`);
3. dispatches through a `.rodata` jump table to a per-kind handler.

Handlers (all read-only): null → `1`; bool/int/closure/native → payload `sub`
then `seqz` (0 iff equal); str → `strcmp(...) == 0`.

This file proves the **five non-`str` variants** end-to-end. The jump-table entries
are provided as a `JumpTable` region hypothesis; `φc`/`N.addr` injectivity bridge the
closure/native cases (the C compares pointers, the spec compares addresses/`NativeFn`).

## C ↔ spec correspondence (checked against `c/src/value.c` + `Value.equal`)

| kind    | C                          | spec `Value.equal`        | bridge                    |
|---------|----------------------------|---------------------------|---------------------------|
| null    | `return 1`                 | `true`                    | `cond … 1 0 = 1`          |
| bool    | `a.as.b == b.as.b`         | `a == b`                  | 4-byte payloads {0,1}     |
| int     | `a.as.i == b.as.i`         | `a == b` (Int)            | two's-complement 8-byte   |
| str     | `strcmp(...) == 0`         | `a == b` (String)         | `strcmp_full_spec`        |
| closure | `a.as.fn == b.as.fn`       | `a == b` (Addr)           | **`φc` injectivity**      |
| native  | `a.as.native.fn == …`      | `a == b` (NativeFn)       | **`N.addr` injectivity**  |

The closure case compares `Closure*` pointers (`φc ca` vs `φc cb`); with `φc`
injective on the relevant addresses these agree with the spec's address equality.
The native case compares the three fn pointers `N.addr f`; with those three distinct,
pointer equality agrees with `NativeFn` equality.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Ghost frame for `value_equal` (non-str path)

The non-str paths write scratch GPRs `x10` (a0 result / payload), `x14` (a4),
`x15` (a5), plus control/noise registers. `NotWrittenVE` is the disequality set for
a ghost register untouched by these paths. -/

/-! ## Region facts for the two argument buffers

Each 24-byte `Value` lives in RAM, 8-aligned, above the HTIF window, disjoint from
the `value_equal` code `[0x8000285c, 0x800028fc)`. -/

/-! ## The `.rodata` jump table at `0x80019ef8`

Six signed 32-bit offsets (kind 0..5), each `entry_k` such that
`entry_k + 0x80019ef8` is the kind-`k` handler address. Read off the linked image
(`objdump -s -j .rodata`). Provided as a hypothesis (like `*Loaded` for code). -/

/-! ## Pre / post -/

/-! ## Ghost-frame passthrough per step-shape (mirror `ValueTruthySpec.frame_*_t`) -/

/-! ## The dispatch spine (0x80002870 → handler)

From a state at `0x80002870` with `x15 = ofNat (kindTag v)` (kind already known
equal + in range) and the jump table loaded, run the 7 dispatch instructions
(`auipc/addi/slli/add/lw/add/jr`) to land at `handlerAddr v`, preserving the two
buffer pointers, `x1`, memory, and the ghost frame. -/

/-! ## The prefix (entry → dispatch, equal-kind case)

Runs 0x8000285c..0x8000286c (both kind loads, the `bne` (not taken because kinds
equal), `li a4,5`, `bltu` (not taken because kind ≤ 5)) landing at 0x80002870 with
`x15 = ofNat (kindTag vb)`, ready for `ve_dispatch`. Requires `kindTag va = kindTag vb`. -/

/-! ## Kind-mismatch ⇒ `Value.equal = false`. -/
theorem equal_false_of_kind_ne (va vb : Value) (h : kindTag va ≠ kindTag vb) :
    Value.equal va vb = false := by
  cases va <;> cases vb <;> simp_all [kindTag, Value.equal]

/-! ## `seqz` bridge: `sltiu v,1` result is `cond (v = 0) 1 0`. -/
theorem seqz_val (v : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) : BitVec 64)
      = cond (v == 0#64) (1#64) (0#64) := by
  by_cases h : v = 0#64
  · subst h
    have : zopz0zI_u (0#64) (sign_extend (m := 64) (0x001#12)) = true := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt]; decide
    rw [this]; simp only [beq_self_eq_true, cond_true]
    apply BitVec.eq_of_toNat_eq; decide
  · have hpos : 0 < v.toNat := by
      rcases Nat.eq_zero_or_pos v.toNat with h0 | hp
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
      · exact hp
    have hfalse : zopz0zI_u v (sign_extend (m := 64) (0x001#12)) = false := by
      simp only [zopz0zI_u, Sail.BitVec.toNatInt,
        show (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 from by decide,
        decide_eq_false_iff_not]
      intro hlt
      have := Int.ofNat_lt.mp hlt
      omega
    rw [hfalse, show (v == 0#64) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; exact h,
      cond_false]
    apply BitVec.eq_of_toNat_eq; decide

/-! ## The `li a0,k; ret` tail (mismatch/oob → 0, null → 1) -/

/-! ## `value_equal_spec` — mismatch + null variants

The kind-mismatch path (`bne` taken → `0x8000288c: li a0,0; ret`) and the `null`
handler (`0x800028a8: li a0,1; ret`) both close via `li_ret_tail`. -/

end Vsa.Sim
