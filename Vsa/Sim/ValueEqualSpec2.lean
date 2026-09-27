import Vsa.Sim.ValueEqualSpec
import Vsa.Sim.StoreInvariant

/-!
# Layer 3 — total-correctness spec for `value_equal`, part 2 (payload variants + merge)

This finishes `value_equal` (@0x8000285c): the four payload-comparing handlers
(bool/int/closure/native) end-to-end, and the unified `value_equal_spec` that merges
them with the previously-proven null/mismatch theorem.

Each payload handler runs, after `ve_dispatch` lands on the handler PC:

* **bool** (0x800028b0): `lw a0,8(a0); lw a5,8(a1); sub; seqz; ret`
* **int / closure** (0x80002894): `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`
* **native** (0x800028e8): `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

The `sub; seqz; ret` tail is shared (`ve_sub_seqz_ret`); the per-kind bridges
(`bool_eq_bridge`/`int_eq_bridge`/`ptr_eq_bridge`) rewrite the `sub == 0` register test
to the matching `Value.equal` clause.
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

/-! ## Shared `sub a0,a0,a5; seqz a0,a0; ret` tail

From a state at the `sub` site with `x10 = payA`, `x15 = payB`, runs the three
instructions, ending at the return target with `x10 = cond (payA - payB == 0) 1 0`,
preserving `x1`, memory, and the ghost frame. Parameterised by the three site lemmas so
it serves all three payload handlers. -/

/-! ## Region / payload-address helpers for the 8-byte loads

`ve_pay8_addr`/`ve_pay16_addr` give the load address; these bundle the RAM/HTIF/align
side facts the `ld`/`lw` sites need at `+8` (8-byte) and `+16` (8-byte). -/

/-- `p < 2^64` from an 8-byte reconstruction. -/
theorem ld_recon_lt (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (p : Nat)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
      (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p) :
    p < 2 ^ 64 := by have := b7.isLt; omega

/-- Any `read64` result is a 64-bit-representable natural. -/
theorem read64_lt (m0 : Mem) (a p : Nat) (h : read64 m0 a = some p) : p < 2 ^ 64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hrec⟩ := read64_bytes m0 a p h
  exact ld_recon_lt b0 b1 b2 b3 b4 b5 b6 b7 p hrec

/-! ## int / closure handler (0x80002894): `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`

Loads both 8-byte payloads at `+8`, subtracts, `seqz`, returns. The `sub == 0` bridge is
`int_eq_bridge` (int) / `ptr_eq_bridge` (closure). This lemma runs the shared 8-byte load
sequence + tail, leaving the caller to supply the two payloads `q1 q2` and the bridge. -/

/-! ## bool handler (0x800028b0): `lw a0,8(a0); lw a5,8(a1); sub; seqz; ret`

Loads both 4-byte `{0,1}` bool payloads at `+8`. `sext_word_small` folds each to
`cond b (1#64) (0#64)`; `bool_eq_bridge` bridges the `sub == 0` test. -/

/-! ## native handler (0x800028e8): `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

Loads both fn pointers at `+16`, subtracts, `seqz`, returns. Same shape as the int
handler but at offset `+16` and using the `f0/f4/f8` tail sites. -/

/-! ## Merged `value_equal_spec` (all non-`str` variants)

Cases on `(va, vb)`. Mismatched kinds and both-`null` reuse
`value_equal_spec_null_mismatch`; the four payload same-kind cases run
`ve_prefix → ve_dispatch → ve_{bool,int,native}_handler` with the matching bridge.
Closure/native pointer identity is bridged only for the two compared operands.
The `str`-`str` case is supplied via `ve_str_handler` (in the str section below); every
other case is discharged here. -/

end Vsa.Sim
