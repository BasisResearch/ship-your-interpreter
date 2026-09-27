import Vsa.Sim.MemcpySites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

/-!
# Layer 3 — `memcpy` byte-copy-path total-correctness spec (`memcpy_bytepath_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/MemcpySites.lean`) into a total-correctness triple for the **byte-copy
path** of newlib `memcpy` — the path taken when the source/destination alignment
fast-path does not apply.

This is the first STORE-heavy M3 spec; it pilots the **described-memory-update Q
pattern**. The loop body stores one byte per iteration, so the config predicate
`St` carries the current memory's relation to the ghosts `m0`/`bs` (a
copied-prefix description) and each `stepObs_store` transition threads it through
the single-byte insert (`Std.ExtHashMap.getElem?_insert` read-over-write; key
disequalities are omega-shaped from the region bounds + non-overlap).

## The byte loop (`[0x80006c48, 0x80006c5c)`, back-edge `0x58 → 0x48`)

At loop head `0x48`, iteration `i` (`0 ≤ i ≤ n`):
* `x11 (a1) = src + i`, `x14 (a4) = dst + i`, `x17 (a7) = dst + n`, `x10 (a0) = dst`;
* memory: bytes `[dst, dst+i)` hold `bs`; bytes outside `[dst, dst+n)` hold `m0`;
  the source region `[src+i, src+n)` still reads `bs` (non-overlap keeps it stable);
* measure `n - i` strictly decreases.

## Ghost parameters

`dst` (x10 in), `src` (x11 in), `n : Nat` (byte count, x12 in), `r` (x1, return
addr, 4-aligned), `m0` (pinned memory), `bs : List (BitVec 8)` (source bytes,
`bs.length = n`, `∀ k < n, m0[(src+k)] = bs[k]`). The described update is stated
observationally in `Q`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded memcpyChunk0 memcpyChunk1 memcpyChunk2 memcpyChunk3 memcpyChunk4)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Pointer arithmetic: `(base + ofNat k).toNat = base.toNat + k` under no-wrap -/

/-- `sbData` on `zero_extend (m := 64) b` recovers the byte `b` (as `BitVec (8*1)`).
The stored low byte of `a5 = zero_extend b` is `b`. -/
theorem sbData_zext (b : BitVec 8) :
    sbData (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.shiftRight_zero]
  have hlt : (b : BitVec 8).toNat < 2^8 := b.isLt
  have key : ∀ W : Nat, (2:Nat)^W = 2^8 → (BitVec.ofNat W (b.toNat % 2^64)).toNat = b.toNat := by
    intro W hW
    rw [BitVec.toNat_ofNat, hW]
    have h2 : (b : BitVec 8).toNat % 2^64 = (b : BitVec 8).toNat := Nat.mod_eq_of_lt (by omega)
    rw [h2, Nat.mod_eq_of_lt hlt]
  exact key _ (by decide)

/-! ## `MemcpyLoaded` preserved by a single byte insert outside the code region -/

/-! ## The described-memory invariant

`MemInv dst src n bs i mem` is the standing description of `mem` at loop iteration
`i` (`0 ≤ i ≤ n`), over the ghost byte function `bs : Nat → BitVec 8`:
* `copied`: the destination prefix `[dst, dst+i)` holds the copied bytes `bs`;
* `outside`: every address outside `[dst, dst+n)` still holds `m0`-content, stated
  as equal to the *source-provided* byte function via the reference map;
* `src_intact`: the remaining source region `[src+i, src+n)` still reads `bs`
  (non-overlap keeps the source stable across the copy).

We package the "outside untouched" description directly against a reference map
`m0` rather than `bs`, and carry `src_intact` explicitly (re-established each
iteration from `outside` + non-overlap). -/

/-! ## Region bounds bundle

The disjointness / no-wraparound side facts used to discharge the store's
read-over-write key disequalities and the pointer arithmetic. `dst`, `src`, `n`
are the ghosts. -/

/-! ## Blanket ghost-frame predicate (`NotWrittenB`) + generic per-class helpers

`StB` tracks the byte-loop live GPRs (`x10, x11, x14, x17, x1`) plus the scratch
`x15`. To make preservation of *every other* register recoverable after packaging
into a `Triple` (needed by callers that need callee-saved / `sp` preservation),
`StB` carries a ghost snapshot `g : (R : Register) → Option (RegisterType R)` and a
blanket conjunct: every register outside the write-set reads as its ghost value.

`NotWrittenB R` is the disequality conjunction over the union of the byte-path
written GPRs (`x11` = `addi a1`, `x14` = `mv a4`/`addi a4`, `x15` = `lbu a5`) and the
per-step write-set / tick-set registers (`PC, nextPC, minstret, minstret_increment,
mcycle, mtime, mip`). The STORE writes only memory (no rd), so it is covered by the
noise disequalities alone. -/

/-- `R` is outside the union of the byte-path written GPRs (`x11, x14, x15`) and
every register any hot-path step (ALU / branch / store / tick) can write. -/
abbrev NotWrittenB (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenB.x11 {R : Register} (h : NotWrittenB R) : (Register.x11 == R) = false := h.1

/-! ## The config-level state predicate

`StB pc i r dst src n m0 bs c` is the standing observation at a byte-loop program
point `pc`, iteration `i`. It bundles `GoodState`, code loaded, PC at `pc`, the
live pointers (`a1 = src+i`, `a4 = dst+i`, `a7 = dst+n`, `a0 = dst`), the return
register `x1 = r`, `minstret` defined, `tick < 2`, the `Regions` bounds, `i ≤ n`,
and the described-memory invariant `MemInv … i`. The scratch register `a5` (x15)
is not tracked (overwritten every iteration).

The pointer registers are stated at their `BitVec` values `src + ofNat i` etc.;
`ptr_toNat` bridges to `.toNat` where the fetch/access bounds need it. -/

/-! ## Pointer BitVec identities (unconditional, mod-2^64) -/

/-! ## State at 0x58 (post-store, pre-`bne`) for iteration `i`

`StB58 i r dst src n m0 bs c` describes the config after one full loop body
(load/addi/addi/store) for iteration `i < n`: the pointers are advanced by one
(`a1 = src+(i+1)`, `a4 = dst+(i+1)`), `a7 = dst+n`, `a0 = dst`, and the memory
invariant has moved to `i+1`. -/

/-! ## RAM/window facts for the per-iteration source and dest pointers

From `Regions` + `i < n`, the pointer `p + ofNat i` (for `p ∈ {dst, src}`) lands in
RAM and above the HTIF window; `ptr_toNat` bridges `.toNat`. -/

/-! ## STORE-observation consumers

From a STORE observation `ReadsLikePost σ' (sigmaPost_store σ pc vm m')`, read the
framing fields: `obs_store_pc` gives PC := pc+4; `obs_store_other` gives any GPR
from `σ` (the STORE writes only memory); `obs_store_minstret` gives minstret
defined. These mirror the `obs_alu_*` consumers over the `sigmaPost_store` frame. -/

theorem post_store_pc (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_store_pc {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_store_pc σ pc vm m')

theorem obs_store_other {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5).trans hσ)

theorem obs_store_minstret {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## One loop body iteration (`0x48 → 0x58`)

Chains `lbu → addi a4 → addi a1 → sb`. The `lbu` reads `bs i` from `src+i`
(`src_intact`); the two `addi`s advance the pointers; the `sb` writes `bs i` back
at `dst+i` (`sbAddr_succ`), and `meminv_store` re-establishes `MemInv … (i+1)`. -/

/-! ## The `bne a7,a4` at 0x58 (loop back-edge / exit to ret)

`a7 = dst+n`, `a4 = dst+(i+1)`. Taken iff `a7 ≠ a4` iff `i+1 < n` (no-wrap); loops
back to `0x48` iteration `i+1`. Not-taken iff `i+1 = n`; falls through to `0x5c`
(ret) with the full described update in place (`MemInv … n`). -/

/-! ## Loop invariant, guard, measure

`LoopIB = AtHeadB ∨ AtDone`: either at `0x48` iteration `i ≤ n` (with the described
memory prefix), or done at `0x5c` (ret) with the full update. `LoopB` = "at `0x48`
with `i < n`" (more to copy). Measure `LoopMuB = a7.toNat - a4.toNat = n - i`
(computed from the pointer registers; total via `getD`). -/

/-! ## Prefix `0x40 → 0x48`: `mv a4,a0` then `bgeu a0,a7` not-taken

Entry (byte path): `a0 = dst`, `a1 = src`, `a7 = dst+n`, with `n > 0`. `mv a4,a0`
sets `a4 := dst`; `bgeu a0,a7` is not-taken (`dst <u dst+n` since `n > 0`, no wrap),
falling to `0x48` iteration `0`. -/

/-! ## `ret` (`0x5c → r`) and the byte-path spec

`ret` reads `x1 = r` (4-aligned), redirects the PC to `r`, and preserves all GPRs
— in particular `x10 = dst` (memcpy returns the destination) and the described
memory update `MemInv … n`. -/

/-- The described-update postcondition: PC back at `r`, `x10 = dst`, `GoodState`,
`x1 = r`, and the observational described update — the `n` copied bytes are present
at `[dst, dst+n)` and everything outside is unchanged from `m0`. -/
def memcpy_bytepath_post (g : (R : Register) → Option (RegisterType R)) (r dst : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k < n → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R)

/-! ## The byte-copy-path total-correctness spec

Entry precondition at `0x80006c40` (the byte-copy path the binary takes when the
alignment fast-path does not apply), `n > 0`. The machine runs (finitely many
architectural steps, tick parity unconstrained) to `r` with `x10 = dst`,
`GoodState`, and the memory holding the described update: the `n` source bytes
copied into `[dst, dst+n)`, everything else untouched. -/

end Vsa.Sim
