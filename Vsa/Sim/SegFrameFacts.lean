import Vsa.Sim.BlockMem
import Vsa.Sim.BlockPilot

/-!
# `SegFrameFacts` — discharge `#derive_case`/`chain_facts` frame-window residuals uniformly

After `chain_facts` strips every decode/byte-pin leaf of a segment, the residual is
exactly a list of `MemFacts` (one per ld/sd) plus the segment's data-dependent
branch guards.  Each `MemFacts` is a pure FRAME-GEOMETRY obligation: a load needs
its 8-byte window in range/aligned/HTIF-disjoint and populated; a store needs only
the window bounds.  None of it depends on the operand DATA — only on where the
frame base sits.

So the whole frame-window residual discharges from ONE `FrameBundle`: the frame
base `base` sits in RAM, is 8-aligned, clears the HTIF window, and the memory is
populated across the frame.  `frame_ld`/`frame_sd` then close any window by `omega`
(bounds) + `pop` (pins), with NO per-window hand plumbing — the `spill_addr` +
`read64_bytes` + `getElem_writeMap8_disjoint` ritual every `blockC_*` row repeats.

Because the binary-op arms (div/mod/eq/ne, the ge dispatch) share the same
1088-byte frame with the same spill slots, one `FrameBundle` discharges every arm's
`SegPre`.  The same tool applies anywhere the codebase hand-threads sp-relative
frame windows (the recursive M4 arms, the M5 error-site reads).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

/-! ## The two `MemFacts` atoms (bounds + pins for one memory op) -/

/-- A `ld` `MemFacts` from its window bounds and 8 byte pins. -/
theorem memFacts_ld_frame (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hk : a.kind = .ld)
    (hlo : 0x80000000 ≤ (eaddrM a L).toNat)
    (hhi : (eaddrM a L).toNat + 8 ≤ 0x100000000)
    (hht : (eaddrM a L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)
    (hal : (eaddrM a L).toNat % 8 = 0)
    (p0 : m[(eaddrM a L).toNat]? = some b0) (p1 : m[(eaddrM a L).toNat + 1]? = some b1)
    (p2 : m[(eaddrM a L).toNat + 2]? = some b2) (p3 : m[(eaddrM a L).toNat + 3]? = some b3)
    (p4 : m[(eaddrM a L).toNat + 4]? = some b4) (p5 : m[(eaddrM a L).toNat + 5]? = some b5)
    (p6 : m[(eaddrM a L).toNat + 6]? = some b6) (p7 : m[(eaddrM a L).toNat + 7]? = some b7) :
    MemFacts m L [b0, b1, b2, b3, b4, b5, b6, b7] a := by
  unfold MemFacts; rw [hk]
  exact ⟨⟨hlo, hhi, hht, hal⟩, lpin_of_present p0, lpin_of_present p1,
    lpin_of_present p2, lpin_of_present p3, lpin_of_present p4,
    lpin_of_present p5, lpin_of_present p6, lpin_of_present p7⟩

/-- A `sd` `MemFacts` from its window bounds (no pins; the data list is irrelevant). -/
theorem memFacts_sd_frame (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (bs : List (BitVec 8)) (hk : a.kind = .sd)
    (hlo : 0x80000000 ≤ (eaddrM a L).toNat)
    (hhi : (eaddrM a L).toNat + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ (eaddrM a L).toNat)
    (hal : (eaddrM a L).toNat % 8 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts; rw [hk]; exact ⟨hlo, hhi, hht, hal⟩

/-! ## `FrameBundle` — the shared frame geometry the whole residual needs -/

/-- The frame-geometry bundle: the frame base `base` sits in RAM (`≥ 0x80000000`),
its whole `[base, base+0x108)` window fits below `2^64` and clears the HTIF window
(`tohostAddr+16 ≤ base`), the base is 8-aligned, and every address is populated in
`m`.  Everything a segment's `MemFacts` residual needs, independent of any arm's
operand data.  `0x108` covers the binary-op arms' widest slot (`+0x100`, an 8-byte
store); widen it if a client seg reaches further. -/
structure FrameBundle (m : Std.ExtHashMap Nat (BitVec 8)) (base : BitVec 64) : Prop where
  pop  : ∀ k : Nat, ∃ w : BitVec 8, m[k]? = some w
  lo   : 0x80000000 ≤ base.toNat
  hi   : base.toNat + 0x108 ≤ 0x100000000
  htif : tohostAddr + 16 ≤ base.toNat
  al   : base.toNat % 8 = 0

/-- The frame effective address reduces: `eaddrM` of a `base`-relative op with a
small non-negative offset is `base.toNat + off`.  The single address-arithmetic
fact `spill_addr` supplies per window, folded here once. -/
theorem frame_ea (a : MInstr) (L : GRegs) (base : BitVec 64) (off : Nat)
    (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off ≤ 0x108) (fb : FrameBundle m base) :
    (eaddrM a L).toNat = base.toNat + off := by
  unfold eaddrM
  rw [hsrc, BitVec.toNat_add, himm]
  have := fb.hi
  rw [Nat.mod_eq_of_lt (by omega)]

/-- **Discharge a `ld` window from the `FrameBundle`.**  Any `base`-relative 8-byte
load at a small aligned offset gets its `MemFacts` for FREE: the bounds by `omega`
from the bundle, the byte pins from `pop`.  Returns the read bytes as the load-data
list so the caller can assemble the seg's `lds`.  No `spill_addr`/`read64_bytes`
ritual, no operand data. -/
theorem frame_ld (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (off : Nat) (fb : FrameBundle m base)
    (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 0x108) (hoff8 : off % 8 = 0) :
    ∃ bs : List (BitVec 8), MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = base.toNat + off :=
    frame_ea a L base off hsrc himm (by omega) fb
  obtain ⟨b0, hb0⟩ := fb.pop (base.toNat + off)
  obtain ⟨b1, hb1⟩ := fb.pop (base.toNat + off + 1)
  obtain ⟨b2, hb2⟩ := fb.pop (base.toNat + off + 2)
  obtain ⟨b3, hb3⟩ := fb.pop (base.toNat + off + 3)
  obtain ⟨b4, hb4⟩ := fb.pop (base.toNat + off + 4)
  obtain ⟨b5, hb5⟩ := fb.pop (base.toNat + off + 5)
  obtain ⟨b6, hb6⟩ := fb.pop (base.toNat + off + 6)
  obtain ⟨b7, hb7⟩ := fb.pop (base.toNat + off + 7)
  refine ⟨[b0, b1, b2, b3, b4, b5, b6, b7], ?_⟩
  refine memFacts_ld_frame m L a b0 b1 b2 b3 b4 b5 b6 b7 hk
    (by rw [hea]; have := fb.lo; omega)
    (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; right; omega)
    (by rw [hea]; have := fb.al; omega)
    (by rw [hea]; exact hb0) (by rw [hea]; exact hb1) (by rw [hea]; exact hb2)
    (by rw [hea]; exact hb3) (by rw [hea]; exact hb4) (by rw [hea]; exact hb5)
    (by rw [hea]; exact hb6) (by rw [hea]; exact hb7)

/-- **Discharge a `sd` window from the `FrameBundle`.**  Any `base`-relative 8-byte
store at a small aligned offset gets its `MemFacts` for FREE — bounds only, no pins,
no data.  `bs` is whatever the seg threads there. -/
theorem frame_sd (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (off : Nat) (bs : List (BitVec 8)) (fb : FrameBundle m base)
    (hk : a.kind = .sd)
    (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 0x108) (hoff8 : off % 8 = 0) :
    MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = base.toNat + off :=
    frame_ea a L base off hsrc himm (by omega) fb
  refine memFacts_sd_frame m L a bs hk
    (by rw [hea]; have := fb.lo; omega)
    (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; omega)
    (by rw [hea]; have := fb.al; omega)

#print axioms memFacts_ld_frame
#print axioms memFacts_sd_frame
#print axioms frame_ea
#print axioms frame_ld
#print axioms frame_sd

/-! ## Composing into a seg's `SegPre` (the next step)

To build `SegPre <arm>Dispatch` from a `FrameBundle`, the caller: (1) reads each
load's 8 bytes via `frame_ld` and assembles the seg's `lds` in load order; (2)
discharges the `chain_facts` residual — each `MemFacts` by `frame_ld`/`frame_sd`,
each store-threaded load window over the ORIGINAL base memory by store
DISJOINTNESS (`getElem?_writeMap8_out`, since the arm's stores at `+0xf0..+0x100`
never overlap its loads at `+0x78..+0xa0`).  A `FrameBundle` store-monotonicity
lemma (`pop` survives `applyW`/`writeMap8`) would let `frame_ld` fire directly at
each threaded chain step instead; it is the one small remaining primitive.  The
only residual `chain_facts` leaves beyond these frame windows is the seg's
data-dependent guard (the `Wr≠0` divisor `beq` for div/mod), a genuine semantic
precondition supplied by the caller — not marshalling. -/

end Vsa.Sim
