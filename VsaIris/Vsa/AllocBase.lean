import VsaIris.Vsa.HeapRoom
import VsaIris.Vsa.AllocCode
import VsaIris.Vsa.MallocConsumer

/-!
# The allocator's calling conditions

The stack scratch `allocHeadroom`, the caller's stack pointer `SpOKA`, and
the live code `AllocLive` under which the allocator's runs
(`AllocHoles.lean`) are stated.
-/

namespace VsaIris.VsaHeap

open VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- Stack scratch for the allocator's deepest call chain: `_realloc_r` (64
bytes) over `_malloc_r` (96), over `_free_r` (32) from `malloc_extend_top`,
`_malloc_trim_r` (48) and `_sbrk_r`/`_sbrk` (32), rounded up. -/
def allocHeadroom : Nat := 512

/-- The caller's stack pointer for an allocator call: 16-aligned, in 32-bit
RAM, with `allocHeadroom` bytes above the HTIF words. -/
structure SpOKA (s : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + allocHeadroom ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

/-- The code bytes of the allocator are `live`. -/
abbrev AllocLive (live : Nat → Prop) : Prop := ∀ p ∈ allocText, live p.1

end VsaIris.VsaHeap
