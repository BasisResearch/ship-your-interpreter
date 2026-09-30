import VsaIris.Vsa.HeapTake

/-!
# Moving a free chunk between bins

`_malloc_r` puts a last remainder that is too small back on its own bin
(`0x8000491c`) and `_free_r` frontlinks a coalesced chunk; both empty one bin
of its single member and link that member in at the head of another, setting
the member's block bit in `binblocks`.

`PHeapAt.moveBin` is that step at the heap: seven words change (bin `i`'s two
links, the victim's two links, bin `j`'s `fd`, the old head's `bk`, and the
bitmap), the walk and every footer are untouched, and the result is the shape
at `updBins (updBins bins i []) j (v :: bins j)`.
-/

