import VsaIris.Vsa.MallocSmallChain
import VsaIris.Vsa.FreeChain
import VsaIris.Vsa.MallocFastImage
import Vsa.Sim.LayoutInstance

/-!
# The allocator's `live` set at the boundary

`vsaModel live` requires every `live` byte to be present (`VsaOk.live`). At
the approved boundary, take `live := liveOf c0`, the bytes present in the
initial memory. Present bytes stay present, since stores never remove one.

* `pathText_live`: the fast paths' code (`pathText`) is live. The `.text` bytes
  come from `FixedTextLoaded` and `_impure_ptr` from `ImageStaticsLoaded`
  (`pathLoaded_of_image`). This discharges the code premise of `fast_run` and
  `free_run`: `vsaDlMallocRoomImpl_boundary`, `vsaDlFreeRoomImpl_boundary`.
* `vsaFoot_live`: the allocator footprint (`allocGlobal` and the arena) is live
  given `AllocBytesPresent`. VSA's boundary states byte presence only for the
  stack (`InterpRunPhysicalFacts.stack_bytes`). For the allocator it states
  presence only at the words `HeapAt` reads. `AllocBytesPresent` is therefore
  a named premise, recorded in `PROOF_CLOSURE_PLAN.md` §2.
-/

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.Sim.Code Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap
open Vsa.Machine (Config)

/-- The fast paths' code bytes are present in any memory holding the image. -/
theorem pathText_live {c : Config} (ht : FixedTextLoaded c.σ.mem)
    (hs : ImageStaticsLoaded c.σ.mem) : ∀ p ∈ pathText, liveOf c p.1 := fun p hp => by
  unfold liveOf
  rw [pathLoaded_of_image ht hs p hp]
  rfl

/-- **`DlMallocRoomImpl` at the boundary.** At an approved boundary
configuration `c0`, `mallocRoomSpec` holds of the binary's `malloc` over
`vsaModel (liveOf c0)`, for the fast heap and requests of at most
`maxReq ≤ 487` bytes. -/
theorem vsaDlMallocRoomImpl_boundary {c0 : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunPhysicalFacts c0 stmts count inp N A φf φc aLeft)
    {maxReq headroom : Nat} (hmax : maxReq ≤ 487) :
    DlMallocRoomImpl (vsaModel (liveOf c0)) vsaLayout (vsaRoomFast maxReq) maxReq
      (SpOKFast headroom) mallocEntryBV gpV vsaClob vsaSaved headroom pathText :=
  vsaDlMallocRoomImpl_fast hmax (pathText_live F.text_image F.statics)

/-- **`DlFreeRoomImpl` at the boundary**: `freeRoomSpec` holds of the binary's
`free` over `vsaModel (liveOf c0)` for a block below the top of a fast heap. -/
theorem vsaDlFreeRoomImpl_boundary {c0 : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat} (F : LayoutInstance.InterpRunPhysicalFacts c0 stmts count inp N A φf φc aLeft)
    {maxReq headroom : Nat} :
    DlFreeRoomImpl (vsaModel (liveOf c0)) vsaLayout (vsaRoomFast maxReq) (vsaFreeTop maxReq)
      (SpOKFast headroom) freeEntryBV gpV vsaClob vsaSaved headroom pathText :=
  vsaDlFreeRoomImpl_fast (pathText_live F.text_image F.statics)

/-- **Presence of the allocator's bytes at the boundary** (a named premise).
Every byte of the allocator's globals and of the arena `[heapStart, heapEnd)`
is present in the boundary memory. The loader supplies it, as
`InterpRunPhysicalFacts.stack_bytes` does for the stack. VSA states presence
only for the words `HeapAt` reads. -/
structure AllocBytesPresent (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  global : ∀ a, allocGlobal a → (m[a]?).isSome
  arena : ∀ a, heapStart ≤ a → a < heapEnd → (m[a]?).isSome

/-- The allocator footprint of any live-block list is live at the boundary. -/
theorem vsaFoot_live {c : Config} (hp : AllocBytesPresent c.σ.mem) (H : List (Nat × Nat)) :
    ∀ a, vsaFoot H a → liveOf c a := by
  rintro a (hg | ⟨h1, h2, _⟩)
  · exact hp.global a hg
  · exact hp.arena a h1 h2

end VsaIris.MallocFast
