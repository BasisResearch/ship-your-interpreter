import VsaIris.Vsa.StdioErr
import VsaIris.Vsa.HeapRoom

/-!
# `errno` out of the allocator's footprint (lane N4)

`errno` (`0x8001ba08`) is one of the allocator's globals (`allocGlobal`:
`_sbrk_r` clears it), so the heap resource owns it. `exit`'s close path
writes it too (`_close_r`, `ExitH/Iris.lean`), as do the `stderr` writers.
An out-of-memory site hands the run's last heap to `exit(1)` as `errnoOwn`
alone (`isHeap_errno`): nothing allocates after it.
-/

namespace VsaIris.Stdio

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris.VsaHeap

/-- `errno` is one of `vsaLayoutP`'s globals. -/
theorem vsaLayoutP_errno : ∀ a, errnoFoot a → vsaLayoutP.global a := by
  intro a h
  unfold errnoFoot errnoAddr at h
  show allocGlobal a
  unfold allocGlobal VsaHeap.InRange
  omega

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`errno` out of a heap** whose globals hold it; the rest is dropped. -/
theorem isHeap_errno (L : DlLayout) (hL : ∀ a, errnoFoot a → L.global a) (H : List (Nat × Nat)) :
    isHeap (GF := GF) L H ⊢ errnoOwn := by
  unfold isHeap errnoOwn
  iintro ⟨%img, -, HF⟩
  ihave ⟨He, -⟩ := ownSet_split (heapFoot L H) errnoFoot _ $$ HF
  ihave He := ownSet_iff _ (T := errnoFoot)
    (fun a => ⟨fun h => h.2, fun h => ⟨.inl (hL a h), h⟩⟩) $$ He
  iapply ownSet_forget errnoFoot img $$ He

end

end VsaIris.Stdio
