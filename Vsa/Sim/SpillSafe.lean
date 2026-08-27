import Vsa.Sim.EvalSimCommon

/-!
# `SpillSafe` — reusable spill-slot memory-safety obligations (omega paid ONCE)

The hand-threaded `Eval*` row proofs discharge, at EVERY spill load/store site, the four
memory-access preconditions of the `site_*_ee` step lemmas — `hlo`/`hhiram`/`hhtif`/`halign` —
each via a fresh `(by rw [haddrK]; omega)`. Across the cohort that is ~900 `omega` invocations,
each paying omega's fixed per-call setup cost regardless of the goal's triviality — the dominant
elaboration cost of the whole tree (measured: `rows/EvalGtRow.lean` = 226s, ~130 omega). See
`experiments/elab-wall-strategy.md` and `memory/elab-wall-diagnosis.md`.

Every such obligation is the SAME fact: for a spill address `sp.toNat - K` with `K ≤ 1088` and the
standard stack-frame bounds, the four preconditions hold. Prove it ONCE here (omega compiled into
these lemmas' oleans); each call site then just APPLIES the lemma (typecheck only, no omega re-run):

    obtain ⟨hlo, hhi, hhtif, halign⟩ := spill_load_safe4 sp v2 SL imm K haddrK
      hSLlo hSLloSp hsphiRam hsp8 hSLwin (by decide) (by decide) (by decide)

The `(by decide)` args prove the GROUND facts `8 ≤ K`, `K ≤ 1088`, `K % 4 = 0` (fast kernel
`Nat.ble`/`Nat.decEq`, ~ms — not omega). Conclusions are stated in the `(v2 + sign_extend imm).toNat`
form so they match the `site_*_ee` argument types verbatim (`exact`-compatible).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Alloc

namespace Vsa.Sim

/-- The four preconditions of a 4-byte spill LOAD (`lw`) at address `sp.toNat - K`, derived once
from the frame bounds + the ground offset facts. Stated over `(v2 + sign_extend imm).toNat` (via
`haddr`) so the conjuncts match `site_*_ee`'s `hlo`/`hhiram`/`hhtif`/`halign` arguments verbatim. -/
theorem spill_load_safe4 (sp v2 : BitVec 64) (SL : StackLayout) (imm : BitVec 12) (K : Nat)
    (haddr : (v2 + sign_extend (m := 64) imm).toNat = sp.toNat - K)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLloSp : SL.lo + 1088 ≤ sp.toNat)
    (hsphiRam : sp.toNat ≤ 0x100000000) (hsp8 : sp.toNat % 8 = 0)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hK8 : 8 ≤ K) (hK1088 : K ≤ 1088) (hK4 : K % 4 = 0) :
    0x80000000 ≤ (v2 + sign_extend (m := 64) imm).toNat ∧
    (v2 + sign_extend (m := 64) imm).toNat + 4 ≤ 0x100000000 ∧
    ((v2 + sign_extend (m := 64) imm).toNat + 4 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) imm).toNat) ∧
    (v2 + sign_extend (m := 64) imm).toNat % 4 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  rw [haddr]
  refine ⟨by omega, by omega, Or.inr (by omega), by omega⟩

/-- The four preconditions of an 8-byte spill LOAD/STORE (`ld`/`sd`) at address `sp.toNat - K`.
Same as `spill_load_safe4` but with the 8-byte span (`+8`) and 8-byte alignment (`% 8`). -/
theorem spill_load_safe8 (sp v2 : BitVec 64) (SL : StackLayout) (imm : BitVec 12) (K : Nat)
    (haddr : (v2 + sign_extend (m := 64) imm).toNat = sp.toNat - K)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLloSp : SL.lo + 1088 ≤ sp.toNat)
    (hsphiRam : sp.toNat ≤ 0x100000000) (hsp8 : sp.toNat % 8 = 0)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hK8 : 8 ≤ K) (hK1088 : K ≤ 1088) (hK8div : K % 8 = 0) :
    0x80000000 ≤ (v2 + sign_extend (m := 64) imm).toNat ∧
    (v2 + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000 ∧
    ((v2 + sign_extend (m := 64) imm).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) imm).toNat) ∧
    (v2 + sign_extend (m := 64) imm).toNat % 8 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  rw [haddr]
  refine ⟨by omega, by omega, Or.inr (by omega), by omega⟩

/-- Byte re-indexing across an 8-byte-shifted spill slot: the `i`-th byte of the slot at
`sp.toNat - K` coincides with the `i`-th byte of the slot at `sp.toNat - (K+8)` offset by 8.
Discharges the `show sp.toNat - K + i = sp.toNat - (K+8) + 8 + i from by omega` re-indexers. -/
theorem spill_shift8 (sp : BitVec 64) (K i : Nat) (hsp : 1088 ≤ sp.toNat) (hK : K + 8 ≤ 1088) :
    sp.toNat - K + i = sp.toNat - (K + 8) + 8 + i := by
  omega

end Vsa.Sim
