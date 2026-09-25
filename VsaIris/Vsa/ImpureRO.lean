import VsaIris.MallocRun
import Vsa.Sim.ConsoleStream

/-!
# `_impure_ptr`, read-only

newlib's `_impure_ptr` (8 bytes at `0x8001b970`) holds `&_impure_data`
(`Vsa.Sim.consoleReent`) and no code writes it. `malloc`, `free`, the
interpreter's out-of-memory arms, `main`'s error line and `native_print` load
it, so its bytes are persistent read-only points-to (`impureRO`) shared by the
code lists (`envText`, `allocText`) and newlib's data (`Stdio.stdioAt`), which
owns every other byte of its footprint exclusively.

`roImg` (a read-only image of a byte set) lives here, below `Stdio`, so that
`stdioAt` can carry `impureRO`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode

section RO

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `S` owned read-only at the image `img`. -/
def roImg (S : Nat → Prop) (img : Nat → BitVec 8) : IProp GF :=
  iprop(□ ∀ k, ⌜S k⌝ → k ↦ₘ□ img k)

instance (S : Nat → Prop) (img : Nat → BitVec 8) : Persistent (roImg (GF := GF) S img) := by
  unfold roImg; infer_instance

/-- A read-only image restricts to a subset, at any image agreeing on it. -/
theorem roImg_restrict {S T : Nat → Prop} {f g : Nat → BitVec 8} (hS : ∀ k, T k → S k)
    (h : ∀ k, T k → f k = g k) : roImg (GF := GF) S f ⊢ roImg T g := by
  unfold roImg
  iintro #H
  imodintro
  iintro %k %hk
  rw [← h k hk]
  iapply H $$ %k %(hS k hk)

/-- The bytes of a list inside a read-only image, one by one. -/
theorem roImg_list (S : Nat → Prop) (f : Nat → BitVec 8) :
    ∀ l : List Nat, (∀ a ∈ l, S a) → roImg (GF := GF) S f ⊢ sepL l (fun a => a ↦ₘ□ f a)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | a :: l, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl []
    · unfold roImg
      iapply H $$ %a %(h a List.mem_cons_self)
    · iapply roImg_list S f l (fun b hb => h b (List.mem_cons_of_mem _ hb)) $$ H

end RO

end VsaIris.Interp

namespace VsaIris.Stdio

open Iris Iris.BI Iris.Std Iris.ProofMode
open Vsa.Sim VsaIris.Interp

/-- The 8 bytes of `_impure_ptr`. -/
def impureW (a : Nat) : Prop := 0x8001b970 ≤ a ∧ a < 0x8001b978

instance (a : Nat) : Decidable (impureW a) := by unfold impureW; infer_instance

/-- The little-endian bytes of `&_impure_data`. -/
def impureByte (a : Nat) : BitVec 8 := BitVec.ofNat 8 (consoleReent / 256 ^ (a - 0x8001b970))

/-- An image holds `&_impure_data` in `_impure_ptr`. -/
def ImpureImg (img : Nat → BitVec 8) : Prop := ∀ a, impureW a → img a = impureByte a

theorem impureImg_impureByte : ImpureImg impureByte := fun _ _ => rfl

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `_impure_ptr`, persistent read-only. -/
def impureRO : IProp GF := roImg impureW impureByte

instance : Persistent (impureRO (GF := GF)) := by unfold impureRO; infer_instance

/-- One byte of `_impure_ptr`. -/
theorem impureRO_byte {a : Nat} (h : impureW a) : impureRO (GF := GF) ⊢ a ↦ₘ□ impureByte a := by
  unfold impureRO roImg
  iintro #H
  iapply H $$ %a %h

end Own

end VsaIris.Stdio
