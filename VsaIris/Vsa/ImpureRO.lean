import VsaIris.MallocRun
import Vsa.Sim.ConsoleStream

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode

section RO

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def roImg (S : Nat → Prop) (img : Nat → BitVec 8) : IProp GF :=
  iprop(□ ∀ k, ⌜S k⌝ → k ↦ₘ□ img k)

instance (S : Nat → Prop) (img : Nat → BitVec 8) : Persistent (roImg (GF := GF) S img) := by
  unfold roImg; infer_instance

theorem roImg_restrict {S T : Nat → Prop} {f g : Nat → BitVec 8} (hS : ∀ k, T k → S k)
    (h : ∀ k, T k → f k = g k) : roImg (GF := GF) S f ⊢ roImg T g := by
  unfold roImg
  iintro #H
  imodintro
  iintro %k %hk
  rw [← h k hk]
  iapply H $$ %k %(hS k hk)

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

def impureW (a : Nat) : Prop := 0x8001b970 ≤ a ∧ a < 0x8001b978

instance (a : Nat) : Decidable (impureW a) := by unfold impureW; infer_instance

def impureByte (a : Nat) : BitVec 8 := BitVec.ofNat 8 (consoleReent / 256 ^ (a - 0x8001b970))

def ImpureImg (img : Nat → BitVec 8) : Prop := ∀ a, impureW a → img a = impureByte a

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def impureRO : IProp GF := roImg impureW impureByte

instance : Persistent (impureRO (GF := GF)) := by unfold impureRO; infer_instance

theorem impureRO_byte {a : Nat} (h : impureW a) : impureRO (GF := GF) ⊢ a ↦ₘ□ impureByte a := by
  unfold impureRO roImg
  iintro #H
  iapply H $$ %a %h

end Own

end VsaIris.Stdio
