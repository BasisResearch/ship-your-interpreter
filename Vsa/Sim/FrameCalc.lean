import Vsa.Sim.SegEvalSound
import Vsa.Sim.KeepRegs
import Vsa.Sim.ReprCopy
import Vsa.Sim.SlotFrame

/-!
# `FrameCalc` — canonical marshalling and frame calculus

A frame calculation records one write log, its concrete memory equation, and
the proof that every write lies in an allowed window. Calculations compose by
log append. Their concrete seam is therefore `writeLog_append`, never reduction
of `ExtHashMap`.

Timing witness (2026-08-26): `lake build Vsa.Sim.FrameCalc` completed the
touched target in 2.6s.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

namespace Vsa.Sim

theorem insideW_append_left {ws1 ws2 : List W} {A n : Nat}
    (h : InsideW ws1 A n) : InsideW (ws1 ++ ws2) A n := by
  induction ws1 with
  | nil => exact False.elim h
  | cons w ws ih =>
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)

theorem insideW_append_right {ws1 ws2 : List W} {A n : Nat}
    (h : InsideW ws2 A n) : InsideW (ws1 ++ ws2) A n := by
  induction ws1 with
  | nil => exact h
  | cons _ ws ih => exact Or.inr ih

theorem logInW_mono {ws ws' : List W} {log : List WEntry}
    (hsub : ∀ A n, InsideW ws A n → InsideW ws' A n)
    (h : LogInW ws log) : LogInW ws' log := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨hsub e.1 e.2.1 h.1, ih h.2⟩

theorem logInW_append {ws1 ws2 : List W} {l1 l2 : List WEntry}
    (h1 : LogInW ws1 l1) (h2 : LogInW ws2 l2) :
    LogInW (ws1 ++ ws2) (l1 ++ l2) := by
  induction l1 with
  | nil => exact logInW_mono (fun _ _ => insideW_append_right) h2
  | cons e l ih =>
      exact ⟨insideW_append_left h1.1, ih h1.2⟩

/-- A canonical memory-frame calculation. -/
structure FrameCalc (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) where
  log : List WEntry
  mem_eq : m = writeLog m0 log
  writes_inside : LogInW ws log

namespace FrameCalc

/-- The empty calculation. -/
def refl (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8)) : FrameCalc ws m m :=
  ⟨[], rfl, trivial⟩

/-- Introduce a calculation from a concrete canonical log. -/
def of_writeLog (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (h : LogInW ws log) : FrameCalc ws m (writeLog m log) :=
  ⟨log, rfl, h⟩

/-- Compose calculations. The output log is syntactically `l1 ++ l2`. -/
def trans {ws1 ws2 : List W} {m0 m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h1 : FrameCalc ws1 m0 m1) (h2 : FrameCalc ws2 m1 m2) :
    FrameCalc (ws1 ++ ws2) m0 m2 := by
  cases h1 with
  | mk l1 heq1 hin1 =>
      cases h2 with
      | mk l2 heq2 hin2 =>
          refine ⟨l1 ++ l2, ?_, logInW_append hin1 hin2⟩
          calc
            m2 = writeLog m1 l2 := heq2
            _ = writeLog (writeLog m0 l1) l2 := congrArg (fun x => writeLog x l2) heq1
            _ = writeLog m0 (l1 ++ l2) := (writeLog_append m0 l1 l2).symm

/-- Forget the log and expose the ordinary `FrameOn` interface. -/
theorem frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameCalc ws m0 m) : FrameOn ws m0 m := by
  rw [h.mem_eq]
  exact frameOn_writeLog ws m0 h.log h.writes_inside

theorem pin8 {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {A : Nat} {v : BitVec 64} (h : FrameCalc ws m0 m)
    (hout : OutWRange ws A 8) (hp : Pin8 m0 A v) : Pin8 m A v :=
  pin8_of_frameOn h.frameOn hout hp

theorem pin4 {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {A : Nat} {v : BitVec 32} (h : FrameCalc ws m0 m)
    (hout : OutWRange ws A 4) (hp : Pin4 m0 A v) : Pin4 m A v :=
  pin4_of_frameOn h.frameOn hout hp

theorem slot {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameCalc ws m0 m) (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (hA : (base + Functions.sign_extend (m := 64)
      (BitVec.ofNat 12 off)).toNat = A)
    (hout : OutWRange ws A 8) (hs : SlotHolds base off v m0) :
    SlotHolds base off v m :=
  slotHolds_of_frameOn base off v A hA h.frameOn hout hs

/-- Copy a `ValueRepr` into the sole write window of a frame calculation. -/
theorem valueRepr_copy {m m' : Mem} {N : NativeAddrs} {phiC : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (h : FrameCalc [{ lo := dstAddr, hi := dstAddr + 24 }] m m')
    (hcopy : ∀ j, j < 24 → m'[dstAddr + j]? = m[srcAddr + j]?)
    (hdisj : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < dstAddr ∨ dstAddr + 24 ≤ p + k))
    (hv : ValueRepr m N phiC srcAddr v) : ValueRepr m' N phiC dstAddr v := by
  apply valueRepr_copy_of_writeWindow hcopy _ hdisj hv
  intro a ha
  exact h.frameOn a ⟨ha, trivial⟩

end FrameCalc

/-- Standard marshalling outputs grouped for O(1) projection. -/
structure MarshalFacts (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8))
    (sigma0 sigma : MState) (pins : List Pin) (kept : List Register) where
  memory : FrameCalc ws m0 m
  pin_values : PinsHold sigma pins
  kept_regs : KeepRegs kept sigma0 sigma

theorem MarshalFacts.frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {sigma0 sigma : MState} {pins : List Pin} {kept : List Register}
    (h : MarshalFacts ws m0 m sigma0 sigma pins kept) : FrameOn ws m0 m :=
  h.memory.frameOn

/-- Projection-only marshalling tactic. It performs no simplification or search. -/
macro "marshal" : tactic =>
  `(tactic|
    first
    | exact MarshalFacts.frameOn (by assumption)
    | exact MarshalFacts.pin_values (by assumption)
    | exact MarshalFacts.kept_regs (by assumption)
    | exact FrameCalc.frameOn (by assumption))

section Sanity

example (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8))
    (sigma0 sigma : MState) (pins : List Pin) (kept : List Register)
    (h : MarshalFacts ws m0 m sigma0 sigma pins kept) : FrameOn ws m0 m := by
  marshal

end Sanity

#print axioms FrameCalc.trans
#print axioms FrameCalc.frameOn
#print axioms FrameCalc.valueRepr_copy
#print axioms MarshalFacts.frameOn

end Vsa.Sim
