import Vsa.Sim.SegEvalSound

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

structure FrameCalc (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) where
  log : List WEntry
  mem_eq : m = writeLog m0 log
  writes_inside : LogInW ws log

namespace FrameCalc

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

theorem frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameCalc ws m0 m) : FrameOn ws m0 m := by
  rw [h.mem_eq]
  exact frameOn_writeLog ws m0 h.log h.writes_inside

end FrameCalc

structure MarshalFacts (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8))
    (sigma0 sigma : MState) (pins : List Pin) (kept : List Register) where
  memory : FrameCalc ws m0 m
  pin_values : PinsHold sigma pins
  kept_regs : KeepRegs kept sigma0 sigma

theorem MarshalFacts.frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {sigma0 sigma : MState} {pins : List Pin} {kept : List Register}
    (h : MarshalFacts ws m0 m sigma0 sigma pins kept) : FrameOn ws m0 m :=
  h.memory.frameOn

end Vsa.Sim
