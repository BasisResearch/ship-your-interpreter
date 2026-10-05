import Vsa.Compiler.ExprSim
import Vsa.Compiler.Fail

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

structure Obs where
  pc : BitVec 64
  ea : Option Nat
  lib : Option (BitVec 64 × BitVec 64)
  deriving DecidableEq

def isLibT (t : Nat) : Prop := t = mulPC ∨ t = divPC ∨ t = modPC

instance (t : Nat) : Decidable (isLibT t) := by unfold isLibT; infer_instance

def insObs (i : Ins) (A : AM) : Obs :=
  match i with
  | .ld _ rs => ⟨A.pc, some (srcVal rs A.regs).toNat, none⟩
  | .sd _ rs => ⟨A.pc, some (srcVal rs A.regs).toNat, none⟩
  | .jal rd off =>
    if rd = 1 ∧ isLibT (A.pc + sign_extend (m := 64) (evenJ off)).toNat then
      ⟨A.pc, none, some (srcVal 10 A.regs, srcVal 11 A.regs)⟩
    else ⟨A.pc, none, none⟩
  | _ => ⟨A.pc, none, none⟩

def obsOf (code : List Ins) (A : AM) : Obs :=
  match fetch code A.pc with
  | some i => insObs i A
  | none => ⟨A.pc, none, none⟩

inductive StarT (code : List Ins) : List Obs → AM → AM → Prop where
  | refl (A : AM) : StarT code [] A A
  | step {A B C : AM} {τ : List Obs} : astep code A = some (.run B) → StarT code τ B C →
      StarT code (obsOf code A :: τ) A C

abbrev ReachesT (code : List Ins) (A : AM) (τ : List Obs) (P : AM → Prop) : Prop :=
  ∃ B, StarT code τ A B ∧ P B

def pobs (k : Nat) : Obs := ⟨pcOf k, none, none⟩
def mobs (k a : Nat) : Obs := ⟨pcOf k, some a, none⟩
def lobs (k : Nat) (x y : BitVec 64) : Obs := ⟨pcOf k, none, some (x, y)⟩

def lin (k : Nat) : Nat → List Obs
  | 0 => []
  | n + 1 => pobs k :: lin (k + 1) n

section
variable {code : List Ins}

theorem StarT.trans {τ1 τ2 : List Obs} {A B C : AM} (h1 : StarT code τ1 A B) (h2 : StarT code τ2 B C) :
    StarT code (τ1 ++ τ2) A C := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact .step e (ih h2)

theorem StarT.toN {τ : List Obs} {A B : AM} (h : StarT code τ A B) : StarN code τ.length A B := by
  induction h with
  | refl A => exact .refl A
  | step e _ ih => exact .step e ih

theorem StarT.toStar {τ : List Obs} {A B : AM} (h : StarT code τ A B) : Star code A B :=
  ⟨_, h.toN⟩

theorem obsOf_at (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i) {A : AM}
    (hA : A.pc = pcOf k) : obsOf code A = insObs i A := by
  unfold obsOf; rw [hA, fetch_pcOf hfit hk]

def Ins.Plain : Ins → Prop
  | .ld .. | .sd .. | .jal .. => False
  | _ => True

theorem insObs_plain {i : Ins} (hi : i.Plain) (A : AM) : insObs i A = ⟨A.pc, none, none⟩ := by
  cases i <;> first | rfl | exact hi.elim

theorem stepP (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i) (hi : i.Plain)
    {A B C : AM} {τ : List Obs} (hA : A.pc = pcOf k) (e : astep code A = some (.run B))
    (r : StarT code τ B C) : StarT code (pobs k :: τ) A C := by
  have := StarT.step e r
  rwa [obsOf_at hfit hk hA, insObs_plain hi, hA] at this

theorem stepM (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i)
    {A B C : AM} {τ : List Obs} (hA : A.pc = pcOf k) (e : astep code A = some (.run B))
    (r : StarT code τ B C) : StarT code (insObs i A :: τ) A C := by
  have := StarT.step e r
  rwa [obsOf_at hfit hk hA] at this

theorem singleP (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i) (hi : i.Plain)
    {A B : AM} (hA : A.pc = pcOf k) (e : astep code A = some (.run B)) : StarT code [pobs k] A B :=
  stepP hfit hk hi hA e (.refl B)

theorem exT_step (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i) (hi : i.Plain)
    {A S : AM} {τ : List Obs} {Q : AM → Prop} (hA : A.pc = pcOf k) (e : astep code A = some (.run S))
    (h : ReachesT code S τ Q) : ReachesT code A (pobs k :: τ) Q := by
  obtain ⟨B, hs, hq⟩ := h; exact ⟨B, stepP hfit hk hi hA e hs, hq⟩

theorem exT_trans {A S : AM} {τ1 τ2 : List Obs} {Q : AM → Prop} (e : StarT code τ1 A S)
    (h : ReachesT code S τ2 Q) : ReachesT code A (τ1 ++ τ2) Q := by
  obtain ⟨B, hs, hq⟩ := h; exact ⟨B, e.trans hs, hq⟩

theorem lin_add (k a b : Nat) : lin k (a + b) = lin k a ++ lin (k + a) b := by
  induction a generalizing k with
  | zero => simp [lin]
  | succ a ih => simp only [Nat.add_right_comm a 1 b, lin, ih, List.cons_append]; congr 3; omega

theorem lin_one (k : Nat) : lin k 1 = [pobs k] := rfl

end

end Vsa.Compiler
