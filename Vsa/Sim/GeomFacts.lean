import Vsa.Sim.Regions

open Vsa Vsa.Alloc Vsa.MemRepr

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

structure ObjGeom (obj : Region) (SL : StackLayout) (sp : Nat) : Prop where

  align8 : obj.1 % 8 = 0

  in_ram : RSub obj ramRegion

  above_tohost : tohostAddr + 16 ≤ obj.1

  stack_disjoint : obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1

theorem ObjGeom.align {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 % 8 = 0 := h.align8

theorem ObjGeom.ram_lo {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : 0x80000000 ≤ obj.1 := by
  have := h.in_ram; simp only [RSub, ramRegion, ramLo, ramHi] at this; omega

theorem ObjGeom.ram_hi {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 + obj.2 ≤ 0x100000000 := by
  have := h.in_ram; simp only [RSub, ramRegion, ramLo, ramHi] at this; omega

theorem ObjGeom.ram {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : 0x80000000 ≤ obj.1 ∧ obj.1 + obj.2 ≤ 0x100000000 :=
  ⟨h.ram_lo, h.ram_hi⟩

theorem ObjGeom.win {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : tohostAddr + 16 ≤ obj.1 := h.above_tohost

theorem ObjGeom.disj_stack {obj : Region} {SL : StackLayout} {sp : Nat}
    (h : ObjGeom obj SL sp) : obj.1 + obj.2 ≤ SL.lo ∨ sp ≤ obj.1 := h.stack_disjoint

structure GeomFacts (code : Region) (SL : StackLayout) (sp : Nat) : Prop where

  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000

  stack_win : tohostAddr + 16 ≤ SL.lo

  code_stack_disjoint : sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo

theorem GeomFacts.stackRam {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 := h.stack_ram

theorem GeomFacts.stackWin {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : tohostAddr + 16 ≤ SL.lo := h.stack_win

theorem GeomFacts.codeStk {code : Region} {SL : StackLayout} {sp : Nat}
    (h : GeomFacts code SL sp) : sp ≤ code.1 ∨ code.1 + code.2 ≤ SL.lo :=
  h.code_stack_disjoint

structure StackDisjoint (lo len : Nat) (SL : StackLayout) (sp : Nat) : Prop where

  stack_disjoint : lo + len ≤ SL.lo ∨ sp ≤ lo

theorem StackDisjoint.disj {lo len : Nat} {SL : StackLayout} {sp : Nat}
    (h : StackDisjoint lo len SL sp) : lo + len ≤ SL.lo ∨ sp ≤ lo := h.stack_disjoint

macro "geom" : tactic =>
  `(tactic|
    first
    | exact StackDisjoint.disj (by assumption)
    | exact ObjGeom.align (by assumption)
    | exact ObjGeom.win (by assumption)
    | exact ObjGeom.disj_stack (by assumption)
    | exact ObjGeom.ram_lo (by assumption)
    | exact ObjGeom.ram_hi (by assumption)
    | exact ObjGeom.ram (by assumption)
    | exact GeomFacts.stackWin (by assumption)
    | exact GeomFacts.stackRam (by assumption)
    | exact GeomFacts.codeStk (by assumption))

end Vsa.Sim
