import Vsa.Sim.Code.FixedImage
import Vsa.MemRepr
import Vsa.Alloc

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.Sim.Code

def StaticImageByte (k : Nat) : Prop := 0x80000000 ≤ k ∧ k < 0x8001acf0

structure StaticImageSupport (m : Mem) (SL : StackLayout) (A : Arena) : Prop where
  text : FixedTextLoaded m
  rodata : FixedRodataLoaded m
  stack : SL.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ SL.lo
  arena : A.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ A.lo

theorem StaticImageSupport.transport {m m' : Mem} {SL : StackLayout} {A : Arena}
    (h : StaticImageSupport m SL A)
    (hag : ∀ k, StaticImageByte k → m'[k]? = m[k]?) :
    StaticImageSupport m' SL A where
  text := h.text.transport (fun k hlo hhi => hag k ⟨hlo, by omega⟩)
  rodata := h.rodata.transport (fun k hlo hhi => hag k ⟨by omega, hhi⟩)
  stack := h.stack
  arena := h.arena

theorem StaticImageSupport.stack_disjoint {m : Mem} {SL : StackLayout} {A : Arena}
    (h : StaticImageSupport m SL A) {lo hi : Nat}
    (hlo : 0x80000000 ≤ lo) (hhi : hi ≤ 0x8001acf0) :
    SL.hi ≤ lo ∨ hi ≤ SL.lo :=
  h.stack.imp (fun hs => by omega) (fun hs => by omega)

theorem StaticImageSupport.arena_disjoint {m : Mem} {SL : StackLayout} {A : Arena}
    (h : StaticImageSupport m SL A) {lo hi : Nat}
    (hlo : 0x80000000 ≤ lo) (hhi : hi ≤ 0x8001acf0) :
    A.hi ≤ lo ∨ hi ≤ A.lo :=
  h.arena.imp (fun ha => by omega) (fun ha => by omega)

theorem StaticImageSupport.outsideStack {m : Mem} {SL : StackLayout} {A : Arena}
    (h : StaticImageSupport m SL A) {k : Nat} (hk : StaticImageByte k) :
    ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
  intro hs
  rcases h.stack with hd | hd <;> obtain ⟨_, _⟩ := hk <;> omega

end Vsa.Sim
