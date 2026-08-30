import Vsa.Sim.StackSlotGeom
import Vsa.Sim.rows.EvalAddRow

/-!
# Shared term-image geometry

`ImageGeom` is deliberately a layout hypothesis, not a theorem from arbitrary
`NativeAddrs`/`Arena` values.  The current rows contain site-dependent facts
about `sp`, result buffers, AST pointers, and memories; those cannot be derived
from the three layout parameters alone.  This record therefore contains only
the static stack-facing facts already present in the add-row residual.

The `N` and `A` parameters are retained as context for the eventual shared
term bundle.  No claim about either is made here.  Site-dependent facts remain
explicit in the case residuals.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable
open Vsa Vsa.Alloc Vsa.MemRepr

namespace Vsa.Sim

/-! Static facts common to the current EvalE rows. -/
structure ImageGeom (N : Vsa.RuntimeRepr.NativeAddrs) (A : Vsa.RuntimeRepr.Arena)
    (SL : StackLayout) : Prop where
  /-- The stack layout lies in RAM. -/
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  /-- The stack lies above the HTIF window. -/
  stack_win : tohostAddr + 16 ≤ SL.lo

theorem ImageGeom.stackRam {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena}
    {SL : StackLayout}
    (h : ImageGeom N A SL) :
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 := h.stack_ram

theorem ImageGeom.stackWin {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena}
    {SL : StackLayout}
    (h : ImageGeom N A SL) : tohostAddr + 16 ≤ SL.lo := h.stack_win

/-! Dynamic frame facts complete the reusable `StackBounds` carrier. -/
theorem ImageGeom.stackBounds {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena}
    {SL : StackLayout}
    (h : ImageGeom N A SL) (sp : BitVec 64)
    (hSLloSp : SL.lo + 1088 ≤ sp.toNat)
    (hsp8 : sp.toNat % 8 = 0)
    (hsphiRam : sp.toNat ≤ 0x100000000) :
    StackBounds sp SL :=
  ⟨hSLloSp, h.stack_ram.1, h.stack_win, hsp8, hsphiRam⟩

/-! Exact compatibility with the concrete add-row residual. -/
theorem imageGeom_of_addResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : AddResid gpre N A SL sp r sret aExpr Wl c') :
    ImageGeom N A SL :=
  ⟨⟨h.SLlo, h.SLhiRam⟩, h.SLwin⟩

theorem addResid_stackBounds
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {c' : Vsa.Machine.Config}
    (h : AddResid gpre N A SL sp r sret aExpr Wl c') :
    StackBounds sp SL :=
  (imageGeom_of_addResid h).stackBounds sp h.SLloSp h.sp8 h.sphiRam

/-! `#print axioms` should contain only the standard Lean axioms. -/
#print axioms ImageGeom.stackBounds
#print axioms imageGeom_of_addResid
#print axioms addResid_stackBounds

end Vsa.Sim
