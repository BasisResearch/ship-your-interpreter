import Vsa.Sim.rows.AssemblySkeleton

/-!
# Fleet B1-leaves — machine-checked obstructions (hInt / hNull / hBool / hStr)

NOT a field supplier: none of the four B1 skeleton holes is provable as stated,
and three are provably FALSE.  This file is the machine-checked obstruction
record (CLAUDE.md Law 4 — return the obstruction, not a workaround).

## The class-level problem

Every `*LeafResid` (`rows/TermRouting.lean`) ∀-closes over the layout ghosts
(`g N A SL φf φc sp r sret m0` and, for null/bool/str, an UNCONSTRAINED
`c : Config`) with a bare conjunction body — the geometry conditioning the
design assigns to `TermShared.geom : ImageGeom N A SL` (`TermBundles.lean`
assembly table: every leaf "draws `TermShared.geom` (G)") is NOT in the
statement, and the TSV-named supplier `GeomFrom` does not exist in the repo
(`grep -rln GeomFrom Vsa` → only the `TermAssembly.lean` doc comment).

* **hNull/hBool/hStr — FALSE** (`skelHNull_false`/`skelHBool_false`/
  `skelHStr_false` below): each residual's sret-vs-`value_*`-code disjointness
  conjunct is asserted for ARBITRARY `sret`; any `sret` inside the code window
  refutes it outright.
* **hInt — unprovable as stated** (`skelHInt_of` below pins the gap): the body
  is `LeafWiden = Widen (EvalExit …) … (stackFoot SL)`, whose two fields
  quantify over EVERY config satisfying the bare `EvalExit`.  `EvalExit` is
  exactly the predicate that FORGETS them (its own doc comments):
  - `pres` needs `MemExtends m0 c.σ.mem`, but `EvalExit.memFrame` leaves
    presence inside `[SL.lo, sp) ∪ [A.lo, A.hi)` and the sret padding bytes
    unconstrained;
  - `surv` needs `StoreRepr` stable under arbitrary rewrites of
    `[SL.lo, SL.hi)`, but `StoreRepr.frames_arena` only places frames in `A`,
    and nothing relates `A` to `SL` for ∀-quantified ghosts (an `A` overlapping
    `[SL.lo, SL.hi)` with a nonempty store refutes it by the same construction
    as the three falsities, modulo building an `EvalExit` witness).
  `skelHInt_of` machine-checks that {`hIntPres`, `hIntSurv`} is EXACTLY the
  remaining gap: given those two named premises the hole is a record fill.

## The amendment this implies (coordinator)

Condition the leaf residuals on the entry geometry — either take
`TermShared.geom`/`ImageGeom N A SL` (+ a populated-`m0`/write-chain fact, the
`hMcallPop` analog) as premises inside each `*LeafResid`, or re-land the leaf
sims to conclude `EvalExitD` directly from their own write chains (the chain
knows `pres`/`surv`; the abstract `EvalExit` does not).

Verified with `lake env lean` only.  NO `sorry`/`axiom`/`native_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.Rows
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

namespace Vsa.Sim.FleetB1Obstructions

/-- Any config at all (the null/bool/str residuals put NO hypothesis on `c`). -/
def cAny : Config := ⟨default, 0, 0⟩

/-- The empty spec state. -/
def stEmpty : SpecSt := ⟨⟨#[], #[]⟩, ""⟩

/-- **`SkelHNull` is FALSE.**  `NullLeafResid`'s first conjunct asserts the
sret buffer misses the `value_null` code window `[0x800027ec, 0x800027f8)` for
ARBITRARY `sret`; `sret := 0x800027f0` sits inside it (both disjuncts fail). -/
theorem skelHNull_false (L : Layout) : ¬ Vsa.Sim.TermAssembly.Skel.SkelHNull L := by
  intro h
  obtain ⟨h1, -⟩ := h stEmpty (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (fun _ => 0) (fun _ => 0) 0 0 (0x800027f0#64) ∅ cAny
  exact absurd h1 (by decide)

/-- **`SkelHBool` is FALSE.**  Same shape at the `value_bool` code window
`[0x800027f8, 0x8000280c)`; `sret := 0x80002800` refutes it. -/
theorem skelHBool_false (L : Layout) : ¬ Vsa.Sim.TermAssembly.Skel.SkelHBool L := by
  intro h
  obtain ⟨h1, -⟩ := h stEmpty false (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (fun _ => 0) (fun _ => 0) 0 0 (0x80002800#64) ∅ cAny
  exact absurd h1 (by decide)

/-- **`SkelHStr` is FALSE.**  `StrLeafResid`'s third conjunct is the same
unconditional shape at the `value_str` code window `[0x8000281c, 0x8000282c)`;
`sret := 0x80002820` refutes it. -/
theorem skelHStr_false (L : Layout) : ¬ Vsa.Sim.TermAssembly.Skel.SkelHStr L := by
  intro h
  obtain ⟨-, -, h3, -⟩ := h stEmpty "" (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (fun _ => 0) (fun _ => 0) 0 0 (0x80002820#64) 0 ∅ cAny
  exact absurd h3 (by decide)

/-! ## hInt — the gap pinned as two named premises

`SkelHInt` has no unconditional geometry conjunct (its body is the bare
`LeafWiden` widener), so it is not refutable this cheaply — refutation needs an
explicit `EvalExit`-satisfying config at an adversarial layout.  Instead,
`skelHInt_of` machine-checks the REDUCTION: the hole is exactly the two facts
`EvalExit` forgets, as named typed premises.  Neither is derivable from
`EvalExit` for ∀-quantified ghosts (see the file doc); both belong to the
absent `GeomFrom`/`TermShared.geom`-conditioned supplier layer. -/

/-- The presence half of the int-leaf gap: `EvalExit` does not carry
`MemExtends` (its `memFrame` leaves `[SL.lo, sp) ∪ A` ∪ sret-padding presence
unconstrained).  Supplied only by the leaf's actual writeMap chain — i.e. by
re-landing `evalIntSim` at `EvalExitD`, not from `EvalExit` post hoc. -/
def IntLeafPres : Prop :=
  ∀ (st : SpecSt) (n : Int) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st (.int n) sp r sret m0 c →
    Vsa.Sim.MemExtends m0 c.σ.mem

/-- The survival half of the int-leaf gap: `StoreRepr` stability under
arbitrary rewrites of `[SL.lo, SL.hi)`.  Needs `A`/`SL` disjointness
(`ImageGeom`-class, absent from the ∀-ghost statement). -/
def IntLeafSurv : Prop :=
  ∀ (st : SpecSt) (n : Int) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st (.int n) sp r sret m0 c →
    ∃ φf' φc' : Addr → Nat,
      Vsa.Sim.PhiExtends φf φf' st.store.frames.size ∧
      Vsa.Sim.PhiExtends φc φc' st.store.closures.size ∧
      ∀ m' : Mem, (∀ k : Nat, ¬ Vsa.Sim.stackFoot SL k → c.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf' φc' st.store

/-- **The reduction**: `{IntLeafPres, IntLeafSurv}` is EXACTLY what `SkelHInt`
still needs — given the two named premises, the hole is a `Widen` record fill.
This machine-checks that no further marshalling is missing. -/
theorem skelHInt_of (hPres : IntLeafPres) (hSurv : IntLeafSurv)
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHInt L := by
  intro st n g N A SL φf φc sp r sret m0
  exact { pres := hPres st n g N A SL φf φc sp r sret m0
          surv := hSurv st n g N A SL φf φc sp r sret m0 }

end Vsa.Sim.FleetB1Obstructions

#print axioms Vsa.Sim.FleetB1Obstructions.skelHNull_false
#print axioms Vsa.Sim.FleetB1Obstructions.skelHBool_false
#print axioms Vsa.Sim.FleetB1Obstructions.skelHStr_false
#print axioms Vsa.Sim.FleetB1Obstructions.skelHInt_of
