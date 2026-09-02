import Vsa.Sim.rows.AssemblySkeleton

/-!
# Wave 47d — the `EvalExitD` re-seat VERDICT (machine-checked, blocked)

Task: re-seat the four leaf sims at `EvalExitD` per the B1 re-attempt worker's
proposal (a) ("the sims already prove the pres/surv facts internally —
`EvalIntSim2.lean:835-844`") and discharge `SkelH{Int,Null,Bool,Str}`.

## The sharpened finding: proposal (a) is INSUFFICIENT on its own

The internally-proven survival witness has the WRONG FOOTPRINT:

* `EvalIntSim2.lean:836-859` (`hagree6`/`hstoreSurv6`) proves survival at
  footprint `[SL.lo, sp) ∪ [sret, sret+24)` — it is the entry's
  `EvalEntry.store_survives` transported through the four spill writes.
* The motive (`mEvalE = EvalIH`, `EvalRecCommon.lean`) demands `EvalExitD`,
  whose survival clause is fixed at `stackFoot SL = [SL.lo, SL.hi)` — and MUST
  be (the recursive caller's post-sub-call writes land in `[sub_sp, sp) ⊄
  [SL.lo, sub_sp)`, so the IH consumers need the full stack region).
* The caller strip `[sp.toNat, SL.hi)` is covered by NO hypothesis, entry or
  internal: `EvalEntry.store_survives`'s footprint stops at `sp`, and
  `StoreRepr` pins only frames/closures to the arena
  (`RuntimeRepr.lean` `frames_arena`/`closures_arena`) — the binding-name
  strings (`CString` targets) and `fn_expr` AST nodes are NOT region-pinned,
  so no arena/stack-disjointness route exists either.

So surfacing the internal facts through the block interfaces closes `pres`
(and the arena-drift half of `surv`) but CANNOT close the caller-strip half of
`surv`.  The minimal amendment is the first half of the worker's proposal (b):

**widen `EvalEntry.store_survives`'s footprint from `[SL.lo, sp)` to
`[SL.lo, SL.hi)`** (keeping the sret window), with the matching
`ExecEntry.store_survives` (`ExecEntry.lean:267`) widening (the exec→eval
bridges construct `EvalEntry` from `ExecEntry`).  Measured fan-out on main @
eb2a139: `store_survives :=` at 15 construction sites across 13 files;
43 `.store_survives` use sites; use sites weaken (wide ⇒ narrow via one mono
lemma), construction sites must supply the wider fact — a wave-scale
amendment (ITEM-ZERO shape), NOT a bounded-task edit.

## What this file proves

The re-seat route is EXACTLY two named premises away — given them, all four
holes are record fills (machine-checked below, so the amendment + re-land land
the fields with no third gap):

* `EntryStackSurv e` — the entry-conditioned WIDENED store survival (footprint
  `[SL.lo, SL.hi) ∪ sret-window`).  Honest supplier: the
  `EvalEntry.store_survives` footprint amendment above.  NOTHING on main
  supplies it today (the fleet's refutation round + re-attempt pinned this).
* `LeafExitPin e v` — the leaf exit memory pinned to its write chain:
  `MemExtends m0` + agreement with `m0` outside `[SL.lo, sp) ∪ sret-window`,
  for every `EvalExit` config under the entry.  Honest supplier: the block
  re-land — thread the two conjuncts through `ArmEntryK`/`PreEpilogueV`
  (`blockD_v`'s `Q : Mem → Prop` parameter, `EvalSimCommon.lean:297+`, already
  transports any memory predicate across the epilogue for free).  In this
  ∀-over-`EvalExit` form it is only suppliable by restating the leaf residual
  at `EvalExitD` inside the sims (the `LeafEntryGap` finding,
  `B1_leaves_reattempt.lean`); stated here to machine-check JOINT SUFFICIENCY.

Null/bool/str additionally need the callee geometry (`{Null,Bool,Str}Geom`,
verbatim the `{Null,Bool,Str}GeomOfEntry` of `B1_leaves_reattempt.lean` —
restated because obstruction files are not importable modules); that gap is
independent (`evalentry-missing-nbs-callee-geom`) and unchanged by this
verdict.

Companion observation: `observations.md` `2026-09-02
leaf-reseat-blocked-on-entry-footprint`.  Verified with `lake env lean` only.
NO `sorry`/`axiom`/`native_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.Rows
open Vsa.Sim.TermSimAssembly
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

namespace Vsa.Sim.FleetB1ReseatVerdict

/-- **The mandatory entry amendment, as ONE typed premise**: under `EvalEntry`,
the represented store survives memory changes confined to the FULL stack
region `[SL.lo, SL.hi)` ∪ the sret window — i.e. `EvalEntry.store_survives`
with its footprint widened from `sp` to `SL.hi`.  The caller strip
`[sp, SL.hi)` is what no current hypothesis covers. -/
def EntryStackSurv (e : Expr) : Prop :=
  ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c →
    ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → m0[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store

/-- **The block-interface re-land, as ONE typed premise**: the leaf's exit
memory is its write chain over `m0` — presence-extended, and equal to `m0`
outside `[SL.lo, sp) ∪ sret-window` (the four spills + the `value_*` sret
write; no arena drift).  The sims prove BOTH facts internally
(`EvalIntSim2.lean:836-859` + the `writeMap8` chain) but drop them at the
`ArmEntryK`/`PreEpilogueV` interfaces; `blockD_v`'s `Q` parameter carries them
to the exit for free once threaded. -/
def LeafExitPin (e : Expr) (v : Value) : Prop :=
  ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c →
    ∀ c' : Config,
      Vsa.Sim.EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st v sp r sret m0 c' →
      Vsa.Sim.MemExtends m0 c'.σ.mem ∧
      ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → c'.σ.mem[k]? = m0[k]?

/-- **Joint sufficiency**: the two premises give the leaf widener — a record
fill.  `pres` is the pin's first half; `surv` chains the pin's `m0`-agreement
(the caller strip `[sp, SL.hi)` is untouched by the leaf, so exit mem = `m0`
there) into the WIDENED entry survival, at the identity φ-pair. -/
theorem leafWiden_of_pins {e : Expr} {v : Value}
    (hS : EntryStackSurv e) (hP : LeafExitPin e v)
    (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config)
    (hc : Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c) :
    Vsa.Sim.LeafWiden g N A SL φf φc st v sp r sret m0 := by
  have hsphi : sp.toNat ≤ SL.hi := hc.stackOK.2.1
  refine
    { pres := fun c' hx =>
        (hP st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc c' hx).1
      surv := fun c' hx =>
        ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, fun m' hm' =>
          hS st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc m'
            (fun k hkstack hkr => ?_)⟩ }
  have hknotsp : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun h =>
    hkstack ⟨h.1, Nat.lt_of_lt_of_le h.2 hsphi⟩
  exact ((hP st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc c' hx).2
      k hknotsp hkr).symm.trans (hm' k hkstack)

/-- **hInt discharges** from the two premises alone (no geometry gap for the
int pilot). -/
theorem skelHInt_of_pins
    (hS : ∀ n : Int, EntryStackSurv (.int n))
    (hP : ∀ n : Int, LeafExitPin (.int n) (.int n))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHInt L := by
  intro st n g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact leafWiden_of_pins (hS n) (hP n) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc

/-- The `EvalNullEntry`-minus-`EvalEntry` callee geometry (independent gap,
`evalentry-missing-nbs-callee-geom`; verbatim `NullGeomOfEntry` of
`B1_leaves_reattempt.lean`). -/
def NullGeom : Prop :=
  ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env .null sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat) ∧
    ((0x800027f8 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
    Value_nullLoaded c.σ.mem ∧
    Vsa.Sim.NullSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 12)

/-- **hNull discharges** from the two premises + the geometry. -/
theorem skelHNull_of_pins (hG : NullGeom)
    (hS : EntryStackSurv .null) (hP : LeafExitPin .null .null)
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHNull L := by
  intro st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5,
    leafWiden_of_pins hS hP st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

/-- The `EvalBoolEntry`-minus-`EvalEntry` callee geometry. -/
def BoolGeom : Prop :=
  ∀ (st : SpecSt) (b : Bool) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.bool b) sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
    ((0x8000280c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027f8) ∧
    Value_boolLoaded c.σ.mem ∧
    Vsa.Sim.BoolSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 8)

/-- **hBool discharges** from the two premises + the geometry. -/
theorem skelHBool_of_pins (hG : BoolGeom)
    (hS : ∀ b : Bool, EntryStackSurv (.bool b))
    (hP : ∀ b : Bool, LeafExitPin (.bool b) (.bool b))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHBool L := by
  intro st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5,
    leafWiden_of_pins (hS b) (hP b) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

/-- The `EvalStrEntry`-minus-`EvalEntry` callee geometry + payload-string
region facts. -/
def StrGeom : Prop :=
  ∀ (st : SpecSt) (s : String) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c →
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + s.length < SL.lo ∨ sp.toNat ≤ p) ∧
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat)) ∧
    (sret.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ sret.toNat) ∧
    ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000281c) ∧
    Value_strLoaded c.σ.mem ∧
    Vsa.Sim.StrSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 8 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 4)

/-- **hStr discharges** from the two premises + the geometry. -/
theorem skelHStr_of_pins (hG : StrGeom)
    (hS : ∀ s : String, EntryStackSurv (.str s))
    (hP : ∀ s : String, LeafExitPin (.str s) (.str s))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHStr L := by
  intro st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    hG st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    leafWiden_of_pins (hS s) (hP s) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

end Vsa.Sim.FleetB1ReseatVerdict

#print axioms Vsa.Sim.FleetB1ReseatVerdict.leafWiden_of_pins
#print axioms Vsa.Sim.FleetB1ReseatVerdict.skelHInt_of_pins
#print axioms Vsa.Sim.FleetB1ReseatVerdict.skelHNull_of_pins
#print axioms Vsa.Sim.FleetB1ReseatVerdict.skelHBool_of_pins
#print axioms Vsa.Sim.FleetB1ReseatVerdict.skelHStr_of_pins
