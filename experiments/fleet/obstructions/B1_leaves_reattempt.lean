import Vsa.Sim.rows.AssemblySkeleton

/-!
# Fleet B1-leaves RE-ATTEMPT (post-a46b7ab) — the entry-conditioned gap, pinned

Adversarial re-attempt after the ITEM-ZERO amendment (298ea7d/a46b7ab): the
four leaf residuals are now ENTRY-CONDITIONED, the old refutation witnesses
(`m0 = ∅` / `sret`-in-code / `sp = 0`) contradict `EvalEntry` — but the fields
are STILL not dischargeable, and this file machine-checks exactly what remains.

## Verdict per the brief's question

*"Does the amended entry hypothesis supply `IntLeafPres`/`IntLeafSurv`?"* — NO.
`EvalEntry` constrains only the ENTRY config `c` and `m0`; `LeafWiden`'s two
fields quantify over EVERY config `c'` satisfying the bare `EvalExit`:

* `pres` (`MemExtends m0 c'.σ.mem`): `EvalExit.memFrame` carves out
  `[SL.lo, sp) ∪ [A.lo, A.hi) ∪ [sret, sret+24)`; an exit config with a
  presence-dropped byte in a carve-out still satisfies every `EvalExit` field,
  and no `EvalEntry` fact reaches `c'`.
* `surv` (StoreRepr survival at `stackFoot SL = [SL.lo, SL.hi)`): the entry's
  `store_survives` footprint is `[SL.lo, sp) ∪ [sret, sret+24)` — the
  caller-stack strip `[sp.toNat, SL.hi)` (nonempty whenever `StackOK`'s
  `sp ≤ SL.hi` is strict) is uncovered, and `memFrame`'s arena carve-out lets
  `c'.σ.mem` drift from `m0` on `A`, where the represented store lives.  The
  `EvalExit.store` transport route needs A/AST/string ∩ `[SL.lo,SL.hi)` = ∅,
  which no hypothesis carries.

For hNull/hBool/hStr there is ADDITIONALLY the callee geometry: `EvalEntry`
carries only the int-pilot fields (`value_int_code`/`int_slot`/`sret_vicode_
disjoint`/`vicode_stack_disjoint`/slot-0 `table_stack_disjoint`); the
`Value_{null,bool,str}Loaded` / `{Null,Bool,Str}SlotPinned` / per-window
disjointness conjuncts are independent layout facts (e.g. `sret = 0x800027e0`
satisfies every `EvalEntry` sret conjunct yet straddles the value_null window
`[0x800027ec, 0x800027f8)`).

## What this file proves

The gap is EXACTLY the named premises below — given them, every hole is a
record fill / conjunction pairing (no further marshalling is missing):

* `LeafEntryGap e v` — the entry-conditioned successors of the falsity round's
  `IntLeafPres`/`IntLeafSurv`, stated once, parametric in the leaf.
* `{Null,Bool,Str}GeomOfEntry` — the `Eval*Entry`-minus-`EvalEntry` callee
  geometry, entry-conditioned.
* `skelH{Int,Null,Bool,Str}_of_entryGap` — the reductions.

Companion observations: `observations.md` `2026-09-02
leafwiden-entry-gap-persists` + `evalentry-missing-nbs-callee-geom`.
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
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

namespace Vsa.Sim.FleetB1Reattempt

/-- **The entry-conditioned widener gap** — the two facts `LeafWiden` needs
about every `EvalExit` config, now demanded only under `EvalEntry` (the
amendment's conditioning), still supplied by NOTHING in the hypothesis set.
`pres`/`surv` are verbatim the `Widen` fields with the entry hypothesis in
front; the falsity round's `IntLeafPres`/`IntLeafSurv`, upgraded. -/
structure LeafEntryGap (e : Expr) (v : Value) : Prop where
  /-- Presence: `EvalExit.memFrame`'s carve-outs (`[SL.lo,sp) ∪ A ∪ sret`)
  leave exit-side presence unconstrained; `EvalEntry` says nothing about `c'`.
  Honest supplier: the leaf walk's own write chain (`EvalExitD` re-land). -/
  pres : ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
      Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c →
      ∀ c' : Config,
        Vsa.Sim.EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
          st v sp r sret m0 c' →
        Vsa.Sim.MemExtends m0 c'.σ.mem
  /-- Survival at `stackFoot SL`: strictly wider than the entry's
  `store_survives` footprint (`[SL.lo,sp) ∪ sret` misses `[sp, SL.hi)`), and
  the `memFrame` arena carve-out blocks the `m0`-agreement route on `A`. -/
  surv : ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
      Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c →
      ∀ c' : Config,
        Vsa.Sim.EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
          st v sp r sret m0 c' →
        ∃ φf' φc' : Addr → Nat,
          Vsa.Sim.PhiExtends φf φf' st.store.frames.size ∧
          Vsa.Sim.PhiExtends φc φc' st.store.closures.size ∧
          ∀ m' : Mem, (∀ k : Nat, ¬ Vsa.Sim.stackFoot SL k → c'.σ.mem[k]? = m'[k]?) →
            StoreRepr m' N A φf' φc' st.store

/-- Given the gap, the widener is a record fill (no marshalling missing). -/
theorem leafWiden_of_gap {e : Expr} {v : Value} (h : LeafEntryGap e v)
    (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config)
    (hc : Vsa.Sim.EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c) :
    Vsa.Sim.LeafWiden g N A SL φf φc st v sp r sret m0 :=
  { pres := fun c' hx => h.pres st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc c' hx
    surv := fun c' hx => h.surv st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc c' hx }

/-- **hInt reduction**: the amended hole is EXACTLY `LeafEntryGap` at the int
leaf — the entry hypothesis conditioned the old two-premise gap but supplies
neither half. -/
theorem skelHInt_of_entryGap (h : ∀ n : Int, LeafEntryGap (.int n) (.int n))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHInt L := by
  intro st n g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact leafWiden_of_gap (h n) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc

/-- The `EvalNullEntry`-minus-`EvalEntry` callee geometry, entry-conditioned:
value_null window `[0x800027ec, 0x800027f8)` disjointness, code + slot-3 pins.
NOT derivable from `EvalEntry` (int-pilot fields only). -/
def NullGeomOfEntry : Prop :=
  ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env .null sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat) ∧
    ((0x800027f8 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
    Value_nullLoaded c.σ.mem ∧
    Vsa.Sim.NullSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 12)

/-- **hNull reduction**: geometry premise + widener gap ⇒ the hole. -/
theorem skelHNull_of_entryGap (hG : NullGeomOfEntry) (hW : LeafEntryGap .null .null)
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHNull L := by
  intro st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5,
    leafWiden_of_gap hW st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

/-- The `EvalBoolEntry`-minus-`EvalEntry` callee geometry (value_bool window
`[0x800027f8, 0x8000280c)`, slot 2). -/
def BoolGeomOfEntry : Prop :=
  ∀ (st : SpecSt) (b : Bool) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.bool b) sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
    ((0x8000280c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027f8) ∧
    Value_boolLoaded c.σ.mem ∧
    Vsa.Sim.BoolSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 8)

/-- **hBool reduction**. -/
theorem skelHBool_of_entryGap (hG : BoolGeomOfEntry)
    (hW : ∀ b : Bool, LeafEntryGap (.bool b) (.bool b))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHBool L := by
  intro st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5,
    leafWiden_of_gap (hW b) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

/-- The `EvalStrEntry`-minus-`EvalEntry` callee geometry (payload-string
region facts + value_str window `[0x8000281c, 0x8000282c)`, slot 1). -/
def StrGeomOfEntry : Prop :=
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

/-- **hStr reduction**. -/
theorem skelHStr_of_entryGap (hG : StrGeomOfEntry)
    (hW : ∀ s : String, LeafEntryGap (.str s) (.str s))
    (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHStr L := by
  intro st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    hG st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    leafWiden_of_gap (hW s) st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc⟩

end Vsa.Sim.FleetB1Reattempt

#print axioms Vsa.Sim.FleetB1Reattempt.skelHInt_of_entryGap
#print axioms Vsa.Sim.FleetB1Reattempt.skelHNull_of_entryGap
#print axioms Vsa.Sim.FleetB1Reattempt.skelHBool_of_entryGap
#print axioms Vsa.Sim.FleetB1Reattempt.skelHStr_of_entryGap
