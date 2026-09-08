import Vsa.Sim.EvalRecCommon
import Vsa.Sim.BlockAdapter

/-!
# `ExitFootprint` — the footprint-carrying exit interface (IH tower, Level 1)

`EvalExitD` frames memory only outside `[SL.lo, sp) ∪ arena ∪ [sret, sret+24)`;
the arena is deliberately unconstrained.  This file adds, ADDITIVELY, the
footprint-carrying siblings every Level-2 clause is derived from:

* `MemFootprint F m0 m` — `m` differs from `m0` at most inside `F` (named field
  `agree`), with the composition laws (`trans` over `F ∪ G`, `mono`,
  `of_writeMap8`, `of_writeLog`, `of_agreeP`, `of_exitFrame`);
* the standard footprint windows (`stackWin`, `resultSlot`, `arenaWin`, `word8`)
  and the footprint FAMILIES (`FootFam`, indexed by the call geometry
  `SL A sp sret`): `noArenaFoot`, `exitFoot`;
* `EvalIHWithM` — `EvalIHWith` whose extra fact may see the call's `sp` and its
  entry memory `m0`.  `EvalIHWith`'s `EvalExtra` sees neither (only
  `N A SL φf φc sret`), and a footprint is a statement relative to `m0`, so the
  footprint sibling cannot be an `EvalIHWith` instance;
* `EvalExitF F` / `EvalIHF F` — the exit and the ∀-closed child contract carrying
  `MemFootprint (F SL A sp sret) m0` at the ACTUAL returned state, with the
  projections back to `EvalExitD` / `EvalIH`, `mono`, and `EvalIH.exitFoot`
  (the weak exit already IS the footprint `exitFoot`);
* `blockD_v_rec_footprint` — the shared epilogue writes no memory, so a
  footprint of the epilogue-entry memory `mpre` is inherited by the exit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## `MemFootprint` -/

/-- `m` differs from `m0` at most inside the footprint `F`. -/
structure MemFootprint (F : Nat → Prop) (m0 m : Mem) : Prop where
  agree : ∀ k, ¬ F k → m[k]? = m0[k]?

namespace MemFootprint

theorem refl (F : Nat → Prop) (m : Mem) : MemFootprint F m m := ⟨fun _ _ => rfl⟩

theorem of_eq {F : Nat → Prop} {m0 m : Mem} (h : m = m0) : MemFootprint F m0 m :=
  ⟨fun _ _ => by rw [h]⟩

/-- Sequential composition: the footprints add up. -/
theorem trans {F G : Nat → Prop} {m0 m1 m2 : Mem}
    (h1 : MemFootprint F m0 m1) (h2 : MemFootprint G m1 m2) :
    MemFootprint (fun k => F k ∨ G k) m0 m2 :=
  ⟨fun k hk => (h2.agree k (fun h => hk (Or.inr h))).trans (h1.agree k (fun h => hk (Or.inl h)))⟩

/-- A footprint may be widened. -/
theorem mono {F G : Nat → Prop} {m0 m : Mem} (hFG : ∀ k, F k → G k)
    (h : MemFootprint F m0 m) : MemFootprint G m0 m :=
  ⟨fun k hk => h.agree k (fun hF => hk (hFG k hF))⟩

theorem of_agreeP {F : Nat → Prop} {m0 m : Mem} (h : AgreeP (fun k => ¬ F k) m0 m) :
    MemFootprint F m0 m :=
  ⟨fun k hk => (h k hk).symm⟩

theorem toAgreeP {F : Nat → Prop} {m0 m : Mem} (h : MemFootprint F m0 m) :
    AgreeP (fun k => ¬ F k) m0 m :=
  fun k hk => (h.agree k hk).symm

/-- Symmetric form of `agree` (the `AgreeP`/`read*_agreeP` orientation). -/
theorem agree' {F : Nat → Prop} {m0 m : Mem} (h : MemFootprint F m0 m)
    (k : Nat) (hk : ¬ F k) : m0[k]? = m[k]? :=
  (h.agree k hk).symm

end MemFootprint

/-! ## Standard footprint windows and families -/

/-- The caller's stack window `[SL.lo, sp)`. -/
def stackWin (SL : StackLayout) (sp : Nat) (k : Nat) : Prop := SL.lo ≤ k ∧ k < sp

/-- The 24-byte result slot `[sret, sret+24)`. -/
def resultSlot (sret : Nat) (k : Nat) : Prop := sret ≤ k ∧ k < sret + 24

/-- The arena `[A.lo, A.hi)`. -/
def arenaWin (A : Arena) (k : Nat) : Prop := A.lo ≤ k ∧ k < A.hi

/-- One 8-byte word `[a, a+8)`. -/
def word8 (a : Nat) (k : Nat) : Prop := a ≤ k ∧ k < a + 8

theorem MemFootprint.of_writeMap8 (m : Mem) (a : Nat) (d : BitVec (8 * 8)) :
    MemFootprint (word8 a) m (writeMap8 m a d) :=
  ⟨fun k hk => getElem_writeMap8_disjoint m a k d
    (by unfold word8 at hk; omega)⟩

/-- A reflected write log has the footprint of its store windows. -/
theorem MemFootprint.of_writeLog (m : Mem) (log : List WEntry)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8) :
    MemFootprint (fun k => ∃ e ∈ log, e.1 ≤ k ∧ k < e.1 + e.2.1) m (writeLog m log) :=
  MemFootprint.of_agreeP (writeLog_agreeP_disjoint m log _ hw
    (fun k hk e he => by
      by_cases hlt : k < e.1
      · exact Or.inl hlt
      · exact Or.inr (by
          by_cases hge : e.1 + e.2.1 ≤ k
          · exact hge
          · exact absurd ⟨e, he, by omega, by omega⟩ hk)))

/-- A footprint family, indexed by the call geometry `SL A sp sret`
(`sp`/`sret` as naturals). -/
abbrev FootFam := StackLayout → Arena → Nat → Nat → Nat → Prop

/-- Pointwise inclusion of families. -/
def FootFam.le (F G : FootFam) : Prop :=
  ∀ SL A sp sret k, F SL A sp sret k → G SL A sp sret k

/-- The footprint of a NON-allocating call: its stack window and its result slot. -/
def noArenaFoot : FootFam := fun SL _ sp sret k => stackWin SL sp k ∨ resultSlot sret k

/-- The footprint `EvalExitD` already frames: stack window, arena, result slot. -/
def exitFoot : FootFam := fun SL A sp sret k =>
  stackWin SL sp k ∨ arenaWin A k ∨ resultSlot sret k

theorem noArenaFoot_le_exitFoot : FootFam.le noArenaFoot exitFoot := by
  intro SL A sp sret k h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- The footprint of the binary arm's two-children head from the row-entry
memory `m0` to the return of both children: the parent's stack window (its
prologue spills, the `s3` spill at `sp-40`, the argument staging at `sp-1088`,
both child result slots) and the two children's footprints at THEIR geometry
(`sp' = sp - 1088`, result slots `sp-968` / `sp-944`). -/
def binaryHeadFoot (Fl Fr : FootFam) (SL : StackLayout) (A : Arena) (sp : Nat)
    (k : Nat) : Prop :=
  stackWin SL sp k ∨ Fl SL A (sp - 1088) (sp - 968) k ∨ Fr SL A (sp - 1088) (sp - 944) k

/-- Two non-allocating children keep the head inside the parent's stack window. -/
theorem binaryHeadFoot_noArena {SL : StackLayout} {A : Arena} {sp : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat)
    (hk : binaryHeadFoot noArenaFoot noArenaFoot SL A sp k) : stackWin SL sp k := by
  unfold binaryHeadFoot noArenaFoot stackWin resultSlot at hk
  unfold stackWin
  omega

/-! ## Shared CELL footprints (the per-arm `<op>CellFoot` are these predicates) -/

/-- The exact footprint of an integer/comparison CELL from the return of its
children to the epilogue entry: the three dispatch-ladder temporaries
`[sp-848, sp-824)` (the `sd`s at `sp-848`, `sp-840`, `sp-832`) and the boxed
result `[sret, sret+24)`.  The eight integer rows' `<op>CellFoot`, the pilot's
`ltCellFoot` and the `neg` cell's `negCellFoot` are stated beside their cells
(in the row files) and are definitionally this predicate; a NEW cell of this
shape uses `intCellFoot` directly. -/
def intCellFoot (sp sret : Nat) (k : Nat) : Prop :=
  word8 (sp - 848) k ∨ word8 (sp - 840) k ∨ word8 (sp - 832) k ∨ resultSlot sret k

/-- The exact footprint of a `value_truthy` CELL: the 24-byte argument copy at
`esp+64 = sp-1024` (`value_truthy` itself writes nothing) and the boxed result
`[sret, sret+24)`.  `truthyCellFoot` (`EvalNotSim.lean`, shared by logical-not
and the two short-circuit arms) is definitionally this predicate. -/
def truthyArgCellFoot (sp sret : Nat) (k : Nat) : Prop :=
  word8 (sp - 1024) k ∨ word8 (sp - 1016) k ∨ word8 (sp - 1008) k ∨ resultSlot sret k

/-- A cell writing only temporaries inside the frame and the result slot is
non-allocating. -/
theorem intCellFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat) (hk : intCellFoot sp sret k) :
    noArenaFoot SL A sp sret k := by
  unfold intCellFoot word8 resultSlot at hk
  unfold noArenaFoot stackWin resultSlot
  omega

/-- The truthiness cell is non-allocating for the same reason. -/
theorem truthyArgCellFoot_noArena {SL : StackLayout} {A : Arena} {sp sret : Nat}
    (h : SL.lo + 1088 ≤ sp) (k : Nat) (hk : truthyArgCellFoot sp sret k) :
    noArenaFoot SL A sp sret k := by
  unfold truthyArgCellFoot word8 resultSlot at hk
  unfold noArenaFoot stackWin resultSlot
  omega

/-- The `EvalExit.memFrame` shape as a footprint. -/
theorem MemFootprint.of_exitFrame {SL : StackLayout} {A : Arena} {sp sret : BitVec 64}
    {m0 m : Mem}
    (h : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ m[a]? = m0[a]?) :
    MemFootprint (exitFoot SL A sp.toNat sret.toNat) m0 m :=
  ⟨fun k hk => by
    rcases h k (fun hs => hk (Or.inl hs)) (fun ha => hk (Or.inr (Or.inl ha))) with hr | heq
    · exact absurd (Or.inr (Or.inr hr)) hk
    · exact heq⟩

/-! ## `EvalIHWithM` — extra child facts that may see `sp` and the entry memory -/

/-- Extra child-return facts over the call's world INCLUDING its `sp` and its
entry memory `m0` (the two `EvalExtra` cannot see). -/
abbrev EvalExtraM := NativeAddrs → Arena → StackLayout →
  (Addr → Nat) → (Addr → Nat) → BitVec 64 → BitVec 64 → Mem → Config → Prop

/-- A child simulation retaining an `sp`/`m0`-aware fact at its actual return. -/
structure EvalIHWithM (Extra : EvalExtraM)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple
      (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
      (ReturnedWith
        (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
          st' v sp r sret m0)
        (Extra N A SL φf φc sp sret m0))

theorem EvalIHWithM.forget {Extra : EvalExtraM}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalIHWithM Extra st d env e st' v) : EvalIH st d env e st' v := by
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact ReturnedWith.forget (h.run g N A SL φf φc sp r sret aEnv aExpr m0)

/-- Every `EvalIHWith` fact is an `sp`/`m0`-blind `EvalIHWithM` fact. -/
theorem EvalIHWith.toM {Extra : EvalExtra}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalIHWith Extra st d env e st' v) :
    EvalIHWithM (fun N A SL φf φc _ sret _ => Extra N A SL φf φc sret.toNat)
      st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    h.run g N A SL φf φc sp r sret aEnv aExpr m0

/-- Strengthen the retained fact pointwise at the returned state. -/
theorem EvalIHWithM.mono {Extra Extra' : EvalExtraM}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (himp : ∀ N A SL φf φc sp sret m0 c,
      Extra N A SL φf φc sp sret m0 c → Extra' N A SL φf φc sp sret m0 c)
    (h : EvalIHWithM Extra st d env e st' v) : EvalIHWithM Extra' st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    (h.run g N A SL φf φc sp r sret aEnv aExpr m0).conseq (fun _ hp => hp)
      (fun c hp => ⟨hp.result, himp N A SL φf φc sp sret m0 c hp.extra⟩)

/-! ## `EvalExitF` / `EvalIHF` — the footprint-carrying exit and child contract -/

/-- `EvalExitD` plus the footprint `F SL A sp sret` of the exit memory relative to
the entry memory `m0`, at the same returned configuration. -/
def EvalExitF (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (m0 : Mem) : Config → Prop :=
  ReturnedWith (EvalExitD g N A SL φf φc nf nc st' v sp r sret m0)
    (fun c => MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem)

/-- The extra of a footprint-carrying child. -/
abbrev footExtra (F : FootFam) : EvalExtraM :=
  fun _ A SL _ _ sp sret m0 c => MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem

/-- The ∀-closed child contract at the footprint family `F`. -/
abbrev EvalIHF (F : FootFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (footExtra F) st d env e st' v

namespace EvalIHF

variable {F : FootFam} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}

/-- The child contract at one call, stated over `EvalExitF`. -/
theorem exitF (h : EvalIHF F st d env e st' v)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) :
    Triple (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
      (EvalExitF F g N A SL φf φc st.store.frames.size st.store.closures.size
        st' v sp r sret m0) :=
  h.run g N A SL φf φc sp r sret aEnv aExpr m0

/-- Build the child contract from its per-call `EvalExitF` triples. -/
theorem of_exitF
    (h : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
      Triple (EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0)
        (EvalExitF F g N A SL φf φc st.store.frames.size st.store.closures.size
          st' v sp r sret m0)) :
    EvalIHF F st d env e st' v where
  run := h

theorem forget (h : EvalIHF F st d env e st' v) : EvalIH st d env e st' v :=
  EvalIHWithM.forget h

theorem mono {G : FootFam} (hFG : FootFam.le F G) (h : EvalIHF F st d env e st' v) :
    EvalIHF G st d env e st' v :=
  EvalIHWithM.mono (fun _ A SL _ _ sp sret _ _ hf =>
    hf.mono (fun k => hFG SL A sp.toNat sret.toNat k)) h

end EvalIHF

/-- The weak exit already carries the footprint `exitFoot` (its `memFrame`). -/
theorem EvalIH.exitFoot {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalIH st d env e st' v) : EvalIHF exitFoot st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    (h g N A SL φf φc sp r sret aEnv aExpr m0).conseq (fun _ hp => hp)
      (fun _ hp => ⟨hp, MemFootprint.of_exitFrame hp.1.memFrame⟩)

/-! ## The epilogue-entry memory and `blockD_v_rec_footprint` -/

/-- The epilogue entry's memory is the named `mpre`. -/
theorem PreEpilogueV.mem
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {v : Value}
    {sp r sret v8 v9 v18 : BitVec 64} {out0 : Array String}
    {m0 mpre : Mem} {c : Config}
    (h : PreEpilogueV g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c) :
    c.σ.mem = mpre := by
  obtain ⟨_good, _tick, _pc, _sret, _sp, _minstret, _out, _outStr, hmem, _rest⟩ := h
  exact hmem

theorem PreEpilogueVD.mem
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {v : Value}
    {sp r sret v8 v9 v18 : BitVec 64} {out0 : Array String}
    {m0 mpre : Mem} {c : Config}
    (h : PreEpilogueVD g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c) :
    c.σ.mem = mpre :=
  PreEpilogueV.mem h.1

/-- The shared epilogue writes no memory: a footprint of the epilogue-entry
memory `mpre` (relative to any `m0`) is inherited by the exit. -/
theorem blockD_v_rec_footprint (F : Nat → Prop)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => ∃ mpre,
        PreEpilogueVD g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c ∧
        MemFootprint F m0 mpre)
      (ReturnedWith
        (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
          st v sp r sret m0)
        (fun c => MemFootprint F m0 c.σ.mem)) :=
  (blockD_v_rec_coherent g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0
    (fun _ _ m => MemFootprint F m0 m)).conseq
    (fun _ hp => ⟨hp⟩)
    (fun _ hp => ⟨hp.result, hp.extra.owned⟩)

/-- `blockD_v_rec_footprint` at the exit family: the row's own footprint. -/
theorem blockD_v_rec_exitF (F : FootFam)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => ∃ mpre,
        PreEpilogueVD g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c ∧
        MemFootprint (F SL A sp.toNat sret.toNat) m0 mpre)
      (EvalExitF F g N A SL φf φc st.store.frames.size st.store.closures.size
        st v sp r sret m0) :=
  blockD_v_rec_footprint (F SL A sp.toNat sret.toNat) g N A SL φf φc st v sp r sret
    v8 v9 v18 out0 m0

#print axioms MemFootprint.trans
#print axioms MemFootprint.of_writeLog
#print axioms MemFootprint.of_exitFrame
#print axioms binaryHeadFoot_noArena
#print axioms intCellFoot_noArena
#print axioms truthyArgCellFoot_noArena
#print axioms EvalIHWithM.forget
#print axioms EvalIHF.mono
#print axioms EvalIH.exitFoot
#print axioms PreEpilogueVD.mem
#print axioms blockD_v_rec_footprint
#print axioms blockD_v_rec_exitF

end Vsa.Sim
