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

/-- Sequential composition: the footprints add up. -/
theorem trans {F G : Nat → Prop} {m0 m1 m2 : Mem}
    (h1 : MemFootprint F m0 m1) (h2 : MemFootprint G m1 m2) :
    MemFootprint (fun k => F k ∨ G k) m0 m2 :=
  ⟨fun k hk => (h2.agree k (fun h => hk (Or.inr h))).trans (h1.agree k (fun h => hk (Or.inl h)))⟩

/-- A footprint may be widened. -/
theorem mono {F G : Nat → Prop} {m0 m : Mem} (hFG : ∀ k, F k → G k)
    (h : MemFootprint F m0 m) : MemFootprint G m0 m :=
  ⟨fun k hk => h.agree k (fun hF => hk (hFG k hF))⟩

end MemFootprint

/-! ## Standard footprint windows and families -/

/-- A footprint family, indexed by the call geometry `SL A sp sret`
(`sp`/`sret` as naturals). -/
abbrev FootFam := StackLayout → Arena → Nat → Nat → Nat → Prop

/-- Pointwise inclusion of families. -/
def FootFam.le (F G : FootFam) : Prop :=
  ∀ SL A sp sret k, F SL A sp sret k → G SL A sp sret k

/-! ## Shared CELL footprints (the per-arm `<op>CellFoot` are these predicates) -/

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

/-- The extra of a footprint-carrying child. -/
abbrev footExtra (F : FootFam) : EvalExtraM :=
  fun _ A SL _ _ sp sret m0 c => MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem

/-- The ∀-closed child contract at the footprint family `F`. -/
abbrev EvalIHF (F : FootFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (footExtra F) st d env e st' v

namespace EvalIHF

variable {F : FootFam} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}

theorem mono {G : FootFam} (hFG : FootFam.le F G) (h : EvalIHF F st d env e st' v) :
    EvalIHF G st d env e st' v :=
  EvalIHWithM.mono (fun _ A SL _ _ sp sret _ _ hf =>
    hf.mono (fun k => hFG SL A sp.toNat sret.toNat k)) h

end EvalIHF

/-! ## The epilogue-entry memory and `blockD_v_rec_footprint` -/

end Vsa.Sim
