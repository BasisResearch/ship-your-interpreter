import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecRetNull
import Vsa.Sim.ExecBlock
import Vsa.Sim.WidenMeta

/-!
# Layer 4 — M4 leaf `ExecS` cases re-landed at `ExecExitD` (the statement shape-gap)

The statement-side twin of `EvalLeafD.lean`.  The recursive motive `mExecS` of
`execSeq_sim_of_cases` (the `ExecIH` shape, `ExecEntry … → ExecExitD …`;
`TermSimAssembly.mExecS = ExecBlock.ExecIH` by definitional unfolding) concludes
the presence/survival-*widened* exit `ExecExitD` (`= ExecExit` ∧ `MemExtends m0
mem` ∧ the `[SL.lo,SL.hi)`-`StoreRepr`-survival clause; see `ExecBlock.lean`).
The landed leaf statement lemmas (`execBrkSim`/`execContSim`/…) conclude the
plain `ExecExit` (over an entry precondition `ExecEntry ∧ sailOutput = out0`), so
`termSimClosed`'s statement minor premises (`hSBrk`/`hSCont`/…) don't yet match
the motive.  This file re-lands the register-only leaves at `ExecExitD`.

## The two gaps (bundle-only; NO new machine proof)

1. **entry `out0`** — the landed lemmas quantify the pre-`sailOutput` array `out0`
   and add `c.σ.sailOutput = out0` to the entry.  The row supplies it by `rfl`
   (`out0 := c.σ.sailOutput`).  This is pure marshalling.
2. **exit `ExecExit → ExecExitD`** — add `MemExtends m0 mem` and the
   `[SL.lo,SL.hi)`-store-survival clause.  For a register-only leaf the entire
   memory delta from `m0` is the four/five prologue `writeMap8` spills (all inside
   `[SL.lo, sp) ⊆ [SL.lo, SL.hi)`), which are presence-preserving; and the exit
   store `= st.store` is footprint-disjoint from `[SL.lo,SL.hi)`.  Both are TRUE
   of the exit but forgotten by `ExecExit`, so they are re-supplied as the honest
   widener residual `ExecLeafWiden` — the statement analog of `LeafWiden`
   (`EvalLeafD.lean`) and of the recursive cases' `hMcallPop`.

`ExecCaseGeom` (below) is the per-case geometry bundle the recursor supplies: the
jump-table slot pin + its stack-disjointness (the `execBlockA` inputs) + the
PINNED `ExecLeafWidenP` widener (wave 48d).  Each `*D` lemma composes the landed
leaf `Triple` output (now at `ExecExitPinned`) with `execExitD_of_pinnedExecExit`
— it does NOT re-prove the machine run.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ExecLeafWidenP` — the PINNED exec-leaf widener (wave 48d, X3-c)

Moved here from `rows/ExecLeafD.lean` and made the `ExecCaseGeom` widener half.

The plain (unpinned) `ExecLeafWiden` — a `Widen` over the bare `ExecExit`, quantified
over EVERY `ExecExit`-satisfying config — is provably UNDERIVABLE from the entry:
`ExecExit` forgets the in-stack presence (`pres`), so a universal `∀ c with ExecExit,
MemExtends m0 c.σ.mem` cannot be supplied (the wave-48c machine-checked obstruction).
The eval leaves (hInt/…) closed exactly this gap in wave 47e NOT with the plain
widener but by RESTATING it at a PINNED exit family (`LeafWidenP` = `Widen` at
`EvalExitPinned`) and proving THAT from the entry alone.  Wave 48d makes
`execBrkSim`/`execContSim` conclude `ExecExitPinned` (the pin threaded through
`execBlockD`'s `Q`), so the pinned widener is now the honest, entry-derivable
residual — the exec twin of `LeafWidenP`.

`ExecLeafMemPin`/`ExecExitPinned` are defined upstream (`ExecBrkCont.lean`).  THIN
ALIAS of the parametric `Widen` (`WidenMeta.lean`) at the pinned exit family. -/
abbrev ExecLeafWidenP
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (status : Status) (sp r aRet : BitVec 64) (m0 : Mem) : Prop :=
  Widen (ExecExitPinned g N A SL φf φc st' status sp r aRet m0)
    N A φf φc st'.store.frames.size st'.store.closures.size st' m0 (stackFoot SL)

/-- **`execLeafWidenP_of_entry`** — the pinned-exit exec widener follows from the
(47e-widened) `ExecEntry.store_survives` alone, at the identity φ-pair.  Since
brk/cont leave the store unchanged the exit store is `st.store` (= `st'.store`),
which the entry survival re-represents over any `[SL.lo,SL.hi)`-confined change;
`pres` is the pin's first half; `surv` chains the pin's `m0`-agreement into the
widened entry survival.  Mirrors `leafWidenP_of_entry` (`EvalLeafD.lean`) exactly. -/
theorem execLeafWidenP_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {s : Stmt} {status : Status}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hc : ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c) :
    ExecLeafWidenP g N A SL φf φc st status sp r aRet m0 where
  pres := fun _ hx => hx.2.pres
  surv := fun _ hx =>
    ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, fun m' hm' => by
      refine hc.store_survives m' (fun k hk => ?_)
      have hksp : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
        hk ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hc.stackOK.2.1⟩
      rw [hc.mem]
      exact (hx.2.agree k hksp).symm.trans (hm' k hk)⟩

/-- **The pinned leaf widening.** `ExecExitPinned … c ∧ ExecLeafWidenP …` gives
`ExecExitD … c` — the `mExecS` motive shape.  Exec twin of `evalExitD_of_pinnedExit`;
a THIN COROLLARY of the parametric family bridge `execExitD_of_widen`. -/
theorem execExitD_of_pinnedExecExit
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st' : Vsa.While.St} {status : Status} {sp r aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hx : ExecExitPinned g N A SL φf φc st' status sp r aRet m0 c)
    (hW : ExecLeafWidenP g N A SL φf φc st' status sp r aRet m0) :
    ExecExitD g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' status sp r aRet m0 c :=
  ⟨hx.1, hW.pres c hx, hW.surv c hx⟩

/-! ## `ExecCaseGeom` — the per-leaf geometry bundle (the recursor-supplied residual)

The union of the `execBlockA` jump-table inputs (`hslot` + its stack-disjointness
`htableStk`) and the `ExecLeafWiden` widener.  Parameterized by the case ROW
`(k, armPC, status)`.  This is the statement-side twin of the EvalE rows' per-case
residual (`IntLeafResid`/…): one bundle threaded once, projected per row. -/
def ExecCaseGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (status : Status) (k : Nat) (armPC : BitVec 64)
    (sp r aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned k armPC m0 ∧
  (stmtJumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * k) ∧
  -- wave 48d (X3-c): the PINNED widener (over `ExecExitPinned`), entry-derivable
  -- via `execLeafWidenP_of_entry` — the plain `ExecLeafWiden` was underivable.
  ExecLeafWidenP g N A SL φf φc st status sp r aRet m0

/-! ## The register-only leaf `*D` lemmas

Each composes the existing leaf simulation `Triple` (`execBrkSim`/`execContSim`,
now at `ExecExitPinned`) with `execExitD_of_pinnedExecExit`, threading the pinned
`ExecLeafWidenP` widener from the `ExecCaseGeom` bundle, and supplying the entry
`out0 := c.σ.sailOutput` by `rfl`.  These are exactly the `mExecS`-motive
(`ExecExitD`) minor premises `termSimClosed` consumes as `hSBrk`/`hSCont`, at the
recursor-supplied `ExecCaseGeom`. -/

/-- **`execBrkSimD`** — the `ExecS.brk` leaf at `ExecExitD` (the `ExecIH` shape). -/
theorem execBrkSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .brk st .brk)
    (hG : ExecCaseGeom g N A SL φf φc st .brk 7 execArmBrk sp r aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .brk sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hW⟩ := hG
  obtain ⟨c', hs, hExitP⟩ :=
    execBrkSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_pinnedExecExit hExitP hW⟩

/-- **`execContSimD`** — the `ExecS.cont` leaf at `ExecExitD` (the `ExecIH` shape). -/
theorem execContSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hE : ExecS st d env .cont st .cont)
    (hG : ExecCaseGeom g N A SL φf φc st .cont 8 execArmCont sp r aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .cont sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hW⟩ := hG
  obtain ⟨c', hs, hExitP⟩ :=
    execContSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 c.σ.sailOutput
      hE hslot htableStk c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_pinnedExecExit hExitP hW⟩

end Vsa.Sim
