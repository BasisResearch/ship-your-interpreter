import Vsa.Sim.EvalVarSim
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.EvalRecCommon

/-!
# Layer 4 — M4 leaf `EvalE` cases re-landed at `EvalExitD` (the shape-gap discharge)

The recursive motive `mEvalE` of `term_sim_of_cases` (the `EvalIH` shape,
`EvalEntry … → EvalExitD …`) concludes the presence/survival-*widened* exit
`EvalExitD` (`= EvalExit` ∧ `MemExtends m0 mem` ∧ the `[SL.lo,SL.hi)`
`StoreRepr`-survival clause; see `EvalRecCommon.lean`). The five LEAF case lemmas
(`evalIntSim`/`evalNullSim`/`evalBoolSim`/`evalStrSim`/`evalVarSim`) conclude the
plain `EvalExit`, so `termSimClosed`'s leaf minor premises (`hInt`/…/`hVar`) don't
yet match the motive. This file re-lands the five leaves at `EvalExitD`.

## How the widening decomposes

A leaf's total memory delta from the entry `m0` is a `writeMap4/writeMap8` chain
(the four prologue spills in `[SL.lo, sp)`, the callee `value_*` write in the
sret buffer `[sret, sret+24)`). `EvalExit.memFrame` pins that delta: outside
`[SL.lo, sp) ∪ A ∪ [sret, sret+24)` the exit memory equals `m0`. From this:

* **`MemExtends m0 mem`** — every `writeMap` insert preserves presence
  (`memExtends_writeMap8`/`memExtends_writeMap4`), so the exit memory is a
  presence-superset of `m0`. `EvalExit` forgets the chain, so this is re-supplied
  as the honest window-presence residual `LeafWiden.pres` — the exact analog of
  the neg case's `hMcallPop` (`EvalNegSim3.lean`), which likewise re-supplies the
  presence `EvalExit` drops.
* **`[SL.lo,SL.hi)`-survival** — the re-represented `st'.store` (`= st.store` for
  every leaf) tolerates further memory changes confined to `[SL.lo, SL.hi)`,
  because the leaf's writes all land inside `[SL.lo, SL.hi)` (spills in
  `[SL.lo, sp) ⊆ [SL.lo, SL.hi)`; the sret write in
  `[sret, sret+24) ⊆ [SL.lo, SL.hi)`). This is the leaf store's footprint
  disjointness, the same fact `EvalEntry.store_survives` carries at the entry
  maps; stated at the exit maps/mem it IS the `EvalExitD` survival clause. Carried
  as `LeafWiden.surv`.

The `*D` lemmas do NOT re-prove the leaf machine run: they compose the existing
`evalIntSim`/… `EvalExit` output with these two clauses (`evalExitD_of_evalExit`).

## Plugging into `termSimClosed`

Each `*D` lemma is the corresponding leaf Triple with `EvalExit` replaced by
`EvalExitD` and the entry precondition strengthened by the `LeafWiden` bundle —
i.e. exactly `term_sim_of_cases`'s `mEvalE`-motive minor premise (`hInt`/`hStr`/
`hBool`/`hNull`/`hVar`) once the recursor supplies the leaf's `LeafWiden` (the
leaf analog of the recursive cases' `hMcallPop`/`NegExtras` residuals).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
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

/-! ## `LeafWiden` — the two exit widening clauses `EvalExit` drops, as an
     exit-quantified widener

The two `EvalExitD` upgrade clauses are facts about the EXIT configuration, which
a leaf's `Triple` produces existentially. So the widening residual is supplied as
a *widener*: a function that, for ANY config `c` satisfying the leaf's own
`EvalExit`, yields the two dropped clauses about `c`. This is TRUE of every leaf
exit (the delta is a `writeMap` chain over `m0` — presence-preserving — and the
store footprint is disjoint from `[SL.lo,SL.hi)`), and is the leaf analog of the
neg case's `hMcallPop`: the honest re-supply of what `EvalExit` forgets. The
recursor's leaf minor premise provides it. -/
def LeafWiden
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (v : Value) (sp r sret : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c : Config, EvalExit g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' v sp r sret m0 c →
    -- (a) presence monotonicity `MemExtends m0 (exit mem)`
    MemExtends m0 c.σ.mem ∧
    -- (b) the `[SL.lo, SL.hi)`-survival of the exit store
    (∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st'.store)

/-- **The leaf widening.** `EvalExit … c ∧ LeafWiden …` gives `EvalExitD … c` —
the `mEvalE` motive shape. `LeafWiden` at the (already-established) `EvalExit`
supplies the `MemExtends` clause and the `[SL.lo,SL.hi)`-survival clause, at the
identity `φ` extensions (a leaf allocates nothing, so `st'.store = st.store` at
the entry maps). -/
theorem evalExitD_of_evalExit
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st' : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hExit : EvalExit g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' v sp r sret m0 c)
    (hW : LeafWiden g N A SL φf φc st' v sp r sret m0) :
    EvalExitD g N A SL φf φc st'.store.frames.size st'.store.closures.size
      st' v sp r sret m0 c :=
  let ⟨hpres, hsurv⟩ := hW c hExit
  ⟨hExit, hpres, φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, hsurv⟩

/-! ## The five leaf `*D` lemmas

Each composes the existing leaf simulation Triple (`evalIntSim`/…) with
`evalExitD_of_evalExit`, threading the `LeafWiden` bundle from the strengthened
precondition. These are the `mEvalE`-motive (`EvalExitD`) minor premises
`termSimClosed` consumes as `hInt`/`hStr`/`hBool`/`hNull`/`hVar`. -/

/-- **`evalIntSimD`** — the `EvalE.int` leaf at `EvalExitD`. -/
theorem evalIntSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (n : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hE : EvalE st d a (.int n) st (.int n))
    (hW : LeafWiden g N A SL φf φc st (.int n) sp r sret m0) :
    Triple
      (EvalEntry g N A SL φf φc st d a (.int n) sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.int n) sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalIntSim g N A SL φf φc st d a n sp r sret aEnv aExpr m0 hE c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit hExit hW⟩

/-- **`evalNullSimD`** — the `EvalE.null` leaf at `EvalExitD`. -/
theorem evalNullSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hE : EvalE st d a .null st .null)
    (hW : LeafWiden g N A SL φf φc st .null sp r sret m0) :
    Triple
      (EvalNullEntry g N A SL φf φc st d a sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st .null sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalNullSim g N A SL φf φc st d a sp r sret aEnv aExpr m0 hE c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit hExit hW⟩

/-- **`evalBoolSimD`** — the `EvalE.bool` leaf at `EvalExitD`. -/
theorem evalBoolSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (b : Bool)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hE : EvalE st d a (.bool b) st (.bool b))
    (hW : LeafWiden g N A SL φf φc st (.bool b) sp r sret m0) :
    Triple
      (EvalBoolEntry g N A SL φf φc st d a b sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.bool b) sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalBoolSim g N A SL φf φc st d a b sp r sret aEnv aExpr m0 hE c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit hExit hW⟩

/-- **`evalStrSimD`** — the `EvalE.str` leaf at `EvalExitD`. -/
theorem evalStrSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (s : String)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hE : EvalE st d a (.str s) st (.str s))
    (hW : LeafWiden g N A SL φf φc st (.str s) sp r sret m0) :
    Triple
      (EvalStrEntry g N A SL φf φc st d a s sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.str s) sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalStrSim g N A SL φf φc st d a s sp r sret aEnv aExpr m0 hE c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit hExit hW⟩

/-- **`evalVarSimD`** — the `EvalE.var` leaf at `EvalExitD` (retaining
`EvalVarEntry`'s explicit `env_get_found` contract, as in `evalVarSim`). -/
theorem evalVarSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (x : String) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hE : EvalE st d a (.var x) st v)
    (hW : LeafWiden g N A SL φf φc st v sp r sret m0) :
    Triple
      (EvalVarEntry g N A SL φf φc st d a x v sp r sret aEnv aExpr m0)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st v sp r sret m0) := by
  intro c hEntry
  obtain ⟨c', hs, hExit⟩ :=
    evalVarSim g N A SL φf φc st d a x v sp r sret aEnv aExpr m0 hE c hEntry
  exact ⟨c', hs, evalExitD_of_evalExit hExit hW⟩

end Vsa.Sim
