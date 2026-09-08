import Vsa.Sim.EvalLeafD
import Vsa.Sim.ExitFootprint

/-!
# `LeafFootprint` — the literal leaves at the footprint-carrying exit (IH tower, Level 1)

The four pinned leaf sims (`evalIntSimP`/`evalNullSimP`/`evalBoolSimP`/`evalStrSimP`)
conclude `EvalExitPinned` = `EvalExit ∧ LeafMemPin`, and `LeafMemPin.agree` IS the
footprint `noArenaFoot`: outside `[SL.lo, sp) ∪ [sret, sret+24)` the exit memory is
the entry memory.  So every literal leaf is non-allocating at `EvalIHF noArenaFoot`
with no new machine reasoning (`pinnedLeafExitF`).

The `int` leaf runs from `EvalEntry` directly (`evalIntIHF`, unconditional).  The
`null`/`bool`/`str` leaves run from their own entry records; the `EvalEntry → Eval*Entry`
bridges are named premises here (`NullEntryBridge`/`BoolEntryBridge`/`StrEntryBridge`),
each with its supplier named in its doc comment.

The `var` leaf (`evalVarSim`) retains no pin: its `env_get` found-case contract
(`env_get_found_uncond''`, `EnvGetSpec9.lean`) exposes only `c'.σ.mem = m'`, so the
variable leaf is available at `exitFoot` only (`EvalIH.exitFoot`); see
`ih-tower/L1B-una.md` for the missing conjunct.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The leaf memory pin is the `noArenaFoot` footprint (for any arena). -/
theorem MemFootprint.of_leafMemPin {SL : StackLayout} (A : Arena) {sp sret : BitVec 64}
    {m0 m : Mem} (h : LeafMemPin SL sp sret m0 m) :
    MemFootprint (noArenaFoot SL A sp.toNat sret.toNat) m0 m :=
  ⟨fun k hk => h.agree k (fun h1 => hk (Or.inl h1)) (fun h2 => hk (Or.inr h2))⟩

/-- `pinnedLeafExitD` with the pin's footprint retained: a pinned leaf run is a
`noArenaFoot` run. -/
theorem pinnedLeafExitF
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem}
    {Pre : Config → Prop}
    (run : Triple Pre (EvalExitPinned g N A SL phiF phiC st v sp r sret m0))
    (widen : LeafWidenP g N A SL phiF phiC st v sp r sret m0)
    (words : ∀ c, Pre c → ValueWordsTotal m0 sret.toNat) :
    Triple Pre (EvalExitF noArenaFoot g N A SL phiF phiC st.store.frames.size
      st.store.closures.size st v sp r sret m0) := by
  intro c hc
  obtain ⟨after, steps, hp⟩ := run c hc
  exact ⟨after, steps, evalExitD_of_pinnedExit hp widen (words c hc),
    MemFootprint.of_leafMemPin A hp.2⟩

/-- **The `int` leaf at `EvalIHF noArenaFoot`** — unconditional. -/
theorem evalIntIHF (st : Vsa.While.St) (d : Nat) (env : Addr) (n : Int) :
    EvalIHF noArenaFoot st d env (.int n) st (.int n) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => by
    intro c hc
    exact pinnedLeafExitF (evalIntSimP g N A SL φf φc st d env n sp r sret aEnv aExpr m0)
      (leafWidenP_of_entry hc) (fun _ he => he.mem ▸ he.sret_words) c hc)

/-- The `EvalEntry → EvalNullEntry` bridge: the `value_null` callee geometry beyond
`EvalEntry`.  Supplier: the record built in `rows/TermRouting.lean` (`eval_null_row`)
from `nullLeafGeom_discharged` (`rows/Field_hNull.lean`, `EvalEntry.nbs_pins` + the
widened disjointness literals). -/
def NullEntryBridge : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem) (c : Config),
    EvalEntry g N A SL φf φc st d env .null sp r sret aEnv aExpr m0 c →
    EvalNullEntry g N A SL φf φc st d env sp r sret aEnv aExpr m0 c

/-- **The `null` leaf at `EvalIHF noArenaFoot`**, from the entry bridge. -/
theorem evalNullIHF (hB : NullEntryBridge) (st : Vsa.While.St) (d : Nat) (env : Addr) :
    EvalIHF noArenaFoot st d env .null st .null :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => by
    intro c hc
    exact pinnedLeafExitF (evalNullSimP g N A SL φf φc st d env sp r sret aEnv aExpr m0)
      (leafWidenP_of_entry hc) (fun _ _ => hc.mem ▸ hc.sret_words) c
      (hB g N A SL φf φc st d env sp r sret aEnv aExpr m0 c hc))

/-- The `EvalEntry → EvalBoolEntry` bridge: the `value_bool` callee geometry beyond
`EvalEntry`.  Supplier: the record built in `rows/TermRouting.lean` (`eval_bool_row`)
from `boolLeafGeom_discharged` (`rows/Field_hBool.lean`). -/
def BoolEntryBridge (b : Bool) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem) (c : Config),
    EvalEntry g N A SL φf φc st d env (.bool b) sp r sret aEnv aExpr m0 c →
    EvalBoolEntry g N A SL φf φc st d env b sp r sret aEnv aExpr m0 c

/-- **The `bool` leaf at `EvalIHF noArenaFoot`**, from the entry bridge. -/
theorem evalBoolIHF (b : Bool) (hB : BoolEntryBridge b) (st : Vsa.While.St) (d : Nat)
    (env : Addr) :
    EvalIHF noArenaFoot st d env (.bool b) st (.bool b) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => by
    intro c hc
    exact pinnedLeafExitF (evalBoolSimP g N A SL φf φc st d env b sp r sret aEnv aExpr m0)
      (leafWidenP_of_entry hc) (fun _ _ => hc.mem ▸ hc.sret_words) c
      (hB g N A SL φf φc st d env sp r sret aEnv aExpr m0 c hc))

/-- The `EvalEntry → EvalStrEntry` bridge: the `value_str` callee geometry AND the
literal's payload region facts.  Supplier: `EvalStrEntry.of_entry` (`EvalStrSim.lean`)
from the code/slot half of `StrLeafGeom` (discharged, `rows/Field_hStr.lean`
`field_hStr_of_payload`) and the payload half `StrPayloadGeom`, which is open on the
named premise `EvalEntryStrAstRegion` (`rows/Field_hStr.lean`). -/
def StrEntryBridge (s : String) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem) (c : Config),
    EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c →
    EvalStrEntry g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c

/-- **The `str` leaf at `EvalIHF noArenaFoot`**, from the entry bridge: the literal's
payload is read, never written, so the string leaf is non-allocating. -/
theorem evalStrIHF (s : String) (hB : StrEntryBridge s) (st : Vsa.While.St) (d : Nat)
    (env : Addr) :
    EvalIHF noArenaFoot st d env (.str s) st (.str s) :=
  EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => by
    intro c hc
    exact pinnedLeafExitF (evalStrSimP g N A SL φf φc st d env s sp r sret aEnv aExpr m0)
      (leafWidenP_of_entry hc) (fun _ _ => hc.mem ▸ hc.sret_words) c
      (hB g N A SL φf φc st d env sp r sret aEnv aExpr m0 c hc))

#print axioms MemFootprint.of_leafMemPin
#print axioms pinnedLeafExitF
#print axioms evalIntIHF
#print axioms evalNullIHF
#print axioms evalBoolIHF
#print axioms evalStrIHF

end Vsa.Sim
