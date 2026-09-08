import Vsa.Sim.rows.EnvDefineEmptyLane

/-!
# `EnvDefineContractSupply` — `EnvDefineContract` from the two ledgers

`EnvDefineContract` (`HelperCallEnvDefine.lean`) is assembled from the landed
lanes, under the two named ledgers per entry:

* hit (`x` bound in the frame): `envDefineUpdateLane_ledger`
  (`rows/EnvDefineContractUpdate.lean`) from `EnvDefineUpdateLedger`;
* miss on a non-empty frame: `envDefineMissLane` (prologue, scan, cap
  dispatch) then `envDefineMissReady_run` (`rows/EnvDefineMissHead.lean`):
  the append arm runs `envDefineAppendLane` (`strlen ≫ malloc ≫ memcpy ≫`
  the append store block `≫` epilogue), the grow arm `envDefineGrowLane`
  (`sw cap'; realloc(names); realloc(values)` over `ReallocOps.grow`, the
  ownership ledger re-seated by `Ledger.replaceArray`/`StoreOwned.replaceArrays`)
  then the append lane;
* miss on the empty frame (`count = 0`): `envDefineEmptyLane`
  (`rows/EnvDefineEmptyLane.lean`): the CAP-INIT block, then the append lane
  (`cap ≠ 0`) or the grow lane's `realloc(NULL,·)` entry (`cap = 0`).

The external facts are `EnvDefineUpdateLedger` and `EnvDefineMissLedger`
(`rows/EnvDefineMissLedger.lean`), each field naming its supplier.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- **`EnvDefineContract` from the two ledgers.** -/
theorem envDefineContract_of_ledgers
    (hU : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
      (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String) (cfg : Config),
      EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out cfg →
      ∃ (gpv : BitVec 64) (headroom maxReq : Nat)
        (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent),
        EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hM : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
      (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String) (cfg : Config),
      EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out cfg →
      ∀ {gpv : BitVec 64} {headroom maxReq : Nat}
        (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent),
        EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts →
        EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    EnvDefineContract := by
  intro g N A SL φf φc st env x v esp aEnv aName pv r m out c h
  obtain ⟨gpv, headroom, maxReq, M, exts, LU⟩ :=
    hU g N A SL φf φc st env x v esp aEnv aName pv r m out c h
  have LM := hM g N A SL φf φc st env x v esp aEnv aName pv r m out c h M exts LU
  have henv : env < st.store.frames.size := h.facts.env_valid
  by_cases hhit : x ∈ st.store.frames[env].vars.map Prod.fst
  · exact envDefineUpdateLane_ledger g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
      LU (fun _ => hhit) c h
  · by_cases hpos : 0 < st.store.frames[env].vars.length
    · obtain ⟨c2, hs2, R⟩ :=
        envDefineMissLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          (EnvDefineUpdateOracles.of_entry h.facts LU) (fun _ => hhit) (fun _ => hpos) c h
      obtain ⟨c3, hs3, hret⟩ :=
        envDefineMissReady_run g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          h.facts LU LM c2 R
      exact ⟨c3, hs2.trans hs3, hret⟩
    · exact envDefineEmptyLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
        h.facts LU LM (fun _ => by omega) c h

#print axioms envDefineContract_of_ledgers

end Vsa.Sim
