import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.HeapOwnershipGeometry
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.rows.EnvDefineEpilogueCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem frameRepr_append (m : Vsa.MemRepr.Mem) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value) (cap pn pv : Nat)

    (hcount : read32 m e = some (vars.length + 1))
    (hcap : read32 m (e + 4) = some cap) (hcapLe : vars.length + 1 ≤ cap)
    (hpn : read64 m (e + 8) = some pn) (hpv : read64 m (e + 16) = some pv)

    (hold : ∀ i, (h : i < vars.length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q (vars[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) (vars[i].2))

    (hparentNone : parent = none → read64 m (e + 24) = some 0)
    (hparentSome : ∀ pa, parent = some pa →
      read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0)

    (hnewName : ∃ q, read64 m (pn + 8 * vars.length) = some q ∧ CString m q x)
    (hnewVal : ValueRepr m N φc (pv + 24 * vars.length) v) :
    FrameRepr m N φf φc e ⟨parent, vars ++ [(x, v)]⟩ := by

  refine ⟨?_, ⟨cap, hcap, ?_⟩, ⟨pn, pv, hpn, hpv, ?_⟩, ?_⟩
  ·
    show read32 m e = some (vars ++ [(x, v)]).length
    rw [define_append_length]; exact hcount
  ·
    show (vars ++ [(x, v)]).length ≤ cap
    rw [define_append_length]; exact hcapLe
  ·
    show ∀ i, (h : i < (vars ++ [(x, v)]).length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q ((vars ++ [(x, v)])[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) ((vars ++ [(x, v)])[i].2)
    intro i hi
    rw [define_append_length] at hi
    by_cases hlt : i < vars.length
    ·
      have hge : (vars ++ [(x, v)])[i] = vars[i]'hlt := define_append_getElem_old vars x v i hlt
      rw [hge]; exact hold i hlt
    ·
      have hieq : i = vars.length := by omega
      subst hieq
      have hge : (vars ++ [(x, v)])[vars.length] = (x, v) := define_append_getElem_new vars x v
      rw [hge]; exact ⟨hnewName, hnewVal⟩
  ·
    cases hpa : parent with
    | none => exact hparentNone hpa
    | some pa => exact hparentSome pa hpa

end Vsa.Sim
