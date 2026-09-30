import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.EnvCallBridge

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

structure EnvDefineAppendReadback
    (m : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value)
    (cap names vals : Nat) : Prop where
  count : read32 m e = some (vars.length + 1)
  capRead : read32 m (e + 4) = some cap
  capBound : vars.length + 1 ≤ cap
  namesRead : read64 m (e + 8) = some names
  valsRead : read64 m (e + 16) = some vals
  old : ∀ i, (h : i < vars.length) →
    (∃ q, read64 m (names + 8 * i) = some q ∧ CString m q (vars[i].1)) ∧
    ValueRepr m N φc (vals + 24 * i) (vars[i].2)
  parentNone : parent = none → read64 m (e + 24) = some 0
  parentSome : ∀ pa, parent = some pa →
    read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0
  newName : ∃ q, read64 m (names + 8 * vars.length) = some q ∧ CString m q name
  newValue : ValueRepr m N φc (vals + 24 * vars.length) v

theorem EnvDefineAppendReadback.frame
    {m : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {e : Nat} {parent : Option Vsa.While.Addr}
    {vars : List (String × Vsa.While.Value)}
    {name : String} {v : Vsa.While.Value}
    {cap names vals : Nat}
    (h : EnvDefineAppendReadback m N φf φc e parent vars name v cap names vals) :
    FrameRepr m N φf φc e ⟨parent, vars ++ [(name, v)]⟩ :=
  frameRepr_append m N φf φc e parent vars name v cap names vals
    h.count h.capRead h.capBound h.namesRead h.valsRead h.old
    h.parentNone h.parentSome h.newName h.newValue

end Vsa.Sim
