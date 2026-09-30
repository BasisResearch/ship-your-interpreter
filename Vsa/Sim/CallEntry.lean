import Vsa.Sim.InductionScaffold
import Vsa.Sim.BlockTerm
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.ConsoleStream
import Vsa.Sim.rows.StoreWF
import Vsa.Sim.HeapOwnershipGeometry

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

local notation "SpecSt" => Vsa.While.St

def ArgVecRepr (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : List Value → Prop
  | [] => True
  | v :: vs =>
      ValueRepr m N φc base v ∧ ArgVecRepr m N φc (base + 24) vs

@[simp] theorem argVecRepr_nil (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : ArgVecRepr m N φc base [] := trivial

theorem argVecRepr_cons (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) (v : Value) (vs : List Value)
    (hv : ValueRepr m N φc base v)
    (hvs : ArgVecRepr m N φc (base + 24) vs) :
    ArgVecRepr m N φc base (v :: vs) := ⟨hv, hvs⟩

def BytesPresent (m : Mem) (base width : Nat) : Prop :=
  ∀ j : Nat, j < width → ∃ b, m[base + j]? = some b

def ArgVecBytes (m : Mem) (base : Nat) (vs : List Value) : Prop :=
  BytesPresent m base (24 * vs.length)

@[simp] theorem argVecBytes_nil (m : Mem) (base : Nat) :
    ArgVecBytes m base [] := by
  intro j hj
  simp at hj

end Vsa.Sim
